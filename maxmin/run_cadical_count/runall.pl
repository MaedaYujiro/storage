#!/usr/bin/perl
use Getopt::Long;
use strict;
use lib qw(./);
require "samprunall.pl";
$| = 1;

# Time-stamp: <2025-12-12 23:42:16 nishimoriken>

##########################################################################
# edit
##########################################################################

### Timeout (sec.)
#my $timeout = 10;
#my $timeout = 60;
#my $timeout = 3*60;
#my $timeout = 5*60;
#my $timeout = 10*60;
#my $timeout = 15*60;
#my $timeout = 16*60;
my $timeout = 30*60;
#my $timeout = 1*60*60;
#my $timeout = 2*60*60;
#my $timeout = 3*60*60;
#my $timeout = 24*60*60;

### ASP encoding

### Solver
my %solver = ();
$solver{"mds-basic"} = "gtime -v gtimeout $timeout ./target/release/maxmin_cadical mds-basic";
$solver{"mds-trans"} = "gtime -v gtimeout $timeout ./target/release/maxmin_cadical mds-trans";
$solver{"mis-basic"} = "gtime -v gtimeout $timeout ./target/release/maxmin_cadical mis-basic";
$solver{"mis-trans"} = "gtime -v gtimeout $timeout ./target/release/maxmin_cadical mis-trans";

### Others
my $date  = "/bin/date";
my $time  = "/usr/bin/time";

##########################################################################

### Options
my ($opt_n, $opt_h, $opt_d);
&GetOptions('n|noexec' => \$opt_n, 'h|help' => \$opt_h, 'd|dir=s' => \$opt_d);
if ($opt_h) { &usage(); }

### Inputs
die if (@ARGV != 1 || ! -e $ARGV[0]);
my $input = $ARGV[0];

### Outputs
my $timestamp = `$date "+%Y-%m-%d-%H-%M"`;
chomp($timestamp);
my $prefix = "result/$timestamp";
if ($opt_d) {
    $prefix = $opt_d;
}
my $log_dir = "$prefix/log";
my @dirs = ($log_dir);
my $copy_input  = "$prefix/BENCH.csv";

### Main
&exec("mkdir -p $prefix");
&exec("cp $input $copy_input");
foreach my $d (@dirs) {
    if (! -e $d) {
	&exec("mkdir -p $d");
    }
}

&read_list($input);
my @list = &get_list();

print "\nSTART solving problems in $input\n";
foreach my $p (@list) {
	foreach my $s (keys %solver) {
	    &solve($p,  $s);
	
    }
}
print "FINISH solving problems in $input\n";
print "See $prefix\n";

exit 0;

sub solve {
    my ($p,   $slv) = @_;
    my ($problem, $col1, $col2) = @{$p};
    my $log = &make_file_name($log_dir, $problem,   $slv) . ".log";
    my $id  = join(" ", ($problem,   $slv));
    my $skip = 0;
    if (-e $log) {
	$skip = 1;
	my %r = &read_log($log);
	foreach my $x (keys %r) {
	    print "$x:\t" . $r{$x} . "\n";
	}
	if (! $r{'RESULT'}) {
	    $skip = 0;
	} elsif ($r{'TIMELIMIT'} && $r{'Time'} < $timeout) {
	    $skip = 0;
	}
    }
    if ($skip) {
	print "# skip $id\n";
	next;
    }
    print "BEGIN $id [", scalar(localtime), "]\n";
    &run($col1, $col2,   $slv, $log);
    print "END $id [", scalar(localtime), "]\n";
    print "\n";
}

sub run {
    my ($col1, $col2, $slv, $log) = @_;
    my $cmd2 = join(" ", ($solver{$slv}, $col1, $col2));
    my $full_cmd = "$cmd2 > $log 2>&1 < /dev/null";
    print "Running: $full_cmd\n";
    # print "$cmd2\n";
    if ($opt_n) {
	return;
    }
    # open(LOG, ">$log") || die("$!");
    # my $old = select; select(LOG); $| = 1; select($old);
    # open(CMD, "$cmd2 2>&1 |") || die;
    # while (<CMD>) {
	# print LOG $_;
	# if (/^(\d+)/) {
	#     print $1."\n";
	# } elsif (/^Command exited/) {
	#     print $_;
	# } elsif (/User time/) {
	#     print $_;
	# } elsif (/System time/) {
	#     print $_;
	# } elsif (/Elapsed/) {
	#     print $_;
	# } elsif (/\*\*\*/) {
	#     print $_;
	# }
    # }
    # close(CMD);
    # close(LOG);
    system($full_cmd);
}

sub exec {
    my ($cmd) = @_;
    print "$cmd\n";
    if (! $opt_n) {
	system($cmd);
    }
}

sub usage {
    print "\nUsage: $0 [options] benchmark.csv\n";
    print "\nParameters:\n";
    print "\t-h  : print this help\n";
    print "\t-n  : no exec\n";
    print "\t-d  : specify a prefix directory\n";
    print "\n";
    exit(1);
}
