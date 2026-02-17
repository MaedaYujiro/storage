# Time-stamp: <2025-08-29 15:03:59 irumisugimori>
use strict;
my @list;

sub get_list {
    return @list;
}

sub read_list {
    my ($in) = @_;
    @list = ();
    open (IN, "$in") || die;
    while(<IN>) {
	tr/\n\r//d;
	next if /^#/;
	next if /^\s*$/;
	my @val = split(/\s+/, $_);
	foreach (@val) {
	    s/^\s+//;
	    s/\s+$//;
	}
	push(@list, \@val);
    }
    close(IN) || die;
}

sub read_log {
    my ($log) = @_;
    my %result;
    $result{'TIMELIMIT'} = 0;
    $result{'Iterations'} = 0;
    open(LOG, "<$log") || die;
    my $state = -1;
    my $initial_cost = "-";
    while (<LOG>) {
	tr/\n\r//d;
	if (/^\s*$/) {
	    next;
	}

	if ($state == -1) {
	    if (/^Optimization: (-?\d+)$/) {
		$initial_cost = $1;
	    } elsif (/^Optimization: (-?\d+) (-?\d+) (-?\d+)/) {
		$initial_cost = "$1,$2,$3";
	    } elsif (/Iteration:? 1/) {
		$state = 0;
		$result{'InitialCost'} = $initial_cost;
	    }
	}
	
	if ($state <= 0) {
	    if (/^(SATISFIABLE)/) {
		$result{'RESULT'} = $1;
		$state = 1;
	    } elsif (/^(UNSATISFIABLE)/) {
		$result{'RESULT'} = $1;
		$state = 1;
	    } elsif (/^(UNKNOWN)/) {
		$result{'RESULT'} = $1;
		$state = 1;
	    } elsif (/^(OPTIMUM FOUND)/) {
		$result{'RESULT'} = $1;
		$state = 1;
	    } elsif (/^s (?:\[.*?\] )?(SATISFIABLE)/) {
		$result{'RESULT'} = $1;
		$state = 2;
	    } elsif (/^s (?:\[.*?\] )?(UNSATISFIABLE)/) {
		$result{'RESULT'} = $1;
		$state = 2;
	    } elsif (/^s (?:\[.*?\] )?(UNKNOWN)/) {
		$result{'RESULT'} = $1;
		$state = 2;
	    } elsif (/^s (?:\[.*?\] )?(OPTIMUM FOUND)/) {
		$result{'RESULT'} = $1;
		$state = 2;
	    } elsif(/^Costs: (-?\d+)$/) {
		$result{'Optimization'} = $1;
	    } elsif(/^Costs: \[-?(\d+), (-?\d+), (-?\d+)\]/) {
		$result{'Optimization'} = "$1,$2,$3";
	    } elsif(/^Cost: (-?\d+)$/) {
		$result{'Optimization'} = $1;
	    } elsif(/^Cost: \[-?(\d+), (-?\d+), (-?\d+)\]/) {
		$result{'Optimization'} = "$1,$2,$3";
	    } elsif(/cost: (-?\d+)$/) {
		$result{'Optimization'} = $1;
	    } elsif(/cost: \[-?(\d+), (-?\d+), (-?\d+)\]/) {
		$result{'Optimization'} = "$1,$2,$3";
	    } elsif (/OPTIMAL SOLUTION FOUND/) {
		$result{'RESULT'} = "OPTIMUM FOUND";
	    }
	}
	
	if ($state >= 1) {
	    if (/^Models\s*: (\S+)/) {
		$result{'Models'} = $1;
	    } elsif (/^Calls\s*: (\S+)/) {
		$result{'Calls'} = $1;
	    } elsif (/^CPU Time\s*: (\S+)s/) {
		$result{'CPUTime'} = $1;
	    } elsif (/^Choices\s*: (\d+)/) {
		$result{'Choices'} = $1;
	    } elsif (/^Conflicts\s*: (\d+)/) {
		$result{'Conflicts'} = $1;
	    } elsif (/^Restarts\s*: (\d+)/) {
		$result{'Restarts'} = $1;
	    } elsif (/^Variables\s*: (\d+)/) {
		$result{'Variables'} = $1;
	    } elsif (/^Constraints\s*: (\d+)/) {
		$result{'Constraints'} = $1;
	    } elsif (/^Time\s*: (\S+)s/) {
		$result{'Time'} = $1;
	    }
	}
	
	if ($state == 1) {
	    if (/^TIME LIMIT\s*: (\d+)/) {
		$result{'TIMELIMIT'} = $1;
	    } elsif (/^\s+Optimum\s*: (\w+)/) {
		$result{'Optimum'} = $1;
	    } elsif (/^\s*Optimization\s*: (-?\d+)$/) {
		$result{'Optimization'} = $1;
	    } elsif (/^\s*Optimization\s*: (-?\d+) (-?\d+) (-?\d+)/) {
		$result{'Optimization'} = "$1,$2,$3";
	    }
	}
	
	if ($state == 2) {
	    if (/^INTERRUPTED\s*: (\d+)/) {
		$result{'TIMELIMIT'} = $1;
	    } elsif (/^c Optimum: (\w+)/) {
		$result{'Optimum'} = $1;
	    } elsif (/^a (?:\[.*?\] )?Optimization: (-?\d+)$/) {
		$result{'Optimization'} = $1;
	    } elsif (/^a (?:\[.*?\] )?Optimization: (-?\d+) (-?\d+) (-?\d+)/) {
		$result{'Optimization'} = "$1,$2,$3";
	    } elsif (/^c (?:\[.*?\] )?Iterations: (\d+)/) {
		$result{'Iterations'} = $1;
	    }
	}
    }
    close(LOG);
    $result{'RESULT'} =~ s/ISFIABLE//;
    $result{'RESULT'} =~ s/UNKNOWN/UNKN/;
    $result{'RESULT'} =~ s/OPTIMUM FOUND/OPTIMUM/;
    return %result;
}

sub read_chk {
    my ($chk) = @_;
    my %result;
    open(CHK, "<$chk") || die;
    while (<CHK>) {
	tr/\n\r//d;
	if (/^\s*$/) {
	    next;
	} elsif (/^Summary: Total Cost = (\d+)/) {
	    $result{'Optimization'} = $1;
	}
    }
    close(CHK);
    return %result;
}

sub make_file_name {
    my ($dir, @x) = @_;
    return "$dir/" . join("__", @x);
}

1;
