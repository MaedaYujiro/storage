\ProvidesClass{abstB}[2005/02/04 v1.7 abstractB class]
% 名古屋大学情報学部
% コンピュータ科学科卒業論文要旨 TeXフォーマット
%
% Ver1.0: 2020/12/09 by Ryohei Sasano
%   名古屋大学大学院工学研究科
%   情報工学コース卒業研究報告要旨 TeXフォーマット を改変
%
% Ver1.0: 2007/11/04 by Ichiro IDE
% changed to H19
%
% Ver1.8: 2006/11/16 by Ichiro IDE
% changed to H18
%
% Ver1.7: 2005/02/04 by KUSAKARI Keiichirou
%
% Ver1.4: 2005/01/26 by KUSAKARI Keiichirou
%   利用しやすいように呼び込む{クラス,スタイル}ファイルを一つにまとめた
% 
% (C) Shoji Yuen (Nagoya University)
% $Id: abstM2.tex,v 1.3 2002/01/21 13:58:41 yuen Exp $
%
% $Log: abstM2.tex,v $
% Revision 1.3  2002/01/21 13:58:41  yuen
% change to H13
%
% Revision 1.2  2001/01/10 09:42:01  yuen
% parameters are finalized
%
% Revision 1.1  2001/01/10 09:13:52  yuen
% Initial revision
%
% Revision 1.1  2001/01/10 08:58:46  yuen
% Initial revision
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\LoadClass[12pt]{jarticle}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% teikei.cls を取り込んでます
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\ProvidesClass{teikei}[2000/11/03]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%
%%%%%%%	定型的書式に文書をはめ込むためのclass Ver 0.96
%%%%%%%        1994/10/15
%%%%%%%        1997/02/02  Ver 0.9 for pLaTeX2e
%%%%%%%        1997/02/07  Ver 0.91 offset bug fixed 
%%%%%%%                     by masahide@mk.ecei.tohoku.ac.jp
%%%%%%%        1997/02/09  Ver 0.92 XYSETGBP and XYPBP added
%%%%%%%        1997/03/27  Ver 0.93 Brule, Vruledash Hruledash added
%%%%%%%                     from 科研マクロ
%%%%%%%        1997/03/28  Ver 0.94 line pointを変数化
%%%%%%%	       1998/09/16  Ver 0.95 Drule bug fixed and line width added
%%%%%%%        2000/11/03  Ver 0.96 Hruledash/Vruledash bug fixed
%%%%%%%			    by sawai@nike.mech.osaka-sandai.ac.jp
%%%%%%%                     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% このstyle fileはもともと科研費調書（A4サイズ新版）として配布されていた
% ものです．
% このバージョンはLaTeX2e専用です．
%
%	by Level3 	hagihira@anes.med.osaka-u.ac.jp
%			PGB00174@niftyserve.or.jp 
%	以下の方々の作成です．
%%%%%%%        Ken-Ichi Aoki (aoki@hep.s.kanazawa-u.ac.jp)
%%%%%%%        Taikan Oki    (taikan@hydro.iis.u-tokyo.ac.jp)
%%%%%%%        Shinichi Nawa (nawa@ps1.yukawa.kyoto-u.ac.jp)
%%%%%%%        Toru Sato     (tsato@ibuki.kuee.kyoto-u.ac.jp)
%%%%%%%  File ID: KAKENHI.STY 基本スタイルファイル (LaTeX版)
%%%%%%%        1993/11/5
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%\LoadClassWithOptions{jarticle}
%
\newdimen\INDENT	% 段落開始位置(文字数)
%
\newcount\DPI\DPI=300
%
\INDENT=0zw
%
%  使用するプリンタのＤＰＩを下でセットして下さい．斜線を最適に印刷する
%  ためのパラメタです．
\DPI=300
%
\newif\if枠表示\枠表示true
\def\FRAMEON{\枠表示true}%with rules and item names
\def\FRAMEOFF{\枠表示false}%without rules nor item names
%
% working variables
%
\newbox\dummybox
\newbox\partbox
\newcount\Ta \Ta=0
\newcount\Tb \Tb=0
\newcount\Tc \Tc=0
\newcount\Td \Td=0
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newif\ifSmallTeX\SmallTeXfalse
% BigLaTeX でない LaTeX を使用する場合は，次のコメントをはずして下さい．
% ただし，その場合は斜線および長円は描かれません．
%\SmallTeXtrue
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newif\ifNTTTeX\NTTTeXfalse
\def\NTTTeX用{\NTTTeXtrue}
%
%NTT-TeXの場合は以下の５つの命令を有効にして下さい．
%このNTT-TeXへの対応は
%電気通信大学電子工学科 伊藤 秀一  itoh@ee.uec.ac.jp
%によります． 
%このLaTeX2e専用のバージョンでは動かないかもしれませんし，
%不要かもしれません．
%
%\NTTTeX用
%\newskip\kanjiskip
%\newskip\xkanjiskip
%\let\kanjiskip=\jintercharskip
%\let\xkanjiskip=\jasciikanjiskip
%
\pagestyle{empty}
\oddsidemargin=0mm
\evensidemargin=0mm
\textwidth=\paperwidth
\topmargin=0mm
\headheight=0pt
\headsep=0pt
\textheight=\paperheight
%
\let\@document=\document
\def\document{\@document\teikeistyle}

% global advance
\def\Advance{\global\advance}
% various skips
%
\def\smallbaselineskip{\baselineskip=2.0mm}
\def\eightbaselineskip{\baselineskip=3.6mm}
\def\sevenbaselineskip{\baselineskip=2.4mm}
\def\sixbaselineskip{\baselineskip=2.1mm}
%\def\bunshobaselineskip{\baselineskip=5.4mm plus0.2mm minus0.15mm}
%\def\lkanjiskip{\kanjiskip=2.5pt plus 1pt minus 0.5pt}
%\def\llkanjiskip{\kanjiskip=5pt plus 2pt minus 2pt}
\def\lllkanjiskip{\kanjiskip=8pt plus 2pt minus 2pt
\xkanjiskip=8pt plus 2pt minus 2pt}
\def\kintokanjiskip{\kanjiskip=0pt plus 1fil minus 1fil%
\xkanjiskip=\kanjiskip}
%\def\msuji{\tenmin\kanjiskip=0.0pt}
%\def\lsuji{\twelvemin\kanjiskip=0.0pt}
%\def\llsuji{\twelvemin\kanjiskip=11pt}
%\def\hsuji{\twelvemin\kanjiskip=11.2pt}
%
% 文章入力のスタイル
\def\bunshostyle{
%  \bunshobaselineskip
   \linewidth=\hsize
%   \parindent=1zw
   \parindent=\INDENT % changed by Level3
   \parskip=1.0mm plus 0.5mm minus 1mm
   \rightskip=0pt
   \kanjiskip=0pt plus0.3pt
}
%
%magic way of pointing a place defined by X-Y coordinate
\newdimen\htbackskip
\newdimen\dpbackskip
\long\def\XY#1#2#3{
  \setbox\dummybox=\vbox{
    \vskip#2
    \vskip\voffset % by masahide@mk.ecei.tohoku.ac.jp
    \hbox to \hsize{%
      \hskip#1
      \hskip\hoffset % by masahide@mk.ecei.tohoku.ac.jp
      \vbox{\advance\hsize by -#1#3}\hfil
    }
  }
  \htbackskip=-\ht\dummybox
  \dpbackskip=-\dp\dummybox
%
  \box\dummybox\nointerlineskip
  \vskip\htbackskip
  \vskip\dpbackskip
%  \box\sepinbox\nointerlineskip
}
%
%A box with something centered both horizontally and vertically
%\def\Cbox#1#2#3{
%   \vbox to #2mm{
%      \vfil
%      \hbox to #1mm{\hfil#3\hfil}
%      \vfil
%   }
%}
% 絶対位置　(#1, #2) (#3, #4)で定まるボックスに
% #5 を入れて上下左右でセンタリングする．
\long\def\XYBC#1#2#3#4#5{
  \X=#3 \Y=#4 \advance\X by -#1 \advance\Y by -#2
  \XY{#1}{#2}{\CBOX{\X}{\Y}{#5}}
}
% BOX を描く．縦横にセンタリングされる．#1, #2引数は長さで与える
% 箱の横の長さ，縦の長さ，中身
%\long\def\CBOX#1#2#3{
%   \vbox to #2{
%      \vfil
%      \hbox to #1{\hsize=#1\hfil#3\hfil}
%      \vfil
%   }
%}
%%%%
\long\def\CBOX#1#2#3{{
  \hsize=#1\linewidth=\hsize
  \setbox\dummybox\hbox{#3}
  \vbox to #2{
    \vfil
    \ifdim#1 < \wd\dummybox
      \X=#1
      \advance\X by -4mm
      \hbox to \hsize{\hfil\vbox{\hsize=\X\linewidth=\hsize #3}\hfil}
    \else
      \hbox to \hsize{\hfil #3\hfil}
    \fi
    \vfil
  }
}}
%
% 絶対位置　(#1, #2) (#3, #4)で定まるボックスに
% パラグラフとして#5 を入れる．マージン（両側）はXM, YM で決まる．
\long\def\XYBP#1#2#3#4#5{
  \X=#3 \Y=#4 \advance\X by -#1 \advance\Y by -#2
  \XY{#1}{#2}{\PBOX{\X}{\Y}{#5}}
}
\long\def\PBOX#1#2#3{
   \X=#1 \Y=#2 \advance\X by -\XM \XA=\X \advance\X by -\XM
               \advance\Y by -\YM \YA=\Y \advance\Y by -\YM
   \vbox to \YA{\vskip\YM
   \hbox to \XA{\hskip\XM\vbox to \Y{\hsize=\X\linewidth=\X #3\vfil}%
   \hfil}
}}
%
% サイズ #1 x #2 で定まるグローバルボックス#4に
% パラグラフとして#3 を入れる．マージン（両側）はXM, YM で決まる．
\long\def\XYSETGBP#1#2#3#4{
  \X=#1 \Y=#2
  \advance\X by -\XM \advance\X by -\XM
  \global\setbox#4=\vbox{\hsize=\X\linewidth=\X #3\vfil}%
}
%
% XYSETGBPで作製したBOX#4を絶対位置　(#1, #2)から高さ#3だけ入れる
%
\long\def\XYPBP#1#2#3#4{
  \YA=#3 \advance\YA by -\YM \advance\YA by -\YM
  \global\setbox\partbox=\vsplit#4 to \YA%
  \X=#1 \Y=#2 \advance\X by \XM \advance\Y by \YM
  \XY{\X}{\Y}{\box\partbox\vfil}%
}
%
% 右詰めボックス
\def\RBOX#1{\hbox to \hsize{\hfil#1}}
% 数字用ボックス（コンマ処理付き）
\def\NBOX#1{\hbox to \hsize{\hfil\Number{#1}}}
%
% \hsizeをセットするマクロ 両端x座標 #1, #2, 両側からのマージン #3
\def\SEThsize#1#2#3{%
\hsize=#2 \advance\hsize by -#1%
\advance\hsize by -#3 \advance\hsize by -#3}
%
%ボックスをつぶさないための横方向の見えない柱
\def\SS{\vskip0pt\hrule width\hsize height0pt depth0pt}
%
% 数字をローカルに足す。空白なら足さない。
\def\Add#1#2{\def\DUMMY{#2}\ifx\DUMMY\empty\else\advance#1 by#2\fi}
%
%BOX rules with 1.0pt width
% 箱型罫線　右下隅の欠けを防ぐためのマクロ
% 対角線指定　(#1, #2) --- (#3, #4)
% #5 line point
\def\Brule#1#2#3#4#5{
   \X=#4 \Add{\X}{#5}
   \Hrule{#1}{#2}{#3}{#5}
   \Hrule{#1}{#4}{#3}{#5}
   \Vrule{#1}{#2}{#4}{#5}
   \Vrule{#3}{#2}{\X}{#5}
}
%
%vertival rule
% 縦罫線　0.1pt 幅　始点座標　(#1, #2) 終点Ｙ座標 #3 線の太さ #4
\newdimen\rulelength
\def\Vrule#1#2#3#4{
   \rulelength=#3
   \advance\rulelength by -#2
   \XY{#1}{#2}{\vrule width#4 height\rulelength depth0pt}
}
%
%horizontal rule
% 横罫線　0.1pt 幅　始点座標　(#1, #2) 終点Ｘ座標 #3 線の太さ #4
\def\Hrule#1#2#3#4{
   \rulelength=#3
   \advance\rulelength by -#1
   \XY{#1}{#2}{\vrule width\rulelength height#4 depth0pt}
}
%
%vertical dotted
% 縦鎖罫線　始点座標　(#1, #2) 終点Ｙ座標 #3 幅 #4
\def\Vruledash#1#2#3#4{{
   \rulelength=#3
   \advance\rulelength by -5pt
   \loop\ifdim\rulelength>#2\XY{#1}{\rulelength}{\vrule
     height 2pt depth0pt width#4}
   \advance\rulelength by -5pt\repeat
}}
% dotted rule
% 横鎖罫線　始点座標　(#1, #2) 終点Ｘ座標 #3 幅 #4
\def\Hruledash#1#2#3#4{{
   \rulelength=#3
   \advance\rulelength by -5pt
   \loop\ifdim\rulelength>#1\XY{\rulelength}{#2}{\vrule
     height#4 depth0pt width 2pt}
   \advance\rulelength by -5pt\repeat
}}
%
% 文字数，行数単位のスキップ
% hskip #1 zw, vskip #1 baselineskip
%
\long\gdef\Sz#1{\hskip #1zw}
\long\gdef\Sb#1{\vskip #1\baselineskip}
%
% print asterisk
%
\long\gdef\ASTER{\lower0.6ex\hbox{*}}
%
%%%%
% underline
\def\undertext#1{\vtop{\hbox{#1}\kern 1pt \hrule}}
%
%%%%
% contributed by T. Sato (Kyoto U)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%
% kinto{size}{KANJI TEXT}
\def\kinto#1#2{\hbox to #1{\kintokanjiskip#2}}
%
% \maru{x} : encircled number x (should be 1digit), easy version
% \maru{x} is replaced to \textcircled{x} in original pLaTeX2e
%%%%
% \Number{number} : 数字の３桁毎にコンマを入れるマクロ（９桁まで）
\newif\ifコンマ付数字 \コンマ付数字true
\def\コンマ付数字{\コンマ付数字true}
\def\コンマなし数字{\コンマ付数字false}
\newcount\Numa
\newcount\Numb
\def\Numempty{}%文字列「-0」が与えられると空白を出力する
\def\Number#1{\edef\Numpar{#1}\ifx\Numempty\Numpar\else%
\ifコンマ付数字\Numa=#1\relax
\ifnum\Numa>999999\divide\Numa by 1000000
\number\Numa,%
\multiply\Numa by -1000000\advance\Numa by #1\relax
\Numb=\Numa\divide\Numa by 1000
\ifnum\Numa<100 \ifnum\Numa<10 0\fi0\fi\number\Numa,%
\multiply\Numa by -1000\advance\Numa by \Numb
\ifnum\Numa<100 \ifnum\Numa<10 0\fi0\fi\number\Numa%
\else\ifnum\Numa>999\divide\Numa by 1000
\number\Numa,%
\multiply\Numa by -1000\advance\Numa by #1\relax
\ifnum\Numa<100 \ifnum\Numa<10 0\fi0\fi\number\Numa%
\else\number\Numa\fi\fi\else\number#1\fi\fi}
%------------------------------------------------------------------------
%
% #2 から #3 までに横罫線を引く．罫線入りのボックスは#1におく．
% 縦位置は呼ばれた時の位置
\def\横区分線#1#2#3{\X=#3\advance\X by -#1%
\hbox to \X{\hfil\X=#3\advance\X by -#2%
\vrule width\X height0.1pt depth0pt}}
%
% 位置の最終調整用変数
\newdimen\HOFFSET \HOFFSET=0mm
\newdimen\VOFFSET \VOFFSET=0mm
% 印刷位置決めを偶奇頁で区別するためのパラメータ
% \doubleHOFFSET は偶奇で逆にずらす．
\newdimen\oddHOFFSET \oddHOFFSET=0mm
\newdimen\evenHOFFSET \evenHOFFSET=0mm
\newdimen\doubleHOFFSET \doubleHOFFSET=0mm
%
%各頁毎に呼ばれる位置調整コマンド
\def\OFFSET{
  \advance\hoffset by \HOFFSET
  \ifodd\count0
    \advance\hoffset by \oddHOFFSET
    \advance\hoffset by \doubleHOFFSET
  \else
    \advance\hoffset by \evenHOFFSET
    \advance\hoffset by -\doubleHOFFSET
  \fi
  \advance\voffset by \VOFFSET
}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 任意の２点に罫線（含む斜線）を引く aoki 93/10/30
%   \Drule{#1}{#2}{#3}{#4}{#5}
%     (#1,#2) --> (#3,#4)  太さは変数#5で与える．
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%以下では，Ｙの正方向は下，Ｘの正方向は右である．
%SmallTeX では定義しない．
\newif\ifSTEEP% 勾配の絶対値が１より大かどうか
\newif\ifVERTICAL% 垂直罫線かどうか
\newif\ifHORIZONTAL% 水平罫線かどうか
\newif\ifREVERSE% Ｙ変位を正にした時にＸ変位が負
\newcount\LOOPcount% loop counter
\newdimen\DOTsize
\newdimen\DW
\newdimen\DH
\newdimen\Xstep% 正負あり
\newdimen\Ystep
\newdimen\Xdiff% 正に固定
\newdimen\DX
\newdimen\DruleThickness \DruleThickness=0.1pt
\newdimen\DruleSize
%
\ifSmallTeX
 \def\Drule#1#2#3#4#5{}
\else
%
 \def\Drule#1#2#3#4#5{{%
%
% まずＹ方向変位を正にセット．(X,Y) ---> (XA,YA)  YA > Y
\DruleThickness=#5
\ifdim#2 > #4
  \X=#3\Y=#4\XA=#1\YA=#2
\else
  \X=#1\Y=#2\XA=#3\YA=#4
\fi
%
% 罫線のＸ方向とＹ方向の変位．この段階ではＤＷは正負あり．
\DW=\XA \advance\DW by -\X
\DH=\YA \advance\DH by -\Y
%
% 垂直または水平の罫線かどうかのチェック，別処理をする．
\VERTICALfalse\HORIZONTALfalse
\ifdim\DW=0cm
  \ifdim\DH=0cm \errmessage{Null Drule ...}\else\VERTICALtrue\fi
\else\ifdim\DH=0cm \HORIZONTALtrue\fi\fi
%
\ifVERTICAL
%  \message{DiagonalRule (\the\X,\the\Y)-->(\the\XA,\the\YA) by vrule
%  Thickness \the\DruleThickness }%
  \message{Drule:1seg }%
  \XY{\X}{\Y}{\noindent\vrule width\DruleThickness height\DH depth0pt}
\else\ifHORIZONTAL% Ｘ方向を正にセットし直す必要がある．
%  \message{DiagonalRule (\the\X,\the\Y)-->(\the\XA,\the\YA) by hrule
%  Thickness \the\DruleThickness }%
  \message{Drule:1seg }%
  \ifdim\DW < 0cm \X=\XA \multiply\DW by -1 \fi
  \XY{\X}{\Y}{\noindent\vrule width\DW height\DruleThickness depth0pt}
\else% 以下すべてがこの場合である．
%
% 勾配の絶対値が１より大きい時には，STEEPtrueをセット
\STEEPfalse
\ifdim\DW < \DH \ifdim\DW > -\DH \STEEPtrue \fi\fi
%
% DW < 0 の時にはREVERSEtrueをセット．
% これ以降，DW も正に固定．
\REVERSEfalse
\ifdim\DW < 0cm \REVERSEtrue \multiply\DW by -1 \fi
%
% 罫線の太さの補正．
\Ta=\DH \divide\Ta by 100
\Tb=\DW \divide\Tb by 100
% 100 倍の tanθ(Tc) を計算．
\ifSTEEP
  \multiply\Tb by 100 \divide\Tb by \Ta \Tc=\Tb
\else
  \multiply\Ta by 100 \divide\Ta by \Tb \Tc=\Ta
\fi
% 補正因子(Td)は cosθ とするが，１から１/ルート２まで動く．
% この区間を７区間に分けて補正する．
%
\ifnum     \Tc < 23 \Td=100
\else\ifnum\Tc < 41 \Td= 95
\else\ifnum\Tc < 55 \Td= 90
\else\ifnum\Tc < 69 \Td= 85
\else\ifnum\Tc < 82 \Td= 80
\else\ifnum\Tc < 95 \Td= 75
\else               \Td= 71
\fi\fi\fi\fi\fi\fi
%
\DruleSize=\DruleThickness
\multiply\DruleSize by 100 \divide\DruleSize by \Td
%
%
% ＤＰＩに対応する１ドットのサイズ
\DOTsize=1in \divide\DOTsize by \DPI \Ystep=\DOTsize
%
% ステップ数（セグメント数）（正に固定）を決める．
% 勾配が１以下の場合はＹ変位から，１以上の場合はＸ変位から決める．
% （太い罫線の場合には）罫線の太さ１セグメント分の補正が必要．
% 相手側の１ステップ変位は，全変位をステップ数で割って得る．
\ifSTEEP
  \LOOPcount=\DW \advance\LOOPcount by -\DruleSize
  \divide\LOOPcount by \DOTsize \advance\LOOPcount by 1
  \Xstep=\DOTsize
  \Ystep=\DH \divide\Ystep by \LOOPcount
\else
  \LOOPcount=\DH \advance\LOOPcount by -\DruleSize
  \divide\LOOPcount by \DOTsize \advance\LOOPcount by 1
  \Ystep=\DOTsize
  \Xstep=\DW \divide\Xstep by \LOOPcount
\fi
%
% REVERSEの時にはXstepを負にセット．絶対値をXdiffにキープ．
\Xdiff=\Xstep
\ifREVERSE\multiply\Xstep by -1 \fi
%
%\message{DiagonalRule (\the\X,\the\Y)-->(\the\XA,\the\YA) by
%(\the\Xstep,\the\Ystep) Thickness \the\DruleSize (\number\Td) }
\message{Drule:\number\LOOPcount segs }
%
% セグメントの初期位置=DX のセット
%
\ifREVERSE
  \DX=\DW
  \ifSTEEP\advance\DX by -\DruleSize\fi%罫線幅戻し
  \advance\DX by \Xdiff%右端から更に１ステップ分右
  \X=\XA% REVERSE 時には，ＸＹボックス命令の左上はXAで与えられる
\else
  \DX=0cm
\fi
%
\XY{\X}{\Y}{%
\advance\LOOPcount by 1
\loop
  \advance\LOOPcount by -1
  \advance\DX by \Xstep
  \ifnum\LOOPcount > 0%
    \vbox to \ifSTEEP\Ystep\else\DruleSize\fi
      {\hsize=\DW\hbox to \DW{%
      \X=\DX\advance\X by -\Xdiff%
        \hskip\X
        \vrule height\ifSTEEP\Ystep\else\DruleSize\fi
               depth0pt
               width\ifSTEEP\DruleSize\else\Xdiff\fi
        \hfill
    }}%
    \ifSTEEP\else\vskip-\DruleSize\vskip\Ystep\fi
    \nointerlineskip%
\repeat
}
\fi\fi% 垂直または水平罫線の別処理のＩＦの終わり
}}
\fi

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dummy definitions for compatibility with plain TeX version
\newcount\pageno
\newtoks\footline
\newdimen\itemsize
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 軽量化の試み
\let\vpt=\relax
\let\viipt=\relax
\let\ixpt=\relax
\let\xviipt=\relax
\let\xxpt=\relax
\let\xxvpt=\relax
%
\let\@starttoc=\relax
\let\addcontentsline=\relax
\let\addtocontents=\relax
\let\contentsline=\relax
\let\@dottedtocline=\relax
\let\numberline=\relax
\let\makeindex=\relax
\let\@wrindex=\relax
\let\index=\relax
\let\@index=\relax
\let\makeglossary=\relax
\let\glossary=\relax
\let\bibitem=\relax
\let\@lbibitem=\relax
\let\@bibitem=\relax
\let\bibcite=\relax
\let\citation=\relax
\let\cite=\relax
\let\@citex=\relax
\let\bibliography=\relax
\let\bibliographystyle=\relax
\let\nocite=\relax
\let\caption=\relax
\let\@caption=\relax
\let\@float=\relax
\let\@xfloat=\relax
\let\end@float=\relax
\let\@dblfloat=\relax
\let\@dbflt=\relax
\let\@xdblfloat=\relax
\let\@floatplacement=\relax
\let\@dblfloatplacement=\relax
\let\marginpar=\relax
\let\@xmpar=\relax
\let\@ympar=\relax
\let\@savemarbox=\relax
\let\@xympar=\relax
\let\reversemarginpar=\relax
\let\normalmarginpar=\relax
% simplify the output routine
\output{\let\par\@@par
  \ifnum\outputpenalty <-\@M\@specialoutput\else
  \begingroup\catcode`\ =10
     \let\-\@dischyph \let\'\@acci \let\`\@accii \let\=\@acciii
     \shipout
     \vbox{%\reset@font %% RmS 91/08/15
           \normalsize \baselineskip\z@ \lineskip\z@
           \let\par\@@par %% 15 Sep 87
           \vskip\topmargin \moveright\@themargin
           \vbox{\vskip \headsep
                 \box255}}\global\@colht\textheight
  \endgroup\stepcounter{page}\let\firstmark\botmark\fi
  \global\vsize\ifnum\outputpenalty >-\@Miv \@colroom
                  \else \maxdimen\fi}
%%\let\@specialoutput=\relax
\def\@doclearpage{
        \setbox\@tempboxa\vsplit\@cclv to\z@ \unvbox\@tempboxa
        \setbox\@tempboxa\box\@cclv
}
\let\@freelist=\relax
\let\@toplist=\relax
\let\@botlist=\relax
\let\@midlist=\relax
\let\@currlist=\relax
\let\@deferlist=\relax
\let\@dbltoplist=\relax
\let\@dbldeferlist=\relax
% \let\@dbltopnum=\relax
\let\@dbltoproom=\relax
\let\@textmin=\relax
\let\@fpmin=\relax
\let\@mparbottom=\relax
\let\@currtype=\relax
\let\cleardoublepage=\relax
\let\twocolumn=\relax
\let\onecolumn=\relax
\let\@topnewpage=\relax
\let\@opcol=\relax
\let\@outputdblcol=\relax
\let\@makecol=\relax
\let\@outputpage=\relax
\let\@floatplacement=\relax
\let\@dblfloatplacement=\relax
\let\@combinefloats=\relax
\let\@cfla=\relax
\let\@cflb=\relax
\let\@comflelt=\relax
\let\@combinedblfloats=\relax
\let\@comdblflelt=\relax
\let\@startcolumn=\relax
\let\@xstartcol=\relax
\let\@scolelt=\relax
\let\@startdblcolumn=\relax
\let\@sdblcolelt=\relax
\let\@tryfcolumn=\relax
\let\@vtryfc=\relax
\let\@wtryfc=\relax
\let\@xtryfc=\relax
\let\@ytryfc=\relax
\let\@ztryfc=\relax
\let\@testfp=\relax
\let\@makefcolumn=\relax
\let\@addtobot=\relax
\let\@addtotoporbot=\relax
\let\@addtonextcol=\relax
\let\@addtodblcol=\relax
\let\@addtocurcol=\relax
\let\@addmarginpar=\relax
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\raggedbottom
\global\columnwidth\textwidth
\global\hsize\columnwidth \global\linewidth\columnwidth
\global\@twocolumnfalse
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% \ls{x} : set line space to be x times the default (modified June 11, 1991)
%          same as \renewcommand{baselinestretch}{ x } , but effective
%          also in the text. (cf: \lsx, \lsxcur)
%          If two or more \ls is used in a paragraph, the last one is taken.
\let\@currsize=\normalsize
\def\ls#1{\let\@@curr=\@currsize\def\baselinestretch{#1}\large\@@curr}

% lsx{x} : set normal line space of all font sizes to be 'x'
%          (a dimension, e.g., 10mm, 5pt). cf: \lsxcur
%    Note: only \baselineskip is changed. Real line space is affected
%          by the glue. Use \raggedbottom for a more accurate spacings.
%  May 13, 1993
\let\@@setsize=\@setsize
\def\lsx#1{\def\@setsize##1##2{\@@setsize##1{#1}}\ls{1.0}}
%%%%
% \nagamaru{xyz} : encircled string 'xyz'.  'xyz' can be a 'tabular'
%                  July 2, 1992
\ifSmallTeX
 \def\nagamaru#1{}
\else
\newdimen\@nagax
\newdimen\@nagaxx
\newdimen\@nagay
\newdimen\@nagayy
\newbox\@nagabox
\def\nagamaru#1{{%
\setlength{\unitlength}{1sp}%
\setbox\@nagabox=\hbox{#1}%
\@nagax=\ht\@nagabox\advance\@nagax by 0.7zw%
\@nagay=\dp\@nagabox\advance\@nagay by 0.7zh%
\@nagayy=\dp\@nagabox\advance\@nagayy by 0.5zh% 
\raisebox{-1\@nagayy}[\@nagax][\@nagay]{%
\@nagax=\wd\@nagabox\advance\@nagax by 1zw%
\@nagay=\ht\@nagabox\advance\@nagay by \dp\@nagabox\advance\@nagay by 1zh%
\begin{picture}(\number\@nagax,\number\@nagay)(0,0)
\thicklines%
\@nagaxx=\@nagax\divide\@nagaxx by 2%
\@nagayy=\@nagay\divide\@nagayy by 2%
\divide\@nagay by 131072 \multiply\@nagay by 131071 % omajinai
\put(\number\@nagaxx,\number\@nagayy){\oval(\number\@nagax,\number\@nagay)}
\put(\number\@nagaxx,\number\@nagayy){\makebox(0,0){#1}}
\end{picture}}%
}}
\fi

%
%basic style
%
\def\teikeistyle{
  \hsize=\paperwidth
  \vsize=\paperheight
  \footline={\hfil}
  \linewidth=\hsize
  \parskip = 0pt
  \parindent=0pt
  \baselineskip = 4.0mm plus1mm minus0.5mm
  \rightskip = 0pt plus 150mm
  \itemsize=20pt
  \lineskip=0pt
  \topskip=0pt
}
%
% end of teikei.cls -----------------------------------------------
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% youshi.sty を取り込んでます
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\ProvidesPackage{youshi}[1997/02/02]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	teikei.clsを用いる場合の枠組のディメンジョン用変数の定義
%	また複雑な枠組で変数を追加する場合にはこのファイルに
%	追加の定義を行う
%
%	以下は設定しなくても可です
%	HOFFSET,VOFFSET,oddHOFFSET,evenHOFFSET
%	doubleHOFFSET
%
%
%
%  位置がずれすぎて印刷が欠けるときには、この下の
%　\HOFFSETと\VOFFSETを調節して下さい。
%\HOFFSET=0mm
%
%更に、頁の偶奇でずらすなら、次のパラメータをセットして下さい。
%\oddHOFFSET=0mm
%\evenHOFFSET=0mm
%
%更に、偶奇の差を一気に埋めたければ次のパラメータを使って下さい。
%このパラメータはodd頁に対してプラス、even頁に対してマイナスで効きます。
%\doubleHOFFSET=0mm
%
% データ入力用token
%
\newdimen\X
\newdimen\XA
\newdimen\Y
\newdimen\YA
\newdimen\XXa
\newdimen\XXb
\newdimen\XXc
\newdimen\XXd
\newdimen\XXe
\newdimen\XXf
\newdimen\XXg
%
% memory for positions of rules
\newdimen\XW%full width of table
\newdimen\YH%full height of table
\newdimen\XM \XM=0mm% X-direction margin
\newdimen\YM \YM=0mm% Y-direction margin
%
% 罫線位置絶対座標　左上角を原点とする
%
% ここで罫線の座標を設定する変数を定義している．
% 必要に応じて追加・削除して下さい．
%
\newdimen\Xa
\newdimen\Xb
\newdimen\Xc
\newdimen\Xd
\newdimen\Xe
\newdimen\Xf
\newdimen\Xg
\newdimen\Xh
\newdimen\XI%これだけ大文字なのは、ギリシャ文字とぶつかるから。
\newdimen\Xj
\newdimen\Xk
\newdimen\Xl
\newdimen\Xm
\newdimen\Xn
\newdimen\Xo
\newdimen\Xp
\newdimen\Xq
\newdimen\Xr
\newdimen\Xs
\newdimen\Xt
\newdimen\Xu
\newdimen\Xv
\newdimen\Xw
\newdimen\Xx
\newdimen\Xy
\newdimen\Xz
\newdimen\Xaa
\newdimen\Xab
\newdimen\Xac
\newdimen\Xad
\newdimen\Xae
\newdimen\Xaf
\newdimen\Xag
\newdimen\Xba
\newdimen\Xbb
\newdimen\Xbc
\newdimen\Xbd
\newdimen\Ya
\newdimen\Yb
\newdimen\Yc
\newdimen\Yd
\newdimen\Ye
\newdimen\Yf
\newdimen\Yg
\newdimen\Ygg
\newdimen\Yh
\newdimen\Yhh
\newdimen\Yi
\newdimen\Yj
\newdimen\Yk
\newdimen\Yl
\newdimen\Ym
\newdimen\Yn
\newdimen\Yo
\newdimen\Yoo
\newdimen\Yp
\newdimen\Yq
\newdimen\Yr
\newdimen\Ys
\newdimen\Yt
\newdimen\Yu
\newdimen\Yv
\newdimen\Yw
\newdimen\Yx
\newdimen\Yy
\newdimen\Yz
%
\newdimen\Ygg
\newdimen\Yhh
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% コンピュータ科学科卒業論文要旨 TeXフォーマット
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% box for separate paragraph
%
\newbox\separatebox
%
%
%	teikei.clsの使用例
%       for teikei.cls Ver 0.95
%
%\FRAMEOFF
%
\DPI=600
%
\def\frameouta{{
  \pageno=1
  \hoffset=0mm
  \voffset=0mm
  \advance\hsize by -\hoffset
  \advance\vsize by -\voffset
  \OFFSET
  \frameparama
  \framedisplaya
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 通常は以下部分を書き換えてどのパラグラフをどこに入れるかを決定
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   {\XYBC{\Xa}{\Ya}{\Xf}{\Yb}
     {\bunshostyle\Large\underline{%
        \@年度~~{\@学科}卒業論文要旨}}}
   {\XYBC{\Xa}{\Yc}{\Xb}{\Yd}{\bunshostyle\large\@研究室名~研究室}}
   {\XYBC{\Xb}{\Yc}{\Xd}{\Yd}{\bunshostyle\large\kinto{4zw}{氏名}}}
   {\XYBC{\Xd}{\Yc}{\Xf}{\Yd}{\bunshostyle\large\@氏名}}
   {\XYBC{\Xa}{\Yd}{\Xb}{\Ye}{\bunshostyle\large\kinto{7zw}{卒業論文題目}}}
   {\XYBC{\Xc}{\Yd}{\Xe}{\Ye}{\large \@卒論題目}}
   {\XM=3mm \YM=3mm \baselineskip 14pt
     {\XYBP{\Xa}{\Ye}{\Xf}{\Yf}{\bunshostyle\parindent=1zw\@卒論要旨}}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% 枠表示する場合には以下に設定する %%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\framedisplaya{%
    \Brule{\Xa}{\Yc}{\Xf}{\Yf}{1pt}
    \Vrule{\Xb}{\Yc}{\Ye}{0.5pt}
    \Vrule{\Xd}{\Yc}{\Yd}{0.5pt}
    \Hrule{\Xa}{\Yd}{\Xf}{0.5pt}
    \Hrule{\Xa}{\Ye}{\Xf}{0.5pt}
}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% parameters %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% 定型枠の各座標データ
%  Xは右方向にYは下方向に正
%
\def\frameparama{
  \Xa=0mm
  \Xb=50mm
  \Xc=53mm
  \Xd=80mm
  \Xe=165mm
  \Xf=168mm
  \Ya=0mm
  \Yb=10mm
  \Yc=15mm
  \Yd=27mm
  \Ye=55mm
  \Yf=255mm
}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\年度#1{\def\@年度{#1}}
\年度{令和7年度}

\def\学科#1{\def\@学科{#1}}
\学科{コンピュータ科学科}
%\学科{情報工学コース}

\long\def\卒論題目#1{\def\@卒論題目{#1}}
\卒論題目{卒論の題目です}

\def\氏名#1{\def\@氏名{#1}}
\氏名{名~~大~~太~~郎}

\def\研究室名#1{\def\@研究室名{#1}}
\研究室名{○○}

\long\def\卒論要旨#1{\long\def\@卒論要旨{#1}\frameouta}

\endinput
%%
%% End of file `abstB.cls'.
