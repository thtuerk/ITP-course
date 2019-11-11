\documentclass{beamer}

\usepackage{pgf,pgfnodes,pgfarrows}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{graphicx}
\usepackage[utf8]{inputenc}
\usepackage{hyperref}
\usepackage{booktabs}
\usepackage{mathpartir}
\usepackage{latexsym}
\usepackage{textcomp}

\newcommand{\ie}{i.\,e.\ }
\newcommand{\eg}{e.\,g.\ }
\newcommand{\wrt}{w.\,r.\,t.\ }
\newcommand{\aka}{a.\,k.\,a.\ }
\newcommand{\cf}{cf.\ }
\newcommand{\etc}{etc.\ }
\newcommand{\cearrow}{\url{~}>}
\renewcommand{\emph}[1]{\structure{\textbf{#1}}}
\newcommand{\entails}{\vdash}
\newcommand{\hol}[1]{\emph{\texttt{#1}}}
\newcommand{\ml}[1]{\emph{\texttt{#1}}}
\newcommand{\textbsl}{\char`\\{}}
\newcommand{\holAnd}{/\textbsl{}}
\newcommand{\holOr}{\textbsl{}/}
\newcommand{\holLambda}{\textbsl{}}
\newcommand{\holImp}{==>}
\newcommand{\holEquiv}{<=>}
\newcommand{\holNeg}{\raisebox{0.5ex}{\texttildelow}}
\newcommand{\mlcomment}[1]{\structure{(* #1 *)}}
\newcommand{\aequiv}{\ensuremath{\stackrel{\alpha}{\equiv}}\ }
\newcommand\pro{\item[$+$]}
\newcommand\con{\item[$-$]}

\newcommand{\bottomstatement}[1]{
\begin{center}
\textbf{#1}
\end{center}
}

\input{version.inc}

\title{Interactive Theorem Proving (ITP) Course}
\institute{
\includegraphics[width=1.25cm]{images/cc/cc.eps}
\includegraphics[width=1.25cm]{images/cc/by.eps}
\includegraphics[width=1.25cm]{images/cc/sa.eps}\\
\scriptsize{Except where otherwise noted, this work is licened under\\
  \href{http://creativecommons.org/licenses/by-sa/4.0/}{Creative Commons Attribution-ShareAlike 4.0 International License}}}
\author{Thomas Tuerk (thomas@tuerk-brechen.de)}
\date{Academic Year 2016/17, Period 4}
\newcommand{\partstitle}[1]{\title{Interactive Theorem Proving (ITP) Course\\#1}}
\newcommand{\titleframe}{\frame[plain]{\titlepage\hfill\tiny version \GITAbrHash{} of \GITAuthorDate{}}}
\newcommand{\partstitleframe}[1]{\partstitle{#1}\titleframe}


\usetheme{Boadilla}
\setbeamertemplate{footline}[frame number]{}


\logo{\pgfputat{\pgfxy(-.5,8.7)}{\pgfbox[center,top]{\includegraphics[width=8mm]{images/cc/by-sa.eps}}}}

\setbeamertemplate{part page}
{
  \begin{centering}
    {\usebeamerfont{part name}\usebeamercolor[fg]{part name}\partname~\insertromanpartnumber}
    \vskip1em\par
    \begin{beamercolorbox}[sep=16pt,center]{part title}
      \usebeamerfont{part title}\insertpart\par
    \end{beamercolorbox}
    \vfill
  \begin{center}
  \includegraphics[width=0.75cm]{images/cc/cc.eps}
  \includegraphics[width=0.75cm]{images/cc/by.eps}
  \includegraphics[width=0.75cm]{images/cc/sa.eps}\\
  \tiny{Except where otherwise noted, this work is licened under\\
  \href{http://creativecommons.org/licenses/by-sa/4.0/}{Creative Commons Attribution-ShareAlike 4.0 International License}}.  
  \end{center}
  \end{centering}
}

\makeatletter
\AtBeginPart{%
  \addtocontents{toc}{\protect\beamer@partintoc{\the\c@part}{\beamer@partnameshort}{\the\c@page}{\the\numexpr\value{framenumber}+1\relax}}%
}
%% number, shortname, page.
\providecommand\beamer@partintoc[4]{%
  \ifnum\c@tocdepth=-1\relax
    % requesting onlyparts.
    \qquad\makebox[5em][l]{\hyperlink{page.#3}{\emph{Part {\uppercase\expandafter{\romannumeral #1\relax}}}}} \makebox[18em][l]{\hyperlink{page.#3}{#2}}
    \makebox[3em][r]{\hyperlink{page.#3}{#4}}

    \par
  \fi
}
\define@key{beamertoc}{onlyparts}[]{%
  \c@tocdepth=-1\relax
}
\makeatother

%\usefonttheme[onlylarge]{structurebold}
%\usepackage{times}

\ifdefined\ttbwflag
  \usecolortheme{seagull}
  \beamertemplatenavigationsymbolsempty
\fi
