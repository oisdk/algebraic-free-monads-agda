BEGIN{x=0;}
/^\\end{code}/{x=0;}
x;
/^\\begin{code}/{x=1;}
