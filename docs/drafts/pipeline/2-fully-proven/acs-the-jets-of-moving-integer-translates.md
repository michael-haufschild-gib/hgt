# The jets of moving integer translates

For a packet $f$ supported between $0$ and $\log K$, integer dilation $d\ge1$ and resolution $r\ge1$, the regularized jet of $f(u-\log d)$ on any original window with $1+L\ge dK$ is exactly the jet of $f$ at resolution $dr$ on the fixed window of length $3K$.

At every positive degree $j$ both samples equal $f(\log(j/(dr)))$. They vanish outside $dr<j\le Kdr$. Both windows contain this interval. The off-diagonal kernel and the counterterm $\log(j/(2\pi))$ depend only on the integer degree indices. Restricting both sums to these common supported degrees proves equality.

For a fixed compact $C^2$ packet vanishing below $\log 3$, the regularized jet therefore tends to its continuous archimedean value whenever $d_nr_n\to\infty$ and the windows contain the translates. The standard fixed-packet limit applies at resolution $d_nr_n$. Both dilation and horizon may vary with $n$. [Fixed-packet limit](../../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm.lean)

For two sampled packets on the same window, suppose that $j\ge H^2i$ whenever the first is nonzero at $i$ and the second at $j$, with $H\ge2$. Their mixed jet in the quadratic form has absolute value at most $(4/H)(\sum_i |f_i|/i)(\sum_j |g_j|/j)$. The diagonal overlap vanishes. For $j\ge H^2i$, the kernel $\tfrac12(|i-j|^{-1}+(i+j)^{-1})/\sqrt{ij}$ is at most $2/(Hij)$. Summing the two orientations proves the bound.
