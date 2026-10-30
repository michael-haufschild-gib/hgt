# Source support and probe support have different terminal dual costs

**ID:** completed-arithmetic-forms-source-probe-boundary  
**Stage:** In progress  
**Type:** Exact covariance domain classification

For a source packet $c$ supported on $1,\ldots,T$, its literal infinite
accumulation energy is
$$\sum_{n\ge1}\frac{(\sum_{j\le\min(n,T)}c_j)^2}{n(n+1)}
=C_T(c)+\frac{(\sum_{j\le T}c_j)^2}{T+1}=\mathcal C_T(c).$$
For a coupling $b$, set $F_0=0$, $F_j=jb_j$ and
$D_T(F)=\sum_{j=1}^T(F_j-F_{j-1})^2$.
Restricting the source to the same coordinates gives sharp dual cost $D_T(F)$.

Instead fix a probe supported through $T$, and allow source packets of arbitrary
finite support. Its proposed sharp dual cost is
$$\sup_{K,c}\left(2\sum_{j\le\min(K,T)}c_jb_j-\mathcal C_K(c)\right)
=D_T(F)+F_T^2.$$
The terminal edge reappears because the source may respond beyond the last
probe coordinate. The maximizing source is supported through $T+1$ and is
neutral: its total increment is zero. Its local formula is the weighted
second difference of the probe extended by zero. This is an exact boundary
cost, not a loss in an estimate. All displayed domain identifications require
Lean formalization.
