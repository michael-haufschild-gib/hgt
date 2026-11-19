# The Mertens abscissa on the entire fixed set of one density-one involution

- **Stage** 3-formalized
- **Target** A single genuine involution with displacement \(o(n)\), unsigned unpaid population \(o(X)\), and the same sharp growth abscissa for its entire fixed signed prefix as for \(M\). In particular the square-root-plus-epsilon estimates on those two prefixes are equivalent.

For each \(j\ge2\), take a finite divisor table of resolution \(1/j\) whose fixed signed prefix detects every Mertens power. Choose all these tables before choosing the block boundaries. On each consecutive block \((L_j,L_{j+1}]\) use table \(j\), retaining only pairs entirely inside the block. Completed blocks have no crossing edges. At each cutoff the total fixed signed prefix is therefore \(M(X)\) minus the crossings in the current block.

**Upper bound uniform over both walls.** For one table of squarefree modulus \(Q\), every upward-moving gcd class has the form \(cd\leftrightarrow ce\) with \(d<e\) and \((c,Q)=1\). Its retained crossing charge at \(X\in(L,U]\) is \(\mu(d)\) times a difference of two coprime prefixes. The upper quotient endpoint is \(b=\min(\lfloor X/d\rfloor,\lfloor U/e\rfloor)\). The lower endpoint is \(\min(b,\max(\lfloor L/d\rfloor,\lfloor X/e\rfloor))\). Both endpoints are at most \(X\). Hence a bound \(|M(t)|\le C t^s\) gives at most \(C K_Q(s)X^s\) in absolute value for the entire clipped crossing sum, with
\[
 K_Q(s)=2\tau(Q)\prod_{p\mid Q}(1-p^{-s})^{-1}.
\]
The bound holds uniformly in both walls. Write \(\alpha=\sup(\{0\}\cup\{t>0:M\ne O(X^t)\})\) and \(\delta_j=1/(j+2)\). Apply the estimate at \(s=\alpha+\delta_j\). Start each block high enough to absorb its complete constant in \(X^{\delta_j}\). Every exponent strictly above \(\alpha\) then passes to the fixed prefix.

**Exact lower witnesses.** Choose a sequence cofinal in the failing positive Mertens exponents, including the maximal failure if one exists. For its \(j\)-th exponent, choose a witness \(X_j>2L_j\) where the fixed charge of the *untruncated* table exceeds \(j X_j^{s_j}\). Finish the block beyond \(2X_j\), also beyond the next table's threshold. Every edge crossing \(X_j\) lies entirely in the block by the displacement bound. Thus at that point the complete fixed signed prefix of the glued map agrees exactly with the table's fixed signed prefix. This retains every failure, also at an unbounded endpoint.

**Density and displacement.** Make each block start beyond the threshold for its own table's unpaid count and beyond \(j\) times the preceding start. Write \(H\) for the glued map and \(U_F\) for the unsigned unpaid prefix of a table. For \(L_j<X\le L_{j+1}\),
\[
 U_H(X)\le U_H(L_j)+U_{F_j}(X)+U_{F_j}(L_j).
\]
An extra fixed vertex whose partner is at most \(L_j\) charges injectively to that crossing partner at the lower wall. Every lost partner above the upper wall already crosses \(X\). Applying the inequality also to the preceding block leaves only \(L_{j-1}\) uncontrolled older integers. The spacing and table tolerances give \(U_H(X)=o(X)\). The same map has displacement \(o(n)\).

`one_density_zero_fixed_set_detects_the_mertens_abscissa` proves the two power transfers. `square_root_on_one_density_zero_fixed_set` gives the square-root-plus-epsilon equivalence. [Lean proof](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheMertensAbscissaOnOneDensityZeroFixedSet.lean)

This yields equality for every family of exponents \(s+\delta\), \(\delta>0\). An exact upper estimate at an attained minimal exponent would require uniform endpoint constants.
