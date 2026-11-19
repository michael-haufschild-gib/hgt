# The second confined state detects every right zeta zero

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

At the second crossing, the normalized real null state's Laplace transform is nonzero at every nonreal point in the open right half-plane. Its meromorphic continuation has a nonzero simple-pole residue at $\rho-17/2$ for every zeta zero with $\Re\rho\geq 1/2$, including an infinite divisor. [Second state](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheSecondConfinedStateSeesEveryRightZero.lean#L443) · [Residues](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheSecondConfinedStateSeesEveryRightZero.lean#L475)

Suppose $LF(\alpha)=0$ at $\alpha=A+iB$, with $A>0$ and $B\ne0$. The causal resolvent $K$ retains half-line support. Its real components $U(c)=\Re(cK)$ have one power of Fourier decay and finite gamma energy. For $J=U(\alpha c)-\pi\Re(c)F$, one has $LJ(z)=zLU(c)(z)$. Fourier uniqueness identifies the undamped resolvent of $J$ with $-\pi U(c)$. Its bare Weil pairing vanishes, and its weighted square gives $Q_R(J,U(c))=-4a(R)W(U(c),U(c))$. [Primitive identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheSecondConfinedStateSeesEveryRightZero.lean#L246)

Since $F$ is null, evaluate this pairing at $c$ and $\bar\alpha c$. Writing $N=|\alpha|^2$ gives
$$
2AN Q_R(U(c),U(c))=-4a(R)\bigl(NW(U(c),U(c))+W(U(\bar\alpha c),U(\bar\alpha c))\bigr).
$$
For $c\ne0$, the two real components determine $K$ because $B\ne0$, and the resolvent recovers $F$. The right side is strictly negative. Thus a missed nonreal point produces a negative plane at the state's own ratio. At the second crossing the index is one. Imaginary-axis nonvanishing also covers zeros on the critical line. [Negative plane](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheSecondConfinedStateSeesEveryRightZero.lean#L411) · [Boundary nonvanishing](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/EveryConfinedEigenspaceIsSimple.lean#L128)

Each right-zero coefficient of this same state is nonzero. Their absolutely convergent sum recovers the averaged state with remainder bounded by $Ce^{-8t}$ for every $t>0$. [Full right-zero signal](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheSecondConfinedStateSeesEveryRightZero.lean#L502) · [Expansion for every confined state](qic-absolute-mode-expansion-for-every-confined-state.md)

The nine audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
