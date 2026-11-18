# Opposite degrees of the perfect-power graph contacts

**Theorem.** Keep precisely the contacts whose ratio is a perfect $d$-th power, for a positive integer $d$. Write $I^{[d]}_X(f,g)$ for the directed height at separation $\log X$, $b=1/d-1/2$, and $M_a(f)=\int f(u)e^{au}\,du$. For real compactly supported $C^2$ profiles,

$$
X^{-b}I^{[d]}_X(f,g)\longrightarrow \frac{2}{d}M_{-b}(f)M_b(g).
$$

**Proof.** On $n=k^d$ the local length gives $\Lambda(k^d)=\Lambda(k)$. Set $a=(d-1)/2$, $F(u)=f(du)e^{au}$ and $G(v)=g(dv)e^{-av}$. Their correlation at $z$ is $d^{-1}e^{-az}$ times the original correlation at $dz$. Reindexing the actual contact sum therefore gives $I^{[d]}_{Y^d}(f,g)=dY^{-a}I_Y(F,G)$ exactly. Applying the full-contact limit at $Y$ and changing variables in each moment gives the displayed formula. The square layer has a finite unscaled limit. Higher layers decay at the indicated power when the two limiting moments are nonzero.

**Lean.** Both the exact descent and the separation limit are proved for every positive $d$. [Power contacts and their opposite degrees](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/PowerContactsAndTheirOppositeDegrees.lean)
