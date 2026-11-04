# Coupled Schur obstruction at scale seven

- **Stage:** 5-failed; obstruction and positive capacity survivor formalized.
- **Wall:** Σ6; integrated rank-nine positivity remains open.
- **Claim:** The pair `(C,D)=(10⁷,10¹²)` fails full source positivity at scale seven, despite its positive origin, tail and two established directional tests. Its literal weighted representative also fails at every sufficiently small positive aperture.
- **Positive survivor:** A positive complete-source direction with exact native and weighted load-capacity half-planes. The origin-and-tail repair remains valid.

Put `x₇=½log(7/π)`, `f=f₁(x₇)`, `g=229/55`, and
`N=10⁷u₁u₁ᵀ+10¹²u₂u₂ᵀ`. Let `H₁` be the first-atom fifth even
matrix divided by `f²`; its moments are `P_k(49,14)/121`.
Eliminate the first two coordinates of `H₁−gN`, clearing the positive
head determinant. Write the resulting Schur matrix as
`[[a,b,c],[b,d,e],[c,e,h]]` and `Δ=ad−b²`.
Exact Lean certificates give `a>0`, `Δ>0`, and negative full determinant.

Choose the last three coordinates of `v` to be
`((dc−be)/(1568Δ), (ae−bc)/(1568Δ), −1/1568)`;
choose its first two coordinates by the exact head elimination.
This specifies one rational vector without approximate data.
For `P_v(A,X)=ΣᵢⱼvᵢvⱼP_(i+j)(A,X)` and
`L(C,D)=C(v₂+420v₃)²+D(v₃+1568v₄)²`, set

`ε_v=Σᵢⱼ|vᵢvⱼ|(2i+2j)!/[10¹³(3/20)^(2i+2j)]`.

For every `0≤z≤10⁻⁹`, exact Lean certificates prove

`121ε_v < P_v(49,14)+8zP_v(196,35)+16z²P_v(784,56)`

and the same retained expression plus `121ε_v−121gL(10⁷,10¹²)` is negative.
Here `z=e⁻²¹` lies in the stated interval. The complete reflected-tail
proof gives disk error at most `1000f²e^(−27q/5)` on radius `3/20`.
For `q≥7`, `e³≥20` and `e≥5/2` imply `e³⁷≥20¹²(5/2)>10¹⁶`,
so this error is at most `f²/10¹³`. Cauchy's estimate supplies exactly
`ε_v f²` in the quadratic form. Thus the complete native energy `E=vᵀH₅(x₇)v`
is positive. Since `G(x₇)≤−gf²`, the corrected energy `E+G(x₇)L(10⁷,10¹²)` is negative.

Consequently `B=E/(−G(x₇))` satisfies `0<B<L(10⁷,10¹²)`, and the
complete source direction is positive exactly when `L(C,D)<B`.
The weighted threshold is `B_a=w_aE/(−K_a′(2x₇))>0`, with the exact
positive region `L(C,D)<B_a` for every `0<a<1/2`.

Finally, write `Q=L(10⁷,10¹²)>0` and `η=−(E+GQ)>0`.
The proved slack bound `0≤K_a′−w_aG≤w_a a(2x₇)Φ(x₇)²` shows that
any positive `δ≤1/2` with `δ(2x₇)Φ(x₇)²Q≤η/2` gives negative
weighted energy for every `0<a<δ`. No claim of failure at all apertures follows.

Lean: `EvenFiveBoundary.schur_energy_pos`, `reduced_schur_energy_negative`,
`schurCapacity_bounds`, `schur_coupled_positive_iff`,
`schurWeightedCapacity_exceeds_source`, `schur_coupled_weighted_positive_iff`,
and `reduced_schur_weighted_negative_small` in
`ThetaCuspSections/FifthEvenInheritedLoadBoundary.lean`.
The actual matrix identities and failures are
`EvenFiveCoherent.coupledRepair_schur_energy`,
`coupledWeightedRepair_schur_energy`, `reduced_coupledRepair_not_posSemidef`,
and `reduced_coupledWeightedRepair_not_posSemidef_small` in
`ThetaCuspSections/FifthEvenCoherentRepair.lean`.
The full reflected-tail estimate is
`ThetaCuspReflectedCauchyTail.native_twoAtom_cauchy_error_of_seven_le`.
Canonical checks and all eleven new boundary/matrix axiom audits pass;
dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
