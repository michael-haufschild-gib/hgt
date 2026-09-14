# Canonical return specialization under detuning

Status: **BRIDGE with a certified scalar continuation and first-jet specialization**, not an RH proof. The material discriminant and multiplier cover below pass a Lean scratch check; the full ramified matrix-response specialization remains on paper. This is classical transfer data. The [envelope response](envelope-response.md) is now the central physical target.

## Source and novelty boundary

The certified parabolic response needs identification with a canonical specialization from neighboring bands. Direct detuning limits fail because the continued return contains singular powers. The proposed replacement is its monodromy-invariant component.

`XiHurwitzConstraintOrientation.openCriticalStrip_monoScalar_negativeReal_iff` already proves the negative-real character criterion for the critical line. This is not new here. The needed result derives that character from physical detuning and recovers the certified response by specialization.

## Scalar germ and canonical projector

For nonintegral `s`, the cover-return function `F_s(X)=Li_s(exp X)` satisfies

`F_s(X)=Γ(1−s)(−X)^(s−1)+H_s(X)`.

Here `H_s` is holomorphic for `|X|<2π`, with derivatives `H_s^(j)(0)=ζ(s−j)`. This is the classical [Jonquière expansion, DLMF 25.12.12](https://dlmf.nist.gov/25.12.E12).

A positive loop around `X=0` fixes `H_s` and multiplies the singular term by `μ(s)=exp(2πi(s−1))`. Thus

`Π_s F_s = (T F_s − μ(s) F_s)/(1−μ(s)) = H_s`.

The projection is determined by continuation and its two characters. It requires no independently chosen Gamma subtraction coefficient.

**Checked scalar bridge:** [PhotonicReturnMonodromy.lean](../../../../../formal/GaloisForLFunctions/RHTower/PhotonicReturnMonodromy.lean) combines `Hurwitz.AnchorTransversality`, `RHTower.JonquiereExpansion`, and `HeatEnergyTangent`. It constructs the actual regular germ in the phase coordinate `θ`, a holomorphic lift over `θ=exp w`, its exact periodic-zeta boundary agreement, its deck law, and its canonical projection. The singular branch is proved nonzero. The regular first jet, converted from phase `θ` to logarithmic multiplier `X=iθ`, equals the certified full parabolic return matrix.

The existing Hurwitz continuation is normalized using zeta, so the proven boundary agreement is essential; the definition alone would not establish a native construction. All 11 public theorems passed scratch checking, the targeted leaf build, and axiom auditing. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Heartbeat limits were unchanged. The analytic claims about the scalar lift are local near the phase puncture; no global holomorphy is asserted.

## Full matrix at a simple band edge

**Concrete material detuning:** keep the slab phase `α=arctan(4/3)` fixed and vary the second frequency `r>0`, using permittivity `r⁻²` and duration `α/r`. The first slab retains permittivity `1` and duration `α`. Then

`M(r)=[[3/5,4/(5r)],[-4r/5,3/5]] [[3/5,4/5],[-4/5,3/5]]`.

This is the same cell at `r=4`. Its trace is `t(r)=(18−16(r+r⁻¹))/25`. For the positive two-cell family `P(r)=M(r)²`, set `c(r)=t(r)²/2−1`. Its eigenvalue discriminant factors as

`c(r)²−1=(r−4)U(r)`,

`U(r)=16 t(r)² (4r−1)(r+1)²/(625r²)`, `U(4)=12/5`.

Thus an analytic nonzero square root of `U` normalizes the spectral cover to `v²=r−4`. This is a physical material detuning; it changes the medium and the second duration together. It is distinct from the fixed-medium momentum crossing recorded in the earlier construction. Both give a simple edge, but their parameters must not be conflated.

The matrix determinant/trace identities, discriminant factorization, analytic normalized cover, and reciprocal eigenvalue branch on `r=4+v²` passed `lake env lean /tmp/ptc-physical-detuning.lean`. One unused-simp-argument warning remains; no errors or limit overrides. This scratch is not a promoted module, and does not prove the phase-log continuation or full quantum response.

For an analytic `SL₂` transfer family near a simple positive parabolic edge, set

`c=tr(M)/2=cosh X`, `A=M−cI`, `A²=sinh²(X)I`.

The local physical coordinate is `τ=X²`. One detuning loop exchanges `X` and `−X`. Spectral functional calculus gives the continued response

`R_s(M) = (F_s(X)+F_s(−X))/2 I + (F_s(X)−F_s(−X))/(2 sinh X) A`.

In a gap the unattenuated cover series generally diverges. This formula retains analytic continuation or its Abel prescription; it is not a convergence assertion there.

The regular coefficients are holomorphic in `τ`: the first is even in `X`, and the odd numerator in the second cancels the simple zero of `sinh X`. At `M₀=I+N`, their specialization is

`ζ(s) I + ζ(s−1) N`.

With compatible branches the singular part is

`C₁ X^(s−1) I + C₂ X^(s−2) (X/sinh X) A`.

Its two detuning characters are `ν=exp(πi(s−1))` and `−ν`. The regular character is `1`. Squaring the physical continuation removes the Floquet-label exchange, giving

`Π_s = (T_τ²−μ(s))/(1−μ(s))`.

This projection is unchanged by reversing the loop generator and commutes with invertible analytic changes of field basis. Independence of the Mellin weighting convention is not asserted.

## The RH question in this geometry

In `0<Re s<1`, `μ(s)≠1`; its negative-real locus is exactly `Re s=1/2`, with value `−exp(−2π Im s)`. Its inverse is the corpus's Hurwitz character.

Candidate formulation: **every noninvertible parabolic specialization of the invariant return component has negative-real complementary squared monodromy.** The certified determinant identity makes this RH-equivalent after the physical germ identification. It does not prove confinement.

Maxwell flux vanishes on every defect kernel. Real coefficients provide conjugate partners, not reality of each individual character. The full return section and its normalization contain information absent from the abstract monodromy representation.

## Whole-route consequences

- Canonical continuation replaces singular subtraction and retains the nilpotent channel: the scalar lift and first-jet identity are Lean-certified.
- The orientation criterion and the regular first derivative already exist in the corpus; duplicating them would not advance the route.
- Remaining classical bridge: certify the ramified matrix-response specialization. `AnalyticDividedDifference.analyticAt_dslope_of_analyticAt` supplies the existing removable-quotient infrastructure; it was source-inspected, not rebuilt here. The central route target has moved to the full envelope/phase/logical cusp response; this classical bridge alone cannot provide that identification or a confinement mechanism.
- A metaplectic Gaussian amplitude contributes exponent `d/2`; it does not alone force `1/2`. The homogeneous PTC source uses opposite-momentum modes. A single-mode reduction and a return-density normalization require justification. [Cahen, August 2026, Proposition 5.4](https://arxiv.org/html/2608.22443v1); [PTC quantum geometry](https://arxiv.org/html/2511.17317v1).

No primary universal conjecture is frozen here: the projector is visible algebra and confinement is an identified RH equivalent. A new mechanism forcing confinement remains the scientific target.
