# BAG uniform damping-height square law

- **Stage:** 3-formalized

- **ID:** C28.56af.2.
- **Route:** BAG actual divisor source to physical contraction normalization.
- **Status:** Paper proof below for every fixed smooth positive-axis window.
  The COMPLETE uniform theorem for the literal bagPhysicalHeightWindow is
  now formalized in af.2b: five new leaves,15 public declarations passed
  production and standard-axiom audits. The general statement for every smooth
  positive-axis window is formalized in ChiRamanujanDampedSquareTestWindow{,Perron,Bounds,JointLimit}
  (`dampedSquare_testWindow_joint_limit`). Actual-source Euler identification and
  uniform double cancellation are formalized in af.1.
- **Active card:** ../1-in-progress/bag-physical-contraction-moving-poles.md.

## Statement

Let D_e(n) be the literal pmPowerDampedDivisorCoeff and let W be a fixed
complex smooth function supported in [a,b], 0<a<=b<infinity. For every C>0,
uniformly 0<e<=C/log X as X tends to infinity,

    sum_n D_e(n)^2 W(n/X)/(X e^2 log X)
      - Psi(e log X) integral W -> 0,

where Psi(c)=(1-exp(-2c))/(2c). In particular, for fixed c>0,

    (log X/X) sum_n D_(c/log X)(n)^2 W(n/X)
      -> (c/2)(1-exp(-2c)) integral W.

The literal bagPhysicalHeightWindow satisfies the smoothness and positive-axis
support conditions. No fixed-damping mean is substituted into a moving limit.

## Actual source identity

Write F(s)=(s-1)zeta(s), extended at one by F(1)=1, and write K for the
already formalized axisEulerCorrection. The complete absolutely convergent
Dirichlet series on Re s>1 is

    S_e(s)=sum_n D_e(n)^2 n^(-s)
          =K(s+e,-e) zeta(s)zeta(s+2e)/zeta(s+e)^2.

At each prime q=p^(-s), t=p^(-e), its full prime-power factor is
1+(1-t)^2 q/(1-q). Multiplication by (1-q)(1-qt^2) verifies that it equals
[1-(qt)^2(1-t)^2/(1-qt)^2](1-qt)^2/((1-q)(1-qt^2)). The bracket is exactly
axisPrimeFactor(p,s+e,-e), including every prime power and every prime.
Bounded coefficients give absolute convergence; multiplicativity and the
unconditional Euler product identify the whole series.

Set Q(sigma,alpha)=regularAxisSource(sigma,alpha)/F(sigma)^2. Then

    S_e(s)=[1+e^2/((s-1)(s+2e-1))] Q(s+e,-e).

Q(sigma,0)=1. Its alpha derivative at zero is zero: the two F derivatives
cancel and the COMPLETE K product has zero alpha derivative at zero.
The actual polynomial zero-free disks around 1+i*t control F and its inverse.
The actual K product has a global tube bound. Second-order Schwarz on each
alpha slice therefore bounds |Q-1| by a polynomial in 1+|t| times |alpha|^2,
uniformly for sigma in smaller disks. Consequently the continued source obeys

    |S_e(s)-1| <= A e^2 (1+|t|)^54
                  (1+|((s-1)(s+2e-1))^(-1)|)

on these disks. The exponent is incidental; finite polynomial growth and the
RETAINED e^2 factor are essential. This estimate remains uniform as e tends
to zero arbitrarily faster than 1/log X.

## Mellin inversion and contour estimate

Let M(s)=integral W(x)x^(s-1) dx. Compact support away from zero makes M
entire. Repeated integration by parts with E=x*d/dx gives
M(E^j W)(s)=(-s)^j M(s). Each E^j W is smooth with the same support, hence
|M(s)|<=A_j(1+|Im s|)^(-j), uniformly 0<=Re s<=2, for every j. Fourier
inversion after x=exp u gives Mellin inversion on every such vertical line.

Put L=log X, beta=1+1/L and J_e=(S_e-1)/e^2. The constant one removes the
coefficient n=1; W(1/X)=0 for large X. For n>1 choose a prime p dividing n.
All factors in D_e are in [0,1], so D_e(n)<=1-p^(-e)<=e log p<=e log n.
Thus the original right-line series for J_e is absolutely dominated by
sum_(n>=2) (log n)^2 n^(-beta)=O(L^3), uniformly in e. For example,
(log n)^2<=8 L^2 n^(1/(2L)) and integral comparison bounds the remaining
positive Dirichlet sum by O(L). This justifies inversion and its tails.

Fix 0<kappa<1/9. Set T=L^kappa and delta=d/[4(1+T)^9], with d from the
actual source disks. For all sufficiently large X, uniformly e<=C/L,
2e<delta/2 and 1/L+e<delta. Shift the truncated right line to Re s=1-delta.
The whole rectangle lies in the proved source domain, except for its two
explicit poles at 1 and 1-2e. The normalized source J_e is holomorphic
elsewhere; no zeta zero or unproved zero-free hypothesis is admitted.

On the left edge both pole distances are at least delta/2. The source bound
and delta^(-2)=O(T^18) give J_e=O(T^72). Bounding the edge length by 2T,
its integral divided by X L is O(exp(-delta L) T^73/L), which tends to zero
since delta L grows like L^(1-9kappa). On the two horizontal edges J_e is
O(T^54), so the normalized contribution is O(T^(54-j)/L). On the discarded
right tails the absolute Dirichlet bound gives O(L^2 T^(1-j)). Choose one
fixed integer j>max(54,1+2/kappa). All three errors vanish uniformly in e.
Every contour edge and both original infinite tails have been retained.

## Both residues and uniform coalescence

The residues of J_e(s)M(s)X^s, divided by X L, sum to

    [Q(1+e,-e) M(1)
      -exp(-2eL) Q(1-e,-e) M(1-2e)]/(2eL).

The sign of the second residue is negative. The source estimate at t=0
gives Q(1+e,-e)=1+O(e^2) and Q(1-e,-e)=1+O(e^2), with fixed constants.
Entire M has M(1-2e)=M(1)+O(e). Since 0<eL<=C and exp(-2eL)<=1,
the difference from Psi(eL)M(1) is O(e/L)+O(1/L), uniformly even when eL
tends to zero. Finally M(1)=integral W. This proves the stated joint law.

## Corpus evidence and remaining formal work

The proof uses the literal divisor finite-product and multiplicativity
sources, complete axis product and its zero derivative, pole-removed zeta,
and actual global zero-free disks. These sources have been read. Corpus
search15925 was nonpartial65597/65597; all candidate/source/idea/ingredient
sections inspected, compiler mostly source-only, refresh incomplete.
MellinTestFunctionPerron supplies Euler differentiation and fixed order-two
strip decay; ChenGuptaLiLemma62MellinKernel supplies log-Fourier inversion and
all-order FIXED-line decay. Neither alone is the full uniform moving-contour
theorem. C28.56af.2a now formalizes arbitrary-order strip decay and inversion for the
actual window, the exact four-edge moving rectangle with its constructed
holomorphic remainder and actual zero-free domain, and uniform original-line
control |S_e(1+b+it)-1|<=24 e^2/b^3 retaining the complete series. The complete actual weighted sum now equals its normalized Mellin contour
integral, with absolute integrability, full series exchange and exact n=1
removal proved. All19 public declarations in four leaves passed production
and standard-axiom audits. C28.56af.2b now also formalizes integrated bounds
for every edge and both tails, uniform coalescence of both residues and the
complete joint-limit assembly for this exact source and window. Its final
shrinking-interval theorem retains arbitrarily small positive e log X.
All15 new public declarations passed production and standard-axiom audits;
see ../3-formalized/bag-uniform-damping-height-square-law.md.

This is a smooth local square law, not the complete physical cubic theorem.
Growing physical profiles, sharp endpoints where still needed, full signed
near-resonances, moving cofactors, growing moments and positive common-height
self-return remain open. No quadratic-to-cubic promotion is asserted. RH
remains unproved.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindow`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowPerron`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowBounds`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowJointLimit`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareAxis`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareRightLine`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
new `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindow`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowPerron`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowBounds`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowJointLimit` (every smooth window `IsTest W a b`, `0 < a ≤ b`); existing `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareAxis`, `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareRightLine` (source), and the literal-window chain `GaloisForLFunctions.RHTower.ChiRamanujanDampedSquare{Mellin,Contour,Perron,Residues,Tails,Edges,Transfer,JointLimit}`.

| Claim | Declaration |
|-|-|
| Statement: uniformly in `0 < ε ≤ C/log X`, `Σ D_ε(n)² W(n/X)/(Xε² log X) − Ψ(ε log X)∫W → 0` for EVERY smooth `W` supported in `[a,b]`, `0 < a` | `dampedSquare_testWindow_joint_limit`, `dampedSquareTestWindowEnergy`, `dampedSquareTestWindowEnergy_uniform_joint_limit`, `dampedSquareTestWindowEnergy_tendstoUniformlyOn` |
| fixed `c > 0`: `(log X/X)Σ D_{c/log X}(n)² W(n/X) → (c/2)(1−e^{−2c})∫W` | `tendsto_dampedSquare_testWindow_fixed_damping` |
| literal `bagPhysicalHeightWindow` case | `dampedSquare_physical_window_joint_limit` |
| source: `S_ε` absolutely convergent, Euler factor, `S_ε = K(s+ε,−ε)ζ(s)ζ(s+2ε)/ζ(s+ε)²`, `S_ε = [1+ε²/((s−1)(s+2ε−1))]Q(s+ε,−ε)`, `Q(σ,0) = 1`, `∂_αQ = 0`, `\|Q−1\| ≪ \|α\|²`, `\|S_ε − 1\| ≤ Aε²(1+\|t\|)^{54}(1+\|((s−1)(s+2ε−1))^{−1}\|)` | `summable_dampedSquareDirichlet`, `dampedSquareDirichlet_hasProd`, `dampedSquareDirichlet_eq_axis`, `dampedSquareDirichlet_eq_twoPole`, `dampedSquareRegularSource_zero`, `hasDerivAt_dampedSquareRegularSource_zero`, `exists_dampedSquareRegularSource_quadratic_bound`, `exists_dampedSquareContinuation_remainder_bound` |
| Mellin: `M_W` entire, all-order strip decay, vertical integrability, inversion, `M_W(1) = ∫W` | `differentiable_dampedSquareTestMellin`, `exists_dampedSquareTestMellin_rapidDecay`, `integrable_dampedSquareTestMellin_vertical`, `mellinInv_dampedSquareTestMellin`, `dampedSquareTestMellin_one` |
| `D_ε(n) ≤ ε log n`; right-line majorant `O(L³)`; original-line control | `pmPowerDampedDivisorCoeff_le_damping_log`, `summable_dampedSquare_log_majorant`, `tsum_dampedSquare_log_majorant_le`, `norm_dampedSquareDirichlet_sub_one_le`, `norm_dampedSquareDirichlet_normalized_le` |
| summed Mellin inversion, `n = 1` removed (`aX ≥ 1`), absolute integrability | `dampedSquareTest_weighted_sum_eq_integral`, `integrable_dampedSquareDirichlet_testWindow`, `integrable_dampedSquareTestContour_original_line`, `dampedSquareTest_weighted_sum_normalized_eq_integral` |
| moving rectangle with both poles `1`, `1−2ε`, actual zero-free domain | `exists_dampedSquareTestContour_rectangle`, `dampedSquareTestContourIntegrand`, `dampedSquareTestMellinNumerator` |
| left edge, horizontal edges, both tails | `exists_dampedSquareTestContour_edge_bounds`, `exists_dampedSquareTestContour_original_line_decay`, `exists_dampedSquareTestContour_two_tail_bound` |
| both residues, uniform coalescence to `Ψ(εL)M(1)` with error `O(1/L)` | `dampedSquareTestResiduePacket`, `dampedSquareTestResiduePacket_eq`, `exists_dampedSquareTestResiduePacket_uniform_coalescence`, `exists_dampedSquareTestResiduePacket_tendstoUniformlyOn` |
| exact transfer identity and complete remainder bound | `exists_dampedSquareTestWindowEnergy_transfer`, `exists_dampedSquareTestWindowEnergy_remainder_bound` |

Growing physical profiles, the signed cubic, growing moments, moving cofactors, common-height self-return and RH are the card's recorded open targets and are not claimed.

The earlier Lean certificate of this lane is `../bag-uniform-damping-height-square-law.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
