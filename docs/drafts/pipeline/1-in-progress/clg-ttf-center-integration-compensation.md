# CLG/TTF center compensation and the remaining signed hierarchy

- **Stage:** 1-in-progress
- **Type:** ALL-ORDER SOURCE POSITIVITY FRONT
- **Full chain:** Literal theta source → all signed center-mixed jet Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Closed:** Global canonical odd compensation; the exact rational band `10^12<C_*<3·10^12`, with corrected even rank-four source strictness on a common seam interval and the explicit ray `x≥6/5` for every coefficient in that band, plus exact integrated entries; complete two-atom error bounds through derivative twelve, including the correction and a finite lower quadratic comparison for the actual canonical matrix; full six-dimensional signed mixed Hankel positivity; arbitrary sufficiently small distinct six-point clusters at every critical aperture; exact all-order successor source integration and RH-equivalent signed source cone.
- **Open:** Close the intervening compact comparison for the corrected even rank-four source, or prove the rank-seven successor integral directly, then cover every remaining order. RH is unproved.

## Exact global odd-block theorem

Let `j_n(x)=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)`. Set `A=−j₂`, `B=j₄`, `C=−j₆`, `D=j₈`, `E=−j₁₀`, `Δ=AC−B²>0`, and `H=ACE−AD²−B²E+2BCD−C³`. The native determinant has `H(0)<0`.

The source-selected coefficient is `K_*=−H(0)/(Δ(0)Φ(0)²)`, with `10⁹<K_*<3·10⁹`. Define `G=3Φ²+2xΦΦ′` and `H_K=H+KΔG`.

`ThetaCuspGlobalOddCompensation` proves `H_K(x)>0` for every `x≥0` and every `10⁹≤K≤3·10⁹`. The canonical theorem has no unproved sign input. The former middle interval is fully covered.

The correction is the derivative of `F_a(r)=r² sinh(ar)Φ(r/2)²`. Its proved integrability and zero half-line integral leave the actual mixed tenth entry unchanged. The corrected weighted determinant is at least `[r sinh(ar)]³H_K(r/2)>0` for `a,r>0`. The existing integral receiver therefore proves the actual mixed odd rank-three determinant strictly positive for every `0<a<1/2`.

See [the full paper proof, exact error estimates and Lean verification](../3-formalized/clg-ttf-global-odd-compensation.md).

## Complete source comparisons available

The proof uses four source regimes, all closed:

- `0≤x≤8/95`: the literal modular orbit has `0≤u,w≤1`, `17≤a≤20`, `w≤5u/4`; the exact positive cubic and remainder give `H_K≥10¹⁴M⁶>0` for `K≥10⁹`.
- `37/10≤q≤5`: the exact two-atom normalized determinant is at least `15·10⁹`; the complete error costs at most `14.5·10⁹`. Since `G≥Φ²/2>0`, compensation preserves the positive reserve.
- `5≤q≤7`: the retained determinant is at least `85·10⁹`; the same error bound leaves `70.5·10⁹`. The complete leading minor is at most `33100` and `G/(φ²q⁵)≥−1/2500`, so `H_K/(φ⁶q⁹)≥30·10⁹` for `0≤K≤3·10⁹`.
- `q≥7`: the existing complete-source tail gives `H_K/(φ⁶q⁹)≥5·10⁹` for `0≤K≤3·10⁹`.

Here `q=π exp(2x)`, `φ` is the first atom and `M` the positive completed theta profile. Every `x≥8/95` has `q≥37/10`, so the comparisons exhaust the half-line.

The middle proof retains the literal first two atoms and the complete deep tail `n≥3`. With `δ=exp(−8(q−49/20))/1000000`, all required normalized entry errors are proved bounded by `(10⁻⁶,10⁻³,1,200,175000)`. Exact cofactor control makes these errors smaller than the determinant reserves. The second-atom moment formula holds at every order. Complete finite derivative and reflected-error bounds now extend through twelve; the displayed flat entry ceilings and the closed determinant reserves belong to the odd rank-three comparison.

## Remaining hierarchy work

The signed Hankel cone of the actual mixed density at the difference origin is already equivalent to RH. `ThetaCuspCenterMixedSixthRank` proves its six-dimensional matrix strictly positive. `ThetaCuspCenterMixedSixPointCluster` gives one diameter bound at each critical aperture for every distinct six-point configuration, without spacing or shape restrictions.

Write `s_k(a)` for the signed mixed jet and `H_n(a)=[s_(i+j)(a)]`. The exact next scalar is

`Σ₆(a)=f_a⁽¹²⁾(0)−Σ_(i,j<6) s_(i+6)(a)(H₆(a)⁻¹)_ij s_(j+6)(a)`.

With `h_k(x)` the literal native signed jet, define

`Q_(a,n)(x)=h_(2n)(x)−Σ_(i,j<n) s_(i+n)(a)(H_n(a)⁻¹)_ij h_(j+n)(x)`.

`ThetaCuspCenterMixedSuccessorSource` proves integrability and the exact identity `Σ_n(a)=∫_(r>0) r sinh(ar)Q_(a,n)(r/2)dr` at every order. Since `H₆` is strictly positive, `H₇` is positive semidefinite exactly when this integral at `n=6` is nonnegative. Its sign remains open. This is the next actual-source comparison; the odd block is already strict, while the even block grows to dimension four. See [rank-six assembly, cluster positivity and the exact successor source](../3-formalized/clg-ttf-sixth-rank-and-successor-source.md).

A finite increase in rank does not propagate by itself. The all-order argument must supply positivity at every remaining order, with full source incidence, integrability and any correction's zero integral proved. Fixed-order decay estimates do not justify exchanging the quantifiers over order and center.

The uncorrected individual-fibre rank-five boundary remains valid: a native odd block is negative near the self-dual seam. The successful correction changes the integrand while preserving its exact integral. This supplies an explicit positive integrated survivor of the obstruction; it does not prove an all-order correction law.

## Current even rank-four source comparison

Let `m_k(x)=(-1)^k j_(2k)(x)`, `A(x)=[m_(i+j)(x)]_(i,j<3)`, and `b=(m₃,m₄,m₅)`. The actual head is strictly positive for every `x≥0`, including the self-dual seam. Define `S(x)=m₆−bᵀA⁻¹b` and the fixed positive coefficient `C_*=(|S(0)|+Φ(0)²)/Φ(0)²`.

`ThetaCuspEvenFourCompensation` proves that `[m_(i+j)]_(i,j<4)+C_*G e₃e₃ᵀ` is strictly positive near zero and on a cofinal ray. Its exact remaining scalar is `S(x)+C_*G(x)`. At zero it equals `S(0)+3|S(0)|+3Φ(0)²>0`. The full source's normalized twelfth jet tends to `2724986880`; the complete even block converges to a strict Gaussian matrix. Every fixed correction is lower order, so this tail theorem retains all source atoms.

`ThetaCuspEvenFourCenterIntegration` proves every corrected weighted entry integrable and its integral equal to the actual signed mixed derivative through order twelve. The exact flux derivative dominates `r sinh(ar)G(r/2)`, so the weighted matrix is strict near zero and on a cofinal ray simultaneously for every `a>0`.

The complete modular seam recurrence through derivative twelve proves `det E₀(0)<0`, `S(0)<0`, and the exact mass-free formula `C_*=1−D₄(X)/(D₃(X)q₀(X))`, where `X=R₀²` is the literal squared modular scale. Symbolic polynomial reserves on `191/10<X<96/5` give `10^12<C_*<3·10^12`. Every coefficient in the closed rational band repairs the seam and works on common near-zero and cofinal regions. The unique sign transition of `G` selects `10^12` as a lower comparison before the transition and `3·10^12` afterwards. See [the rational calibration, native boundary and positive survivor](../3-formalized/clg-ttf-even-compensation-rational-band.md).

The remaining sufficient source comparison is `S(x)+C_*G(x)>0` on `[δ,6/5]`. The inner threshold `δ>0` remains existential; the outer endpoint is explicit. Complete error control through derivative twelve is proved. A strictly positive interior comparison and quantitative small-center control remain to be established. The rank-seven integral sign is still unproved. See [the exact integrated compact-gap theorem](../3-formalized/clg-ttf-even-four-compact-gap.md).

## Complete finite lower comparison

`ThetaCuspEvenFourTwoAtomError` proves a finite lower bound for the actual canonical four-by-four quadratic form on `x≥8/95`. The retained matrix uses the two literal atoms and `min(10^12 G[T],3·10^12 G[T])` in its last correction entry. Its complete error matrix retains every reflected cross term, quadratic tail term and correction error. For every real vector, the canonical quadratic form is at least the retained lower form minus the full absolute-coordinate error form.

With `δ=exp(−8(q−49/20))/1000000`, the complete deep-tail derivative bound is `D_n=c_n(16q)^nδ`, where `c_n=1` through ten and `c_n=5/4` at eleven and twelve. Exact stationary-radius inequalities prove the new constants while preserving the spectral edge and calibration. All seven normalized even entries now have finite error bars. Positivity of the finite lower expression is still open; the small-center four-dimensional comparison also remains quantitative work. See [the complete source-to-matrix error proof](../3-formalized/clg-ttf-even-four-complete-error.md).

## Explicit complete-source outer margin

On `q≥30`, all seven normalized even entries differ from their literal first-atom values by at most `10^−10`. Dividing entry `k` by `32^k` and reserving `10^8` in the original last normalized coordinate gives an exact first-atom determinant of at least `1/10000`. The complete-source determinant is at least `1/20000`. Exact cofactor normalization and the strictly positive actual head then prove `S/(φ²q⁶)>10^8`.

The full correction satisfies `G/(φ²q⁶)≥−2/30⁴`. Therefore `(S+C G)/(φ²q⁶)>9·10^7` for every `0≤C≤3·10^12`. `ThetaCuspEvenFourExplicitTail` proves strictness for every `x≥6/5`, including the actual canonical coefficient, and weighted strictness for every positive aperture on `r≥12/5`. The rational family shares one remaining gap below `6/5`. See [the exact reserve, complete-source transfer and explicit tail proof](../3-formalized/clg-ttf-even-four-explicit-tail.md).

## Quantitative inner comparison target

The actual energy interval `0≤x≤8/95` gives `0≤u,w≤1`, `17≤a≤20`, `u≤w≤5u/4`, `u≥39x/4` and `a≥R₀²−228x²`. `ThetaCuspEvenCompactState` proves the coupled bounds `191/10−12u²/5≤a≤96/5−4u²/3` and exact unit parameters `a=191/10−12u²/5+t(1/10+16u²/15)`, `w=u(1+v/4)`. `ThetaCuspEvenCompactCorrection` proves `G/M²≥Q(3Q−6/19)`, where `Q=u²/24+a/16−3/8` and `M` is the completed theta mass. The exact arbitrary-center modular source and reflected polynomials now extend through twelve. A positive quartic certificate is checked, but its full determinant decomposition and transfer to the literal even matrix remain to be checked. Guidance calculations supply no sign premise.

## Available general source structure

- `ThetaCuspCenterMixedAllOrderIntegration`: exact native-to-mixed identities at every order and finite signed quadratic form.
- `ThetaCuspCenterMixedSignedJetCompleteness`: the complete signed source cone is exactly RH.
- `ThetaCuspAllOrderLikelihoodCooling` and `ThetaCuspFirstAtomAllOrderApproximation`: every fixed derivative has a complete relative error smaller than every fixed inverse scale power on a cofinal ray.
- `ThetaCuspSecondAtomAllMoments`: exact all-order polynomial-exponential second-atom moments.
- `ThetaCuspModularGlobalDriftBarrier` and `ThetaCuspModularEnergyBounds`: `0≤u<3`, decreasing `a+4u²/3<96/5`, `u≤57x/5`, `w≥u` globally.
- `ThetaCuspCenterCompensationSign`: `3+2xΦ′/Φ` decreases through one positive zero, making the dependence on the coefficient explicit on both sides.

All new capstones are kernel-checked and use only standard Lean logical axioms. Umbrella imports are wired without umbrella builds. The next task must reuse these oleans and audit only newly created results.
