# 5b-2 assembly module — complete implementation specification (handoff)

Goal: the widening-limit theorem gluing the certified chain into the machine-checked eigen-pair
Guinand-Weil identity. ALL dependencies certified/owned; two known coordinate frictions listed.

## Target statement (shape)

For zeros α, β of XiC (|Im| < 1/2), Y ∈ (1/2, 1), p := the α-fiber pole of the single-pole
integrand G(z) := deriv XiC z * xiWeilSharp F_β z * (z − p)⁻¹ (F_β := xiThetaEigenFourier β):
as X → ∞, rectIntegral G (−X − iY) (X + iY) is CONSTANT = 2πi·(deriv XiC p · sharp F_β p)
[S5B1, fixed aperture], while edge-wise:
- verticals → 0 [HTGeometry.tendsto_vertical_edge_zero_right/left with bounds from
  XiCDerivStripDecay (2A) + exists_norm_xiThetaEigenFourier_horizontal_le (18a) + the linear
  denominator ≥ X − ‖p‖];
- bottom edge (Im z = −Y) → the Λ-series + arch integral [see edge expansion below];
- top edge (Im z = +Y) → the reflected series [XiC_even folding: XiC'(−z) = −XiC'(z);
  substitute x ↦ −x via integral_neg_eq_self].
Limit identity: Λ-series-side value = 2πi·Gram-datum − arch terms — i.e., the prime-sum form.

## Edge expansion (bottom), step by step

1. On Im z = −Y: G(x − iY) = (logDeriv XiC)(x−iY)·XiC(x−iY)·sharpF_β(x−iY)·((x−iY)−p)⁻¹.
   Identity: XiC(z)/(z−p) = −I·... relate to xiThetaEigenFourier α z = I·dslope XiC α z
   (away from p: dslope = XiC(z)/(z−p) since XiC(p)=0): so XiC(z)·(z−p)⁻¹ =
   −I·xiThetaEigenFourier α z?? CHECK SIGN: I·dslope = quotient def; dslope f p z =
   (f z − f p)/(z − p) = XiC z/(z−p). So xiThetaEigenFourier α z = I·XiC(z)/(z−α) away from α
   ⇒ XiC(z)/(z−α) = −I·xiThetaEigenFourier α z (I⁻¹ = −I). With p := α (the pole at the zero
   itself — NOTE: in the D7 write-up the pole is at −α with F(z) = −XiC/(z+α); RECONCILE: use
   p = α and the quotient at parameter α directly — the fiber-delta evaluations
   (xiThetaEigenFourier_spectralPoint_eq_zero) are stated at parameter α, value at α =
   I·deriv XiC α: S5B1's residue datum deriv XiC p · sharp F_β p matches the diagonal Gram
   through these; the assembly should stay in the (parameter α, pole at α) convention
   throughout and NEVER mix with the −α convention of the transform identity — friction #1.)
2. So bottom-edge integrand = (logDeriv XiC)(x−iY)·(−I·F_α(x−iY))·sharpF_β(x−iY).
   logDeriv split: logDeriv_completed_split (read in source, XiRelativeResolventFlux) gives
   arch part + zeta part; zeta part at s = 1/2 + (x−iY)·I... CHECK the corpus's s(z) map:
   primeArchSourceRelativeTrace uses s = 1/2 + z·I: for z = x − iY: s = (1/2 + Y) + x·I:
   Re s = 1/2 + Y > 1 ✓ vertical line in s ⇔ horizontal in z; the LSeries lives on
   σ := 1/2 + Y with frequency x — MATCHES stage 1's parametrization
   (integral_LSeries_vonMangoldt_mul_eq_tsum at σ = 1/2+Y, F := pair-line) ✓ — friction #2 is
   only the I-factor bookkeeping between logDeriv XiC (z-derivative) and the s-derivative:
   d/dz = I·d/ds; the resolvent trace already absorbs this (primeArchSourceRelativeTrace has
   the −i prefactor) — pin against XiRelativeResolventFlux's exact statements.
3. Pair-line F := fun x => F_α(x−iY)·sharpF_β(x−iY): integrable = EigenPairLineIntegrable
   (sharpF_β on the line: sharp F(x−iY) = conj(F_β(conj(x−iY))) = conj(F_β(x+iY)) ✓ exactly
   5a-2's second factor).
4. Per-frequency integrals: stage 1 gives Σ' n ∫ term·F; each ∫ = time-side sample via:
   pair-line = phase × transform-pair (T = i·quotient(−α)-form — the (α ↔ −α) reconciliation
   AGAIN: alternatively re-prove 5a-3a directly for quotient pairs: quotient F_α =
   i·dslope-form has the same 𝓕-representation with tilted eigenfunction of parameter −α...
   safest: state the assembly's prime side abstractly as Σ' n Λ(n)·(pair-line frequency
   integrals) and identify with time-side samples via 5a-3a/5a-3b applied to the transform
   pair, then convert quotient↔transform by the phase identity
   hedenmalmThetaEigenTransform_eq_xiThetaEigenFourier (i·(−α)-parameter) ONCE, at the end.
5. Widening limit: the tsum is X-independent only after the FULL-line integral is taken — the
   edges at finite X are truncated integrals; the limit step needs dominated convergence of
   truncated line integrals to the full-line integral (interval → ℝ): use
   intervalIntegral_tendsto_integral (mathlib: `MeasureTheory.intervalIntegral_tendsto_integral`
   for integrable functions, atTop... exists) with 5a-2's integrability — per-term, then
   dominated again for the tsum (bounds from integral_norm_vonMangoldtLine_term's exact values).

## Module plan

`RHTower/EigenPairWideningAssembly.lean`:
  L1: bottom-edge rewrite lemma (integrand → logDeriv-split × quotient pair) [frictions 1-2].
  L2: truncated-to-full-line limits (per term + tsum) via intervalIntegral_tendsto_integral.
  L3: vertical instantiation (2B with 2A + 18a + ‖(z−p)⁻¹‖ ≤ (X − ‖p‖)⁻¹).
  L4: top-edge folding via XiC_even/deriv-odd + integral_neg_eq_self.
  MAIN: limit of rectIntegral = const (S5B1) ⇒ prime-sum identity.

Est. 300-500 lines; recommend splitting L1-L2 as their own module first.

## Convention pins already verified (do not re-derive)

e^{−izx} transform; XiC z = xi(1/2+zI), even; xiWeilSharp F z = conj(F(conj z));
rectIntegral = (bottom − top) + i·right − i·left with intervalIntegral edges; quotient =
I·dslope XiC α; 18a substrip decay both for XiC and the quotient; deriv-XiC decay (2A).
