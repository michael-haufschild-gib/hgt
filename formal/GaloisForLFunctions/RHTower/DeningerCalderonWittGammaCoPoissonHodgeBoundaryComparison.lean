import GaloisForLFunctions.RHTower.DeningerCalderonWittSingularGammaTransgression
import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedGammaCoPoissonGreenTransport
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedChainSource

/-!
# Calderón--Witt Green comparison with the Gamma/co-Poisson Hodge boundary

The singular Calderón--Witt transport and the polarized Gamma/Hardy
boundary are not merely governed by similar exponential coefficients.
This file constructs their chain-level comparison.

For a pair of prime/depth cells `i,j`, the positive source action is

`t(i,j) = -(r_i + r_j) = 2(h_i+h_j)`.

The primitive modular exterior is exactly evaluation at `t(i,j)` of the
actual two-channel Euler boundary common test, multiplied by the undeformed
vector-valued exterior amplitude.  The same evaluation is the confluent
Gamma/co-Poisson modular exterior.  Applying this feature to the nonlocal
Calderón--Witt cross-effect gives a vector-valued polarized boundary
transport; evaluation recovers the previously constructed singular
transport exactly.

The comparison is analytic rather than fitted coefficient matching: the
full weighted head/tail pairing gives the unshifted Cauchy response, and
differentiating the literal moving Gamma head and translated Hardy tail
gives the oriented source transport `(E,-E)`.  Thus the source Green
primitive is the actual moving-horizon boundary Green endpoint.

The scalar singular Hodge rotation on the Gamma-head/Hardy-tail feature is
lifted to the vector-valued suspension center before normalized Haar
orientation.  Orientation strictly intertwines the two Hodge rotations.
Finally, the reflection defect read from the two actual boundary channels
is proved equal to the source reflection-odd transport.  Consequently the
concrete admitted sector is literally the kernel of the Gamma/co-Poisson
Hodge-boundary defect, rather than a separately declared proxy sector.

No Xi divisor, Ward response, positivity premise, or RH hypothesis enters
the construction or proofs.
-/

namespace RHTower

open scoped DirectSum

noncomputable section

/-! ## The actual common-test realization of the modular exterior -/

/-- Positive Gamma/Hardy action carried by two source cells. -/
def xiGammaEulerPrimitivePolarizedPairAction
    (i j : Nat.Primes × ℕ) : ℝ :=
  -(xiGammaEulerPrimitiveModularRate i +
    xiGammaEulerPrimitiveModularRate j)

theorem xiGammaEulerPrimitivePolarizedPairAction_pos
    (i j : Nat.Primes × ℕ) :
    0 < xiGammaEulerPrimitivePolarizedPairAction i j := by
  rw [xiGammaEulerPrimitivePolarizedPairAction,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  have hi := xiGammaEulerBoundaryHalfHeight_pos i
  have hj := xiGammaEulerBoundaryHalfHeight_pos j
  linarith

/--
Two-channel Gamma/Hardy feature whose evaluation is the primitive modular
exterior.  Both channels retain the common test; their different energies
and Hodge exchange are supplied by the polarized boundary source.
-/
def xiGammaEulerPrimitivePolarizedExteriorFeature
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  let c : ℂ :=
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2) : ℝ)
  let x :=
    eulerPrimitiveBoundaryPolarizedTest (a : ℂ)
  (fun t => c * x.1 t, fun t => c * x.2 t)

/-- Undeformed oriented two-cell amplitude, before the common test acts. -/
def xiGammaEulerPrimitiveUndeformedExteriorAmplitude
    (i j : Nat.Primes × ℕ) : ℂ :=
  ((xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2) : ℝ) : ℂ)

theorem xiGammaEulerPrimitivePolarizedExteriorFeature_eq_smul_test
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitivePolarizedExteriorFeature a i j =
      xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j •
        eulerPrimitiveBoundaryPolarizedTest (a : ℂ) := by
  rfl

/-- The actual head/tail pairing is complex-linear in its first input. -/
theorem eulerPrimitiveBoundaryPolarizedPairing_smul_left
    (c : ℂ) (x y : EulerPrimitiveBoundaryPolarizedFeature) :
    eulerPrimitiveBoundaryPolarizedPairing (c • x) y =
      c * eulerPrimitiveBoundaryPolarizedPairing x y := by
  simp only [eulerPrimitiveBoundaryPolarizedPairing,
    Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1
  · rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  · rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring

/--
The transported exterior is not merely point-evaluated from an exponential:
against every right-half-plane common test it has the exact unshifted
Gamma/Hardy Cauchy response.
-/
theorem xiGammaEulerPrimitivePolarizedExteriorFeature_pairing_test
    {a : ℝ} (ha : 0 < a) {b : ℂ} (hb : 0 < b.re)
    (i j : Nat.Primes × ℕ) :
    eulerPrimitiveBoundaryPolarizedPairing
        (xiGammaEulerPrimitivePolarizedExteriorFeature a i j)
        (eulerPrimitiveBoundaryPolarizedTest b) =
      xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j /
        ((a : ℂ) + star b) := by
  rw [xiGammaEulerPrimitivePolarizedExteriorFeature_eq_smul_test,
    eulerPrimitiveBoundaryPolarizedPairing_smul_left,
    eulerPrimitiveBoundaryPolarizedPairing_test_test
      (by simpa using ha) hb]
  rw [mul_one_div]

/--
At every source action the common test is the literal moving-horizon
endpoint kernel with symmetric spectral arguments.
-/
theorem
    xiGammaEulerPrimitivePolarizedExteriorFeature_eq_horizonEndpoint
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction i j
    (xiGammaEulerPrimitivePolarizedExteriorFeature a i j).1 t =
        xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j *
          eulerPrimitiveAnalyticHorizonEndpointKernel (t : ℂ)
            ((a / 2 : ℝ) : ℂ) ((a / 2 : ℝ) : ℂ) ∧
      (xiGammaEulerPrimitivePolarizedExteriorFeature a i j).2 t =
        xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j *
          eulerPrimitiveAnalyticHorizonEndpointKernel (t : ℂ)
            ((a / 2 : ℝ) : ℂ) ((a / 2 : ℝ) : ℂ) := by
  dsimp only
  constructor <;>
    simp only [xiGammaEulerPrimitivePolarizedExteriorFeature,
      xiGammaEulerPrimitiveUndeformedExteriorAmplitude,
      eulerPrimitiveBoundaryPolarizedTest,
      eulerPrimitiveAnalyticHorizonEndpointKernel,
      Function.comp_apply, RCLike.star_def, Complex.conj_ofReal]
  all_goals
    congr 2
    push_cast
    ring

/--
The two polarized channels are exactly the oriented derivative of the
actual compact Gamma head and translated Hardy tail.  Their common value is
the boundary Green primitive, with signs `(E,-E)`.
-/
theorem
    xiGammaEulerPrimitivePolarizedExteriorFeature_movingHorizon_boundary
    {a : ℝ} (ha : a ≠ 0) (i j : Nat.Primes × ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction i j
    let u : ℂ := ((a / 2 : ℝ) : ℂ)
    let c := xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j
    HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonHeadKernel L u u)
        ((xiGammaEulerPrimitivePolarizedExteriorFeature a i j).1 t)
        (t : ℂ) ∧
      HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonTailKernel L u u)
        (-(xiGammaEulerPrimitivePolarizedExteriorFeature a i j).2 t)
        (t : ℂ) := by
  dsimp only
  have hu :
      ((a / 2 : ℝ) : ℂ) + star ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    simpa [RCLike.star_def] using (Complex.ofReal_ne_zero.mpr ha)
  have hboundary :=
    xiGammaEulerPrimitivePolarizedExteriorFeature_eq_horizonEndpoint
      a i j
  constructor
  · rw [hboundary.1]
    exact
      (hasDerivAt_eulerPrimitiveAnalyticHorizonHeadKernel
        (L := (xiGammaEulerPrimitivePolarizedPairAction i j : ℂ))
        (w := ((a / 2 : ℝ) : ℂ)) (v := ((a / 2 : ℝ) : ℂ)) hu).const_mul
          (xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j)
  · rw [hboundary.2]
    simpa only [mul_neg, neg_mul] using
      (hasDerivAt_eulerPrimitiveAnalyticHorizonTailKernel
        (L := (xiGammaEulerPrimitivePolarizedPairAction i j : ℂ))
        (w := ((a / 2 : ℝ) : ℂ)) (v := ((a / 2 : ℝ) : ℂ)) hu).const_mul
          (xiGammaEulerPrimitiveUndeformedExteriorAmplitude i j)

theorem xiGammaEulerPrimitivePolarizedExteriorFeature_fst_eval
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    (xiGammaEulerPrimitivePolarizedExteriorFeature a i j).1
        (xiGammaEulerPrimitivePolarizedPairAction i j) =
      (xiGammaEulerPrimitiveModularExterior a i j : ℂ) := by
  rw [xiGammaEulerPrimitiveModularExterior_eq]
  simp only [xiGammaEulerPrimitivePolarizedExteriorFeature,
    eulerPrimitiveBoundaryPolarizedTest,
    xiGammaEulerPrimitivePolarizedPairAction]
  rw [show
    -((a : ℂ)) *
        ((-(xiGammaEulerPrimitiveModularRate i +
          xiGammaEulerPrimitiveModularRate j) : ℝ) : ℂ) =
      ((a * (xiGammaEulerPrimitiveModularRate i +
        xiGammaEulerPrimitiveModularRate j) : ℝ) : ℂ) by
      push_cast
      ring]
  rw [← Complex.ofReal_exp]
  norm_cast
  ring

theorem xiGammaEulerPrimitivePolarizedExteriorFeature_snd_eval
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    (xiGammaEulerPrimitivePolarizedExteriorFeature a i j).2
        (xiGammaEulerPrimitivePolarizedPairAction i j) =
      (xiGammaEulerPrimitiveModularExterior a i j : ℂ) := by
  rw [xiGammaEulerPrimitiveModularExterior_eq]
  simp only [xiGammaEulerPrimitivePolarizedExteriorFeature,
    eulerPrimitiveBoundaryPolarizedTest,
    xiGammaEulerPrimitivePolarizedPairAction]
  rw [show
    -((a : ℂ)) *
        ((-(xiGammaEulerPrimitiveModularRate i +
          xiGammaEulerPrimitiveModularRate j) : ℝ) : ℂ) =
      ((a * (xiGammaEulerPrimitiveModularRate i +
        xiGammaEulerPrimitiveModularRate j) : ℝ) : ℂ) by
      push_cast
      ring]
  rw [← Complex.ofReal_exp]
  norm_cast
  ring

/--
The common-test evaluation is the actual confluent Gamma/co-Poisson
exterior, not a fitted replacement coefficient.
-/
theorem
    xiGammaEulerPrimitivePolarizedExteriorFeature_eval_eq_gammaCoPoisson
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    (xiGammaEulerPrimitivePolarizedExteriorFeature a i j).1
        (xiGammaEulerPrimitivePolarizedPairAction i j) =
      xiGammaEulerPrimitiveGammaCoPoissonModularExterior a i j := by
  rw [xiGammaEulerPrimitivePolarizedExteriorFeature_fst_eval,
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]

/-! ## Vector-valued boundary comparison before orientation -/

/-- Polarized boundary feature retaining the actual suspension center. -/
abbrev DeningerCalderonWittGammaHodgeBoundaryVectorFeature
    (q : Nat.Primes) :=
  (ℝ → DeningerCalderonWittAlgebraicDegreeTwo q) ×
    (ℝ → DeningerCalderonWittAlgebraicDegreeTwo q)

/-- Prime/depth-labelled vector-valued polarized boundary profile. -/
abbrev DeningerCalderonWittGammaHodgeBoundaryVectorProfile :=
  (p : Nat.Primes) → (q : Nat.Primes) → ℕ → ℕ →
    DeningerCalderonWittGammaHodgeBoundaryVectorFeature q

/--
The actual common-test feature acts on the nonlocal vector-valued
Calderón--Witt exterior.  No scalar trace has yet been taken.
-/
def deningerCalderonWittGammaPolarizedVectorTransport
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaHodgeBoundaryVectorProfile where
  toFun s p q e f :=
    (fun t =>
      deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).1 t)
        p q s.1,
    fun t =>
      deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).2 t)
        p q s.1)
  map_add' s u := by
    funext p q e f
    apply Prod.ext <;> funext t <;> simp
  map_smul' c s := by
    funext p q e f
    apply Prod.ext <;> funext t <;> simp

/-- Head-channel evaluation recovers the singular vector transport. -/
theorem deningerCalderonWittGammaPolarizedVectorTransport_fst_eval
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaPolarizedVectorTransport
        a s p q e f).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerCalderonWittGammaModularVectorTransport
        a s p q e f := by
  change
    deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).1
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)))
        p q s.1 =
      deningerCalderonWittWeightedNonlocalExterior
        (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ)
        p q s.1
  rw [xiGammaEulerPrimitivePolarizedExteriorFeature_fst_eval]

/-- Tail-channel evaluation recovers the same unsplit vector transport. -/
theorem deningerCalderonWittGammaPolarizedVectorTransport_snd_eval
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaPolarizedVectorTransport
        a s p q e f).2
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerCalderonWittGammaModularVectorTransport
        a s p q e f := by
  change
    deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).2
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)))
        p q s.1 =
      deningerCalderonWittWeightedNonlocalExterior
        (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ)
        p q s.1
  rw [xiGammaEulerPrimitivePolarizedExteriorFeature_snd_eval]

/-! ## Vector lift of the singular Hodge rotation -/

/-- Normalized Haar orientation applied componentwise after transport. -/
def deningerCalderonWittGammaBoundaryVectorOrientation
    (q : Nat.Primes)
    (x : DeningerCalderonWittGammaHodgeBoundaryVectorFeature q) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t => deningerCalderonWittAlgebraicCenterTrace q (x.1 t),
    fun t => deningerCalderonWittAlgebraicCenterTrace q (x.2 t))

theorem
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f)).1
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerCalderonWittGammaModularScalarTransport
        a s p q e f := by
  change
    deningerCalderonWittAlgebraicCenterTrace q
        ((deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f).1
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f))) =
      deningerCalderonWittAlgebraicCenterTrace q
        (deningerCalderonWittGammaModularVectorTransport
          a s p q e f)
  rw [deningerCalderonWittGammaPolarizedVectorTransport_fst_eval]

theorem
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_snd_eval
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f)).2
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerCalderonWittGammaModularScalarTransport
        a s p q e f := by
  change
    deningerCalderonWittAlgebraicCenterTrace q
        ((deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f).2
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f))) =
      deningerCalderonWittAlgebraicCenterTrace q
        (deningerCalderonWittGammaModularVectorTransport
          a s p q e f)
  rw [deningerCalderonWittGammaPolarizedVectorTransport_snd_eval]

/--
Vector-valued lift of the actual singular head/tail Hodge rotation.  It is
defined before Haar orientation on the suspension center.
-/
def deningerCalderonWittGammaBoundaryVectorOddHodge
    (q : Nat.Primes)
    (x : DeningerCalderonWittGammaHodgeBoundaryVectorFeature q) :
    DeningerCalderonWittGammaHodgeBoundaryVectorFeature q :=
  (fun t =>
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) • x.2 t,
    fun t =>
      (-(eulerPrimitiveBoundaryHodgeScale t : ℂ)⁻¹) • x.1 t)

/--
Haar orientation strictly intertwines the vector lift with the actual
scalar Gamma/Hardy Hodge rotation.
-/
theorem deningerCalderonWittGammaBoundaryVectorOrientation_oddHodge
    (q : Nat.Primes)
    (x : DeningerCalderonWittGammaHodgeBoundaryVectorFeature q) :
    deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaBoundaryVectorOddHodge q x) =
      eulerPrimitiveBoundaryOddHodge
        (deningerCalderonWittGammaBoundaryVectorOrientation q x) := by
  apply Prod.ext <;> funext t
  · simp [deningerCalderonWittGammaBoundaryVectorOrientation,
      deningerCalderonWittGammaBoundaryVectorOddHodge,
      eulerPrimitiveBoundaryOddHodge]
  · simp [deningerCalderonWittGammaBoundaryVectorOrientation,
      deningerCalderonWittGammaBoundaryVectorOddHodge,
      eulerPrimitiveBoundaryOddHodge, div_eq_mul_inv]
    ring

/-- The vector Hodge lift squares to `-1` on the open source ray. -/
theorem deningerCalderonWittGammaBoundaryVectorOddHodge_sq
    (q : Nat.Primes)
    (x : DeningerCalderonWittGammaHodgeBoundaryVectorFeature q)
    {t : ℝ} (ht : 0 < t) :
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaBoundaryVectorOddHodge q x)).1 t =
        -x.1 t ∧
      (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaBoundaryVectorOddHodge q x)).2 t =
        -x.2 t := by
  have hq :
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (eulerPrimitiveBoundaryHodgeScale_pos ht).ne'
  constructor
  · simp only [deningerCalderonWittGammaBoundaryVectorOddHodge]
    rw [smul_smul]
    change
      ((eulerPrimitiveBoundaryHodgeScale t : ℂ) *
        (-(eulerPrimitiveBoundaryHodgeScale t : ℂ)⁻¹)) • x.1 t =
          -x.1 t
    rw [mul_neg, mul_inv_cancel₀ hq]
    simp
  · simp only [deningerCalderonWittGammaBoundaryVectorOddHodge,
      smul_smul]
    change
      ((-(eulerPrimitiveBoundaryHodgeScale t : ℂ)⁻¹) *
        (eulerPrimitiveBoundaryHodgeScale t : ℂ)) • x.2 t =
          -x.2 t
    rw [neg_mul, inv_mul_cancel₀ hq]
    simp

/-- Exact Hodge rotation of the evaluated singular source transport. -/
theorem deningerCalderonWittGammaBoundaryVectorOddHodge_transport_eval
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f)).1 t =
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) •
        deningerCalderonWittGammaModularVectorTransport a s p q e f ∧
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f)).2 t =
      (-(eulerPrimitiveBoundaryHodgeScale t : ℂ)⁻¹) •
        deningerCalderonWittGammaModularVectorTransport a s p q e f := by
  dsimp only
  constructor
  · change
      (eulerPrimitiveBoundaryHodgeScale
          (xiGammaEulerPrimitivePolarizedPairAction
            (p, e) (q, f)) : ℂ) •
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f).2
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
        _
    rw [deningerCalderonWittGammaPolarizedVectorTransport_snd_eval]
  · change
      (-(eulerPrimitiveBoundaryHodgeScale
          (xiGammaEulerPrimitivePolarizedPairAction
            (p, e) (q, f)) : ℂ)⁻¹) •
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f).1
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
        _
    rw [deningerCalderonWittGammaPolarizedVectorTransport_fst_eval]

/-- Every source-cell pair lies in the open domain of the Hodge lift. -/
theorem
    deningerCalderonWittGammaBoundaryVectorOddHodge_sq_on_sourceAction
    (q : Nat.Primes)
    (x : DeningerCalderonWittGammaHodgeBoundaryVectorFeature q)
    (i j : Nat.Primes × ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction i j
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaBoundaryVectorOddHodge q x)).1 t =
        -x.1 t ∧
      (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaBoundaryVectorOddHodge q x)).2 t =
        -x.2 t := by
  exact deningerCalderonWittGammaBoundaryVectorOddHodge_sq q x
    (xiGammaEulerPrimitivePolarizedPairAction_pos i j)

/-! ## Exact identification of the admitted sector -/

/-- Coefficient dependence of the nonlocal vector exterior is linear. -/
def deningerCalderonWittNonlocalExteriorCoefficientMap
    (p q : Nat.Primes) :
    ℂ →ₗ[ℂ]
      ((⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne) →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo q) where
  toFun c := deningerCalderonWittWeightedNonlocalExterior c p q
  map_add' c d := by
    unfold deningerCalderonWittWeightedNonlocalExterior
    rw [← map_add]
    apply congrArg exteriorPower.alternatingMapLinearEquiv
    apply AlternatingMap.ext
    intro v
    change
      (c + d) •
          deningerCalderonWittNonlocalCrossEffect p q (v 0) (v 1) =
        c • deningerCalderonWittNonlocalCrossEffect p q (v 0) (v 1) +
          d • deningerCalderonWittNonlocalCrossEffect p q (v 0) (v 1)
    rw [add_smul]
  map_smul' c d := by
    unfold deningerCalderonWittWeightedNonlocalExterior
    rw [← map_smul]
    apply congrArg exteriorPower.alternatingMapLinearEquiv
    apply AlternatingMap.ext
    intro v
    change
      (c * d) •
          deningerCalderonWittNonlocalCrossEffect p q (v 0) (v 1) =
        c • (d •
          deningerCalderonWittNonlocalCrossEffect p q (v 0) (v 1))
    rw [smul_smul]

/--
Undeformed oriented Calderón--Witt coefficient carried by one labelled
incidence relation.  The suspension center remains vector-valued until the
last displayed Haar trace.
-/
def deningerCalderonWittGammaUndeformedScalarCoefficient
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) : ℂ :=
  deningerCalderonWittAlgebraicCenterTrace q
    (deningerCalderonWittWeightedNonlocalExterior
      (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
        (p, e) (q, f)) p q s.1)

/--
Before evaluation, the oriented Calderón--Witt boundary transport is
exactly its source coefficient times the actual two-channel common test.
-/
theorem
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_eq_smul_test
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f) =
      deningerCalderonWittGammaUndeformedScalarCoefficient
          s p q e f •
        eulerPrimitiveBoundaryPolarizedTest (a : ℂ) := by
  unfold deningerCalderonWittGammaBoundaryVectorOrientation
  apply Prod.ext
  · funext t
    simp only [Prod.smul_fst, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul]
    change
      deningerCalderonWittAlgebraicCenterTrace q
          ((deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f).1 t) =
        deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    change
      deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittWeightedNonlocalExterior
            ((xiGammaEulerPrimitivePolarizedExteriorFeature
              a (p, e) (q, f)).1 t) p q s.1) =
        deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    rw [xiGammaEulerPrimitivePolarizedExteriorFeature_eq_smul_test]
    simp only [Prod.smul_fst, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul]
    change
      deningerCalderonWittAlgebraicCenterTrace q
          ((deningerCalderonWittNonlocalExteriorCoefficientMap p q
            (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f) *
              Complex.exp (-(a : ℂ) * (t : ℂ)))) s.1) = _
    rw [show
      xiGammaEulerPrimitiveUndeformedExteriorAmplitude
              (p, e) (q, f) *
            Complex.exp (-(a : ℂ) * (t : ℂ)) =
        Complex.exp (-(a : ℂ) * (t : ℂ)) •
          xiGammaEulerPrimitiveUndeformedExteriorAmplitude
            (p, e) (q, f) by
          simp only [smul_eq_mul]
          ring]
    rw [map_smul, LinearMap.smul_apply, map_smul]
    simp only [deningerCalderonWittGammaUndeformedScalarCoefficient,
      smul_eq_mul]
    change
      Complex.exp (-(a : ℂ) * (t : ℂ)) *
          deningerCalderonWittAlgebraicCenterTrace q
            (deningerCalderonWittWeightedNonlocalExterior
              (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f)) p q s.1) =
        deningerCalderonWittAlgebraicCenterTrace q
            (deningerCalderonWittWeightedNonlocalExterior
              (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f)) p q s.1) *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    ring
  · funext t
    simp only [Prod.smul_snd, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul]
    change
      deningerCalderonWittAlgebraicCenterTrace q
          ((deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f).2 t) =
        deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    change
      deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittWeightedNonlocalExterior
            ((xiGammaEulerPrimitivePolarizedExteriorFeature
              a (p, e) (q, f)).2 t) p q s.1) =
        deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    rw [xiGammaEulerPrimitivePolarizedExteriorFeature_eq_smul_test]
    simp only [Prod.smul_snd, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul]
    change
      deningerCalderonWittAlgebraicCenterTrace q
          ((deningerCalderonWittNonlocalExteriorCoefficientMap p q
            (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f) *
              Complex.exp (-(a : ℂ) * (t : ℂ)))) s.1) = _
    rw [show
      xiGammaEulerPrimitiveUndeformedExteriorAmplitude
              (p, e) (q, f) *
            Complex.exp (-(a : ℂ) * (t : ℂ)) =
        Complex.exp (-(a : ℂ) * (t : ℂ)) •
          xiGammaEulerPrimitiveUndeformedExteriorAmplitude
            (p, e) (q, f) by
          simp only [smul_eq_mul]
          ring]
    rw [map_smul, LinearMap.smul_apply, map_smul]
    simp only [deningerCalderonWittGammaUndeformedScalarCoefficient,
      smul_eq_mul]
    change
      Complex.exp (-(a : ℂ) * (t : ℂ)) *
          deningerCalderonWittAlgebraicCenterTrace q
            (deningerCalderonWittWeightedNonlocalExterior
              (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f)) p q s.1) =
        deningerCalderonWittAlgebraicCenterTrace q
            (deningerCalderonWittWeightedNonlocalExterior
              (xiGammaEulerPrimitiveUndeformedExteriorAmplitude
                (p, e) (q, f)) p q s.1) *
          Complex.exp (-(a : ℂ) * (t : ℂ))
    ring

/--
The full source transport has the exact Gamma/Hardy Cauchy response.  This
is the weighted boundary pairing, not evaluation at a fitted source time.
-/
theorem
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_pairing_test
    {a : ℝ} (ha : 0 < a) {b : ℂ} (hb : 0 < b.re)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    eulerPrimitiveBoundaryPolarizedPairing
        (deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f))
        (eulerPrimitiveBoundaryPolarizedTest b) =
      deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f /
        ((a : ℂ) + star b) := by
  rw [
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_eq_smul_test,
    eulerPrimitiveBoundaryPolarizedPairing_smul_left,
    eulerPrimitiveBoundaryPolarizedPairing_test_test
      (by simpa using ha) hb,
    mul_one_div]

/--
The oriented source transport is itself the Green endpoint of the genuine
moving Gamma-head/Hardy-tail boundary.
-/
theorem
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_movingHorizon
    {a : ℝ} (ha : a ≠ 0)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    let u : ℂ := ((a / 2 : ℝ) : ℂ)
    let c :=
      deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f
    HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonHeadKernel L u u)
        ((deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f)).1 t)
        (t : ℂ) ∧
      HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonTailKernel L u u)
        (-((deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f)).2 t))
        (t : ℂ) := by
  dsimp only
  have hu :
      ((a / 2 : ℝ) : ℂ) + star ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    simpa [RCLike.star_def] using (Complex.ofReal_ne_zero.mpr ha)
  have hfeature :=
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_eq_smul_test
      a s p q e f
  have hhead :
      (deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f)).1
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
        deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f *
          eulerPrimitiveAnalyticHorizonEndpointKernel
            (xiGammaEulerPrimitivePolarizedPairAction
              (p, e) (q, f) : ℂ)
            ((a / 2 : ℝ) : ℂ) ((a / 2 : ℝ) : ℂ) := by
    rw [hfeature]
    simp only [Prod.smul_fst, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul,
      eulerPrimitiveAnalyticHorizonEndpointKernel,
      Function.comp_apply, RCLike.star_def, Complex.conj_ofReal]
    congr 2
    push_cast
    ring
  have htail :
      (deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f)).2
          (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
        deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f *
          eulerPrimitiveAnalyticHorizonEndpointKernel
            (xiGammaEulerPrimitivePolarizedPairAction
              (p, e) (q, f) : ℂ)
            ((a / 2 : ℝ) : ℂ) ((a / 2 : ℝ) : ℂ) := by
    rw [hfeature]
    simp only [Prod.smul_snd, Pi.smul_apply,
      eulerPrimitiveBoundaryPolarizedTest, smul_eq_mul,
      eulerPrimitiveAnalyticHorizonEndpointKernel,
      Function.comp_apply, RCLike.star_def, Complex.conj_ofReal]
    congr 2
    push_cast
    ring
  constructor
  · rw [hhead]
    exact
      (hasDerivAt_eulerPrimitiveAnalyticHorizonHeadKernel
        (L := (xiGammaEulerPrimitivePolarizedPairAction
          (p, e) (q, f) : ℂ))
        (w := ((a / 2 : ℝ) : ℂ)) (v := ((a / 2 : ℝ) : ℂ)) hu).const_mul
          (deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f)
  · rw [htail]
    simpa only [mul_neg, neg_mul] using
      (hasDerivAt_eulerPrimitiveAnalyticHorizonTailKernel
        (L := (xiGammaEulerPrimitivePolarizedPairAction
          (p, e) (q, f) : ℂ))
        (w := ((a / 2 : ℝ) : ℂ)) (v := ((a / 2 : ℝ) : ℂ)) hu).const_mul
          (deningerCalderonWittGammaUndeformedScalarCoefficient
            s p q e f)

/--
Reflection defect read from the oriented head and reflected tail of the
actual polarized boundary feature.
-/
def deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaScalarProfile where
  toFun s p q e f :=
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    ((deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport
          a s p q e f)).1 t -
      (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport
          (-a) s p q e f)).2 t) / 2
  map_add' s u := by
    funext p q e f
    simp [deningerCalderonWittGammaBoundaryVectorOrientation,
      deningerCalderonWittGammaPolarizedVectorTransport]
    ring
  map_smul' c s := by
    funext p q e f
    simp [deningerCalderonWittGammaBoundaryVectorOrientation,
      deningerCalderonWittGammaPolarizedVectorTransport]
    ring

/--
The actual Gamma/Hardy boundary reflection defect equals the previously
constructed source reflection-odd transport on every incidence relation.
-/
theorem
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq
    (a : ℝ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a =
      deningerCalderonWittGammaReflectionOddScalarTransport a := by
  apply LinearMap.ext
  intro s
  funext p q e f
  change
    ((deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            a s p q e f)).1
            (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) -
        (deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedVectorTransport
            (-a) s p q e f)).2
            (xiGammaEulerPrimitivePolarizedPairAction
              (p, e) (q, f))) / 2 =
      deningerCalderonWittGammaReflectionOddScalarTransport
        a s p q e f
  rw [
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval,
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_snd_eval]
  change
    (deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittGammaModularVectorTransport
            a s p q e f) -
        deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittGammaModularVectorTransport
            (-a) s p q e f)) / 2 =
    deningerCalderonWittAlgebraicCenterTrace q
      (deningerCalderonWittWeightedNonlocalExterior
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, e) (q, f) : ℂ) p q s.1)
  rw [show
    (deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittGammaModularVectorTransport
            a s p q e f) -
        deningerCalderonWittAlgebraicCenterTrace q
          (deningerCalderonWittGammaModularVectorTransport
            (-a) s p q e f)) / 2 =
      deningerCalderonWittAlgebraicCenterTrace q
        ((2 : ℂ)⁻¹ •
          (deningerCalderonWittGammaModularVectorTransport
              a s p q e f -
            deningerCalderonWittGammaModularVectorTransport
              (-a) s p q e f)) by
      rw [map_smul, map_sub]
      simp only [smul_eq_mul]
      ring]
  apply congrArg (deningerCalderonWittAlgebraicCenterTrace q)
  change
    (2 : ℂ)⁻¹ •
        ((deningerCalderonWittNonlocalExteriorCoefficientMap p q
            (xiGammaEulerPrimitiveModularExterior
              a (p, e) (q, f) : ℂ)) s.1 -
          (deningerCalderonWittNonlocalExteriorCoefficientMap p q
            (xiGammaEulerPrimitiveModularExterior
              (-a) (p, e) (q, f) : ℂ)) s.1) =
      (deningerCalderonWittNonlocalExteriorCoefficientMap p q
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, e) (q, f) : ℂ)) s.1
  rw [← LinearMap.sub_apply, ← LinearMap.smul_apply,
    ← map_sub, ← map_smul]
  apply congrArg
    (fun c : ℂ =>
      (deningerCalderonWittNonlocalExteriorCoefficientMap p q c) s.1)
  unfold xiGammaEulerPrimitiveReflectionOddExterior
  push_cast
  ring

/--
The source-defined admitted sector is exactly the kernel of the actual
Gamma/co-Poisson Hodge-boundary reflection defect.
-/
theorem
    deningerCalderonWittGammaAdmittedHodgeSector_eq_boundaryDefectKernel
    (a : ℝ) :
    deningerCalderonWittGammaAdmittedHodgeSector a =
      LinearMap.ker
        (deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a) := by
  rw [deningerCalderonWittGammaAdmittedHodgeSector,
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq]

/--
On the canonical exact cross-prime Green boundary, orientation of the
vector comparison is literally the confluent Gamma/co-Poisson exterior.
-/
theorem
    deningerCalderonWittGammaPolarizedVectorTransport_crossPrime_orientation_eq_coPoisson
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport a
          (deningerCalderonWittCrossPrimeGammaWitness hpq)
          p q e f)).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      xiGammaEulerPrimitiveGammaCoPoissonModularExterior
        a (p, e) (q, f) := by
  rw [
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval,
    deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness,
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]

/-! ## Comparison on the canonical Green primitive -/

/-- Green retraction fixes every actual incidence relation. -/
theorem deningerCalderonWittGlobalMilnorGreenRetraction_incidence
    (s : deningerCalderonWittGlobalMilnorIncidence) :
    deningerCalderonWittGlobalMilnorGreenRetraction s.1 = s := by
  apply Subtype.ext
  rw [deningerCalderonWittGlobalMilnorGreenRetraction_coe,
    s.2, map_zero, sub_zero]

/--
Polarized Gamma/co-Poisson boundary comparison applied to the canonical
source Green primitive of an arbitrary exterior cochain.
-/
def deningerCalderonWittGammaPolarizedGreenTransport
    (a : ℝ) :
    (⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne) →ₗ[ℂ]
      DeningerCalderonWittGammaHodgeBoundaryVectorProfile :=
  (deningerCalderonWittGammaPolarizedVectorTransport a).comp
    deningerCalderonWittGlobalMilnorGreenRetraction

/--
The canonical source Green primitive is carried to the genuine
moving-horizon Gamma/Hardy boundary.  Head derivative is its oriented
transport and tail derivative is its negative.
-/
theorem deningerCalderonWittGammaPolarizedGreenTransport_movingHorizon
    {a : ℝ} (ha : a ≠ 0)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (p q : Nat.Primes) (e f : ℕ) :
    let s := deningerCalderonWittGlobalMilnorGreenRetraction w
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    let u : ℂ := ((a / 2 : ℝ) : ℂ)
    let c :=
      deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f
    HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonHeadKernel L u u)
        ((deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedGreenTransport
            a w p q e f)).1 t)
        (t : ℂ) ∧
      HasDerivAt
        (fun L => c * eulerPrimitiveAnalyticHorizonTailKernel L u u)
        (-((deningerCalderonWittGammaBoundaryVectorOrientation q
          (deningerCalderonWittGammaPolarizedGreenTransport
            a w p q e f)).2 t))
        (t : ℂ) := by
  simpa only [deningerCalderonWittGammaPolarizedGreenTransport,
    LinearMap.comp_apply] using
    deningerCalderonWittGammaBoundaryVectorOrientation_transport_movingHorizon
      ha (deningerCalderonWittGlobalMilnorGreenRetraction w) p q e f

/--
On every labelled source Green primitive, the singular Hodge rotation
exactly exchanges Gamma-head and Hardy-tail energy at the positive source
action.
-/
theorem deningerCalderonWittGammaPolarizedGreenTransport_hodge_energy
    (a : ℝ)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (p q : Nat.Primes) (e f : ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    let x :=
      deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedGreenTransport
          a w p q e f)
    eulerPrimitiveBoundaryHeadWeight t *
          Complex.normSq ((eulerPrimitiveBoundaryOddHodge x).1 t) +
        eulerPrimitiveBoundaryTailWeight t *
          Complex.normSq ((eulerPrimitiveBoundaryOddHodge x).2 t) =
      eulerPrimitiveBoundaryTailWeight t * Complex.normSq (x.2 t) +
        eulerPrimitiveBoundaryHeadWeight t * Complex.normSq (x.1 t) := by
  dsimp only
  exact eulerPrimitiveBoundaryOddHodge_pointwise_energy _
    (xiGammaEulerPrimitivePolarizedPairAction_pos (p, e) (q, f))

/-- The Green comparison restricts to the boundary transport on incidence. -/
theorem deningerCalderonWittGammaPolarizedGreenTransport_incidence
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence) :
    deningerCalderonWittGammaPolarizedGreenTransport a s.1 =
      deningerCalderonWittGammaPolarizedVectorTransport a s := by
  rw [deningerCalderonWittGammaPolarizedGreenTransport,
    LinearMap.comp_apply,
    deningerCalderonWittGlobalMilnorGreenRetraction_incidence]

/--
Evaluation of the actual boundary feature is exactly singular transport of
the canonical Calderón--Witt Green primitive.
-/
theorem deningerCalderonWittGammaPolarizedGreenTransport_fst_eval
    (a : ℝ)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaPolarizedGreenTransport
        a w p q e f).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerCalderonWittGammaModularVectorTransport a
        (deningerCalderonWittGlobalMilnorGreenRetraction w)
        p q e f := by
  exact deningerCalderonWittGammaPolarizedVectorTransport_fst_eval
    a (deningerCalderonWittGlobalMilnorGreenRetraction w) p q e f

/--
The singular vector Hodge rotation of the Green comparison evaluates to
the exact Hodge rotation of the singular Green transport.
-/
theorem
    deningerCalderonWittGammaBoundaryVectorOddHodge_greenTransport_eval
    (a : ℝ)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (p q : Nat.Primes) (e f : ℕ) :
    let t := xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)
    let s := deningerCalderonWittGlobalMilnorGreenRetraction w
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaPolarizedGreenTransport
          a w p q e f)).1 t =
      (eulerPrimitiveBoundaryHodgeScale t : ℂ) •
        deningerCalderonWittGammaModularVectorTransport
          a s p q e f ∧
    (deningerCalderonWittGammaBoundaryVectorOddHodge q
        (deningerCalderonWittGammaPolarizedGreenTransport
          a w p q e f)).2 t =
      (-(eulerPrimitiveBoundaryHodgeScale t : ℂ)⁻¹) •
        deningerCalderonWittGammaModularVectorTransport
          a s p q e f := by
  exact
    deningerCalderonWittGammaBoundaryVectorOddHodge_transport_eval
      a (deningerCalderonWittGlobalMilnorGreenRetraction w) p q e f

end

end RHTower
