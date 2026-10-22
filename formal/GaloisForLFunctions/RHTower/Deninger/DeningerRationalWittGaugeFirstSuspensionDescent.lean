import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittPacketGaugeLimit
import GaloisForLFunctions.RHTower.Deninger.DeningerSquareZeroFirstSuspensionCrossEffect

/-!
# Affine-gauge first-suspension descent

Finite rational-Witt evaluation is contravariant for the forced affine packet transitions, not
for the standard quotient reductions.  This module constructs the resulting source-varying
packet directly on the affine inverse limit.

Every finite-stage function pulls back injectively to the affine limit and to its transported
complex Haar `L²`.  These pullbacks are literally equal under gauge-corrected refinement.
Tensoring with the first suspension character and then applying the Calderón cross-effect
preserves that equality.  Thus one arithmetic-Frobenius-fixed rational-Witt witness produces one
nonzero cofinal tensor class, rather than a family depending on independently chosen primitive
roots.

The construction is primewise.  It does not attach the complete prime-normal reader through an
ungraded closed relation; maximal verticality of that relation is proved separately in
`CompleteResolutionCofinalConditioningLaw`.
-/

namespace RHTower

open MeasureTheory Topology
open scoped ENNReal TensorProduct

noncomputable section

/-- Coordinate projection from the affine rational-Witt packet limit to one finite stage. -/
def deningerPrimeFinitePacketGaugeLimitProjection
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerPrimeFinitePacketGaugeLimit p →
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
  fun a => a.1 s

theorem deningerPrimeFinitePacketGaugeLimitProjection_continuous
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Continuous (deningerPrimeFinitePacketGaugeLimitProjection p s) := by
  exact (continuous_apply s).comp continuous_subtype_val

/-- Every finite affine packet occurs as one coordinate of a coherent affine packet. -/
theorem deningerPrimeFinitePacketGaugeLimitProjection_surjective
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Surjective
      (deningerPrimeFinitePacketGaugeLimitProjection p s) := by
  intro q
  let a₀ := deningerPrimeFinitePacketGaugeLimitBasepoint p
  obtain ⟨x, hx⟩ :=
    deningerPrimeFiniteStageQuotientReduction_surjective p s
      ((a₀.1 s)⁻¹ * q)
  refine
    ⟨deningerPrimeFinitePacketGaugeLimitMul p a₀
      (deningerPrimePacketToFiniteLimit p x), ?_⟩
  change
    a₀.1 s * deningerPrimeFiniteStageQuotientReduction p s x = q
  rw [hx]
  simp

/-- Pull a complex finite-stage packet function to the affine packet limit. -/
def deningerPrimeFinitePacketGaugeStageComplexPullback
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    C(DeningerPrimeFinitePacketGaugeLimit p, ℂ) where
  toFun a := F (deningerPrimeFinitePacketGaugeLimitProjection p s a)
  continuous_toFun :=
    continuous_of_discreteTopology.comp
      (deningerPrimeFinitePacketGaugeLimitProjection_continuous p s)

/-- Finite-stage pullback loses no packet coefficient. -/
theorem deningerPrimeFinitePacketGaugeStageComplexPullback_injective
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective
      (deningerPrimeFinitePacketGaugeStageComplexPullback p s) := by
  intro F G hFG
  funext q
  obtain ⟨a, ha⟩ :=
    deningerPrimeFinitePacketGaugeLimitProjection_surjective p s q
  have hpoint := DFunLike.congr_fun hFG a
  change
    F (deningerPrimeFinitePacketGaugeLimitProjection p s a) =
      G (deningerPrimeFinitePacketGaugeLimitProjection p s a) at hpoint
  simpa [ha] using hpoint

/-- Complex Haar `L²` on the affine rational-Witt packet limit. -/
abbrev DeningerPrimeFinitePacketGaugeComplexHaarL2
    (p : Nat.Primes) : Type :=
  Lp ℂ 2 (deningerPrimeFinitePacketGaugeHaarMeasure p)

/-- A finite-stage packet function in affine-limit complex Haar `L²`. -/
def deningerPrimeFinitePacketGaugeStageComplexHaarL2
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    DeningerPrimeFinitePacketGaugeComplexHaarL2 p :=
  ContinuousMap.toLp 2
    (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ
    (deningerPrimeFinitePacketGaugeStageComplexPullback p s F)

/-- Full support makes every finite-stage coefficient visible in affine Haar `L²`. -/
theorem deningerPrimeFinitePacketGaugeStageComplexHaarL2_injective
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective
      (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s) := by
  intro F G hFG
  apply deningerPrimeFinitePacketGaugeStageComplexPullback_injective p s
  apply ContinuousMap.toLp_injective
    (𝕜 := ℂ) (p := 2) (E := ℂ)
    (deningerPrimeFinitePacketGaugeHaarMeasure p)
  exact hFG

/-- Complex Haar `L²` on the affine packet times the prime-period suspension circle. -/
abbrev DeningerPrimeFinitePacketGaugeSuspensionHaarL2
    (p : Nat.Primes) : Type :=
  Lp ℂ 2
    ((deningerPrimeFinitePacketGaugeHaarMeasure p).prod
      (AddCircle.haarAddCircle :
        Measure (AddCircle (Real.log (p : ℝ)))))

/-- First suspension transgression on the affine packet limit. -/
def deningerPrimeFinitePacketGaugeSuspensionFirstMode
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeComplexHaarL2 p →L[ℂ]
      DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p :=
  MeasureTheory.l2SeparatedProductContinuousBilinear.flip
    (deningerPrimeFirstCircleMode p)

@[simp]
theorem deningerPrimeFinitePacketGaugeSuspensionFirstMode_apply
    (p : Nat.Primes)
    (f : DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :
    deningerPrimeFinitePacketGaugeSuspensionFirstMode p f =
      MeasureTheory.l2SeparatedProduct f
        (deningerPrimeFirstCircleMode p) :=
  rfl

/-- Affine first suspension preserves Haar `L²` norm exactly. -/
theorem norm_deningerPrimeFinitePacketGaugeSuspensionFirstMode
    (p : Nat.Primes)
    (f : DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :
    ‖deningerPrimeFinitePacketGaugeSuspensionFirstMode p f‖ = ‖f‖ := by
  rw [deningerPrimeFinitePacketGaugeSuspensionFirstMode_apply,
    MeasureTheory.l2SeparatedProduct_norm,
    norm_deningerPrimeFirstCircleMode, mul_one]

/-- Affine first suspension is injective. -/
theorem deningerPrimeFinitePacketGaugeSuspensionFirstMode_injective
    (p : Nat.Primes) :
    Function.Injective
      (deningerPrimeFinitePacketGaugeSuspensionFirstMode p) := by
  intro f g hfg
  apply sub_eq_zero.mp
  rw [← norm_eq_zero]
  rw [← norm_deningerPrimeFinitePacketGaugeSuspensionFirstMode p (f - g),
    map_sub, hfg, sub_self, norm_zero]

/-- Gauge-corrected refinement gives the same continuous function on the affine limit. -/
theorem deningerPrimeFinitePacketGaugeStageComplexPullback_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    deningerPrimeFinitePacketGaugeStageComplexPullback p t
        (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F) =
      deningerPrimeFinitePacketGaugeStageComplexPullback p s F := by
  ext a
  change
    F (deningerFiniteFrobeniusPacketGaugeTransition p hst (a.1 t)) =
      F (a.1 s)
  rw [a.2 hst]

/-- Gauge-corrected refinement gives the same affine Haar `L²` vector. -/
theorem deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
        (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F) =
      deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F := by
  change
    (ContinuousMap.toLp 2
      (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
        (deningerPrimeFinitePacketGaugeStageComplexPullback p t
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F)) =
      (ContinuousMap.toLp 2
        (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
          (deningerPrimeFinitePacketGaugeStageComplexPullback p s F)
  rw [deningerPrimeFinitePacketGaugeStageComplexPullback_transition p hst F]

/-- Gauge-corrected refinement gives the same affine first-suspension vector. -/
theorem deningerPrimeFinitePacketGaugeSuspensionFirstMode_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    deningerPrimeFinitePacketGaugeSuspensionFirstMode p
        (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F)) =
      deningerPrimeFinitePacketGaugeSuspensionFirstMode p
        (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F) := by
  rw [deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition p hst F]

/-- Source-varying Calderón cross-effect on affine packet coefficients. -/
def deningerMeyerCalderonGaugePacketCrossEffect
    (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      DeningerPrimeFinitePacketGaugeComplexHaarL2 p →ₗ[ℂ]
        DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p where
  toFun q :=
    { toFun := fun packet =>
        deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) q •
          (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
            deningerPrimeFinitePacketGaugeSuspensionFirstMode p packet)
      map_add' := by
        intro a b
        rw [map_add]
        module
      map_smul' := by
        intro c a
        simp [smul_smul]
        module }
  map_add' := by
    intro q r
    ext packet
    simp [add_smul]
  map_smul' := by
    intro c q
    ext packet
    simp [smul_smul]

/-- Tensor linearisation of the affine-limit Calderón cross-effect. -/
def deningerMeyerCalderonGaugePacketTensorRegulator
    (p : Nat.Primes) :
    TensorProduct ℂ
      (DeningerMeyerPrimeCalderonQuotient p)
      (DeningerPrimeFinitePacketGaugeComplexHaarL2 p) →ₗ[ℂ]
        DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p :=
  TensorProduct.lift (deningerMeyerCalderonGaugePacketCrossEffect p)

@[simp]
theorem deningerMeyerCalderonGaugePacketTensorRegulator_tmul
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p)
    (packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :
    deningerMeyerCalderonGaugePacketTensorRegulator p
        (q ⊗ₜ[ℂ] packet) =
      deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) q •
        (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          deningerPrimeFinitePacketGaugeSuspensionFirstMode p packet) :=
  rfl

/-- The affine tensor cross-effect is strictly invariant under rational-Witt refinement. -/
theorem deningerMeyerCalderonGaugePacketTensorRegulator_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (q : DeningerMeyerPrimeCalderonQuotient p) :
    deningerMeyerCalderonGaugePacketTensorRegulator p
        (q ⊗ₜ[ℂ]
          deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
            (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F)) =
      deningerMeyerCalderonGaugePacketTensorRegulator p
        (q ⊗ₜ[ℂ]
          deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F) := by
  rw [deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition p hst F]

/-- The canonical unit defect detects every nonzero affine finite-stage packet. -/
theorem deningerMeyerCalderonGaugePacketTensorRegulator_unit_ne_zero
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) :
    deningerMeyerCalderonGaugePacketTensorRegulator p
      (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
        deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F) ≠ 0 := by
  rw [deningerMeyerCalderonGaugePacketTensorRegulator_tmul]
  simp only [deningerMeyerPoissonCalderonQuotientEquiv_mk,
    deningerMeyerReflectedCollarDefect_apply, mul_zero, sub_zero,
    one_smul]
  apply smul_ne_zero
  · exact
      Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne'
  · intro hmode
    have hpacket :
        deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F = 0 := by
      apply deningerPrimeFinitePacketGaugeSuspensionFirstMode_injective p
      rw [map_zero]
      exact hmode
    apply hF
    apply deningerPrimeFinitePacketGaugeStageComplexHaarL2_injective p s
    calc
      deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F = 0 :=
        hpacket
      _ = deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s 0 := by
        change
          0 =
            (ContinuousMap.toLp 2
              (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
                (deningerPrimeFinitePacketGaugeStageComplexPullback p s 0)
        rw [show
          deningerPrimeFinitePacketGaugeStageComplexPullback p s 0 = 0 by
            ext a
            rfl,
          map_zero]

/-- **Cofinal arithmetic capstone.** Every nonzero finite packet coefficient has one
arithmetic-Frobenius-fixed rational-Witt witness whose values at every larger stage give the same
nonzero affine-limit tensor class. -/
theorem deningerPrimeComplexifiedRationalWitt_exists_cofinalGaugeTensorClass
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (hF : F ≠ 0) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      (∀ (t : DeningerFiniteFrobeniusStage (p : ℕ))
        (hst : s ≤ t) (u : (ZMod t.modulus)ˣ),
        deningerFiniteCyclotomicWittEvaluation t.modulus u
            (deningerPrimeFiniteCyclotomicWittTransition p hst w) =
          deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F
            (QuotientGroup.mk u)) ∧
      (∀ (t : DeningerFiniteFrobeniusStage (p : ℕ))
        (hst : s ≤ t),
        deningerMeyerCalderonGaugePacketTensorRegulator p
            (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
              deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
                (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F)) =
          deningerMeyerCalderonGaugePacketTensorRegulator p
            (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
              deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F)) ∧
      deningerMeyerCalderonGaugePacketTensorRegulator p
        (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
          deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F) ≠ 0 := by
  obtain ⟨w, hwfixed, heval, hcoherent⟩ :=
    deningerPrimeComplexifiedRationalWitt_exists_coherentPacketGaugeDescent
      p s F
  refine ⟨w, hwfixed, heval, hcoherent, ?_, ?_⟩
  · intro t hst
    exact
      deningerMeyerCalderonGaugePacketTensorRegulator_transition p hst F
        (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)))
  · exact
      deningerMeyerCalderonGaugePacketTensorRegulator_unit_ne_zero p s hF

end

end RHTower
