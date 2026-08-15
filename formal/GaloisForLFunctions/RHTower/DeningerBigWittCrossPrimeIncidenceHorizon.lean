import GaloisForLFunctions.RHTower.DeningerGammaSixBigWittStokesSource
import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeIncidenceKoszul
import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaGreenQuadraticMateCurvature

open Complex Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

def deningerBigWittPrimeFace (p : Nat.Primes) : ℚ :=
  (((p : ℕ) : ℚ))⁻¹

def deningerBigWittCrossPrimeAtom
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℚ :=
  deningerBigWittPrimeFace i.1.1 * deningerBigWittPrimeFace i.1.2

def deningerBigWittCrossPrimeTail
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℚ :=
  deningerBigWittPrimeFace i.1.1 + deningerBigWittPrimeFace i.1.2

def deningerBigWittCrossPrimeStokesSource
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    DeningerBigWittRing ℚ :=
  deningerBigWittTeichmullerCrossEffect
    (deningerBigWittPrimeFace i.1.1)
    (deningerBigWittPrimeFace i.1.2)

theorem deningerBigWittPrimeFace_ne_zero (p : Nat.Primes) :
    deningerBigWittPrimeFace p ≠ 0 := by
  rw [deningerBigWittPrimeFace]
  exact inv_ne_zero (by exact_mod_cast p.2.ne_zero)

theorem deningerBigWittCrossPrimeAtom_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimeAtom i ≠ 0 := by
  exact mul_ne_zero
    (deningerBigWittPrimeFace_ne_zero i.1.1)
    (deningerBigWittPrimeFace_ne_zero i.1.2)

theorem deningerBigWittCrossPrimeStokesSource_ghost_one
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittCrossPrimeStokesSource i) = 0 := by
  exact deningerBigWittTeichmullerCrossEffect_ghost_one _ _

theorem deningerBigWittCrossPrimeStokesSource_green
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittFactor (deningerBigWittCrossPrimeTail i) 1 *
        (deningerBigWittRingSeries
            (deningerBigWittCrossPrimeStokesSource i) - 1) =
      PowerSeries.C (deningerBigWittCrossPrimeAtom i) * PowerSeries.X ^ 2 := by
  exact deningerBigWittTeichmullerCrossEffect_green _ _

theorem deningerBigWittCrossPrimeStokesSource_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimeStokesSource i ≠ 0 := by
  rw [deningerBigWittCrossPrimeStokesSource,
    ne_eq, deningerBigWittTeichmullerCrossEffect_eq_zero_iff]
  exact deningerBigWittCrossPrimeAtom_ne_zero i

@[simp] theorem deningerBigWittCrossPrimeAtom_two_three :
    deningerBigWittCrossPrimeAtom
        deningerCalderonWittTwoThreePacketIndex =
      deningerGammaSixBigWittAtom := by
  norm_num [deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace,
    deningerCalderonWittTwoThreePacketIndex, deningerGammaSixBigWittAtom]

@[simp] theorem deningerBigWittCrossPrimeTail_two_three :
    deningerBigWittCrossPrimeTail
        deningerCalderonWittTwoThreePacketIndex =
      deningerGammaSixBigWittTail := by
  norm_num [deningerBigWittCrossPrimeTail, deningerBigWittPrimeFace,
    deningerCalderonWittTwoThreePacketIndex, deningerGammaSixBigWittTail]

@[simp] theorem deningerBigWittCrossPrimeStokesSource_two_three :
    deningerBigWittCrossPrimeStokesSource
        deningerCalderonWittTwoThreePacketIndex =
      deningerGammaSixBigWittStokesSource := by
  norm_num [deningerBigWittCrossPrimeStokesSource,
    deningerBigWittPrimeFace, deningerCalderonWittTwoThreePacketIndex,
    deningerGammaSixBigWittStokesSource]

def deningerBigWittCrossPrimePacketRawCoefficient
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℂ :=
  deningerBigWittCrossPrimeAtom i

theorem deningerBigWittCrossPrimePacketRawCoefficient_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimePacketRawCoefficient i ≠ 0 := by
  change ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ) ≠ 0
  exact_mod_cast deningerBigWittCrossPrimeAtom_ne_zero i

theorem summable_norm_sq_deningerBigWittCrossPrimePacketRawCoefficient :
    Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖deningerBigWittCrossPrimePacketRawCoefficient i‖ ^ 2) := by
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  have hpair : Summable (fun pq : Nat.Primes × Nat.Primes =>
      (((pq.1 : ℝ)⁻¹) ^ 2) * (((pq.2 : ℝ)⁻¹) ^ 2)) :=
    Summable.mul_of_nonneg hprime hprime
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  refine (hpair.subtype (fun pq : Nat.Primes × Nat.Primes => pq.1 ≠ pq.2)).congr ?_
  intro i
  simp only [Function.comp_apply,
    deningerBigWittCrossPrimePacketRawCoefficient,
    deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, norm_mul, norm_inv,
    Complex.norm_natCast]
  ring

def deningerBigWittCrossPrimePacketRawHorizon :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ⟨deningerBigWittCrossPrimePacketRawCoefficient, by
    apply memℓp_gen
    simpa using summable_norm_sq_deningerBigWittCrossPrimePacketRawCoefficient⟩

@[simp] theorem deningerBigWittCrossPrimePacketRawHorizon_apply
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimePacketRawHorizon i =
      deningerBigWittCrossPrimePacketRawCoefficient i := rfl

theorem deningerBigWittCrossPrimePacketRawHorizon_ne_zero :
    deningerBigWittCrossPrimePacketRawHorizon ≠ 0 := by
  intro h
  have hi := congrFun (congrArg Subtype.val h)
    deningerCalderonWittTwoThreePacketIndex
  exact deningerBigWittCrossPrimePacketRawCoefficient_ne_zero
    deningerCalderonWittTwoThreePacketIndex (by simpa using hi)

def deningerBigWittCrossPrimePacketHorizon :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹) •
    deningerBigWittCrossPrimePacketRawHorizon

@[simp] theorem deningerBigWittCrossPrimePacketHorizon_norm :
    ‖deningerBigWittCrossPrimePacketHorizon‖ = 1 := by
  rw [deningerBigWittCrossPrimePacketHorizon, norm_smul]
  have hnorm : ‖deningerBigWittCrossPrimePacketRawHorizon‖ ≠ 0 :=
    norm_ne_zero_iff.mpr deningerBigWittCrossPrimePacketRawHorizon_ne_zero
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

@[simp] theorem deningerBigWittCrossPrimePacketHorizon_apply
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimePacketHorizon i =
      ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹) *
        deningerBigWittCrossPrimePacketRawCoefficient i := rfl

theorem deningerBigWittCrossPrimePacketHorizon_apply_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimePacketHorizon i ≠ 0 := by
  rw [deningerBigWittCrossPrimePacketHorizon_apply]
  exact mul_ne_zero
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr
        deningerBigWittCrossPrimePacketRawHorizon_ne_zero)))
    (deningerBigWittCrossPrimePacketRawCoefficient_ne_zero i)

@[simp] theorem deningerBigWittCrossPrimePacketRawHorizon_two_three :
    deningerBigWittCrossPrimePacketRawHorizon
        deningerCalderonWittTwoThreePacketIndex =
      ((deningerGammaSixBigWittAtom : ℚ) : ℂ) := by
  simp [deningerBigWittCrossPrimePacketRawHorizon,
    deningerBigWittCrossPrimePacketRawCoefficient]

private def deningerBigWittAllCrossPrimeXiIncidenceComparisonToFun
    (x : DeningerArithmeticCompletedH1) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  ⟨fun r => x r • deningerBigWittCrossPrimePacketHorizon,
    Memℓp.mono (lp.memℓp x).norm (fun r => by
      rw [norm_smul, deningerBigWittCrossPrimePacketHorizon_norm]
      simp)⟩

/-- Source-normalized simultaneous comparison with every ordered prime pair. -/
def deningerBigWittAllCrossPrimeXiIncidenceComparison :
    DeningerArithmeticCompletedH1 →ₗᵢ[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion where
  toFun := deningerBigWittAllCrossPrimeXiIncidenceComparisonToFun
  map_add' x y := by
    apply lp.ext
    funext r
    exact add_smul _ _ _
  map_smul' c x := by
    apply lp.ext
    funext r
    exact mul_smul _ _ _
  norm_map' x := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun r => by
        change ‖x r • deningerBigWittCrossPrimePacketHorizon‖ ≤ ‖x r‖
        rw [norm_smul, deningerBigWittCrossPrimePacketHorizon_norm]
        simp)
    · exact lp.norm_mono (by norm_num) (fun r => by
        change ‖x r‖ ≤
          ‖(deningerBigWittAllCrossPrimeXiIncidenceComparisonToFun x) r‖
        change ‖x r‖ ≤
          ‖x r • deningerBigWittCrossPrimePacketHorizon‖
        rw [norm_smul, deningerBigWittCrossPrimePacketHorizon_norm]
        simp)

@[simp] theorem deningerBigWittAllCrossPrimeXiIncidenceComparison_apply
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittAllCrossPrimeXiIncidenceComparison x r i =
      x r * deningerBigWittCrossPrimePacketHorizon i := rfl

/-- Unnormalized comparison retaining literal Big-Witt atom `1/(pq)` at every prime pair. -/
def deningerBigWittRawAllCrossPrimeXiIncidenceComparison :
    DeningerArithmeticCompletedH1 →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) •
    deningerBigWittAllCrossPrimeXiIncidenceComparison.toContinuousLinearMap

@[simp] theorem deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittRawAllCrossPrimeXiIncidenceComparison x r i =
      x r * deningerBigWittCrossPrimePacketRawCoefficient i := by
  have hnorm : ‖deningerBigWittCrossPrimePacketRawHorizon‖ ≠ 0 :=
    norm_ne_zero_iff.mpr deningerBigWittCrossPrimePacketRawHorizon_ne_zero
  change
    (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) *
        (x r *
          ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹ *
            deningerBigWittCrossPrimePacketRawCoefficient i)) =
      x r * deningerBigWittCrossPrimePacketRawCoefficient i
  field_simp [Complex.ofReal_ne_zero.mpr hnorm]

theorem norm_deningerBigWittRawAllCrossPrimeXiIncidenceComparison
    (x : DeningerArithmeticCompletedH1) :
    ‖deningerBigWittRawAllCrossPrimeXiIncidenceComparison x‖ =
      ‖deningerBigWittCrossPrimePacketRawHorizon‖ * ‖x‖ := by
  change
    ‖(‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) •
        deningerBigWittAllCrossPrimeXiIncidenceComparison x‖ = _
  rw [norm_smul,
    deningerBigWittAllCrossPrimeXiIncidenceComparison.norm_map,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- Literal source-weighted completed Green comparison. -/
def deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence :
    DeningerArithmeticTopologicalH1Compact →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  deningerBigWittRawAllCrossPrimeXiIncidenceComparison.comp
    deningerArithmeticSourceGreen

@[simp] theorem
    deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence_apply
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence ell =
      deningerBigWittRawAllCrossPrimeXiIncidenceComparison
        (deningerArithmeticSourceGreen ell) := rfl

@[simp] theorem
    deningerBigWittAllCrossPrimeXiIncidenceSourceValue_rawComparison
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue r i
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison x) =
      (x r * ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ)) •
        deningerCalderonWittCrossPrimeGammaWitness i.property := by
  change
    deningerBigWittRawAllCrossPrimeXiIncidenceComparison x r i •
        deningerCalderonWittCrossPrimeGammaWitness i.property = _
  rw [deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply]
  rfl

/-- Actual completed Green comparison using only source-derived prime-pair weights. -/
def deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence :
    DeningerArithmeticTopologicalH1Compact →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  deningerBigWittAllCrossPrimeXiIncidenceComparison.toContinuousLinearMap.comp
    deningerArithmeticSourceGreen

@[simp] theorem
    deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence_apply
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence ell =
      deningerBigWittAllCrossPrimeXiIncidenceComparison
        (deningerArithmeticSourceGreen ell) := rfl

theorem norm_deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence
    (ell : DeningerArithmeticTopologicalH1Compact) :
    ‖deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence ell‖ =
      ‖deningerArithmeticSourceGreen ell‖ :=
  deningerBigWittAllCrossPrimeXiIncidenceComparison.norm_map _

@[simp] theorem deningerBigWittAllCrossPrimeXiIncidenceSourceValue_comparison
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue r i
        (deningerBigWittAllCrossPrimeXiIncidenceComparison x) =
      (x r * deningerBigWittCrossPrimePacketHorizon i) •
        deningerCalderonWittCrossPrimeGammaWitness i.property := rfl

/-- Contracted source-arithmetic packet differential. -/
def deningerBigWittCrossPrimePacketKoszulDifferential :
    DeningerCalderonWittCrossPrimePacketHilbert →ₗ[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert where
  toFun z :=
    deningerBigWittCrossPrimePacketHorizon
        deningerCalderonWittTwoThreePacketIndex • z -
      z deningerCalderonWittTwoThreePacketIndex •
        deningerBigWittCrossPrimePacketHorizon
  map_add' z w := by
    apply lp.ext
    funext i
    change
      deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex * (z i + w i) -
          (z deningerCalderonWittTwoThreePacketIndex +
            w deningerCalderonWittTwoThreePacketIndex) *
            deningerBigWittCrossPrimePacketHorizon i =
        (deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * z i -
            z deningerCalderonWittTwoThreePacketIndex *
              deningerBigWittCrossPrimePacketHorizon i) +
          (deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * w i -
            w deningerCalderonWittTwoThreePacketIndex *
              deningerBigWittCrossPrimePacketHorizon i)
    ring
  map_smul' c z := by
    apply lp.ext
    funext i
    change
      deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex * (c * z i) -
          (c * z deningerCalderonWittTwoThreePacketIndex) *
            deningerBigWittCrossPrimePacketHorizon i =
        c * (deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * z i -
            z deningerCalderonWittTwoThreePacketIndex *
              deningerBigWittCrossPrimePacketHorizon i)
    ring

@[simp] theorem deningerBigWittCrossPrimePacketKoszulDifferential_apply
    (z : DeningerCalderonWittCrossPrimePacketHilbert)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimePacketKoszulDifferential z i =
      deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex * z i -
        z deningerCalderonWittTwoThreePacketIndex *
          deningerBigWittCrossPrimePacketHorizon i := rfl

@[simp] theorem deningerBigWittCrossPrimePacketKoszulDifferential_horizon :
    deningerBigWittCrossPrimePacketKoszulDifferential
        deningerBigWittCrossPrimePacketHorizon = 0 := by
  apply lp.ext
  funext i
  change
    deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex *
        deningerBigWittCrossPrimePacketHorizon i -
      deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex *
        deningerBigWittCrossPrimePacketHorizon i = 0
  ring

theorem deningerBigWittCrossPrimePacketKoszulDifferential_eq_zero_iff
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    deningerBigWittCrossPrimePacketKoszulDifferential z = 0 ↔
      ∃ c : ℂ, z = c • deningerBigWittCrossPrimePacketHorizon := by
  constructor
  · intro hz
    let i₀ := deningerCalderonWittTwoThreePacketIndex
    let η := deningerBigWittCrossPrimePacketHorizon
    have hη : η i₀ ≠ 0 :=
      deningerBigWittCrossPrimePacketHorizon_apply_ne_zero i₀
    refine ⟨z i₀ / η i₀, ?_⟩
    apply lp.ext
    funext i
    have hi := congrFun (congrArg Subtype.val hz) i
    change η i₀ * z i - z i₀ * η i = 0 at hi
    rw [sub_eq_zero] at hi
    change z i = (z i₀ / η i₀) * η i
    calc
      z i = (z i₀ * η i) / η i₀ := by
        apply (eq_div_iff hη).2
        simpa [mul_comm] using hi
      _ = (z i₀ / η i₀) * η i := by field_simp
  · rintro ⟨c, rfl⟩
    apply lp.ext
    funext i
    rw [deningerBigWittCrossPrimePacketKoszulDifferential_apply]
    simp
    ring

theorem ker_deningerBigWittCrossPrimePacketKoszulDifferential :
    LinearMap.ker deningerBigWittCrossPrimePacketKoszulDifferential =
      LinearMap.range
        (LinearMap.toSpanSingleton ℂ
          DeningerCalderonWittCrossPrimePacketHilbert
          deningerBigWittCrossPrimePacketHorizon) := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨c, rfl⟩ :=
      (deningerBigWittCrossPrimePacketKoszulDifferential_eq_zero_iff z).mp hz
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    exact
      (deningerBigWittCrossPrimePacketKoszulDifferential_eq_zero_iff
        (c • deningerBigWittCrossPrimePacketHorizon)).2 ⟨c, rfl⟩

theorem norm_deningerBigWittCrossPrimePacketKoszulDifferential_le
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    ‖deningerBigWittCrossPrimePacketKoszulDifferential z‖ ≤ 2 * ‖z‖ := by
  rw [deningerBigWittCrossPrimePacketKoszulDifferential]
  calc
    ‖deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex • z -
        z deningerCalderonWittTwoThreePacketIndex •
          deningerBigWittCrossPrimePacketHorizon‖
        ≤ ‖deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex • z‖ +
            ‖z deningerCalderonWittTwoThreePacketIndex •
              deningerBigWittCrossPrimePacketHorizon‖ :=
      norm_sub_le _ _
    _ = ‖deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex‖ * ‖z‖ +
          ‖z deningerCalderonWittTwoThreePacketIndex‖ := by
      rw [norm_smul, norm_smul,
        deningerBigWittCrossPrimePacketHorizon_norm, mul_one]
    _ ≤ 2 * ‖z‖ := by
      have hη := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        deningerBigWittCrossPrimePacketHorizon
        deningerCalderonWittTwoThreePacketIndex
      have hz := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        z deningerCalderonWittTwoThreePacketIndex
      rw [deningerBigWittCrossPrimePacketHorizon_norm] at hη
      nlinarith [norm_nonneg z]

private def deningerBigWittGlobalPacketKoszulDifferentialToFun
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  ⟨fun r => deningerBigWittCrossPrimePacketKoszulDifferential (z r),
    Memℓp.mono ((lp.memℓp z).norm.const_smul (2 : ℝ)) (fun r => by
      simpa [Pi.smul_apply, smul_eq_mul] using
        norm_deningerBigWittCrossPrimePacketKoszulDifferential_le (z r))⟩

/-- Fibrewise bounded source-arithmetic packet differential. -/
def deningerBigWittGlobalPacketKoszulDifferential :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  LinearMap.mkContinuous
    { toFun := deningerBigWittGlobalPacketKoszulDifferentialToFun
      map_add' := fun z w => by
        apply lp.ext
        funext r
        exact map_add deningerBigWittCrossPrimePacketKoszulDifferential
          (z r) (w r)
      map_smul' := fun c z => by
        apply lp.ext
        funext r
        exact map_smul deningerBigWittCrossPrimePacketKoszulDifferential c
          (z r) }
    2 (fun z => by
      have hmono :
          ‖deningerBigWittGlobalPacketKoszulDifferentialToFun z‖ ≤
            ‖(2 : ℂ) • z‖ :=
        lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun r => by
          change
            ‖deningerBigWittCrossPrimePacketKoszulDifferential (z r)‖ ≤
              ‖((2 : ℂ) • z) r‖
          rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]
          norm_num
          exact norm_deningerBigWittCrossPrimePacketKoszulDifferential_le
            (z r))
      rw [norm_smul] at hmono
      norm_num at hmono
      exact hmono)

@[simp] theorem deningerBigWittGlobalPacketKoszulDifferential_apply
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion)
    (r : XiZeroCopy) :
    deningerBigWittGlobalPacketKoszulDifferential z r =
      deningerBigWittCrossPrimePacketKoszulDifferential (z r) := rfl

/-- Source-arithmetic completed comparison is an unconditional packet cycle. -/
@[simp] theorem deningerBigWittGlobalPacketKoszulDifferential_comparison
    (x : DeningerArithmeticCompletedH1) :
    deningerBigWittGlobalPacketKoszulDifferential
        (deningerBigWittAllCrossPrimeXiIncidenceComparison x) = 0 := by
  apply lp.ext
  funext r
  rw [deningerBigWittGlobalPacketKoszulDifferential_apply]
  exact
    (deningerBigWittCrossPrimePacketKoszulDifferential_eq_zero_iff
      (x r • deningerBigWittCrossPrimePacketHorizon)).2
      ⟨x r, rfl⟩

@[simp] theorem deningerBigWittGlobalPacketKoszulDifferential_rawComparison
    (x : DeningerArithmeticCompletedH1) :
    deningerBigWittGlobalPacketKoszulDifferential
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison x) = 0 := by
  change deningerBigWittGlobalPacketKoszulDifferential
      ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) •
        deningerBigWittAllCrossPrimeXiIncidenceComparison x) = 0
  rw [map_smul, deningerBigWittGlobalPacketKoszulDifferential_comparison,
    smul_zero]

/-- Actual completed Xi Green vector descends to a source-arithmetic packet cycle. -/
@[simp] theorem deningerBigWittGlobalPacketKoszulDifferential_completedGreen
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerBigWittGlobalPacketKoszulDifferential
        (deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence ell) = 0 := by
  rw [deningerArithmeticCompletedGreenToBigWittCrossPrimeIncidence_apply]
  exact deningerBigWittGlobalPacketKoszulDifferential_comparison
    (deningerArithmeticSourceGreen ell)

@[simp] theorem deningerBigWittGlobalPacketKoszulDifferential_rawCompletedGreen
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerBigWittGlobalPacketKoszulDifferential
        (deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence ell) =
      0 := by
  rw [deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence_apply]
  exact deningerBigWittGlobalPacketKoszulDifferential_rawComparison
    (deningerArithmeticSourceGreen ell)

@[simp] theorem deningerBigWittAllCrossPrimeXiIncidenceSourceValue_rawGreen
    (ell : DeningerArithmeticTopologicalH1Compact) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue r i
        (deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence ell) =
      (deningerArithmeticSourceGreen ell r *
          ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ)) •
        deningerCalderonWittCrossPrimeGammaWitness i.property := by
  rw [deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence_apply,
    deningerBigWittAllCrossPrimeXiIncidenceSourceValue_rawComparison]

private def deningerBigWittPacketKoszulResidualCoefficientToFun
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion) :
    DeningerArithmeticCompletedH1 :=
  ⟨fun r =>
      z r deningerCalderonWittTwoThreePacketIndex /
        deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex,
    Memℓp.mono
      ((lp.memℓp z).norm.const_smul
        ‖(deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex)⁻¹‖)
      (fun r => by
        have hr := lp.norm_apply_le_norm
          (by norm_num : (2 : ENNReal) ≠ 0)
          (z r) deningerCalderonWittTwoThreePacketIndex
        simpa [div_eq_mul_inv, norm_mul, Pi.smul_apply, smul_eq_mul,
          mul_comm] using
          mul_le_mul_of_nonneg_right hr
            (norm_nonneg
              (deningerBigWittCrossPrimePacketHorizon
                deningerCalderonWittTwoThreePacketIndex)⁻¹))⟩

/-- Residual completed Xi coefficient after exact arithmetic packet compatibility. -/
def deningerBigWittPacketKoszulResidualCoefficient :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →ₗ[ℂ]
      DeningerArithmeticCompletedH1 where
  toFun := deningerBigWittPacketKoszulResidualCoefficientToFun
  map_add' z w := by
    apply lp.ext
    funext r
    change
      (z r deningerCalderonWittTwoThreePacketIndex +
          w r deningerCalderonWittTwoThreePacketIndex) /
          deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex =
        z r deningerCalderonWittTwoThreePacketIndex /
            deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex +
          w r deningerCalderonWittTwoThreePacketIndex /
            deningerBigWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex
    ring
  map_smul' c z := by
    apply lp.ext
    funext r
    change
      (c * z r deningerCalderonWittTwoThreePacketIndex) /
          deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex =
        c * (z r deningerCalderonWittTwoThreePacketIndex /
          deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex)
    ring

@[simp] theorem deningerBigWittPacketKoszulResidualCoefficient_comparison
    (x : DeningerArithmeticCompletedH1) :
    deningerBigWittPacketKoszulResidualCoefficient
        (deningerBigWittAllCrossPrimeXiIncidenceComparison x) = x := by
  apply lp.ext
  funext r
  change
    (x r * deningerBigWittCrossPrimePacketHorizon
      deningerCalderonWittTwoThreePacketIndex) /
        deningerBigWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex = x r
  exact mul_div_cancel_right₀ (x r)
    (deningerBigWittCrossPrimePacketHorizon_apply_ne_zero
      deningerCalderonWittTwoThreePacketIndex)

/-- Exact global kernel: arithmetic packet compatibility leaves precisely completed Xi data. -/
theorem ker_deningerBigWittGlobalPacketKoszulDifferential :
    LinearMap.ker
        deningerBigWittGlobalPacketKoszulDifferential.toLinearMap =
      LinearMap.range
        deningerBigWittAllCrossPrimeXiIncidenceComparison.toLinearMap := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    refine ⟨deningerBigWittPacketKoszulResidualCoefficient z, ?_⟩
    apply lp.ext
    funext r
    have hr :
        deningerBigWittCrossPrimePacketKoszulDifferential (z r) = 0 := by
      have hcoord := congrFun (congrArg Subtype.val hz) r
      simpa [deningerBigWittGlobalPacketKoszulDifferential_apply] using hcoord
    obtain ⟨c, hc⟩ :=
      (deningerBigWittCrossPrimePacketKoszulDifferential_eq_zero_iff
        (z r)).mp hr
    have hη := deningerBigWittCrossPrimePacketHorizon_apply_ne_zero
      deningerCalderonWittTwoThreePacketIndex
    change
      (z r deningerCalderonWittTwoThreePacketIndex /
          deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) •
          deningerBigWittCrossPrimePacketHorizon = z r
    rw [hc]
    apply lp.ext
    funext i
    change
      ((c * deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) /
          deningerBigWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) *
        deningerBigWittCrossPrimePacketHorizon i =
      c * deningerBigWittCrossPrimePacketHorizon i
    rw [mul_div_cancel_right₀ c hη]
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact deningerBigWittGlobalPacketKoszulDifferential_comparison x

theorem range_deningerBigWittRawAllCrossPrimeXiIncidenceComparison :
    LinearMap.range
        deningerBigWittRawAllCrossPrimeXiIncidenceComparison.toLinearMap =
      LinearMap.range
        deningerBigWittAllCrossPrimeXiIncidenceComparison.toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) • x, ?_⟩
    change
      deningerBigWittAllCrossPrimeXiIncidenceComparison
          ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) • x) =
        (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) •
          deningerBigWittAllCrossPrimeXiIncidenceComparison x
    exact map_smul deningerBigWittAllCrossPrimeXiIncidenceComparison
      (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) x
  · rintro ⟨x, rfl⟩
    have hnorm : ‖deningerBigWittCrossPrimePacketRawHorizon‖ ≠ 0 :=
      norm_ne_zero_iff.mpr deningerBigWittCrossPrimePacketRawHorizon_ne_zero
    have hnormC :
        (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hnorm
    refine ⟨(‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹ • x, ?_⟩
    change
      (‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ) •
          deningerBigWittAllCrossPrimeXiIncidenceComparison
            ((‖deningerBigWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹ • x) =
        deningerBigWittAllCrossPrimeXiIncidenceComparison x
    rw [map_smul, smul_smul, mul_inv_cancel₀ hnormC, one_smul]

theorem ker_deningerBigWittGlobalPacketKoszulDifferential_eq_rawRange :
    LinearMap.ker
        deningerBigWittGlobalPacketKoszulDifferential.toLinearMap =
      LinearMap.range
        deningerBigWittRawAllCrossPrimeXiIncidenceComparison.toLinearMap := by
  rw [ker_deningerBigWittGlobalPacketKoszulDifferential,
    range_deningerBigWittRawAllCrossPrimeXiIncidenceComparison]

/-- Actual Gamma admission of source-derived Big-Witt incidence coefficients is the positive
mate curvature times oriented Hodge transport and the literal atom `1/(pq)`. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittGreen_apply_eq_mateCurvature
    (a : XiDivisorL2) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a)) r i =
      ((deningerCalderonWittGammaGreenMateCurvature r : ℝ) : ℂ) *
        deningerArithmeticOrientedHodgeLp
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation a) r *
        ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ) := by
  rw [deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_apply]
  change
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a) r i) = _
  rw [deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply]
  change
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
        (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a r *
          ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ)) = _
  rw [
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_mateGauge,
    DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance_apply,
    deningerCalderonWittGammaGreenMateCurvature,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [ofReal_re]
  push_cast
  ring

/-- With source-derived prime-pair weights, every individual Gamma-admitted reflected-Gaussian
coordinate has exactly the critical line as radical. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittReflectedGaussian_eq_zero_iff
    (r : XiZeroCopy) (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
          DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) r i = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  change
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)) r i = 0 ↔ _
  rw [
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittGreen_apply_eq_mateCurvature]
  have hhodge :
      deningerArithmeticOrientedHodgeLp
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2) r ≠ 0 := by
    rw [deningerArithmeticOrientedHodgeLp_apply,
      DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation_apply]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero r)
    · rw [starRingEnd_self_apply]
      exact DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade_ne_zero
        (xiZeroCopyReflectEquiv r)
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hhodge, or_false]
  have hatom : ((deningerBigWittCrossPrimeAtom i : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast deningerBigWittCrossPrimeAtom_ne_zero i
  rw [or_iff_left hatom]
  exact_mod_cast deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff r

/-- Unconditional source-native all-prime incidence descent package. -/
theorem DAC_DENINGER_BIG_WITT_ALL_CROSS_PRIME_INCIDENCE_DESCENT :
    (∀ i : DeningerCalderonWittCrossPrimePacketIndex,
        deningerBigWittGhostComponent 1 Nat.zero_lt_one
            (deningerBigWittCrossPrimeStokesSource i) = 0 ∧
          deningerBigWittCrossPrimeStokesSource i ≠ 0) ∧
      deningerBigWittCrossPrimePacketRawHorizon
          deningerCalderonWittTwoThreePacketIndex =
        ((deningerGammaSixBigWittAtom : ℚ) : ℂ) ∧
      (∀ ell : DeningerArithmeticTopologicalH1Compact,
        deningerBigWittGlobalPacketKoszulDifferential
          (deningerArithmeticCompletedGreenToRawBigWittCrossPrimeIncidence ell) =
            0) ∧
      LinearMap.ker
          deningerBigWittGlobalPacketKoszulDifferential.toLinearMap =
        LinearMap.range
          deningerBigWittRawAllCrossPrimeXiIncidenceComparison.toLinearMap ∧
      (∀ (r : XiZeroCopy) (i : DeningerCalderonWittCrossPrimePacketIndex),
        deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
            (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
              DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) r i = 0 ↔
          (r.1 : ℂ).re = 1 / 2) := by
  exact ⟨fun i => ⟨deningerBigWittCrossPrimeStokesSource_ghost_one i,
      deningerBigWittCrossPrimeStokesSource_ne_zero i⟩,
    deningerBigWittCrossPrimePacketRawHorizon_two_three,
    deningerBigWittGlobalPacketKoszulDifferential_rawCompletedGreen,
    ker_deningerBigWittGlobalPacketKoszulDifferential_eq_rawRange,
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittReflectedGaussian_eq_zero_iff⟩

end

end RHTower
