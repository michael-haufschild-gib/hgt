import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Native Selberg Hilbert coordinates

Finite divisor-sieve coefficients carry their literal full-period mean-square norm.
Totient-normalized multiples coordinates give an explicit Hilbert isometry; its inverse
is finite Ramanujan inversion. The actual compressed lag predictor becomes the existing
Ramanujan lag multiplier. This does not identify compression with true translation.
-/

open Finset RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators InnerProductSpace
noncomputable section


namespace GaloisForLFunctions.BezoutValuationIncidence

abbrev SieveActiveIndex (N : ℕ) := ↥(Finset.Icc 1 N)

/-- Raw active sieve coefficients; its native norm is the literal periodic mean square. -/
def SieveCoefficientSpace (N : ℕ) := SieveActiveIndex N → ℝ

instance (N : ℕ) : AddCommGroup (SieveCoefficientSpace N) :=
  inferInstanceAs (AddCommGroup (SieveActiveIndex N → ℝ))

instance (N : ℕ) : Module ℝ (SieveCoefficientSpace N) :=
  inferInstanceAs (Module ℝ (SieveActiveIndex N → ℝ))

def sieveCoefficientExtension (N : ℕ) : SieveCoefficientSpace N →ₗ[ℝ] (ℕ → ℝ) where
  toFun c d := if h : d ∈ Icc 1 N then c ⟨d, h⟩ else 0
  map_add' c b := by
    funext d
    by_cases h : d ∈ Icc 1 N
    · simp only [Pi.add_apply, dif_pos h]
      rfl
    · simp only [dif_neg h, Pi.add_apply, zero_add]
  map_smul' r c := by
    funext d
    by_cases h : d ∈ Icc 1 N
    · simp only [Pi.smul_apply, RingHom.id_apply, dif_pos h]
      rfl
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

@[simp] theorem sieveCoefficientExtension_active (N : ℕ) (c : SieveCoefficientSpace N)
    (q : SieveActiveIndex N) : sieveCoefficientExtension N c q.val = c q :=
  dif_pos q.property

def sieveCoefficientRestriction (N : ℕ) (c : ℕ → ℝ) : SieveCoefficientSpace N := fun q => c q.val

theorem selbergMultiplesCoord_restrict (N : ℕ) (c : ℕ → ℝ) (q : ℕ) :
    selbergMultiplesCoord N (sieveCoefficientExtension N (sieveCoefficientRestriction N c)) q =
      selbergMultiplesCoord N c q := by
  unfold selbergMultiplesCoord
  apply sum_congr rfl
  intro d hd
  have hd' := (mem_filter.mp hd).1
  change (if h : d ∈ Icc 1 N then c d else 0) / (d : ℝ) = c d / d
  rw [dif_pos hd']

private theorem active_sqrt_totient_pos (N : ℕ) (q : SieveActiveIndex N) :
    0 < Real.sqrt (q.val.totient : ℝ) := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp q.property).1

def weightedSelbergLinear (N : ℕ) :
    SieveCoefficientSpace N →ₗ[ℝ] EuclideanSpace ℝ (SieveActiveIndex N) :=
  (EuclideanSpace.equiv (SieveActiveIndex N) ℝ).symm.toLinearMap.comp
    (show SieveCoefficientSpace N →ₗ[ℝ] (SieveActiveIndex N → ℝ) from
    { toFun := fun c q => Real.sqrt (q.val.totient : ℝ) *
        selbergMultiplesCoord N (sieveCoefficientExtension N c) q.val
      map_add' := by
        intro c b
        funext q
        simp only [map_add, selbergMultiplesCoord, Pi.add_apply, add_div, sum_add_distrib,
          mul_add]
      map_smul' := by
        intro r c
        funext q
        simp only [map_smul, selbergMultiplesCoord, Pi.smul_apply, smul_eq_mul,
          mul_div_assoc, ← mul_sum, RingHom.id_apply]
        ring })

@[simp] theorem weightedSelbergLinear_apply (N : ℕ) (c : SieveCoefficientSpace N)
    (q : SieveActiveIndex N) :
    weightedSelbergLinear N c q = Real.sqrt (q.val.totient : ℝ) *
      selbergMultiplesCoord N (sieveCoefficientExtension N c) q.val := rfl

theorem weightedSelbergLinear_injective (N : ℕ) : Function.Injective (weightedSelbergLinear N) := by
  intro c b h
  have heq : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N (sieveCoefficientExtension N c) q =
      selbergMultiplesCoord N (sieveCoefficientExtension N b) q := by
    intro q hq
    have hq' := congrArg (fun x : EuclideanSpace ℝ (SieveActiveIndex N) => x ⟨q, hq⟩) h
    exact mul_left_cancel₀ (active_sqrt_totient_pos N ⟨q, hq⟩).ne' hq'
  have hraw := (sieve_active_coefficients_eq_iff N _ _).mpr heq
  funext q
  simpa only [sieveCoefficientExtension_active] using hraw q.val q.property

/-- Explicit inverse: remove the totient normalization, then apply finite Ramanujan inversion. -/
def weightedSelbergInverse (N : ℕ) (x : EuclideanSpace ℝ (SieveActiveIndex N)) :
    SieveCoefficientSpace N :=
  sieveCoefficientRestriction N (pmRamanujanResidueCoeff
    (fun q => if h : q ∈ Icc 1 N then x ⟨q, h⟩ / Real.sqrt (q.totient : ℝ) else 0) N)

theorem weightedSelbergLinear_inverse (N : ℕ) (x : EuclideanSpace ℝ (SieveActiveIndex N)) :
    weightedSelbergLinear N (weightedSelbergInverse N x) = x := by
  ext q
  rw [weightedSelbergLinear_apply]
  unfold weightedSelbergInverse
  rw [selbergMultiplesCoord_restrict, selbergMultiplesCoord_ramanujan_inverse, if_pos q.property,
    dif_pos q.property]
  field_simp [(active_sqrt_totient_pos N q).ne']

def weightedSelbergEquiv (N : ℕ) :
    SieveCoefficientSpace N ≃ₗ[ℝ] EuclideanSpace ℝ (SieveActiveIndex N) where
  toLinearMap := weightedSelbergLinear N
  invFun := weightedSelbergInverse N
  left_inv _ := weightedSelbergLinear_injective N (weightedSelbergLinear_inverse N _)
  right_inv := weightedSelbergLinear_inverse N

instance sieveCoefficient_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (SieveCoefficientSpace N) :=
  NormedAddCommGroup.induced _ _ (weightedSelbergLinear N) (weightedSelbergLinear_injective N)

instance sieveCoefficient_innerProductSpace (N : ℕ) : InnerProductSpace ℝ (SieveCoefficientSpace N) :=
  InnerProductSpace.induced (weightedSelbergLinear N)

/-- A genuine isometry: the norm is identified below with the original periodic response norm. -/
def weightedSelbergIsometry (N : ℕ) :
    SieveCoefficientSpace N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (SieveActiveIndex N) where
  toLinearEquiv := weightedSelbergEquiv N
  norm_map' _ := rfl

instance sieveCoefficient_complete (N : ℕ) : CompleteSpace (SieveCoefficientSpace N) :=
  (weightedSelbergIsometry N).toIsometryEquiv.completeSpace

theorem norm_sieveCoefficient_sq (N : ℕ) (c : SieveCoefficientSpace N) :
    ‖c‖ ^ 2 = selbergTotientDiagonalForm N (sieveCoefficientExtension N c) := by
  change ‖weightedSelbergLinear N c‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [weightedSelbergLinear_apply, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  unfold selbergTotientDiagonalForm
  exact Finset.sum_coe_sort (Icc 1 N) (fun q => (q.totient : ℝ) *
    selbergMultiplesCoord N (sieveCoefficientExtension N c) q ^ 2)

/-- Native meaning of the induced Hilbert norm: exact mean square of the literal sieve signal. -/
theorem norm_sieveCoefficient_sq_eq_period_mean (N : ℕ) (c : SieveCoefficientSpace N) :
    ‖c‖ ^ 2 = (∑ k ∈ Ioc 0 N.factorial,
      sieveSeq N (sieveCoefficientExtension N c) k ^ 2) / (N.factorial : ℝ) := by
  rw [norm_sieveCoefficient_sq]
  simpa only [selbergTotientDiagonalForm, pow_two, mul_assoc] using
    (mean_sieveSeq_mul_eq_totient_pairing N (sieveCoefficientExtension N c)
      (sieveCoefficientExtension N c)).symm

/-- The actual best prediction of a true lag, in the native coefficient Hilbert space. -/
def nativeSieveTranslationPredictor (N h : ℕ) (c : SieveCoefficientSpace N) :
    SieveCoefficientSpace N :=
  sieveCoefficientRestriction N (sieveTranslationPredictor N h (sieveCoefficientExtension N c))

/-- Exact intertwining with the normalized Ramanujan lag multiplier, at every active modulus. -/
theorem weightedSelbergIsometry_translation (N h : ℕ) (c : SieveCoefficientSpace N)
    (q : SieveActiveIndex N) :
    weightedSelbergIsometry N (nativeSieveTranslationPredictor N h c) q =
      sieveLagMultiplier q.val h * weightedSelbergIsometry N c q := by
  change weightedSelbergLinear N (nativeSieveTranslationPredictor N h c) q =
    sieveLagMultiplier q.val h * weightedSelbergLinear N c q
  rw [weightedSelbergLinear_apply, weightedSelbergLinear_apply]
  unfold nativeSieveTranslationPredictor
  rw [selbergMultiplesCoord_restrict, selbergMultiplesCoord_translationPredictor, if_pos q.property]
  ring

end GaloisForLFunctions.BezoutValuationIncidence
