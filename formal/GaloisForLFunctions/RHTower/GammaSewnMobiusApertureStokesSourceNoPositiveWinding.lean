import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesReflectedCompactCarrier
import GaloisForLFunctions.RHTower.CCMArithmeticPrimeFredholmOrientation

/-!
# Source-only no-positive winding for the reflected Stokes flow

At critical aperture, normalize real spectral coordinate by first Stokes gap
`Real.log 2`. Every reflected prime-power branch then has literal positive source weight and
strictly downward orientation throughout canonical common pole-free chamber `(-1, 1)`.

Absolute summability preserves strict order after infinite completion. Reflection makes completed
flow odd, its only chamber crossing is at center, and crossing is positive-to-negative. Hardy
polarization assigns Fredholm index `-1`; compact perturbations cannot erase this class.

No Xi zero or zero-location statement enters construction. This theorem does not identify Stokes
flow with completed Xi/CCM source; such receiver equality remains separate weld.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators

noncomputable section
namespace RHTower

open GaloisForLFunctions.HTGeometry

def gammaSewnCriticalStokesNormalizedNode (pk : Nat.Primes × ℕ) : ℝ :=
  Real.log 2 * gammaSewnMobiusApertureStokesReciprocalGapNode (1 / 2) pk

def gammaSewnCriticalStokesSpectralAtom (t : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  -2 * gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk *
      Real.log 2 * t /
    (1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2)

def gammaSewnCriticalStokesSpectralFlow (t : ℝ) : ℝ :=
  ∑' pk : Nat.Primes × ℕ, gammaSewnCriticalStokesSpectralAtom t pk

/-- Signed crossing count for scalar path known to have at most one chamber zero. -/
def scalarUniqueCrossingWinding (left right : ℝ) : ℤ :=
  if 0 < left ∧ right < 0 then -1
  else if left < 0 ∧ 0 < right then 1
  else 0

/-- Source-computed winding across symmetric interior chamber. -/
def gammaSewnCriticalStokesSourceWinding : ℤ :=
  scalarUniqueCrossingWinding
    (gammaSewnCriticalStokesSpectralFlow (-1 / 2))
    (gammaSewnCriticalStokesSpectralFlow (1 / 2))

/-- Hardy/Fredholm winding selected by fundamental downward source orientation. -/
def gammaSewnCriticalStokesFredholmSpectralFlow : ℤ :=
  signedToeplitzIndex 1

theorem gammaSewnCriticalStokesNormalizedNode_mem_unit
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalStokesNormalizedNode pk ∈ Set.Ioc 0 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnode :=
    gammaSewnMobiusApertureStokesReciprocalGapNode_pos
      (s := (1 / 2 : ℝ)) (by norm_num) pk
  refine ⟨mul_pos hlog hnode, ?_⟩
  rw [gammaSewnCriticalStokesNormalizedNode]
  calc
    Real.log 2 * gammaSewnMobiusApertureStokesReciprocalGapNode (1 / 2) pk
        ≤ Real.log 2 * (Real.log 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (gammaSewnMobiusApertureStokesReciprocalGapNode_le
          (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) pk) hlog.le
    _ = 1 := by field_simp

private theorem gammaSewnCriticalStokes_denominator_pos
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1)
    (pk : Nat.Primes × ℕ) :
    0 < 1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 := by
  have ha := gammaSewnCriticalStokesNormalizedNode_mem_unit pk
  have htAbs : |t| < (1 : ℝ) := (abs_lt).2 ht
  have hatAbs :
      |gammaSewnCriticalStokesNormalizedNode pk * t| < (1 : ℝ) := by
    rw [abs_mul, abs_of_pos ha.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg t) ha.2) htAbs
  have hsq :
      (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 < (1 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 hatAbs
  nlinarith

theorem summable_gammaSewnCriticalStokesSpectralAtom
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Summable (gammaSewnCriticalStokesSpectralAtom t) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hweight :=
    summable_gammaSewnMobiusApertureStokesSignedWeight
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hbase :
      Summable (fun pk : Nat.Primes × ℕ =>
        gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk) := by
    have hcomp := hweight.comp_injective
      (fun _ _ h => Sum.inl.inj h)
    exact hcomp.congr (fun _ => rfl)
  have htAbs : |t| < (1 : ℝ) := (abs_lt).2 ht
  have htSq : t ^ 2 < 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_lt_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).2 htAbs
  have hmargin : 0 < 1 - t ^ 2 := sub_pos.mpr htSq
  apply Summable.of_norm_bounded
    (hbase.mul_left (2 * Real.log 2 * |t| / (1 - t ^ 2)))
  intro pk
  have hden := gammaSewnCriticalStokes_denominator_pos ht pk
  have hdenLower :
      1 - t ^ 2 ≤
        1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 := by
    have ha := gammaSewnCriticalStokesNormalizedNode_mem_unit pk
    have hatAbsLe :
        |gammaSewnCriticalStokesNormalizedNode pk * t| ≤ |t| := by
      rw [abs_mul, abs_of_pos ha.1]
      exact mul_le_of_le_one_left (abs_nonneg t) ha.2
    have hsqLe :
        (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 ≤ t ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (abs_nonneg t)).2 hatAbsLe
    linarith
  have hw := gammaSewnMobiusApertureStokesReflectedWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk
  rw [gammaSewnCriticalStokesSpectralAtom, Real.norm_eq_abs, abs_div,
    abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hw, abs_of_pos hlog,
    abs_of_pos hden]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  let mass := 2 *
    gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk *
      Real.log 2 * |t|
  have hmass : 0 ≤ mass := by
    dsimp only [mass]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hw.le) hlog.le)
      (abs_nonneg t)
  calc
    mass / (1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2)
        ≤ mass / (1 - t ^ 2) :=
      div_le_div_of_nonneg_left hmass hmargin hdenLower
    _ = (2 * Real.log 2 * |t| / (1 - t ^ 2)) *
        gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk := by
      dsimp only [mass]
      ring

theorem gammaSewnCriticalStokesSpectralAtom_neg
    (t : ℝ) (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalStokesSpectralAtom (-t) pk =
      -gammaSewnCriticalStokesSpectralAtom t pk := by
  unfold gammaSewnCriticalStokesSpectralAtom
  ring

theorem gammaSewnCriticalStokesSpectralFlow_neg (t : ℝ) :
    gammaSewnCriticalStokesSpectralFlow (-t) =
      -gammaSewnCriticalStokesSpectralFlow t := by
  rw [gammaSewnCriticalStokesSpectralFlow,
    gammaSewnCriticalStokesSpectralFlow,
    tsum_congr (gammaSewnCriticalStokesSpectralAtom_neg t),
    tsum_neg]

private theorem gammaSewnCriticalStokesSpectralAtom_strictAntiOn
    (pk : Nat.Primes × ℕ) :
    StrictAntiOn (fun t => gammaSewnCriticalStokesSpectralAtom t pk)
      (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  let a := gammaSewnCriticalStokesNormalizedNode pk
  let w := gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk
  have ha := gammaSewnCriticalStokesNormalizedNode_mem_unit pk
  have hw : 0 < w := gammaSewnMobiusApertureStokesReflectedWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdx : 0 < 1 - (a * x) ^ 2 := by
    simpa only [a] using gammaSewnCriticalStokes_denominator_pos hx pk
  have hdy : 0 < 1 - (a * y) ^ 2 := by
    simpa only [a] using gammaSewnCriticalStokes_denominator_pos hy pk
  have hxyFactor : 0 < 1 + a ^ 2 * x * y := by
    have hax : |a * x| < (1 : ℝ) := by
      rw [abs_mul, abs_of_pos ha.1]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left (abs_nonneg x) ha.2) ((abs_lt).2 hx)
    have hay : |a * y| < (1 : ℝ) := by
      rw [abs_mul, abs_of_pos ha.1]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left (abs_nonneg y) ha.2) ((abs_lt).2 hy)
    have hprod : |(a * x) * (a * y)| < (1 : ℝ) := by
      have hsum : |a * x| + |a * y| < (2 : ℝ) := by linarith
      have hsumsq : (|a * x| + |a * y|) ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ (by positivity) (by norm_num)).2 hsum
      calc
        |(a * x) * (a * y)| = |a * x| * |a * y| := abs_mul _ _
        _ < 1 := by
          nlinarith [sq_nonneg (|a * x| - |a * y|)]
    have hlower : -(1 : ℝ) < (a * x) * (a * y) :=
      (abs_lt.1 hprod).1
    nlinarith
  have hmono :
      x / (1 - (a * x) ^ 2) < y / (1 - (a * y) ^ 2) := by
    rw [div_lt_div_iff₀ hdx hdy]
    have hfactorization :
        y * (1 - (a * x) ^ 2) - x * (1 - (a * y) ^ 2) =
          (y - x) * (1 + a ^ 2 * x * y) := by ring
    rw [← sub_pos, hfactorization]
    positivity
  unfold gammaSewnCriticalStokesSpectralAtom
  dsimp only [a, w] at hmono ⊢
  have hscale : -2 * w * Real.log 2 < 0 := by
    nlinarith [mul_pos hw hlog]
  have hscaled := mul_lt_mul_of_neg_left hmono hscale
  simpa only [mul_div_assoc] using hscaled

theorem gammaSewnCriticalStokesSpectralFlow_strictAntiOn :
    StrictAntiOn gammaSewnCriticalStokesSpectralFlow
      (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [gammaSewnCriticalStokesSpectralFlow,
    gammaSewnCriticalStokesSpectralFlow]
  have hxsum := summable_gammaSewnCriticalStokesSpectralAtom hx
  have hysum := summable_gammaSewnCriticalStokesSpectralAtom hy
  exact hysum.tsum_lt_tsum
    (i := ((⟨2, Nat.prime_two⟩ : Nat.Primes), 0))
    (fun pk =>
      (gammaSewnCriticalStokesSpectralAtom_strictAntiOn pk hx hy hxy).le)
    (gammaSewnCriticalStokesSpectralAtom_strictAntiOn
      ((⟨2, Nat.prime_two⟩ : Nat.Primes), 0) hx hy hxy)
    hxsum

theorem gammaSewnCriticalStokesSpectralFlow_zero :
    gammaSewnCriticalStokesSpectralFlow 0 = 0 := by
  simp [gammaSewnCriticalStokesSpectralFlow,
    gammaSewnCriticalStokesSpectralAtom]

/-- Completed response is positive before center and negative after center. -/
theorem gammaSewnCriticalStokesSpectralFlow_center_sign :
    (∀ t ∈ Set.Ioo (-1 : ℝ) 0,
        0 < gammaSewnCriticalStokesSpectralFlow t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1,
        gammaSewnCriticalStokesSpectralFlow t < 0) := by
  constructor
  · intro t ht
    have hdrop :=
      gammaSewnCriticalStokesSpectralFlow_strictAntiOn
        ⟨ht.1, ht.2.trans (by norm_num)⟩
        (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1) ht.2
    simpa only [gammaSewnCriticalStokesSpectralFlow_zero] using hdrop
  · intro t ht
    have hdrop :=
      gammaSewnCriticalStokesSpectralFlow_strictAntiOn
        (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
        ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) ht.1, ht.2⟩ ht.1
    simpa only [gammaSewnCriticalStokesSpectralFlow_zero] using hdrop

/-- Literal source flow has crossing number `-1`: unique crossing is downward. -/
theorem gammaSewnCriticalStokesSourceWinding_eq_neg_one :
    gammaSewnCriticalStokesSourceWinding = -1 := by
  have hdown :
      0 < gammaSewnCriticalStokesSpectralFlow (-1 / 2) ∧
        gammaSewnCriticalStokesSpectralFlow (1 / 2) < 0 := by
    exact ⟨gammaSewnCriticalStokesSpectralFlow_center_sign.1
        (-1 / 2) (by norm_num),
      gammaSewnCriticalStokesSpectralFlow_center_sign.2
        (1 / 2) (by norm_num)⟩
  rw [gammaSewnCriticalStokesSourceWinding,
    scalarUniqueCrossingWinding, if_pos hdown]

theorem gammaSewnCriticalStokesFredholmSpectralFlow_eq_neg_one :
    gammaSewnCriticalStokesFredholmSpectralFlow = -1 := by
  rw [gammaSewnCriticalStokesFredholmSpectralFlow,
    signedToeplitzIndex_eq]

theorem gammaSewnCriticalStokesFredholmSpectralFlow_compact_stable :
    ∀ U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ,
      ¬ IsCompactOperator
        ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) - signedToeplitzOp 1) := by
  intro U
  exact signedToeplitz_no_unit_compact_perturbation
    (⟨1, by norm_num⟩ : {m : ℤ // m ≠ 0}) U

/-- Source crossing winding and Hardy/Fredholm index agree exactly. -/
theorem gammaSewnCriticalStokesSourceWinding_eq_fredholmSpectralFlow :
    gammaSewnCriticalStokesSourceWinding =
      gammaSewnCriticalStokesFredholmSpectralFlow := by
  rw [gammaSewnCriticalStokesSourceWinding_eq_neg_one,
    gammaSewnCriticalStokesFredholmSpectralFlow_eq_neg_one]

theorem gammaSewnCriticalStokesSourceOnlyNoPositiveWinding :
    StrictAntiOn gammaSewnCriticalStokesSpectralFlow
        (Set.Ioo (-1 : ℝ) 1) ∧
      gammaSewnCriticalStokesSpectralFlow 0 = 0 ∧
      (∀ t : ℝ, gammaSewnCriticalStokesSpectralFlow (-t) =
        -gammaSewnCriticalStokesSpectralFlow t) ∧
      gammaSewnCriticalStokesSourceWinding = -1 ∧
      gammaSewnCriticalStokesSourceWinding =
        gammaSewnCriticalStokesFredholmSpectralFlow ∧
      gammaSewnCriticalStokesFredholmSpectralFlow = -1 ∧
      (∀ U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ,
        ¬ IsCompactOperator
          ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) - signedToeplitzOp 1)) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 0,
        0 < gammaSewnCriticalStokesSpectralFlow t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1,
        gammaSewnCriticalStokesSpectralFlow t < 0) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        gammaSewnCriticalStokesSpectralFlow t = 0 ↔ t = 0) ∧
      ¬ ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
          ∃ y ∈ Set.Ioo (-1 : ℝ) 1,
            x < y ∧ gammaSewnCriticalStokesSpectralFlow x < 0 ∧
              0 < gammaSewnCriticalStokesSpectralFlow y := by
  refine ⟨gammaSewnCriticalStokesSpectralFlow_strictAntiOn,
    gammaSewnCriticalStokesSpectralFlow_zero,
    gammaSewnCriticalStokesSpectralFlow_neg,
    gammaSewnCriticalStokesSourceWinding_eq_neg_one,
    gammaSewnCriticalStokesSourceWinding_eq_fredholmSpectralFlow,
    gammaSewnCriticalStokesFredholmSpectralFlow_eq_neg_one,
    gammaSewnCriticalStokesFredholmSpectralFlow_compact_stable,
    gammaSewnCriticalStokesSpectralFlow_center_sign.1,
    gammaSewnCriticalStokesSpectralFlow_center_sign.2, ?_, ?_⟩
  · intro t ht
    constructor
    · intro hzero
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with htneg | htpos
      · have hdrop :=
          gammaSewnCriticalStokesSpectralFlow_strictAntiOn ht
            (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1) htneg
        rw [gammaSewnCriticalStokesSpectralFlow_zero, hzero] at hdrop
        exact lt_irrefl 0 hdrop
      · have hdrop :=
          gammaSewnCriticalStokesSpectralFlow_strictAntiOn
            (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
            ht htpos
        rw [gammaSewnCriticalStokesSpectralFlow_zero, hzero] at hdrop
        exact lt_irrefl 0 hdrop
    · rintro rfl
      exact gammaSewnCriticalStokesSpectralFlow_zero
  · rintro ⟨x, hx, y, hy, hxy, hxneg, hypos⟩
    have hdrop :=
      gammaSewnCriticalStokesSpectralFlow_strictAntiOn hx hy hxy
    linarith

end RHTower
