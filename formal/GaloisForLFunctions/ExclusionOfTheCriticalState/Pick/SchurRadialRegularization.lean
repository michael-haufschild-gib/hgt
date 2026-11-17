import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ReciprocalProbeKernel
import GaloisForLFunctions.RHTower.CCM.CCMDiagonalFockLift

/-!
# Radial Schur regularization of the Weil probe kernel

Common disc coordinates, as used in the Pick-body classification of
arXiv:2610.28972, give an explicit radial contraction of the probe symbol.
After diagonal congruence its kernel is the original Weil kernel plus two
positive Cauchy Gram forms. Complete contraction erases every negative
direction. Nevertheless, varying the contraction retains exactly the
negative directions detectable by some finite coefficient vector.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
noncomputable section

def radialScale (a : ℝ) : ℝ := 1 + |a|

private theorem radialScale_pos (a : ℝ) : 0 < radialScale a := by
  unfold radialScale
  positivity

private theorem normalizer_pos (a t : ℝ) : 0 < symbol t + radialScale a :=
  add_pos (symbol_pos t) (radialScale_pos a)

/-- Radial contraction of the Schur value, expressed in right-half-plane coordinates. -/
def radialSymbol (a t : ℝ) : ℝ :=
  (radialScale a * symbol t + 1) / (symbol t + radialScale a)

theorem radialSymbol_pos (a t : ℝ) : 0 < radialSymbol a t := by
  unfold radialSymbol
  exact div_pos (by have := symbol_pos t; have := radialScale_pos a; positivity)
    (normalizer_pos a t)

/-- The parameter contracts every Cayley coordinate by the same real factor. -/
theorem radial_cayley (a t : ℝ) :
    (radialSymbol a t - 1) / (radialSymbol a t + 1) =
      ((radialScale a - 1) / (radialScale a + 1)) *
        ((symbol t - 1) / (symbol t + 1)) := by
  have hD := symbol_pos t
  have hk := radialScale_pos a
  unfold radialSymbol
  field_simp (disch := positivity)
  ring

def radialKernel (a s t : ℝ) : ℝ :=
  (radialSymbol a s + radialSymbol a t) / (node s + node t)

/-- Exact positive-defect decomposition before summing coefficient vectors. -/
theorem radial_scaled_kernel (a s t : ℝ) :
    (symbol s + radialScale a) * (symbol t + radialScale a) * radialKernel a s t =
      (radialScale a ^ 2 + 1) * bareMixedEnergy (probe (node s)) (probe (node t)) +
      2 * radialScale a * ((symbol s * symbol t + 1) / (node s + node t)) := by
  have hs : (1 / 2 : ℝ) < node s := by unfold node; linarith only [abs_nonneg s]
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith only [abs_nonneg t]
  rw [bareMixedEnergy_probe hs ht]
  change (symbol s + radialScale a) * (symbol t + radialScale a) * radialKernel a s t =
    (radialScale a ^ 2 + 1) * ((symbol s + symbol t) / (node s + node t)) +
      2 * radialScale a * ((symbol s * symbol t + 1) / (node s + node t))
  have hD := symbol_pos s
  have hE := symbol_pos t
  have hk := radialScale_pos a
  have hn : 0 < node s + node t := by linarith only [hs, ht]
  unfold radialKernel radialSymbol
  field_simp (disch := positivity)
  ring

/-- The original finite Weil probe quadratic form. -/
def sourceQuadratic (n : ℕ) (p c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * bareMixedEnergy (probe (node (p i))) (probe (node (p j)))

def radialQuadratic (a : ℝ) (n : ℕ) (p c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * radialKernel a (p i) (p j)

/-- The positive Cauchy mass form of the same probe exponents. -/
def massQuadratic (n : ℕ) (p c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * (1 / (node (p i) + node (p j)))

theorem massQuadratic_nonneg (n : ℕ) (p c : Fin n → ℝ) : 0 ≤ massQuadratic n p c := by
  have hp (i : Fin n) : 0 < node (p i) := by unfold node; positivity
  have h := GaloisForLFunctions.RHTower.cauchy_quadratic_form hp c
  change massQuadratic n p c = _ at h
  rw [h]
  exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- Two positive Gram masses account for the entire radial defect. -/
def defectMass (n : ℕ) (p c : Fin n → ℝ) : ℝ :=
  massQuadratic n p c + massQuadratic n p (fun i => c i * symbol (p i))

theorem defectMass_nonneg (n : ℕ) (p c : Fin n → ℝ) : 0 ≤ defectMass n p c :=
  add_nonneg (massQuadratic_nonneg n p c) (massQuadratic_nonneg n p _)

/-- Diagonal congruence isolates the original form and its positive regularization cost. -/
theorem radial_quadratic_recovery (a : ℝ) (n : ℕ) (p c : Fin n → ℝ) :
    radialQuadratic a n p (fun i => c i * (symbol (p i) + radialScale a)) =
      (radialScale a ^ 2 + 1) * sourceQuadratic n p c +
        2 * radialScale a * defectMass n p c := by
  unfold defectMass
  rw [mul_add]
  simp only [radialQuadratic, sourceQuadratic, massQuadratic,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (c i * c j) * ((symbol (p i) + radialScale a) *
        (symbol (p j) + radialScale a) * radialKernel a (p i) (p j)) := by ring
    _ = _ := by
      rw [radial_scaled_kernel]
      simp only [div_eq_mul_inv]
      ring

/-- Regularization dominates a positive multiple of the original form after rescaling. -/
theorem radial_quadratic_lower_bound (a : ℝ) (n : ℕ) (p c : Fin n → ℝ) :
    (radialScale a ^ 2 + 1) *
        sourceQuadratic n p (fun i => c i / (symbol (p i) + radialScale a)) ≤
      radialQuadratic a n p c := by
  have h := radial_quadratic_recovery a n p
    (fun i => c i / (symbol (p i) + radialScale a))
  simp only [div_mul_cancel₀ _ (normalizer_pos a _).ne'] at h
  rw [h]
  exact le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (by norm_num) (radialScale_pos a).le) (defectMass_nonneg n p _))

/-- Varying the radial contraction preserves the existence of a negative finite Weil witness. -/
theorem radial_family_negative_iff (n : ℕ) (p : Fin n → ℝ) :
    (∃ a : ℝ, ∃ c : Fin n → ℝ, radialQuadratic a n p c < 0) ↔
      ∃ c : Fin n → ℝ, sourceQuadratic n p c < 0 := by
  constructor
  · rintro ⟨a, c, hc⟩
    refine ⟨fun i => c i / (symbol (p i) + radialScale a), ?_⟩
    by_contra h
    have hn := mul_nonneg (by positivity : 0 ≤ radialScale a ^ 2 + 1) (le_of_not_gt h)
    exact (not_lt_of_ge (hn.trans (radial_quadratic_lower_bound a n p c))) hc
  · rintro ⟨c, hc⟩
    let q := -sourceQuadratic n p c
    have hq : 0 < q := neg_pos.mpr hc
    let a := 2 * defectMass n p c / q
    have ha : 0 ≤ a := div_nonneg
      (mul_nonneg (by norm_num) (defectMass_nonneg n p c)) hq.le
    have hae : a * q = 2 * defectMass n p c := div_mul_cancel₀ _ hq.ne'
    have hk : radialScale a = 1 + a := by rw [radialScale, abs_of_nonneg ha]
    refine ⟨a, fun i => c i * (symbol (p i) + radialScale a), ?_⟩
    rw [radial_quadratic_recovery, hk]
    calc
      _ = -(a + 2) * q + (a + 1) * (2 * defectMass n p c - a * q) := by
        dsimp only [q]
        ring
      _ = -(a + 2) * q := by rw [hae, sub_self, mul_zero, add_zero]
      _ < 0 := mul_neg_of_neg_of_pos (by linarith only [ha]) hq

/-- At complete contraction the symbol is constant, regardless of the original Weil geometry. -/
theorem radialSymbol_zero (t : ℝ) : radialSymbol 0 t = 1 := by
  have h0 : symbol t + 1 ≠ 0 := by have := symbol_pos t; positivity
  simp only [radialSymbol, radialScale, abs_zero, add_zero, one_mul, div_self h0]

/-- Complete contraction produces the positive Cauchy kernel and masks all negative tests. -/
theorem radial_zero_nonnegative (n : ℕ) (p c : Fin n → ℝ) :
    0 ≤ radialQuadratic 0 n p c := by
  have he : radialQuadratic 0 n p c = 2 * massQuadratic n p c := by
    simp only [radialQuadratic, radialKernel, radialSymbol_zero, massQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact mul_nonneg (by norm_num) (massQuadratic_nonneg n p c)

/-- The Cauchy defect always compensates the negative part at complete contraction. -/
theorem source_plus_defect_nonneg (n : ℕ) (p c : Fin n → ℝ) :
    0 ≤ sourceQuadratic n p c + defectMass n p c := by
  have h := radial_zero_nonnegative n p (fun i => c i * (symbol (p i) + radialScale 0))
  rw [radial_quadratic_recovery] at h
  simp only [radialScale, abs_zero, add_zero, one_pow, mul_one] at h
  linarith only [h]

/-- The exact disc-radius threshold for exposing a fixed finite negative direction. -/
theorem radial_negative_threshold (a : ℝ) (n : ℕ) (p c : Fin n → ℝ) :
    radialQuadratic a n p (fun i => c i * (symbol (p i) + radialScale a)) < 0 ↔
      sourceQuadratic n p c + defectMass n p c <
        ((radialScale a - 1) / (radialScale a + 1)) ^ 2 *
          (defectMass n p c - sourceQuadratic n p c) := by
  have hk := radialScale_pos a
  have hd : 0 < (radialScale a + 1) ^ 2 := sq_pos_of_pos (by linarith only [hk])
  rw [radial_quadratic_recovery, div_pow, div_mul_eq_mul_div,
    lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

#print axioms radial_cayley
#print axioms radial_quadratic_recovery
#print axioms radial_quadratic_lower_bound
#print axioms radial_family_negative_iff
#print axioms radial_zero_nonnegative
#print axioms radial_negative_threshold

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
