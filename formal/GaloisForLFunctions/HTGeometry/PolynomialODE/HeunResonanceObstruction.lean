import GaloisForLFunctions.HTGeometry.PolynomialODE.HeunResonantBranch

/-!
# Compatibility and freedom at a Heun resonance

A single collision equation decides normalized formal solvability. Every nonempty normalized solution set is an affine line in the free branch.
-/

open scoped PowerSeries
noncomputable section
namespace GaloisForLFunctions.HTGeometry.Heun

/-- The sole compatibility equation at the negative-integer coefficient collision. -/
def resonantObstruction (m : ℕ) (β γ q : ℂ) : ℂ :=
  match m with
  | 0 => q
  | n + 1 =>
    (β * ((n + 1 : ℕ) : ℂ) + q) * normalizedCoefficient (-((n + 2 : ℕ) : ℂ)) β γ q (n + 1) +
      (2 * ((n + 1 : ℕ) : ℂ) - ((n + 2 : ℕ) : ℂ) - γ) *
        normalizedCoefficient (-((n + 2 : ℕ) : ℂ)) β γ q n

private theorem resonant_denominator_ne (m r : ℕ) (hr : r ≠ 0) (hne : r ≠ m + 1) :
    (r : ℂ) * ((r : ℂ) + -((m + 1 : ℕ) : ℂ)) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast hr
  · rw [← sub_eq_add_neg]
    apply sub_ne_zero.mpr
    exact_mod_cast hne

/-- Below the collision, a normalized solution has the explicitly divided coefficients. -/
theorem resonant_recurrence_below (m : ℕ) (β γ q : ℂ) (d : ℕ → ℂ)
    (hd : CoefficientRecurrence (-((m + 1 : ℕ) : ℂ)) β γ q d) (h0 : d 0 = 1)
    (r : ℕ) (hr : r < m + 1) :
    d r = normalizedCoefficient (-((m + 1 : ℕ) : ℂ)) β γ q r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases r with _ | r
    · exact h0
    · rcases r with _ | n
      · have hden : (1 : ℂ) + -((m + 1 : ℕ) : ℂ) ≠ 0 := by
          have h := resonant_denominator_ne m 1 (by omega) (by omega)
          simpa only [Nat.cast_one, one_mul] using h
        rw [normalizedCoefficient]
        apply (eq_div_iff hden).mpr
        simpa only [h0, mul_one, mul_comm] using hd.1
      · rw [normalizedCoefficient]
        apply (eq_div_iff (resonant_denominator_ne m (n + 2) (by omega) (by omega))).mpr
        rw [mul_comm, hd.2 n, ih (n + 1) (by omega) (by omega), ih n (by omega) (by omega)]

/-- The canonical divided sequence solves precisely when its collision obstruction vanishes. -/
theorem normalized_resonant_recurrence_iff (m : ℕ) (β γ q : ℂ) :
    CoefficientRecurrence (-((m + 1 : ℕ) : ℂ)) β γ q
      (normalizedCoefficient (-((m + 1 : ℕ) : ℂ)) β γ q) ↔
      resonantObstruction m β γ q = 0 := by
  constructor
  · intro hd
    cases m with
    | zero =>
      have h := hd.1
      simpa [normalizedCoefficient, resonantObstruction] using h.symm
    | succ n =>
      have h := hd.2 n
      simpa only [resonantObstruction, add_neg_cancel, mul_zero, zero_mul, sub_eq_add_neg] using h.symm
  · intro ho
    constructor
    · by_cases hm : m = 0
      · subst m
        have hq : q = 0 := ho
        simp [normalizedCoefficient, hq]
      · have hden : (1 : ℂ) + -((m + 1 : ℕ) : ℂ) ≠ 0 := by
          have h := resonant_denominator_ne m 1 (by omega) (by omega)
          simpa only [Nat.cast_one, one_mul] using h
        simp only [normalizedCoefficient, mul_one]
        exact (mul_comm _ _).trans (div_mul_cancel₀ _ hden)
    · intro n
      by_cases hcol : n + 2 = m + 1
      · have hm : m = n + 1 := by omega
        subst m
        simpa only [resonantObstruction, add_neg_cancel, mul_zero, zero_mul, sub_eq_add_neg] using ho.symm
      · rw [normalizedCoefficient]
        exact (mul_comm _ _).trans (div_mul_cancel₀ _
          (resonant_denominator_ne m (n + 2) (by omega) hcol))

/-- A normalized formal solution exists exactly when the single collision equation is compatible. -/
theorem exists_normalized_resonant_iff (m : ℕ) (β γ q : ℂ) :
    (∃ f : ℂ⟦X⟧, formalAction (-((m + 1 : ℕ) : ℂ)) β γ q f = 0 ∧
      PowerSeries.coeff 0 f = 1) ↔ resonantObstruction m β γ q = 0 := by
  constructor
  · rintro ⟨f, hf, h0⟩
    have hd := (formalAction_eq_zero_iff _ _ _ _ f).mp hf
    cases m with
    | zero =>
      have h := hd.1
      simpa [h0, resonantObstruction] using h.symm
    | succ n =>
      have h := hd.2 n
      dsimp only at h
      rw [resonant_recurrence_below (n + 1) β γ q _ hd h0 (n + 1) (by omega),
        resonant_recurrence_below (n + 1) β γ q _ hd h0 n (by omega)] at h
      simpa only [resonantObstruction, add_neg_cancel, mul_zero, zero_mul, sub_eq_add_neg] using h.symm
  · intro ho
    refine ⟨normalizedFormalSolution (-((m + 1 : ℕ) : ℂ)) β γ q, ?_, ?_⟩
    · apply (formalAction_eq_zero_iff _ _ _ _ _).mpr
      simpa only [normalizedFormalSolution, PowerSeries.coeff_mk] using
        (normalized_resonant_recurrence_iff m β γ q).mpr ho
    · simp only [normalizedFormalSolution, PowerSeries.coeff_mk, normalizedCoefficient]

/-- The constant term and the collided coefficient determine every resonant formal solution. -/
theorem resonant_recurrence_unique (m : ℕ) (β γ q : ℂ) (d e : ℕ → ℂ)
    (hd : CoefficientRecurrence (-((m + 1 : ℕ) : ℂ)) β γ q d)
    (he : CoefficientRecurrence (-((m + 1 : ℕ) : ℂ)) β γ q e)
    (h0 : d 0 = e 0) (hcol : d (m + 1) = e (m + 1)) : d = e := by
  funext r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r = m + 1
    · simpa only [hr] using hcol
    · rcases r with _ | r
      · exact h0
      · rcases r with _ | n
        · have hden : (1 : ℂ) + -((m + 1 : ℕ) : ℂ) ≠ 0 := by
            have h := resonant_denominator_ne m 1 (by omega) hr
            simpa only [Nat.cast_one, one_mul] using h
          apply mul_left_cancel₀ hden
          rw [hd.1, he.1, h0]
        · apply mul_left_cancel₀ (resonant_denominator_ne m (n + 2) (by omega) hr)
          rw [hd.2 n, he.2 n, ih (n + 1) (by omega), ih n (by omega)]

private theorem formalAction_add_smul (α β γ q c : ℂ) (f g : ℂ⟦X⟧) :
    formalAction α β γ q (f + c • g) = formalAction α β γ q f + c • formalAction α β γ q g := by
  have hD (h : ℂ⟦X⟧) : PowerSeries.derivative ℂ (c • h) =
      c • PowerSeries.derivative ℂ h := PowerSeries.derivativeFun_smul c h
  simp only [formalAction, _root_.RHTower.hypergeometricEulerOperator, map_add, hD,
    mul_add, mul_smul_comm, smul_sub, smul_add]
  module

/-- Every nonempty normalized resonant solution set is precisely an affine line in the free branch. -/
theorem normalized_resonant_affine_line (m : ℕ) (β γ q : ℂ) (f g : ℂ⟦X⟧)
    (hf : formalAction (-((m + 1 : ℕ) : ℂ)) β γ q f = 0)
    (hf0 : PowerSeries.coeff 0 f = 1) :
    (formalAction (-((m + 1 : ℕ) : ℂ)) β γ q g = 0 ∧ PowerSeries.coeff 0 g = 1) ↔
      ∃! c : ℂ, g = f + c • resonantFormalBranch m β γ q := by
  have hb := resonantFormalBranch_solves m β γ q
  constructor
  · rintro ⟨hg, hg0⟩
    let c := PowerSeries.coeff (m + 1) g - PowerSeries.coeff (m + 1) f
    have hc : g = f + c • resonantFormalBranch m β γ q := by
      apply PowerSeries.ext
      intro n
      apply congrFun (resonant_recurrence_unique m β γ q
        (fun n => PowerSeries.coeff n g)
        (fun n => PowerSeries.coeff n (f + c • resonantFormalBranch m β γ q))
        ((formalAction_eq_zero_iff _ _ _ _ g).mp hg)
        ((formalAction_eq_zero_iff _ _ _ _ _).mp (by
          rw [formalAction_add_smul, hf, hb.1, smul_zero, add_zero]))
        (by simp only [map_add, map_smul, hg0, hf0, hb.2.1, smul_zero, add_zero])
        (by
          simp only [map_add, map_smul, hb.2.2, smul_eq_mul, mul_one]
          dsimp only [c]
          ring)) n
    refine ⟨c, hc, ?_⟩
    intro d hd
    have h := congrArg (PowerSeries.coeff (m + 1)) hd
    simp only [map_add, map_smul, hb.2.2, smul_eq_mul, mul_one] at h
    dsimp only [c]
    linear_combination -h
  · rintro ⟨c, rfl, _⟩
    constructor
    · rw [formalAction_add_smul, hf, hb.1, smul_zero, add_zero]
    · simp only [map_add, map_smul, hf0, hb.2.1, smul_zero, add_zero]

#print axioms exists_normalized_resonant_iff
#print axioms resonant_recurrence_unique
#print axioms normalized_resonant_affine_line
end GaloisForLFunctions.HTGeometry.Heun
