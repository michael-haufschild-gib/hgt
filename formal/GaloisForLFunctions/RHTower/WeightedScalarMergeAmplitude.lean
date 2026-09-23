import GaloisForLFunctions.RHTower.SignedScalarMergeOrder

/-!
# Sharp head amplitude for positively weighted scalar mergers

The energy inequality controls each outward head excursion by the absorbed
leaf magnitude times `(1+alpha)/(2*alpha)`. A unit leaf attains this
coefficient. The same ceiling propagates along every bounded-leaf path.
-/

noncomputable section
open Finset
namespace RHTower

/-- A decreasing positively weighted scalar merger cannot cross this sharp head amplitude. -/
theorem abs_weightedScalarMerge_le {α h a : ℝ} (hα : 0<α)
    (hstep : α*(h+a)^(2 : ℕ) ≤ α*h^(2 : ℕ)+a^(2 : ℕ)) :
    |h+a| ≤ max |h| (((1+α)/(2*α))*|a|) := by
  by_cases hh : |h+a| ≤ |h|
  · exact hh.trans (le_max_left _ _)
  have hsq : h^(2 : ℕ) < (h+a)^(2 : ℕ) := by
    have ht := (sq_lt_sq₀ (abs_nonneg h) (abs_nonneg (h+a))).mpr (lt_of_not_ge hh)
    simpa only [sq_abs] using ht
  have hprod : 0<(h+a)*a := by nlinarith only [hsq,sq_nonneg a]
  have hab : |h+a| * |a| = (h+a)*a := by rw [← abs_mul,abs_of_pos hprod]
  have ha : 0< |a| := abs_pos.mpr (by intro he; subst a; simp at hprod)
  have hineq : 2*α*(|h+a| * |a|) ≤ (1+α)*|a|^(2 : ℕ) := by
    rw [hab,sq_abs]
    nlinarith only [hstep]
  have hcancel : 2*α*|h+a| ≤ (1+α)*|a| := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hineq]
  have hb : |h+a| ≤ ((1+α)/(2*α))*|a| := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0<2*α)).mpr
    nlinarith only [hcancel]
  exact hb.trans (le_max_right _ _)

/-- The head coefficient cannot be lowered: a unit leaf attains it with exact energy equality. -/
theorem weightedScalarMerge_amplitude_sharp {α : ℝ} (hα : 0<α) :
    ∃ h : ℝ, α*(h+1)^(2 : ℕ)=α*h^(2 : ℕ)+1 ∧
      |h| < |h+1| ∧ |h+1| = (1+α)/(2*α) := by
  let κ : ℝ := (1+α)/(2*α)
  have hκ : 1/2<κ := by
    dsimp [κ]
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : 2*α*κ=1+α := by
    dsimp [κ]
    field_simp
  refine ⟨κ-1,?_,?_,?_⟩
  · nlinarith only [he]
  · rw [sub_add_cancel,abs_of_pos (by linarith : 0<κ)]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · rw [sub_add_cancel,abs_of_pos (by linarith : 0<κ)]

/-- The same amplitude ceiling holds at every step of a finite sequence of bounded scalar mergers. -/
theorem abs_weightedScalarMerge_path_le {α A : ℝ} (hα : 0<α)
    (h : ℕ → ℝ) (a : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ k<N,h (k+1)=h k+a k)
    (hleaf : ∀ k<N,|a k| ≤ A)
    (hstep : ∀ k<N,α*(h (k+1))^(2 : ℕ)≤α*(h k)^(2 : ℕ)+(a k)^(2 : ℕ)) :
    ∀ k≤N,|h k| ≤ max |h 0| (((1+α)/(2*α))*A) := by
  intro k hk
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    have hkN : k<N := by omega
    have hbound := abs_weightedScalarMerge_le hα (by rw [← hrec k hkN]; exact hstep k hkN)
    rw [← hrec k hkN] at hbound
    exact hbound.trans (max_le (ih (by omega))
      ((mul_le_mul_of_nonneg_left (hleaf k hkN) (by positivity)).trans (le_max_right _ _)))

end RHTower
