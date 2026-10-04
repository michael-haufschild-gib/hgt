import GaloisForLFunctions.RHTower.RoutePCausalWindowRecovery
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite prime-cube covariance with the causal recovery cost retained

The finite algebra below keeps every cofactor and every earlier-clock
square. It supplies the prime-set induction for the native biased
covariance comparison, without assuming a full-ray energy bound.
-/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

variable {ι : Type*} [DecidableEq ι]

/-- Apply a finite family of commuting causal differences. -/
noncomputable def head (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ S ∈ P.powerset, (∏ p ∈ S, -b p) * f (t - ∑ p ∈ S, a p)

/-- The exact cofactor-square form of the finite covariance. -/
noncomputable def covariance (P : Finset ι) (a b w : ι → ℝ)
    (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ R ∈ P.powerset, (∏ p ∈ R, w p) *
    (head (P \ R) a b f (t - ∑ p ∈ R, a p))^2

omit [DecidableEq ι] in
@[simp] theorem head_empty (a b : ι → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    head ∅ a b f t = f t := by simp [head]

@[simp] theorem covariance_empty (a b w : ι → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    covariance ∅ a b w f t = (f t)^2 := by simp [covariance]

omit [DecidableEq ι] in
theorem head_shift (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ) (c t : ℝ) :
    head P a b (fun x => f (x-c)) t = head P a b f (t-c) := by
  unfold head
  apply sum_congr rfl
  intro S _
  dsimp only
  rw [show t-(∑ p ∈ S, a p)-c = t-c-(∑ p ∈ S, a p) by ring]

omit [DecidableEq ι] in
theorem head_difference (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ) (c d t : ℝ) :
    head P a b (fun x => f x-c*f (x-d)) t =
      head P a b f t-c*head P a b f (t-d) := by
  unfold head
  simp only [mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro S _
  rw [show t-(∑ p ∈ S, a p)-d = t-d-(∑ p ∈ S, a p) by ring]
  ring

theorem head_insert (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ)
    {p : ι} (hp : p ∉ P) (t : ℝ) :
    head (insert p P) a b f t = head P a b f t-b p*head P a b f (t-a p) := by
  unfold head
  rw [sum_powerset_insert hp, sub_eq_add_neg]
  congr 1
  rw [← neg_mul, mul_sum]
  apply sum_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h => hp ((mem_powerset.mp hS) h)
  rw [prod_insert hpS, sum_insert hpS]
  rw [show t-(a p+∑ q ∈ S, a q) = t-a p-(∑ q ∈ S, a q) by ring]
  ring

omit [DecidableEq ι] in
theorem continuous_head (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) : Continuous (head P a b f) := by
  apply continuous_finsetSum
  intro S _
  exact (hf.comp (continuous_id.sub continuous_const)).const_mul _

omit [DecidableEq ι] in
theorem head_zero_of_nonpos (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0) {t : ℝ} (ht : t ≤ 0) :
    head P a b f t = 0 := by
  apply sum_eq_zero
  intro S _
  have hsum : 0 ≤ ∑ p ∈ S, a p := sum_nonneg (fun p _ => ha p)
  rw [hz _ (by linarith), mul_zero]

theorem continuous_covariance (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) : Continuous (covariance P a b w f) := by
  apply continuous_finsetSum
  intro R _
  exact (((continuous_head (P \ R) a b f hf).comp
    (continuous_id.sub continuous_const)).pow 2).const_mul _

theorem covariance_insert (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    {p : ι} (hp : p ∉ P) (t : ℝ) :
    covariance (insert p P) a b w f t =
      covariance P a b w (fun x => f x-b p*f (x-a p)) t +
        w p*covariance P a b w (fun x => f (x-a p)) t := by
  unfold covariance
  rw [sum_powerset_insert hp, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro R hR
    have hpR : p ∉ R := fun h => hp ((mem_powerset.mp hR) h)
    have hpD : p ∉ P \ R := fun h => hp (mem_sdiff.mp h).1
    rw [insert_sdiff_of_notMem P hpR, head_insert _ _ _ _ hpD, head_difference]
  · apply sum_congr rfl
    intro R hR
    have hpR : p ∉ R := fun h => hp ((mem_powerset.mp hR) h)
    have hdiff : insert p P \ insert p R = P \ R := by
      ext x
      by_cases hx : x = p
      · subst x
        simp [hp]
      · simp [mem_sdiff, mem_insert, hx]
    rw [prod_insert hpR, sum_insert hpR, hdiff, head_shift]
    rw [show t-(a p+∑ q ∈ R, a q) = t-a p-(∑ q ∈ R, a q) by ring]
    ring_nf

theorem head_sq_le_covariance (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    (hw : ∀ p, 0 ≤ w p) (t : ℝ) :
    (head P a b f t)^2 ≤ covariance P a b w f t := by
  have h := single_le_sum
    (s := P.powerset)
    (f := fun R => (∏ p ∈ R, w p)*(head (P \ R) a b f (t-∑ p ∈ R, a p))^2)
    (fun R _ => mul_nonneg (prod_nonneg (fun p _ => hw p)) (sq_nonneg _))
    (mem_powerset.mpr (empty_subset P))
  simpa only [prod_empty, sum_empty, sdiff_empty, sub_zero, one_mul, covariance] using h

/-- The whole covariance is controlled by its mean head with the exact
finite product of causal prime-deletion costs. -/
theorem integral_covariance_le (P : Finset ι) (a b w : ι → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p < 1)
    (hw : ∀ p, 0 ≤ w p) (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ≤ 0, f t = 0) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, covariance P a b w f t) ≤
      (∏ p ∈ P, (1+w p/(1-b p)^2)) *
        (∫ t in (0 : ℝ)..T, (head P a b f t)^2) := by
  induction P using Finset.induction_on generalizing f with
  | empty => simp
  | @insert p P hp ih =>
    let g : ℝ → ℝ := fun t => f t-b p*f (t-a p)
    let s : ℝ → ℝ := fun t => f (t-a p)
    have hs : Continuous s := hf.comp (continuous_id.sub continuous_const)
    have hg : Continuous g := hf.sub (hs.const_mul (b p))
    have hsz : ∀ t ≤ 0, s t = 0 := fun t ht => hz _ (by linarith [ha p])
    have hgz : ∀ t ≤ 0, g t = 0 := by
      intro t ht
      dsimp [g]
      rw [hz t ht, hz _ (by linarith [ha p])]
      simp
    have hgIH := ih g hg hgz
    have hsIH := ih s hs hsz
    have hsplit : (∫ t in (0 : ℝ)..T, covariance (insert p P) a b w f t) =
        (∫ t in (0 : ℝ)..T, covariance P a b w g t) +
          w p*(∫ t in (0 : ℝ)..T, covariance P a b w s t) := by
      simp_rw [covariance_insert P a b w f hp]
      rw [intervalIntegral.integral_add
          ((continuous_covariance P a b w g hg).intervalIntegrable 0 T)
          (((continuous_covariance P a b w s hs).const_mul (w p)).intervalIntegrable 0 T),
        intervalIntegral.integral_const_mul]
    have hheadg : ∀ t, head P a b g t = head (insert p P) a b f t := by
      intro t
      rw [head_insert P a b f hp]
      exact head_difference P a b f (b p) (a p) t
    have hheads : ∀ t, head P a b s t = head P a b f (t-a p) :=
      fun t => head_shift P a b f (a p) t
    simp_rw [hheadg] at hgIH
    simp_rw [hheads] at hsIH
    have hF := continuous_head P a b f hf
    have hFz : ∀ t ≤ 0, head P a b f t = 0 :=
      fun _ ht => head_zero_of_nonpos P a b f ha hz ht
    have hdelay := shift_square_integral_le (head P a b f) hF hFz (ha p) hT
    have hrecover := delay_recovery_square (head P a b f) hF hFz
      (ha p) hT (hb0 p) (hb1 p).le
    have hrec : (∫ t in (0 : ℝ)..T, (head P a b f t)^2) ≤
        (∫ t in (0 : ℝ)..T, (head (insert p P) a b f t)^2)/(1-b p)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr (hb1 p)))).mpr
      simp_rw [head_insert P a b f hp]
      nlinarith [hrecover]
    have hprod : 0 ≤ ∏ q ∈ P, (1+w q/(1-b q)^2) :=
      prod_nonneg (fun q _ => add_nonneg zero_le_one (div_nonneg (hw q) (sq_nonneg _)))
    rw [hsplit, prod_insert hp]
    calc
      _ ≤ (∏ q ∈ P, (1+w q/(1-b q)^2))*
            (∫ t in (0 : ℝ)..T, (head (insert p P) a b f t)^2) +
          w p*((∏ q ∈ P, (1+w q/(1-b q)^2))*
            (∫ t in (0 : ℝ)..T, (head P a b f (t-a p))^2)) :=
        add_le_add hgIH (mul_le_mul_of_nonneg_left hsIH (hw p))
      _ ≤ (∏ q ∈ P, (1+w q/(1-b q)^2))*
            (∫ t in (0 : ℝ)..T, (head (insert p P) a b f t)^2) +
          w p*((∏ q ∈ P, (1+w q/(1-b q)^2))*
            ((∫ t in (0 : ℝ)..T, (head (insert p P) a b f t)^2)/(1-b p)^2)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hdelay.trans hrec) hprod) (hw p))
      _ = _ := by ring

theorem integral_head_sq_le_covariance (P : Finset ι) (a b w : ι → ℝ)
    (hw : ∀ p, 0 ≤ w p) (f : ℝ → ℝ) (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (head P a b f t)^2) ≤
      ∫ t in (0 : ℝ)..T, covariance P a b w f t := by
  exact intervalIntegral.integral_mono_on hT
    (((continuous_head P a b f hf).pow 2).intervalIntegrable 0 T)
    ((continuous_covariance P a b w f hf).intervalIntegrable 0 T)
    (fun t _ => head_sq_le_covariance P a b w f hw t)

end RHTower.RoutePWindow
