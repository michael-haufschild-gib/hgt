import GaloisForLFunctions.RHTower.RoutePFinitePrimeCovariance

/-! # Exact finite-window stability under primes beyond the horizon -/

open Finset

namespace RHTower.RoutePWindow

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem head_congr_below (P : Finset ι) (a b : ι → ℝ) (f g : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) {t : ℝ} (he : ∀ x ≤ t, f x = g x) :
    head P a b f t = head P a b g t := by
  apply sum_congr rfl
  intro S _
  rw [he _ (sub_le_self _ (sum_nonneg (fun p _ => ha p)))]

theorem covariance_congr_below (P : Finset ι) (a b w : ι → ℝ) (f g : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) {t : ℝ} (he : ∀ x ≤ t, f x = g x) :
    covariance P a b w f t = covariance P a b w g t := by
  apply sum_congr rfl
  intro R _
  rw [head_congr_below (P \ R) a b f g ha (fun x hx =>
    he x (hx.trans (sub_le_self _ (sum_nonneg (fun p _ => ha p)))))]

theorem covariance_zero_of_nonpos (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0) {t : ℝ} (ht : t ≤ 0) :
    covariance P a b w f t = 0 := by
  apply sum_eq_zero
  intro R _
  rw [head_zero_of_nonpos (P \ R) a b f ha hz
    ((sub_le_self _ (sum_nonneg (fun p _ => ha p))).trans ht)]
  simp

theorem covariance_shift (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ) (c t : ℝ) :
    covariance P a b w (fun x => f (x-c)) t = covariance P a b w f (t-c) := by
  apply sum_congr rfl
  intro R _
  rw [head_shift]
  rw [show t-(∑ p ∈ R, a p)-c = t-c-(∑ p ∈ R, a p) by ring]

theorem head_insert_beyond (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0)
    {p : ι} (hp : p ∉ P) {t : ℝ} (htp : t ≤ a p) :
    head (insert p P) a b f t = head P a b f t := by
  rw [head_insert P a b f hp,
    head_zero_of_nonpos P a b f ha hz (sub_nonpos.mpr htp)]
  simp

theorem covariance_insert_beyond (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0)
    {p : ι} (hp : p ∉ P) {t : ℝ} (htp : t ≤ a p) :
    covariance (insert p P) a b w f t = covariance P a b w f t := by
  rw [covariance_insert P a b w f hp, covariance_shift,
    covariance_zero_of_nonpos P a b w f ha hz (sub_nonpos.mpr htp)]
  simp only [mul_zero, add_zero]
  apply covariance_congr_below P a b w _ f ha
  intro x hx
  rw [hz (x-a p) (by linarith)]
  simp

/-- A larger prime core agrees at the original clock whenever every added
prime has delay at least that clock. No limiting argument occurs. -/
theorem head_eq_of_extra_beyond (P Q : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0) (hPQ : P ⊆ Q)
    {t : ℝ} (hextra : ∀ p ∈ Q, p ∉ P → t ≤ a p) :
    head Q a b f t = head P a b f t := by
  have hu (R : Finset ι) (hR : ∀ p ∈ R, p ∉ P → t ≤ a p) :
      head (P ∪ R) a b f t = head P a b f t := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert p R hp ih =>
      have hi := ih (fun q hq hn => hR q (mem_insert_of_mem hq) hn)
      rw [union_insert]
      by_cases hpm : p ∈ P ∪ R
      · rw [insert_eq_of_mem hpm, hi]
      · rw [head_insert_beyond (P ∪ R) a b f ha hz hpm
          (hR p (mem_insert_self p R) (fun h => hpm (mem_union_left R h))), hi]
  simpa only [union_eq_right.mpr hPQ] using hu Q hextra

theorem covariance_eq_of_extra_beyond (P Q : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hz : ∀ t ≤ 0, f t = 0) (hPQ : P ⊆ Q)
    {t : ℝ} (hextra : ∀ p ∈ Q, p ∉ P → t ≤ a p) :
    covariance Q a b w f t = covariance P a b w f t := by
  have hu (R : Finset ι) (hR : ∀ p ∈ R, p ∉ P → t ≤ a p) :
      covariance (P ∪ R) a b w f t = covariance P a b w f t := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert p R hp ih =>
      have hi := ih (fun q hq hn => hR q (mem_insert_of_mem hq) hn)
      rw [union_insert]
      by_cases hpm : p ∈ P ∪ R
      · rw [insert_eq_of_mem hpm, hi]
      · rw [covariance_insert_beyond (P ∪ R) a b w f ha hz hpm
          (hR p (mem_insert_self p R) (fun h => hpm (mem_union_left R h))), hi]
  simpa only [union_eq_right.mpr hPQ] using hu Q hextra

end RHTower.RoutePWindow
