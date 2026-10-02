import GaloisForLFunctions.RHTower.ZetaChiDualCoherentCrossMean
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower


/-- The actual signed physical first-moment matrix of the literal coherent block. -/
def zetaChiDualCoherentFirstMomentKernel (s : ℂ) (m a q : ℕ) : ℂ :=
  ∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
    zetaChiDualCoherentCarrier s m t * bourgainOscillation (t * Real.log ((a : ℝ) / q))

private theorem norm_quadratic_form_sub_scalar_le
    (S : Finset ℕ) (c : ℕ → ℂ) (K : ℕ → ℕ → ℂ) (J : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hdiag : ∀ a ∈ S, K a a = J)
    (hoff : ∀ a ∈ S, ∀ q ∈ S, a ≠ q → ‖K a q‖ ≤ M) :
    ‖(∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * K a q) -
      (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) * J‖ ≤
      M * S.card * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  classical
  have hdiagSum : (∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * (if a = q then J else 0)) =
      (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) * J := by
    calc
      _ = ∑ a ∈ S, (c a * conj (c a)) * J := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [mul_ite, ha]
      _ = _ := by
        simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        rw [Finset.sum_mul]
  have heq : (∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * K a q) -
      (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) * J =
      ∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * (K a q - if a = q then J else 0) := by
    rw [← hdiagSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hentry (a : ℕ) (ha : a ∈ S) (q : ℕ) (hq : q ∈ S) :
      ‖K a q - if a = q then J else 0‖ ≤ M := by
    by_cases he : a = q
    · subst q
      rw [if_pos rfl, hdiag a ha, sub_self, norm_zero]
      exact hM
    · rw [if_neg he, sub_zero]
      exact hoff a ha q hq he
  have hcs : (∑ a ∈ S, ‖c a‖) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖c a‖)
  rw [heq]
  calc
    _ ≤ ∑ a ∈ S, ‖∑ q ∈ S, c a * conj (c q) * (K a q - if a = q then J else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, ∑ q ∈ S, ‖c a‖ * ‖c q‖ * M := by
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hentry a ha q hq) (by positivity)
    _ = M * (∑ a ∈ S, ‖c a‖) ^ 2 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ M * ((S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2) := mul_le_mul_of_nonneg_left hcs hM
    _ = _ := by ring

private theorem narrow_band_ratio {Q a q : ℕ} (hQ : 0 < Q)
    (ha : 100 * Q ≤ a ∧ a ≤ 101 * Q) (hq : 100 * Q ≤ q ∧ q ≤ 101 * Q) (hne : a ≠ q) :
    0 < q ∧ ¬ q ∣ a ∧ 49 / 50 ≤ (a : ℝ) / q ∧ (a : ℝ) / q ≤ 51 / 50 := by
  have hq0 : 0 < q := by omega
  have ha0 : 0 < a := by omega
  have hdiv : ¬ q ∣ a := by
    rintro ⟨k, hak⟩
    have hk0 : 0 < k := by nlinarith
    have hk2 : 2 ≤ k := by
      by_contra hk
      have he : k = 1 := by omega
      simp [he] at hak
      exact hne hak
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have haR : 100 * (Q : ℝ) ≤ a ∧ (a : ℝ) ≤ 101 * Q := by exact_mod_cast ha
  have hqR' : 100 * (Q : ℝ) ≤ q ∧ (q : ℝ) ≤ 101 * Q := by exact_mod_cast hq
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨hq0, hdiv, (le_div_iff₀ hqR).mpr ?_, (div_le_iff₀ hqR).mpr ?_⟩ <;> nlinarith

/-- A complete source-built narrow frequency family has a scalar first-moment
matrix up to a uniform quadratic-energy error. No target-error sign is asserted. -/
theorem exists_zetaChi_dual_coherent_moment_matrix_bound
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ Q : ℕ, 0 < Q → ∀ S : Finset ℕ,
      (∀ a ∈ S, 100 * Q ≤ a ∧ a ≤ 101 * Q) → ∀ c : ℕ → ℂ,
      ‖(∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * zetaChiDualCoherentFirstMomentKernel s m a q) -
        (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) *
          (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10), zetaChiDualCoherentCarrier s m t)‖ ≤
        C * (101 * (Q : ℝ) + (5 * (m : ℝ)) ^ 10 / m) * S.card * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaChi_dual_coherent_cross_mean_bound z hr hz0 hz1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs Q hQ S hS c
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  apply norm_quadratic_form_sub_scalar_le S c (zetaChiDualCoherentFirstMomentKernel s m) _ _
    (by positivity)
  · intro a ha
    have ha0 : 0 < a := by have := (hS a ha).1; omega
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
    simp [zetaChiDualCoherentFirstMomentKernel, div_self haR, bourgainOscillation]
  · intro a ha q hq hne
    obtain ⟨hq0, hdiv, hlo, hhi⟩ := narrow_band_ratio hQ (hS a ha) (hS q hq) hne
    have hbnd := hm s hs a q hq0 hdiv hlo hhi
    have hqbound : (q : ℝ) ≤ 101 * Q := by exact_mod_cast (hS q hq).2
    exact hbnd.trans (mul_le_mul_of_nonneg_left (add_le_add hqbound le_rfl) hC.le)

end RHTower
