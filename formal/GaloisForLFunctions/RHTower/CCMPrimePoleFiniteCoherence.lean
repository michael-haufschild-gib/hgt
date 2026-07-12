import GaloisForLFunctions.RHTower.CCMPrimePoleDiophantineCoherence
import Mathlib.NumberTheory.WellApproximable

/-!
# Finite-place common coherence for CCM prime-pole vectors

Compact recurrence on a finite unit torus supplies one integer clock and a
simultaneous integer approximation at every local scale.  Combined with the
exact CCM Cauchy covariance law, this produces a common coherent unit direction
for every finite family of local-factor Hardy pole spaces, with an explicit
scale-sensitive squared-distance bound.

This is a positive carrier theorem: finite semilocal CCM systems necessarily
possess arbitrarily coherent cross-place pole vectors.
-/

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

noncomputable section

namespace RHTower

theorem exists_fin_unitAddCircle_nsmul_norm_le
    {d : ℕ} (ξ : Fin d → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ‖n • ξ‖ ≤ δ := by
  let μ : Measure (Fin d → UnitAddCircle) := volume
  let B : Set (Fin d → UnitAddCircle) := closedBall 0 (δ / 2)
  have hrad : 0 < δ / 2 := by positivity
  have hopenpos : 0 < μ (ball 0 (δ / 2)) :=
    isOpen_ball.measure_pos μ (nonempty_ball.mpr hrad)
  have hBpos : 0 < μ B :=
    hopenpos.trans_le (measure_mono ball_subset_closedBall)
  have hBne : μ B ≠ 0 := ne_of_gt hBpos
  have htop : μ univ ≠ ∞ := measure_ne_top μ univ
  obtain ⟨N, hNmass⟩ := ENNReal.exists_nat_mul_gt hBne htop
  have hNpos : 0 < N := by
    by_contra hN
    simp only [Nat.not_lt, Nat.le_zero] at hN
    subst N
    simp at hNmass
  have hbound : μ univ ≤ (N + 1) • μ B := by
    calc
      μ univ ≤ N * μ B := hNmass.le
      _ ≤ (N + 1) * μ B := by
        gcongr
        exact_mod_cast Nat.le_succ N
      _ = (N + 1) • μ B := by simp [nsmul_eq_mul]
  obtain ⟨n, hn, hnorm⟩ :=
    NormedAddCommGroup.exists_norm_nsmul_le (μ := μ) ξ hNpos δ hbound
  exact ⟨n, hn.1, hnorm⟩

/-- Finite-torus recurrence can be forced beyond every prescribed index. -/
theorem exists_fin_unitAddCircle_nsmul_norm_le_of_lt
    {d : ℕ} (ξ : Fin d → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ‖n • ξ‖ ≤ δ := by
  have hscale : (0 : ℝ) < (B + 1 : ℕ) := by positivity
  obtain ⟨k, hk, hnorm⟩ :=
    exists_fin_unitAddCircle_nsmul_norm_le ξ (div_pos hδ hscale)
  refine ⟨k * (B + 1), ?_, ?_⟩
  · have hk1 : 1 ≤ k := hk
    nlinarith
  · rw [mul_nsmul]
    calc
      ‖(B + 1) • k • ξ‖ ≤ (B + 1 : ℕ) * ‖k • ξ‖ := norm_nsmul_le
      _ ≤ (B + 1 : ℕ) * (δ / (B + 1 : ℕ)) := by
        gcongr
      _ = δ := by
        field_simp

theorem exists_fin_simultaneous_integer_approximation
    {d : ℕ} (α : Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ δ := by
  let ξ : Fin d → UnitAddCircle := fun i => (α i : UnitAddCircle)
  obtain ⟨n, hn, hnorm⟩ := exists_fin_unitAddCircle_nsmul_norm_le ξ hδ
  refine ⟨n, hn, fun i => round ((n : ℝ) * α i), ?_⟩
  intro i
  have hi : ‖(n • ξ) i‖ ≤ δ := (norm_le_pi_norm (n • ξ) i).trans hnorm
  simp only [ξ, Pi.smul_apply] at hi
  rw [← AddCircle.coe_nsmul, UnitAddCircle.norm_eq] at hi
  simpa only [nsmul_eq_mul] using hi

/-- Simultaneous integer approximation with an arbitrarily large common
denominator. -/
theorem exists_fin_simultaneous_integer_approximation_of_lt
    {d : ℕ} (α : Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ δ := by
  let ξ : Fin d → UnitAddCircle := fun i => (α i : UnitAddCircle)
  obtain ⟨n, hn, hnorm⟩ := exists_fin_unitAddCircle_nsmul_norm_le_of_lt ξ hδ B
  refine ⟨n, hn, fun i => round ((n : ℝ) * α i), ?_⟩
  intro i
  have hi : ‖(n • ξ) i‖ ≤ δ := (norm_le_pi_norm (n • ξ) i).trans hnorm
  simp only [ξ, Pi.smul_apply] at hi
  rw [← AddCircle.coe_nsmul, UnitAddCircle.norm_eq] at hi
  simpa only [nsmul_eq_mul] using hi

theorem exists_fin_ccmPrimePole_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (L i) (hL i) (r i) -
          ccmNormalizedPrimePoleVector Lref href n‖ ^ 2 ≤
        2 * (2 * Real.pi * (δ / L i)) ^ 2 := by
  obtain ⟨n, hn, r, happrox⟩ :=
    exists_fin_simultaneous_integer_approximation (fun i => L i / Lref) hδ
  refine ⟨n, hn, r, ?_⟩
  intro i
  apply (norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect
    href (hL i) n (r i)).trans
  have hgap :
      |(r i : ℝ) / L i - (n : ℝ) / Lref| ≤ δ / L i := by
    have heq :
        (r i : ℝ) / L i - (n : ℝ) / Lref =
          -(((n : ℝ) * (L i / Lref) - r i) / L i) := by
      field_simp [href.ne', (hL i).ne']
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos (hL i)]
    exact div_le_div_of_nonneg_right (happrox i) (hL i).le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscaled :
      |2 * Real.pi * ((r i : ℝ) / L i - (n : ℝ) / Lref)| ≤
        2 * Real.pi * (δ / L i) := by
    rw [abs_mul, abs_of_nonneg hpi]
    exact mul_le_mul_of_nonneg_left hgap hpi
  have hright : 0 ≤ 2 * Real.pi * (δ / L i) :=
    mul_nonneg hpi (div_nonneg hδ.le (hL i).le)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hscaled
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- Cofinal finite-place coherence: the common reference pole index can be
forced beyond any prescribed bound without weakening the defect estimate. -/
theorem exists_fin_ccmPrimePole_cofinal_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (L i) (hL i) (r i) -
          ccmNormalizedPrimePoleVector Lref href n‖ ^ 2 ≤
        2 * (2 * Real.pi * (δ / L i)) ^ 2 := by
  obtain ⟨n, hn, r, happrox⟩ :=
    exists_fin_simultaneous_integer_approximation_of_lt
      (fun i => L i / Lref) hδ B
  refine ⟨n, hn, r, ?_⟩
  intro i
  apply (norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect
    href (hL i) n (r i)).trans
  have hgap :
      |(r i : ℝ) / L i - (n : ℝ) / Lref| ≤ δ / L i := by
    have heq :
        (r i : ℝ) / L i - (n : ℝ) / Lref =
          -(((n : ℝ) * (L i / Lref) - r i) / L i) := by
      field_simp [href.ne', (hL i).ne']
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos (hL i)]
    exact div_le_div_of_nonneg_right (happrox i) (hL i).le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscaled :
      |2 * Real.pi * ((r i : ℝ) / L i - (n : ℝ) / Lref)| ≤
        2 * Real.pi * (δ / L i) := by
    rw [abs_mul, abs_of_nonneg hpi]
    exact mul_le_mul_of_nonneg_left hgap hpi
  have hright : 0 ≤ 2 * Real.pi * (δ / L i) :=
    mul_nonneg hpi (div_nonneg hδ.le (hL i).le)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hscaled
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- Prime specialization of finite common coherence.  Every finite family of
prime local factors has arbitrarily coherent normalized CCM pole vectors with
the displayed logarithmic scale loss. -/
theorem exists_fin_prime_ccmPrimePole_common_coherence
    {d pref : ℕ} (hpref : pref.Prime)
    (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (Real.log (p i))
          (Real.log_pos (by exact_mod_cast (hp i).one_lt)) (r i) -
        ccmNormalizedPrimePoleVector (Real.log pref)
          (Real.log_pos (by exact_mod_cast hpref.one_lt)) n‖ ^ 2 ≤
      2 * (2 * Real.pi * (δ / Real.log (p i))) ^ 2 := by
  exact exists_fin_ccmPrimePole_common_coherence
    (Real.log_pos (by exact_mod_cast hpref.one_lt))
    (fun i => Real.log (p i))
    (fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)) hδ

end RHTower
