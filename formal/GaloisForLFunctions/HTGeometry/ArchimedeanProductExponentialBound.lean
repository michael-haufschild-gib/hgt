import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit
import GaloisForLFunctions.HTGeometry.ArchimedeanMonomialValuation

/-!
# The archimedean product is exponentially small, with a rate

Multiplying the per-factor bounds gives one polynomial-times-exponential bound for the whole
product; the exponential gauge has constant modulus on the line and only changes the constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **A quantitative bound for the archimedean product on a vertical line.** -/
theorem exists_exponential_bound_archimedeanProduct {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ)
    (hlam : ∀ j, 0 < lam j) {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ) (hd : 0 < d) :
    ∃ (C δ : ℝ) (N : ℕ), 0 ≤ C ∧ 0 < δ ∧ ∀ᶠ t : ℝ in atTop,
      ‖archimedeanProductLine lam μ α σ t‖ ≤ C * t ^ N * Real.exp (-(δ * t)) := by
  classical
  choose Cf δf Nf hC0 hδ0 hbound using fun j : Fin d =>
    exists_exponential_bound_gammaScale (hlam j) (hσ j)
  refine ⟨Real.exp (α * σ) * ∏ j, Cf j, ∑ j, δf j, ∑ j, Nf j,
    mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun j _ => hC0 j), ?_, ?_⟩
  · refine Finset.sum_pos (fun j _ => hδ0 j) ?_
    exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ), Filter.eventually_all.mpr hbound] with t ht hall
    have hexp : ‖Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ = Real.exp (α * σ) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [archimedeanProductLine, norm_mul, hexp, norm_prod]
    have hstep : ∏ j : Fin d,
        ‖Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)‖
        ≤ ∏ j : Fin d, (Cf j * t ^ Nf j * Real.exp (-(δf j * t))) :=
      Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hall j)
    have hrhs : ∏ j : Fin d, (Cf j * t ^ Nf j * Real.exp (-(δf j * t)))
        = (∏ j, Cf j) * t ^ (∑ j, Nf j) * Real.exp (-((∑ j, δf j) * t)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        ← Real.exp_sum]
      congr 2
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [hrhs] at hstep
    have hnn : (0 : ℝ) ≤ Real.exp (α * σ) := Real.exp_nonneg _
    calc Real.exp (α * σ) * ∏ j : Fin d,
          ‖Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)‖
        ≤ Real.exp (α * σ)
            * ((∏ j, Cf j) * t ^ (∑ j, Nf j) * Real.exp (-((∑ j, δf j) * t))) :=
          mul_le_mul_of_nonneg_left hstep hnn
      _ = Real.exp (α * σ) * (∏ j, Cf j) * t ^ (∑ j, Nf j)
            * Real.exp (-((∑ j, δf j) * t)) := by ring

/-- **A positive power of the archimedean product kills polynomial growth.**  This is the
exponential separation of distinct `G`-powers that the monomial valuation law rests on. -/
theorem tendsto_polyGrowth_mul_archimedeanProduct_pow_zero {d : ℕ} (lam : Fin d → ℝ)
    (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ)
    (hd : 0 < d) {f : ℝ → ℂ} {Cf : ℝ} (hCf0 : 0 ≤ Cf) {m : ℕ}
    (hf : ∀ᶠ t : ℝ in atTop, ‖f t‖ ≤ Cf * t ^ m)
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => f t * (archimedeanProductLine lam μ α σ t) ^ k) atTop (nhds 0) := by
  obtain ⟨C, δ, N, hC0, hδ0, hb⟩ :=
    exists_exponential_bound_archimedeanProduct lam μ hlam hσ α hd
  refine tendsto_zero_of_eventually_norm_le_polyExp (C := Cf * C ^ k) (N := m + k * N)
    (δ := (k : ℝ) * δ) (by positivity) ?_
  filter_upwards [hf, hb, eventually_ge_atTop (0 : ℝ)] with t hft hbt ht
  have hGk : ‖archimedeanProductLine lam μ α σ t‖ ^ k
      ≤ (C * t ^ N * Real.exp (-(δ * t))) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hbt k
  have hrhs : (C * t ^ N * Real.exp (-(δ * t))) ^ k
      = C ^ k * t ^ (k * N) * Real.exp (-((k : ℝ) * δ * t)) := by
    have hexpk : (Real.exp (-(δ * t))) ^ k = Real.exp (-((k : ℝ) * δ * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, mul_pow, ← pow_mul, hexpk]
    rw [mul_comm N k]
  rw [hrhs] at hGk
  rw [norm_mul, norm_pow]
  have hnn : (0 : ℝ) ≤ ‖archimedeanProductLine lam μ α σ t‖ ^ k := by positivity
  have hnn2 : (0 : ℝ) ≤ C ^ k * t ^ (k * N) * Real.exp (-((k : ℝ) * δ * t)) := by positivity
  calc ‖f t‖ * ‖archimedeanProductLine lam μ α σ t‖ ^ k
      ≤ (Cf * t ^ m) * (C ^ k * t ^ (k * N) * Real.exp (-((k : ℝ) * δ * t))) :=
        mul_le_mul hft hGk hnn (mul_nonneg hCf0 (pow_nonneg ht m))
    _ = Cf * C ^ k * t ^ (m + k * N) * Real.exp (-((k : ℝ) * δ * t)) := by
        rw [pow_add]
        ring

end

end GaloisForLFunctions.HTGeometry
