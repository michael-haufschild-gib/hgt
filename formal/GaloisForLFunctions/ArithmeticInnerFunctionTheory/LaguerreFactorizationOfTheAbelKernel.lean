import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ConformalDirichletGram
import GaloisForLFunctions.HTGeometry.HardyDiskSpace

/-! # Complete Laguerre factorization of the Abel kernel

Bounded Hardy data satisfy boundary Parseval by interior Gutzmer and dominated convergence.
For finite Dirichlet polynomials, their total Laguerre coefficient energy is therefore exactly
the Abel Gram form. Finite conformal projections converge in squared boundary norm.
-/

open Complex Metric Filter Topology MeasureTheory Set Finset
open scoped Real ComplexConjugate NNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory
open _root_.RHTower
noncomputable section


/-- Bounded radial means converge to the boundary mean; the exceptional point at one is null. -/
theorem IsHardyDisc.tendsto_radial_norm_sq_of_bounded {Φ : ℂ → ℂ} (h : IsHardyDisc Φ)
    {M : ℝ} (hb : ∀ z, ‖z‖ ≤ 1 → ‖Φ z‖ ≤ M) :
    Tendsto (fun r : ℝ => Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 r)
      (𝓝[<] 1) (𝓝 (Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1)) := by
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  simp only [Real.circleAverage_def]
  apply Tendsto.const_smul
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M ^ 2)
  · exact Eventually.of_forall fun r =>
      ((h.meas.comp (continuous_circleMap 0 r).measurable).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [hIoo] with r hr
    exact Eventually.of_forall fun θ _ => by
      have hn : ‖circleMap 0 r θ‖ ≤ 1 := by
        rw [norm_circleMap_zero, abs_of_pos hr.1]
        exact hr.2.le
      change ‖‖Φ (circleMap 0 r θ)‖ ^ 2‖ ≤ M ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _ hn) 2
  · exact intervalIntegrable_const
  · have hae : ∀ᵐ θ : ℝ, θ ≠ 2 * Real.pi := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with θ hθ hθI
    rw [uIoc_of_le Real.two_pi_pos.le] at hθI
    have hne : circleMap 0 1 θ ≠ 1 :=
      circleMap_zero_ne_one zero_le_one le_rfl ⟨hθI.1, lt_of_le_of_ne hθI.2 hθ⟩
    have hc := (h.diff.differentiableAt (isOpen_compl_singleton.mem_nhds hne)).continuousAt
    have hmap : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] 1) (𝓝 (circleMap 0 1 θ)) :=
      ((by fun_prop : Continuous (fun r : ℝ => circleMap 0 r θ)).tendsto 1).mono_left
        nhdsWithin_le_nhds
    exact ((hc.tendsto.comp hmap).norm).pow 2

/-- Boundary Parseval for bounded Hardy data. Interior Gutzmer gives the reverse Bessel bound. -/
theorem IsHardyDisc.hasSum_norm_sq_of_bounded {Φ : ℂ → ℂ} (h : IsHardyDisc Φ)
    {M : ℝ} (hb : ∀ z, ‖z‖ ≤ 1 → ‖Φ z‖ ≤ M) :
    HasSum (fun k => ‖taylorCoeff Φ k‖ ^ 2)
      (Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1) := by
  have hs : Summable (fun k => ‖taylorCoeff Φ k‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) h.sum_norm_sq_le
  have hle : ∑' k, ‖taylorCoeff Φ k‖ ^ 2 ≤
      Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 :=
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) h.sum_norm_sq_le
  have hcoeff (k : ℕ) : taylorCoeff Φ k = GaloisForLFunctions.HTGeometry.diskCoeff Φ k := by
    have ha : AnalyticAt ℂ Φ 0 :=
      h.diff.analyticAt (isOpen_compl_singleton.mem_nhds (by simp))
    exact _root_.HTGeometry.iterate_dslope_self_eq_iteratedDeriv_div_factorial ha k
  have hd : DifferentiableOn ℂ Φ (ball 0 1) := h.diff.mono fun z hz => by
    intro he
    have : z = 1 := he
    simp [this] at hz
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] 1,
      Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 r ≤ ∑' k, ‖taylorCoeff Φ k‖ ^ 2 := by
    filter_upwards [hIoo] with r hr
    have hg : HasSum (fun k => ‖taylorCoeff Φ k‖ ^ 2 * r ^ (2 * k))
        (Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 r) := by
      simpa only [hcoeff, Real.circleAverage_def, smul_eq_mul] using
        GaloisForLFunctions.HTGeometry.hasSum_circleAverage_normSq_diskCoeff hd hr.1.le hr.2
    rw [← hg.tsum_eq]
    exact Summable.tsum_le_tsum
      (fun k => mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr.1.le hr.2.le))
      hg.summable hs
  have hge := le_of_tendsto (h.tendsto_radial_norm_sq_of_bounded hb) hbound
  exact (le_antisymm hle hge) ▸ hs.hasSum


/-- The complete conformal coefficient energy of one logarithmic Dirichlet frequency. -/
theorem hasSum_dirichletDisc_energy {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k => ‖taylorCoeff (dirichletDisc t) k‖ ^ 2) (Real.exp (-t)) := by
  simpa only [circleAverage_norm_sq_dirichletDisc] using
    (isHardyDisc_dirichletDisc ht).hasSum_norm_sq_of_bounded
      (fun _ hz => norm_dirichletDisc_le_one ht hz)

/-- An exact series identity for the finite Laguerre jet polynomials. -/
theorem hasSum_laguerreJet_energy {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k => ‖Complex.exp (-(t : ℂ)) *
      (laguerreJetPoly t k).eval 1 / (k.factorial : ℂ)‖ ^ 2) (Real.exp (-t)) := by
  simpa only [taylorCoeff_dirichletDisc] using hasSum_dirichletDisc_energy ht

/-- The Abel kernel has a complete factorization through conformal Dirichlet coefficients. -/
theorem hasSum_dirichletGram (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    HasSum (fun k => ‖taylorCoeff (dirichletDiscPoly M b δ) k‖ ^ 2)
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ)) := by
  simpa only [circleAverage_norm_sq_dirichletDiscPoly] using
    (isHardyDisc_dirichletDiscPoly M b δ).hasSum_norm_sq_of_bounded
      (fun _ hz => norm_dirichletDiscPoly_le M b δ hz)

/-- Abel partial-sum squares and total squared Laguerre moments are the same energy. -/
theorem hasSum_laguerre_abel {M : ℕ} (hM : 1 ≤ M) (b : ℕ → ℝ) (δ : ℝ) :
    HasSum (fun k => ‖∑ m ∈ Finset.Icc 1 M,
      ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) *
        (Complex.exp (-(Real.log m : ℂ)) * (laguerreJetPoly (Real.log m) k).eval 1 /
          (k.factorial : ℂ))‖ ^ 2)
      ((∑ m ∈ Finset.Icc 1 M, b m * (m : ℝ) ^ (-δ)) ^ 2 / (M : ℝ) +
        ∑ j ∈ Finset.Icc 1 (M - 1),
          (((j : ℝ)⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) *
            (∑ m ∈ Finset.Icc 1 j, b m * (m : ℝ) ^ (-δ)) ^ 2)) := by
  have h := hasSum_dirichletGram M b δ
  rw [dirichletGram_eq_abel_squares hM] at h
  simpa only [taylorCoeff_dirichletDiscPoly] using h

/-- Conformal projections of a finite Dirichlet polynomial converge in squared boundary norm. -/
theorem dirichlet_projection_remainder_tendsto_zero (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    Tendsto (fun N : ℕ => Real.circleAverage (fun z =>
      ‖dirichletDiscPoly M b δ z -
        ∑ k ∈ Finset.range N, z ^ k * taylorCoeff (dirichletDiscPoly M b δ) k‖ ^ 2) 0 1)
      atTop (𝓝 0) := by
  simp_rw [dirichletGram_minus_conformal_squares]
  simpa only [sub_self] using (hasSum_dirichletGram M b δ).tendsto_sum_nat.const_sub
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ))

#print axioms hasSum_dirichletDisc_energy
#print axioms hasSum_laguerre_abel
#print axioms dirichlet_projection_remainder_tendsto_zero

#print axioms IsHardyDisc.hasSum_norm_sq_of_bounded
end
end GaloisForLFunctions.ArithmeticInnerFunctionTheory

