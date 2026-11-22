import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CharacterGrowth
import GaloisForLFunctions.MatomakiRadziwill.LFunctionThreeFourOne

/-! Local moment expansion for nonprincipal Dirichlet characters. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

lemma dhl_core {A : ℝ} (hA : 0 < A) (hCau : DHCauchyFor A) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 2 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, m ρ = analyticOrderNatAt f ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 6 * A * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          6 * A * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hXX : 2 ≤ X ^ 2 := by nlinarith
  have hB1 : 2 ≤ K * X ^ 2 := hXX.trans (le_mul_of_one_le_left (by positivity) hK)
  obtain ⟨Z, m, hZ, hm, horder, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hp : 0 ≤ A * ((Real.log K + 2) * Real.log X) :=
    mul_nonneg hA.le (mul_nonneg (add_nonneg (Real.log_nonneg hK) (by norm_num))
      (Real.log_nonneg (one_le_two.trans hX)))
  refine ⟨Z, m, ?_, hm, horder, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ((mul_le_mul_of_nonneg_left hlog hA.le).trans ?_)
    nlinarith only [hp]
  · intro k s hs hfs
    have hh := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    norm_num only [show (12 : ℝ) / (12 / 25) = 25 by norm_num] at hh
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc A * Real.log (K * X ^ 2) / (12 / 25)
        ≤ A * (2 * ((Real.log K + 2) * Real.log X)) / (12 / 25) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hA.le) (by norm_num)
      _ ≤ _ := by nlinarith only [hp]

lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := GaloisForLFunctions.MatomakiRadziwill.inv_le_norm_LFunction ψ
    (σ := 26 / 25) (by norm_num) t
  norm_num at h
  linarith only [h]

lemma dhl_X (M : ℕ) [NeZero M] (t : ℝ) : 2 ≤ (M : ℝ) * (|t| + 2) := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  exact (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2).trans
    (le_mul_of_one_le_left (by positivity) hM)

lemma dhl_nontriv {A : ℝ} (hA : 0 < A) (hCau : DHCauchyFor A) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) : DHLocalAt (6 * A * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, horder, hsum, hexp⟩ := dhl_core hA hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, horder, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end QH.PrimeProgressions
