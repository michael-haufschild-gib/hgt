import GaloisForLFunctions.RHTower.ThmEUniformEnds
import GaloisForLFunctions.RHTower.DirichletFamilyEndEffects
import GaloisForLFunctions.RHTower.FamilyTaperBridge

/-!
# Odd characters as a bounded perturbation of even ones

The archimedean densities of odd and even characters of the same modulus differ by
`δ(τ) = μ_{1,q}(τ) − μ_{0,q}(τ) = μ_{1,1}(τ) − μ_{0,1}(τ)`, independent of `q` (`muq_one_eq_add`) and bounded
on `ℝ` (`exists_abs_parityShift_le`: both densities have the same Stirling main term).  The prime-side Gram
matrix is linear in the density, so for an odd character

`tr G̃²(μ_{1,q} + P) ≤ (1 + η) tr G̃²(μ_{0,q} + P) + (1 + 1/η) tr G̃²(δ)`        (`trGt2_odd_le`)

for every `η > 0`, and `tr G̃²(δ) ≤ M² T ∫Φ² + C L l log l · max(l, M)²` (`trGt2_parityShift_le`).  With
`η = 1/l` the perturbation costs a relative `O(1/l)` of the Frobenius main term `≍ T L l²`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- The parity shift `δ = μ_{1,1} − μ_{0,1}`. -/
def parityShift (τ : ℝ) : ℝ := muq 1 1 τ - muq 0 1 τ

theorem muq_one_eq_add (q : ℕ) (hq : 1 ≤ q) (τ : ℝ) :
    muq 1 q τ = muq 0 q τ + parityShift τ := by
  rw [muq_eq_muq_one_add 1 q hq, muq_eq_muq_one_add 0 q hq, parityShift]; ring

theorem continuous_parityShift : Continuous parityShift :=
  ((GammaChi.gammaFactsChi (κ := 1) (q := 1) le_rfl le_rfl).smooth.continuous).sub
    ((GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl).smooth.continuous)

/-- **The parity shift is bounded.** -/
theorem exists_abs_parityShift_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |parityShift τ| ≤ M := by
  obtain ⟨C₀, hC₀⟩ := (GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl).stirling
  obtain ⟨C₁, hC₁⟩ := (GammaChi.gammaFactsChi (κ := 1) (q := 1) le_rfl le_rfl).stirling
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_parityShift.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  refine ⟨max M₁ (|C₀| + |C₁|), le_max_of_le_right (by positivity), fun τ => ?_⟩
  rcases le_or_gt 1 |τ| with h1 | h1
  · have a := hC₀ τ h1
    have b := hC₁ τ h1
    have hτ2 : 1 ≤ τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    have hd0 : C₀ / τ ^ 2 ≤ |C₀| :=
      (div_le_div_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (div_le_self (abs_nonneg _) hτ2)
    have hd1 : C₁ / τ ^ 2 ≤ |C₁| :=
      (div_le_div_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (div_le_self (abs_nonneg _) hτ2)
    have e : parityShift τ = (muq 1 1 τ - (1 / (2 * π)) * Real.log ((1:ℕ) * |τ| / (2 * π)))
        - (muq 0 1 τ - (1 / (2 * π)) * Real.log ((1:ℕ) * |τ| / (2 * π))) := by
      unfold parityShift; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := le_max_right M₁ (|C₀| + |C₁|)
    linarith [b.trans hd1, a.trans hd0]
  · have := hM₁ τ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- `(a + b)² ≤ (1 + η) a² + (1 + 1/η) b²`. -/
theorem sq_add_le_eta (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  have h : 2 * a * b ≤ η * a ^ 2 + b ^ 2 / η := by
    have h1 : 0 ≤ (η * a - b) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    have e : (η * a - b) ^ 2 / η = η * a ^ 2 - 2 * a * b + b ^ 2 / η := by
      field_simp; ring
    linarith
  have e : (1 + 1 / η) * b ^ 2 = b ^ 2 + b ^ 2 / η := by ring
  nlinarith

/-- The squared Frobenius norm of the Gram matrix of a density. -/
def trGt2Nu (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) : ℝ :=
  (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2

theorem trGt2ChiA_eq (κ q : ℕ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) :
    trGt2ChiA κ q c p F = trGt2Nu (nuXc κ q c p.X) p F := rfl

/-- `|P_c(τ)| ≤ Σ_{n ≤ X} Λ(n)/√n`, for every coefficient sequence with `|c(n)| ≤ 1`. -/
theorem abs_PXc_le_sum {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) (X τ : ℝ) :
    |PXc c X τ| ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n := by
  unfold PXc
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hsum : |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    rw [norm_mul, norm_mul]
    have h1 : ‖((Λ n : ℝ) : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h2 : ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)‖ = 1 / Real.sqrt n := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      have hre : (-(1 / 2 : ℂ) - Complex.I * τ).re = -(1/2 : ℝ) := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    rw [h1, h2]
    calc Λ n * ‖c n‖ * (1 / Real.sqrt n) ≤ Λ n * 1 * (1 / Real.sqrt n) := by
          gcongr; exact hc n
      _ = Λ n / Real.sqrt n := by ring
  have hS0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n :=
    Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hπ : 1 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  calc 1 / π * |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ 1 * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n :=
        mul_le_mul hπ hsum (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Odd characters, perturbatively.** -/
theorem trGt2_odd_le :
    ∃ T₀ : ℝ, ∀ (q : ℕ), 1 ≤ q → ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ 1) → ∀ {cϱ : ℝ} (p : Setting)
      (F : LocalFun), T₀ ≤ p.T → LocalHypsCoreW cϱ p F → ∀ {η : ℝ}, 0 < η →
      trGt2ChiA 1 q c p F ≤ (1 + η) * trGt2ChiA 0 q c p F + (1 + 1 / η) * trGt2Nu parityShift p F := by
  obtain ⟨C₀, T₀, hC₀, hμ⟩ := muq_nuBound_uniform
  obtain ⟨M, hM0, hM⟩ := exists_abs_parityShift_le
  refine ⟨max T₀ 1, fun q hq c hc cϱ p F hT hF η hη => ?_⟩
  have hTμ : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  set S := ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) / Real.sqrt n with hS
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  -- the two densities
  have hu : Continuous (nuXc 0 q c p.X) :=
    ((GammaChi.gammaFactsChi (κ := 0) (by norm_num) hq).smooth.continuous).add
      (PXc_continuous c p.X_pos)
  have hνu : NuBound p ((C₀ + Real.log q) * p.l + S) (nuXc 0 q c p.X) := by
    intro τ
    have h1 := hμ 0 q (by norm_num) hq p hTμ τ
    have h2 := abs_PXc_le_sum hc p.X τ
    have h3 : |nuXc 0 q c p.X τ| ≤ |muq 0 q τ| + |PXc c p.X τ| := abs_add_le _ _
    linarith
  have hνδ : NuBound p M parityShift := nuBound_of_abs_le hM
  have hBu : 0 ≤ (C₀ + Real.log q) * p.l + S := by
    have : 0 ≤ (C₀ + Real.log q) * p.l := mul_nonneg (by linarith) (by linarith)
    linarith
  have hsplit : nuXc 1 q c p.X = nuXc 0 q c p.X + parityShift := by
    funext τ; simp only [nuXc, Pi.add_apply, muq_one_eq_add q hq τ]; ring
  have hG : ∀ k l : ℤ, GentryNu (nuXc 1 q c p.X) p F k l
      = GentryNu (nuXc 0 q c p.X) p F k l + GentryNu parityShift p F k l := by
    intro k l
    rw [hsplit]
    exact GentryNu_add hF hT1 hu continuous_parityShift hBu hM0 hνu hνδ k l
  rw [trGt2ChiA_eq, trGt2ChiA_eq]
  unfold trGt2Nu
  have hL2 : 0 ≤ (p.L)⁻¹ ^ 2 := by positivity
  calc (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (nuXc 1 q c p.X) p F k l ^ 2
      ≤ (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d,
          ((1 + η) * GentryNu (nuXc 0 q c p.X) p F k l ^ 2
            + (1 + 1 / η) * GentryNu parityShift p F k l ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hL2
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        rw [hG]
        exact sq_add_le_eta _ _ hη
    _ = (1 + η) * ((p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d,
          GentryNu (nuXc 0 q c p.X) p F k l ^ 2)
        + (1 + 1 / η) * ((p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d,
          GentryNu parityShift p F k l ^ 2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

/-- **The Frobenius norm of the parity shift is small.** -/
theorem trGt2_parityShift_le (cϱ lam : ℝ) :
    ∃ C T₀ M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l →
      trGt2Nu parityShift p F
        ≤ M ^ 2 * (p.T * ∫ x, F.Phi x ^ 2) + C * (p.L * p.l * Real.log p.l * (p.l + M) ^ 2) := by
  obtain ⟨C, T₀, hC⟩ := exists_abs_endForm_self_le cϱ lam
  obtain ⟨M, hM0, hM⟩ := exists_abs_parityShift_le
  refine ⟨|C|, max T₀ 1, M, abs_nonneg _, hM0, fun p F hp hT hF hL => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hνδ : NuBound p (p.l + M) parityShift := nuBound_of_abs_le fun τ => by
    linarith [hM τ]
  have he := hC p F (p.l + M) parityShift hp hT0 hF hL continuous_parityShift hνδ (by linarith)
  have hM2 : |Mform F.Phi p.T parityShift parityShift| ≤ M * M * (p.T * ∫ x, F.Phi x ^ 2) :=
    abs_Mform_le (by linarith) hF.Phi_contDiff.continuous continuous_parityShift
      continuous_parityShift hF.Phi_sq_integrable (fun τ _ => hM τ) (fun τ _ => hM τ)
  have e : trGt2Nu parityShift p F = Mform F.Phi p.T parityShift parityShift
      + endForm p F parityShift parityShift := by
    rw [endForm_self]; unfold trGt2Nu MtotalNu; ring
  rw [e]
  have h1 := (abs_le.mp hM2).2
  have h2 := (abs_le.mp he).2
  have h3 : C * (p.L * p.l * Real.log p.l * (p.l + M) ^ 2)
      ≤ |C| * (p.L * p.l * Real.log p.l * (p.l + M) ^ 2) := by
    apply mul_le_mul_of_nonneg_right (le_abs_self _)
    have := Real.log_nonneg hl1
    have := hF.L_pos
    positivity
  have e2 : M * M = M ^ 2 := by ring
  rw [e2] at h1
  linarith

end RHTower
