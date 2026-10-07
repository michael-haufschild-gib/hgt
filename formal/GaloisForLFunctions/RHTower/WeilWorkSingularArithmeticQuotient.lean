import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticWeightedZeta
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellinMass

/-!
# Ordinary half-power cancellation for the literal zeta quotient

For every full-cone Weil-positive system, the coefficients of `ζ G` have
ordinary partial sums `O(N^(1/2+ε))`. The actual weighted zeta mass pays the
fractional Mellin integral; no coefficient-size or zero-free premise is added.
The bound is not asserted uniformly after arbitrary vertical twisting.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem exists_polynomial_zetaProduct_strip_bound {G Q : ℂ → ℂ} {c a K : ℝ}
    (hc : 1 / 2 < c) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (hQ : ContinuousOn Q {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, s ≠ 1 → Q s = riemannZeta s * G s)
    (hG : ∀ s ∈ verticalStrip c 2, ‖G s‖ ≤ K * (2 + |s.im|) ^ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ verticalStrip c 2,
      ‖Q s‖ ≤ D * (2 + |s.im|) ^ (2 : ℝ) := by
  let S : Set ℂ := (Icc c 2) ×ℂ (Icc (-2 : ℝ) 2)
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hSH : S ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    exact hc.trans_le (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hQ.mono hSH)
  let D : ℝ := max C 0 + 8 * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, fun s hs => ?_⟩
  have hS1 : 1 ≤ 2 + |s.im| := by have := abs_nonneg s.im; linarith
  rw [Real.rpow_two]
  rcases le_or_gt |s.im| 2 with ht | ht
  · have hmem : s ∈ S := Complex.mem_reProdIm.mpr ⟨hs, abs_le.mp ht⟩
    have hCD : C ≤ D := by dsimp [D]; have := le_max_left C 0; linarith
    exact ((hC s hmem).trans hCD).trans
      (by simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hS1 : 1 ≤ (2 + |s.im|) ^ 2) hD)
  · have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
    have hz := norm_riemannZeta_le_quarter
      (show 1 / 4 ≤ s.re by have := hs.1; linarith) ht.le
    have hz' : ‖riemannZeta s‖ ≤ 8 * (2 + |s.im|) := by linarith
    have hg' : ‖G s‖ ≤ K * (2 + |s.im|) := by
      refine (hG s hs).trans ?_
      simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS1 ha1) hK
    have hKD : 8 * K ≤ D := by dsimp [D]; have := le_max_right C 0; linarith
    calc
      _ = ‖riemannZeta s‖ * ‖G s‖ := by rw [hid s hs1, norm_mul]
      _ ≤ (8 * (2 + |s.im|)) * (K * (2 + |s.im|)) :=
        mul_le_mul hz' hg' (norm_nonneg _) (by positivity)
      _ = (8 * K) * (2 + |s.im|) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKD (by positivity)

private theorem integrable_norm_zetaProduct_mul_weight {G Q : ℂ → ℂ} {σ a q K : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (haq : a < q)
    (hQ : ContinuousOn Q {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, s ≠ 1 → Q s = riemannZeta s * G s)
    (hG : ∀ y : ℝ, ‖G ((σ : ℂ) + (y : ℂ) * I)‖ ≤ K * (2 + |y|) ^ a) :
    Integrable (fun y : ℝ =>
      ‖Q ((σ : ℂ) + (y : ℂ) * I)‖ * (2 + |y|) ^ (-1 - q)) := by
  have hz := integrable_norm_zeta_mul_weight hσ.le (by linarith : σ ≤ 3)
    (ne_of_lt hσ1) (show 0 < q - a by linarith)
  have hline : Continuous (fun y : ℝ => Q ((σ : ℂ) + (y : ℂ) * I)) :=
    hQ.comp_continuous (continuous_const.add (Complex.continuous_ofReal.mul_const I))
      fun y => by simpa using hσ
  have hcont : Continuous (fun y : ℝ =>
      ‖Q ((σ : ℂ) + (y : ℂ) * I)‖ * (2 + |y|) ^ (-1 - q)) :=
    hline.norm.mul ((continuous_const.add continuous_abs).rpow_const
      fun y => Or.inl (by
        change (2 : ℝ) + |y| ≠ 0
        positivity))
  refine (hz.const_mul K).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro y
  have hs1 : (σ : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, add_zero, Complex.one_re] at this
    linarith
  have hpow : (2 + |y|) ^ a * (2 + |y|) ^ (-1 - q) =
      (2 + |y|) ^ (-1 - (q - a)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hid _ hs1, norm_mul]
  calc
    _ ≤ (‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ * (K * (2 + |y|) ^ a)) *
        (2 + |y|) ^ (-1 - q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _))
        (by positivity)
    _ = K * (‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ *
        ((2 + |y|) ^ a * (2 + |y|) ^ (-1 - q))) := by ring
    _ = _ := by rw [hpow]

/-- Ordinary square-root cancellation for the actual quotient coefficients,
with every nontrivial input derived from full Weil positivity. -/
theorem exists_sharp_quotient_sum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.range (N + 1),
        LSeries.convolution 1 (producerMobius (fun n => if 2 ≤ n then lam n else 0)) n‖ ≤
          C * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  let b : ℕ → ℂ := LSeries.convolution 1 (producerMobius lam')
  have hb0 : b 0 = 0 := LSeries.convolution_map_zero _ _
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have h1 : lam' 1 = 0 := by simp [lam']
  have hA : DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  obtain ⟨Φ, hΦd, -, hΦid⟩ := hH.herglotz
  obtain ⟨κ, P, -, hPd, hGL⟩ := exists_reciprocalZeta_primitive hH h1 hA hΦd hΦid
  let G : ℂ → ℂ := fun s => κ * ((s - 1) * cexp (P s))
  let Q : ℂ → ℂ := fun s => κ * zetaEntire s * cexp (P s)
  have hGid : ∀ s : ℂ, 1 < s.re → G s = cexp (-LSeries (logZetaCoeff lam') s) := hGL
  have hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul κ).differentiableAt
      |>.differentiableWithinAt
  have hQd : DifferentiableOn ℂ Q {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    (((differentiable_zetaEntire s).const_mul κ).mul
      (hPd s hs).differentiableAt.cexp).differentiableWithinAt
  have hQG : ∀ s : ℂ, s ≠ 1 → Q s = riemannZeta s * G s := by
    intro s hs
    dsimp [Q, G]
    rw [zetaEntire_eq hs]
    ring
  let q : ℝ := min (ε / 4) (1 / 4)
  let a : ℝ := q / 2
  let c : ℝ := 1 / 2 + q
  have hq : 0 < q := by dsimp [q]; positivity
  have hq4 : q ≤ 1 / 4 := min_le_right _ _
  have hqε : q ≤ ε / 4 := min_le_left _ _
  have haq : a < q := by dsimp [a]; linarith
  have hc : 1 / 2 < c := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by linarith
  have hcr : c + q ≤ 1 / 2 + ε := by dsimp [c]; linarith
  have hstrip : verticalStrip c 2 ⊆ {s : ℂ | 1 / 2 < s.re} :=
    fun s hs => hc.trans_le hs.1
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  obtain ⟨Kb, hKb, hbd⟩ := exists_reciprocalZeta_strip_bound hH h1 hK hA hAK hq
    (by linarith : q < 1 / 2) (ε := a) (by dsimp [a]; positivity) hGd hGid
  have hGline : ∀ y : ℝ, ‖G ((c : ℂ) + (y : ℂ) * I)‖ ≤ Kb * (2 + |y|) ^ a := by
    intro y
    simpa using hbd ((c : ℂ) + (y : ℂ) * I) ⟨by simp [c], by simp; exact hc2⟩
  have hweighted := integrable_norm_zetaProduct_mul_weight hc hc1 haq hQd.continuousOn hQG hGline
  obtain ⟨D, hD, hQD⟩ := exists_polynomial_zetaProduct_strip_bound hc
    (by dsimp [a]; linarith : a ≤ 1) hKb hQd.continuousOn hQG hbd
  have hprod : ∀ N : ℕ, 0 < N → Integrable (fun y : ℝ =>
      Q ((c : ℂ) + (y : ℂ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℂ) * I)) := by
    intro N hN
    exact integrable_mul_mellin_smoothWeight_line (by exact_mod_cast hN) (by norm_num)
      hc0 (hQd.mono hstrip).continuousOn hD (by norm_num : (0 : ℝ) ≤ 2) hQD le_rfl hc2
  obtain ⟨Cm, hCm, hmass⟩ := exists_mellin_halfWidth_mass_le hc0 hq.le
    (by linarith : q ≤ 1) hweighted hprod
  have hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    have h : LSeriesSummable b 2 := (LSeriesSummable_one_iff.mpr (by norm_num)).convolution
      (LSeries_producerMobius hH.summable (s := 2) (by norm_num)).1
    refine h.norm.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · subst hn
      rw [hb0, norm_zero, zero_mul]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
      norm_num
  have hseries : ∀ s : ℂ, 1 < s.re → (∑' n : ℕ, b n * (n : ℂ) ^ (-s)) = Q s := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
    have heq : (∑' n : ℕ, b n * (n : ℂ) ^ (-s)) = LSeries b s := by
      unfold LSeries
      apply tsum_congr
      intro n
      rw [LSeries.term_def]
      split_ifs with hn
      · subst hn
        rw [hb0, zero_mul]
      · rw [Complex.cpow_neg, div_eq_mul_inv]
    rw [heq, hQG s hs1, hGid s hs]
    exact (LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
      (LSeries_producerMobius hH.summable hs).1).trans
        (by rw [LSeries_one_eq_riemannZeta hs, (LSeries_producerMobius hH.summable hs).2])
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨Cm / (2 * Real.pi), div_nonneg hCm hpi.le, fun N => ?_⟩
  change ‖∑ n ∈ Finset.range (N + 1), b n‖ ≤ _
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [hb0, div_nonneg hCm hpi.le]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hperron := Sieve.tsum_mul_smoothWeight_eq_integral_summable hb0 hN0
    (by norm_num : (0 : ℝ) < 1 / 2) (σ := 2) (by norm_num) hsum
  norm_num only [Complex.ofReal_ofNat] at hperron
  have heq : (fun y : ℝ => (∑' n : ℕ, b n * (n : ℂ) ^ (-((2 : ℂ) + y * I))) *
      mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ)) (2 + y * I)) =
      fun y : ℝ => Q (2 + y * I) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ)) (2 + y * I) := by
    funext y
    rw [hseries _ (by simp)]
  rw [heq] at hperron
  have hshift := integral_mul_mellin_smoothWeight_shift hN0
    (by norm_num : (0 : ℝ) < 1 / 2) hc0 hc2 (hQd.mono hstrip) hD
      (by norm_num : (0 : ℝ) ≤ 2) hQD
  norm_num only [Complex.ofReal_ofNat] at hshift
  rw [hshift] at hperron
  have hnorm : (2 * Real.pi) * ‖∑ n ∈ Finset.range (N + 1), b n‖ ≤
      Cm * ((N : ℝ) + 1) ^ (c + q) := by
    rw [← tsum_halfWidth_eq_sum, ← abs_of_pos hpi, ← Real.norm_eq_abs, ← norm_smul, hperron]
    exact (norm_integral_le_integral_norm _).trans (hmass N hN)
  have hpower : ((N : ℝ) + 1) ^ (c + q) ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hcr
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  have hnorm' : ‖∑ n ∈ Finset.range (N + 1), b n‖ * (2 * Real.pi) ≤
      Cm * ((N : ℝ) + 1) ^ (c + q) := by simpa only [mul_comm] using hnorm
  exact hnorm'.trans (mul_le_mul_of_nonneg_left hpower hCm)

/-- The actual quotient coefficients have ordinary Dirichlet convergence
throughout `Re s > 1/2`; absolute or uniform convergence is not asserted. -/
theorem quotient_dirichletConvergesAt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DirichletConvergesAt (fun n =>
      LSeries.convolution 1 (producerMobius (fun n => if 2 ≤ n then lam n else 0)) (n + 1)) s := by
  let ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_sharp_quotient_sum_le hW hε
  apply tendsto_dirichlet_partialSum_of_poly_bounded hC
    (show 0 ≤ 1 / 2 + ε by linarith) _ (show 1 / 2 + ε < s.re by dsimp [ε]; linarith)
  intro N
  simpa only [Finset.sum_range_succ', LSeries.convolution_map_zero, add_zero] using hbound N

end RHTower.WeilSingularArithmetic
