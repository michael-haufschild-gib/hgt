import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseForwardRegularPart
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolePerron

/-!
# Ordinary summatory law for the actual forward coefficients

The pole at one contributes its actual residue. Exact Perron smoothing and
source subpower growth give square-root-plus-epsilon error without a sign or
size premise. This is the principal arithmetic mode, not additive cancellation.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSingularArithmetic

/-- The original full-positive source determines the forward mean with a
square-root-plus-epsilon error. Its density is the completion at one. -/
theorem exists_sharp_forward_sum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖(∑ n ∈ Finset.range (N + 1), sourceCoeff lam n) - sourceCompletion hW 1 * N‖ ≤
        C * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
  let b : ℕ → ℂ := fun n => sourceCoeff lam n
  let q : ℝ := min (ε / 4) (1 / 4)
  let a : ℝ := q / 2
  let c : ℝ := 1 / 2 + q
  have hq : 0 < q := by dsimp [q]; positivity
  have hq4 : q ≤ 1 / 4 := min_le_right _ _
  have hqε : q ≤ ε / 4 := min_le_left _ _
  have ha : 0 < a := by dsimp [a]; positivity
  have haq : a < q := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c]; linarith
  have hcr : c + q ≤ 1 / 2 + ε := by dsimp [c]; linarith
  obtain ⟨R, hRd, hRL, hRbound⟩ := exists_forward_regularPart hW
  obtain ⟨K, hK, hRb⟩ := hRbound q a hq ha
  let β : ℂ := sourceCompletion hW 1
  have hstrip : verticalStrip c 2 ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have := hs.1
    change 1 / 2 < s.re
    dsimp [c] at this
    linarith
  have hbd : ∀ s ∈ verticalStrip c 2, ‖R s‖ ≤ K * (2 + |s.im|) ^ a :=
    fun s hs => hRb s hs.1 hs.2
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ :=
    exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let B : ℝ := 2 * (K * 3 ^ a) / c + 2 * (K * 3 ^ a) * P * 2 ^ q / (q - a)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨B / (2 * Real.pi) + 2 * ‖β‖, by positivity, fun N => ?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [sourceCoeff, GaloisForLFunctions.HTGeometry.dirichletExp_zero]
    positivity
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNX : 1 ≤ (N : ℝ) + 1 := by linarith
  have hb0 : b 0 = 0 := by simp [b, sourceCoeff, dirichletExp_zero]
  have hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    have h := (sourceCoeff_LSeries hW (s := 2) (by norm_num)).1.norm
    refine h.congr fun n => ?_
    by_cases hn : n = 0
    · subst n; simp [b, sourceCoeff, dirichletExp_zero]
    · rw [LSeries.norm_term_eq, if_neg hn]
      simp [b, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hseries (s : ℂ) : (∑' n : ℕ, b n * (n : ℂ) ^ (-s)) = LSeries b s := by
    rw [LSeries]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def]
    split_ifs with hn
    · subst hn
      simp [hb0]
    · rw [Complex.cpow_neg, div_eq_mul_inv]
  have hperron := Sieve.tsum_mul_smoothWeight_eq_integral_summable hb0 hN0
    (by norm_num : (0 : ℝ) < 1 / 2) (σ := 2) (by norm_num) hsum
  norm_num only [Complex.ofReal_ofNat] at hperron
  simp_rw [hseries] at hperron
  rw [tsum_halfWidth_eq_sum] at hperron
  have hpole := integral_pole_mul_mellin_smoothWeight hN0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hint2 := integrable_mul_mellin_smoothWeight_line hN0
    (by norm_num : (0 : ℝ) < 1 / 2) hc (hRd.mono hstrip).continuousOn hK ha.le hbd hc2 le_rfl
  have hint := integrable_mul_mellin_smoothWeight_line hN0
    (by norm_num : (0 : ℝ) < 1 / 2) hc (hRd.mono hstrip).continuousOn hK ha.le hbd le_rfl hc2
  have hshift := integral_mul_mellin_smoothWeight_shift hN0
    (by norm_num : (0 : ℝ) < 1 / 2) hc hc2 (hRd.mono hstrip) hK ha.le hbd
  norm_num only [Complex.ofReal_ofNat] at hint2 hshift
  have hdecomp : (fun y : ℝ => LSeries b (2 + y * I) *
      mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) (2 + y * I)) =
      fun y : ℝ => β * ((1 / ((2 : ℂ) + y * I - 1)) *
        mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) (2 + y * I)) +
        R (2 + y * I) * mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) (2 + y * I) := by
    funext y
    rw [hRL _ (by simp)]
    change _ = _ + (LSeries b _ - β / _) * _
    ring
  rw [hdecomp, integral_add (hpole.1.const_mul β) hint2, integral_const_mul,
    hpole.2, hshift] at hperron
  have hfracN := hfrac N (1 / 2) c a q K hN0 (by norm_num) hc ha.le haq
    (by linarith : q ≤ 1) hK R (fun y => by
      simpa using hRb ((c : ℂ) + y * I) (by simp [c]) (by simpa using hc2)) hint
  have hX : ((N : ℝ) + 1 / 2) ^ c ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
    (Real.rpow_le_rpow (by positivity) (by linarith) hc.le).trans
      (Real.rpow_le_rpow_of_exponent_le hNX (by linarith))
  have hRX : (((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c ≤
      2 ^ q * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    calc
      _ ≤ (2 * ((N : ℝ) + 1)) ^ q * ((N : ℝ) + 1) ^ c :=
        mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hq.le)
          (Real.rpow_le_rpow (by positivity) (by linarith) hc.le) (by positivity) (by positivity)
      _ = 2 ^ q * ((N : ℝ) + 1) ^ (c + q) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), mul_assoc,
          ← Real.rpow_add (by positivity), add_comm q c]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNX hcr) (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hX (show 0 ≤ 2 * (K * 3 ^ a) / c by positivity)
  have htail := mul_le_mul_of_nonneg_left hRX
    (show 0 ≤ 2 * (K * 3 ^ a) * P / (q - a) by positivity)
  have hmass : (∫ y : ℝ, ‖R ((c : ℂ) + y * I) *
      mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) ((c : ℂ) + y * I)‖) ≤
        B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    refine hfracN.trans ?_
    convert add_le_add hmain htail using 1 <;> dsimp [B, P] <;> ring
  let J : ℂ := ∫ x in Ioi (1 : ℝ), (smoothWeight N (1 / 2) x : ℂ)
  have herr : (2 * Real.pi) * ‖(∑ n ∈ Finset.range (N + 1), b n) - β * J‖ ≤
      B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    rw [← abs_of_pos hpi, ← Real.norm_eq_abs, ← norm_smul, smul_sub, hperron]
    simpa [J, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      (norm_integral_le_integral_norm _).trans hmass
  have herr' : ‖(∑ n ∈ Finset.range (N + 1), b n) - β * J‖ ≤
      (B / (2 * Real.pi)) * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    simpa [mul_comm] using herr
  have hJ : ‖β * J - β * N‖ ≤ 2 * ‖β‖ := by
    rw [← mul_sub, norm_mul]
    simpa [J, mul_comm] using mul_le_mul_of_nonneg_left
      (norm_integral_halfWidth_sub_le hN1) (norm_nonneg β)
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
    Real.one_le_rpow hNX (by linarith)
  change ‖(∑ n ∈ Finset.range (N + 1), b n) - sourceCompletion hW 1 * N‖ ≤ _
  calc
    _ ≤ ‖(∑ n ∈ Finset.range (N + 1), b n) - β * J‖ + ‖β * J - β * N‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (B / (2 * Real.pi)) * ((N : ℝ) + 1) ^ (1 / 2 + ε) + 2 * ‖β‖ := add_le_add herr' hJ
    _ ≤ _ := by nlinarith [norm_nonneg β]
/-- Centering at the actual pole residue gives ordinary Dirichlet convergence
throughout the open critical half-plane. -/
theorem centered_forward_dirichletConvergesAt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DirichletConvergesAt (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) s := by
  let ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_sharp_forward_sum_le hW hε
  apply tendsto_dirichlet_partialSum_of_poly_bounded hC
    (show 0 ≤ 1 / 2 + ε by linarith) _
    (show 1 / 2 + ε < s.re by dsimp [ε]; linarith)
  intro N
  simpa [Finset.sum_range_succ', Finset.sum_sub_distrib, sourceCoeff,
    dirichletExp_zero, mul_comm] using hbound N

end RHTower.WeilWorkSettledPhase
