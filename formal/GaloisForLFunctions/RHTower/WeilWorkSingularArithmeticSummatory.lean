import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolePerron
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.WeilOneSidedConvergenceRigidity

/-!
# A sharp summatory law for every full Weil-positive source

For each positive epsilon, the original signed coefficients have summatory
function `N + O(N^(1/2+epsilon))`. The pole supplies the main term; the
holomorphic remainder has logarithmic vertical growth. Smoothing within one
integer gap loses no coefficient and requires no sign or size premise.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem regularPart_power_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    ∃ (R : ℂ → ℂ) (K : ℝ), 0 ≤ K ∧
      DifferentiableOn ℂ R {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → R s =
        LSeries (fun n => ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) s - 1 / (s - 1)) ∧
      ∀ s : ℂ, 1 / 2 + q ≤ s.re → ‖R s‖ ≤ K * (2 + |s.im|) ^ a := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  obtain ⟨Φ, hΦd, hΦre, hΦid⟩ := hH.herglotz
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  let L : ℝ := ∑' n : ℕ, |lam' n| / (n : ℝ) ^ (2 : ℝ)
  let B : ℝ := 2 * (6 * (K + 1 + L)) / (2 * q)
  have hL : 0 ≤ L := tsum_nonneg fun _ => by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨fun s => zetaArchimedeanDatum s - Φ s,
    B * (2 ^ a / a) + (L + 1), by positivity, ?_, ?_, ?_⟩
  · exact (differentiableOn_zetaArchimedeanDatum.mono
      (fun s (hs : 1 / 2 < s.re) => show 0 < s.re by linarith)).sub hΦd
  · intro s hs
    change zetaArchimedeanDatum s - Φ s = _
    rw [hΦid s hs]
    ring
  · intro s hs
    have hb := norm_regularPart_le_of_re_ge hK hH.summable hΦd hΦre hΦid hAK
      (show 0 < 2 * q by positivity) (w := s) (by linarith)
    change ‖zetaArchimedeanDatum s - Φ s‖ ≤ B * Real.log (|s.im| + 3) + L + 1 at hb
    have hl : Real.log (|s.im| + 3) ≤ (2 ^ a / a) * (2 + |s.im|) ^ a := by
      calc
        _ ≤ (|s.im| + 3) ^ a / a := Real.log_le_rpow_div (by positivity) ha
        _ ≤ (2 * (2 + |s.im|)) ^ a / a :=
          div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) ha.le) ha.le
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    have hp : 1 ≤ (2 + |s.im|) ^ a :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) ha.le
    calc
      _ ≤ B * Real.log (|s.im| + 3) + L + 1 := hb
      _ ≤ B * ((2 ^ a / a) * (2 + |s.im|) ^ a) + (L + 1) * (2 + |s.im|) ^ a := by
        nlinarith [mul_le_mul_of_nonneg_left hl hB,
          mul_le_mul_of_nonneg_left hp (show 0 ≤ L + 1 by positivity)]
      _ = _ := by ring

/-- Full positivity alone forces square-root, up to epsilon, summatory error
for the original signed source coefficients. -/
theorem exists_sharp_source_sum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖(∑ n ∈ Finset.range (N + 1), ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) - N‖ ≤
        C * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
  let b : ℕ → ℂ := fun n => ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)
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
  obtain ⟨R, K, hK, hRd, hRL, hRb⟩ := regularPart_power_bound hW hq ha
  have hstrip : verticalStrip c 2 ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have := hs.1
    change 1 / 2 < s.re
    dsimp [c] at this
    linarith
  have hbd : ∀ s ∈ verticalStrip c 2, ‖R s‖ ≤ K * (2 + |s.im|) ^ a :=
    fun s hs => hRb s hs.1
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ :=
    exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let B : ℝ := 2 * (K * 3 ^ a) / c + 2 * (K * 3 ^ a) * P * 2 ^ q / (q - a)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨B / (2 * Real.pi) + 2, by positivity, fun N => ?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
    positivity
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNX : 1 ≤ (N : ℝ) + 1 := by linarith
  have hb0 : b 0 = 0 := by simp [b]
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    refine (hH.summable 2 (by norm_num)).congr fun n => ?_
    simp only [b, Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
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
      fun y : ℝ => (1 / ((2 : ℂ) + y * I - 1)) *
        mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) (2 + y * I) +
        R (2 + y * I) * mellin (fun x : ℝ => (smoothWeight N (1 / 2) x : ℂ)) (2 + y * I) := by
    funext y
    rw [hRL _ (by simp)]
    change _ = _ + (LSeries b _ - _) * _
    ring
  rw [hdecomp, integral_add hpole.1 hint2, hpole.2, hshift] at hperron
  have hfracN := hfrac N (1 / 2) c a q K hN0 (by norm_num) hc ha.le haq
    (by linarith : q ≤ 1) hK R (fun y => by simpa using hRb ((c : ℂ) + y * I) (by simp [c])) hint
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
  have herr : (2 * Real.pi) * ‖(∑ n ∈ Finset.range (N + 1), b n) - J‖ ≤
      B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    rw [← abs_of_pos hpi, ← Real.norm_eq_abs, ← norm_smul, smul_sub, hperron]
    simpa [J] using (norm_integral_le_integral_norm _).trans hmass
  have herr' : ‖(∑ n ∈ Finset.range (N + 1), b n) - J‖ ≤
      (B / (2 * Real.pi)) * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    simpa [mul_comm] using herr
  have hJ : ‖J - N‖ ≤ 2 := norm_integral_halfWidth_sub_le hN1
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
    Real.one_le_rpow hNX (by linarith)
  change ‖(∑ n ∈ Finset.range (N + 1), b n) - N‖ ≤ _
  calc
    _ ≤ ‖(∑ n ∈ Finset.range (N + 1), b n) - J‖ + ‖J - N‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (B / (2 * Real.pi)) * ((N : ℝ) + 1) ^ (1 / 2 + ε) + 2 := add_le_add herr' hJ
    _ ≤ _ := by nlinarith

/-- Centering by the constant density one gives ordinary Dirichlet convergence
throughout the critical half-plane, for every full-positive source. -/
theorem centered_source_dirichletConvergesAt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DirichletConvergesAt (fun n => ((if 2 ≤ n + 1 then lam (n + 1) else 0 : ℝ) : ℂ) - 1) s := by
  let ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_sharp_source_sum_le hW hε
  apply tendsto_dirichlet_partialSum_of_poly_bounded hC
    (show 0 ≤ 1 / 2 + ε by linarith) _
    (show 1 / 2 + ε < s.re by dsimp [ε]; linarith)
  intro N
  simpa [Finset.sum_range_succ', Finset.sum_sub_distrib] using hbound N

/-- Ordinary harmonic convergence of the signed deviation, with no local-mass
or pointwise regularity premise. -/
theorem exists_tendsto_coneDeviation_harmonic {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam n / n) atTop (𝓝 L) := by
  let v : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  obtain ⟨L, hL⟩ := centered_source_dirichletConvergesAt hW (s := 1) (by norm_num)
  have hc : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (v (n + 1) - 1) / ((n : ℝ) + 1)) atTop (𝓝 L.re) := by
    have ht (n : ℕ) : ((v (n + 1) : ℂ) - 1) *
        ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ))) =
        (((v (n + 1) - 1) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      rw [Complex.cpow_neg_one]
      push_cast
      rfl
    have hreal := Complex.continuous_re.tendsto L |>.comp hL
    refine hreal.congr fun N => ?_
    change (∑ n ∈ Finset.range N, ((v (n + 1) : ℂ) - 1) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ)))).re = _
    simp_rw [ht]
    rw [← Complex.ofReal_sum]
    rfl
  have hh : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
      1 / ((n : ℝ) + 1)) - Real.log ((N : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have ht := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    refine ht.congr fun N => ?_
    simp [harmonic, Nat.cast_add, Nat.cast_one, one_div]
  have hsrc := (hc.comp (tendsto_add_atTop_nat 1)).add hh
  have hdev := hsrc.sub tendsto_vonMangoldt_harmonicWeighted
  refine ⟨(L.re + Real.eulerMascheroniConstant) -
    (Real.eulerMascheroniConstant + mertensAbelTail), ?_⟩
  have hdev' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 ((L.re + Real.eulerMascheroniConstant) -
        (Real.eulerMascheroniConstant + mertensAbelTail))) := by
    refine hdev.congr fun N => ?_
    simp only [Function.comp_apply]
    have hterm (n : ℕ) : WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1) =
        (v (n + 1) - 1) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) -
          ArithmeticFunction.vonMangoldt (n + 1) / ((n : ℝ) + 1) := by
      have heq : WeilOneSided.coneDeviation lam (n + 1) =
          v (n + 1) - ArithmeticFunction.vonMangoldt (n + 1) := by
        by_cases hn : 2 ≤ n + 1
        · simp [v, WeilOneSided.coneDeviation, hn]
        · have hn0 : n = 0 := by omega
          subst n
          simp [v, WeilOneSided.coneDeviation]
      rw [heq]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have hzero : WeilOneSided.coneDeviation lam 0 = 0 := by simp [WeilOneSided.coneDeviation]
  have hreindex (N : ℕ) : (∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1)) =
      ∑ n ∈ Finset.range (N + 2), WeilOneSided.coneDeviation lam n / n := by
    conv_rhs => rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [hzero, zero_div, add_zero, Nat.cast_add, Nat.cast_one]
  have hshift := hdev'.congr hreindex
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end RHTower.WeilSingularArithmetic
