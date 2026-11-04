import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalNearCenterHasAHarmonicModel
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalHarmonicMeansRetainTheirFiniteParts

/-!
# Terminal windows retain the near-center finite part

The local harmonic cutoff is asymptotic to twice the overlap times the
terminal coordinate. Its polar finite part therefore retains `log(2x)`;
every other matching conductor retains its von Mangoldt charge.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)

private theorem tendsto_terminal_harmonic_scale_div_overlap
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((Real.exp (2 * c N / N) - 1) * N) / c N) atTop (𝓝 2) := by
  have htlim : Tendsto (fun N : ℕ => 2 * c N / N) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hcN.const_mul 2
  have he := (Real.continuous_exp.tendsto 0).comp htlim
  have h := (tendsto_nearCenterGapCutoff_div_overlap hc hcN).mul he
  simp only [Real.exp_zero, mul_one] at h
  apply h.congr
  intro N
  dsimp only [nearCenterGapCutoff, Function.comp_def]
  field_simp [Real.exp_ne_zero]
  ring

private theorem tendsto_log_overlap_riemann_error
    {F : ℝ → ℝ} {LF : ℝ}
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      ((∑ n ∈ Icc 1 N, F ((n : ℝ) / N)) / N - ∫ x in (0 : ℝ)..1, F x))
      atTop (𝓝 0) := by
  have hsmall : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogN : Tendsto (fun N : ℕ => Real.log (c N) / N) atTop (𝓝 0) := by
    have h := (hsmall.comp hcinf).mul hcN
    simp only [mul_zero] at h
    exact h.congr fun N => by
      dsimp only [Function.comp_def]
      field_simp [(hc N).ne']
  have hlim := hlogN.const_mul LF
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1, hcinf.eventually_ge_atTop 1] with N hN hc1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hc1)]
  exact (mul_le_mul_of_nonneg_left (abs_riemannSum_sub_integral_le hFL hN)
    (Real.log_nonneg hc1)).trans_eq (by ring)

/-- A compact terminal window retains the local polar logarithm and each diagonal arithmetic
charge of the exact near center. The overlap may grow at any sublinear rate. -/
theorem tendsto_terminal_nearCenterPair_finite_part
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      nearCenterPair (c N) N
        (fun n => logProfile h ((n : ℝ) / N) * ramanujanLagCoefficient l n)
        (ramanujanLagCoefficient m) / N -
      (if m = 1 ∧ l = 1 then Real.log (c N) * ∫ x in (0 : ℝ)..1, logProfile h x else 0))
      atTop (𝓝 (if m = l then
        (if m = 1 then (Real.log 2 + Real.eulerMascheroniConstant) *
            (∫ x in (0 : ℝ)..1, logProfile h x) +
            ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x
          else -vonMangoldt m * ∫ x in (0 : ℝ)..1, logProfile h x) else 0)) := by
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤ ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  have hz := tendsto_terminal_nearCenterPair_sub_harmonic
    (fun x => abs_logProfile_le hBF x) (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A))
    hFL hm hl hc hcN
  by_cases hml : m = l
  · subst l
    simp only [if_true, and_self] at hz ⊢
    let a : ℕ → ℝ := fun N => (Real.exp (2 * c N / N) - 1) * N
    have hr : Tendsto (fun N => a N / c N) atTop (𝓝 2) :=
      tendsto_terminal_harmonic_scale_div_overlap hc hcN
    have hainf : Tendsto a atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [hcinf.eventually_ge_atTop b,
        hr.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with N hNb hratio
      exact hNb.trans (by simpa only [one_mul] using (le_div_iff₀ (hc N)).mp hratio.le)
    have hharm := tendsto_terminal_lagHarmonic_centered_mean hh hA hsupp hm hainf
    have harg (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
        a N * ((n : ℝ) / N) = (Real.exp (2 * c N / N) - 1) * n := by
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      dsimp only [a]
      field_simp
    by_cases hm1 : m = 1
    · subst m
      simp only [if_true] at hharm ⊢
      have hmean := tendsto_weighted_riemannSum (w := fun _ : ℕ => (1 : ℝ))
        (M := 1) (W := 1) (by norm_num) (by intros; rfl) (by intros; norm_num)
        hFL (fun x _ => abs_logProfile_le hBF x) 0
      simp only [Nat.sub_zero, one_mul, sum_range_one, Nat.cast_one, div_one] at hmean
      have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hr
      have hmain : Tendsto (fun N : ℕ =>
          (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) *
            lagHarmonic 1 ⌊(Real.exp (2 * c N / N) - 1) * n⌋₊) / N -
          Real.log (c N) * ((∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N)) / N)) atTop
          (𝓝 ((Real.log 2 + Real.eulerMascheroniConstant) *
            (∫ x in (0 : ℝ)..1, logProfile h x) +
              ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x)) := by
        have ht := hharm.add (hlog.mul hmean)
        have he : Real.eulerMascheroniConstant * (∫ x in (0 : ℝ)..1, logProfile h x) +
            (∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x) +
            Real.log 2 * (∫ x in (0 : ℝ)..1, logProfile h x) =
            (Real.log 2 + Real.eulerMascheroniConstant) *
              (∫ x in (0 : ℝ)..1, logProfile h x) +
              ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x := by ring
        rw [he] at ht
        apply ht.congr'
        filter_upwards [eventually_ge_atTop 1, hainf.eventually_gt_atTop 0] with N hN haN
        simp only [Function.comp_def, harg N hN, Real.log_div haN.ne' (hc N).ne',
          mul_sub, sum_sub_distrib, ← sum_mul]
        ring
      have herr := tendsto_log_overlap_riemann_error hFL hc hcinf hcN
      have ht := (hz.add hmain).add herr
      simp only [zero_add, add_zero] at ht
      exact ht.congr fun N => by ring
    · simp only [if_neg hm1, sub_zero] at hharm ⊢
      have hmain : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
          logProfile h ((n : ℝ) / N) * lagHarmonic m ⌊(Real.exp (2 * c N / N) - 1) * n⌋₊) / N)
          atTop (𝓝 (-vonMangoldt m * ∫ x in (0 : ℝ)..1, logProfile h x)) := by
        apply hharm.congr'
        filter_upwards [eventually_ge_atTop 1] with N hN
        simp only [harg N hN]
      simpa only [zero_add, sub_add_cancel] using hz.add hmain
  · have hnot : ¬(m = 1 ∧ l = 1) := by rintro ⟨rfl, rfl⟩; exact hml rfl
    simpa only [if_neg hml, if_neg hnot, sub_zero] using hz

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nearCenterPair_finite_part
