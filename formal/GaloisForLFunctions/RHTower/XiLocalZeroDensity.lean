import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.HTGeometry.DigammaValuationBoundary

/-!
# The local density of the zeros of the completed zeta

Titchmarsh's `N(t+1) − N(t) = O(log t)` in the multiplicity-exact form the corpus's divisor
supplies.  The proof is the classical one, read off the corpus's partial fraction
`logDeriv xi s = Σ'_ρ (1/(ρ−1/2) + 1/(s−ρ))`: reindexing the (absolutely convergent) sum by the
functional-equation reflection `ρ ↦ 1−ρ` cancels the centring terms and leaves

`2·logDeriv xi s = Σ'_ρ (1/(s−ρ) + 1/(s−1+ρ))`,

whose terms have *positive real part* everywhere right of the critical strip.  At `s = 2+it` each
zero with `|γ − t| ≤ 1` contributes at least `1/5`, so the number of such zeros is at most
`10·Re logDeriv xi (2+it)`, and the factor split bounds that by `C log t`.

## Main results

* `two_logDeriv_xi_eq_pair_tsum` — the symmetrised partial fraction
* `exists_re_logDeriv_xi_two_line_le`
* `exists_card_near_xi_zeros_le` — **`N(t+1) − N(t) = O(log t)`**
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The symmetrised partial fraction -/

theorem xiPartialFractionTerm_eq (s : ℂ) (q : XiZeroCopy) :
    xiRelativeResolventTerm ((s - 1 / 2) * -Complex.I) q * -Complex.I
      = (((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ := by
  rw [xiRelativeResolventTerm]
  have hspec : xiSpectralPoint q = (((q.1 : ℂ)) - 1 / 2) * -Complex.I := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
  rw [hspec]
  have hth := resolvent_coordinate_transport (((q.1 : ℂ)) - 1 / 2) (s - 1 / 2)
  calc ((((q.1 : ℂ) - 1 / 2) * -Complex.I)⁻¹
        - (((q.1 : ℂ) - 1 / 2) * -Complex.I - (s - 1 / 2) * -Complex.I)⁻¹) * -Complex.I
      = (((q.1 : ℂ)) - 1 / 2)⁻¹ - (((q.1 : ℂ)) - 1 / 2 - (s - 1 / 2))⁻¹ := hth
    _ = (((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ := by
        rw [show ((q.1 : ℂ)) - 1 / 2 - (s - 1 / 2) = -(s - (q.1 : ℂ)) by ring, inv_neg]
        ring

theorem summable_xiPartialFractionTerm {s : ℂ} (hs : xi s ≠ 0) :
    Summable (fun q : XiZeroCopy => ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)) := by
  have hz : XiC ((s - 1 / 2) * -Complex.I) ≠ 0 := by
    rw [← xi_eq_XiC_comp]
    exact hs
  refine ((summable_xiRelativeResolventTerm hz).mul_right (-Complex.I)).congr fun q => ?_
  exact xiPartialFractionTerm_eq s q

theorem xiZeroCopyReflect_coe (q : XiZeroCopy) :
    (((xiZeroCopyReflectEquiv q).1 : XiDivisorSupport) : ℂ) = 1 - (q.1 : ℂ) := by
  change ((xiZeroReflectEquiv q.1 : XiDivisorSupport) : ℂ) = 1 - (q.1 : ℂ)
  exact xiZeroReflectEquiv_apply q.1

theorem summable_xiReflectedTerm {s : ℂ} (hs : xi s ≠ 0) :
    Summable (fun q : XiZeroCopy => (-(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹)) := by
  refine ((summable_xiPartialFractionTerm hs).comp_injective
    (xiZeroCopyReflectEquiv).injective).congr fun q => ?_
  show (((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2)⁻¹ + (s - ((xiZeroCopyReflectEquiv q).1 : ℂ))⁻¹
      = -(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹
  rw [xiZeroCopyReflect_coe]
  congr 1
  · rw [show (1 : ℂ) - (q.1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2) by ring, inv_neg]
  · congr 1
    ring

/-- The symmetrised terms are summable. -/
theorem summable_xiPairTerm {s : ℂ} (hs : xi s ≠ 0) :
    Summable (fun q : XiZeroCopy => ((s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹)) := by
  refine ((summable_xiPartialFractionTerm hs).add (summable_xiReflectedTerm hs)).congr fun q => ?_
  show ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)
      + (-(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹)
      = (s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹
  ring

/-- **The symmetrised partial fraction.**  Reflection cancels the centring terms. -/
theorem two_logDeriv_xi_eq_pair_tsum {s : ℂ} (hs : xi s ≠ 0) :
    2 * logDeriv xi s
      = ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) := by
  have hsum := summable_xiPartialFractionTerm hs
  have hpf := logDeriv_xi_eq_partialFraction hs
  have hrefl : (∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹))
      = ∑' q : XiZeroCopy, (-(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) := by
    rw [← (xiZeroCopyReflectEquiv).tsum_eq
      (fun q : XiZeroCopy => (((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)]
    refine tsum_congr fun q => ?_
    rw [xiZeroCopyReflect_coe]
    congr 1
    · rw [show (1 : ℂ) - (q.1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2) by ring, inv_neg]
    · congr 1
      ring
  have hsum2 := summable_xiReflectedTerm hs
  calc 2 * logDeriv xi s
      = (∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹))
        + ∑' q : XiZeroCopy, (-(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) := by
        rw [← hrefl, hpf]
        ring
    _ = ∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
          + (-(((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹)) := (hsum.tsum_add hsum2).symm
    _ = ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) := by
        refine tsum_congr fun q => ?_
        ring

/-! ## Positivity of the symmetrised terms -/

theorem re_xiPairTerm_nonneg {σ t : ℝ} (hσ : 2 ≤ σ) (q : XiZeroCopy) :
    0 ≤ ((((σ : ℂ) + (t : ℂ) * I) - (q.1 : ℂ))⁻¹
      + (((σ : ℂ) + (t : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hre1 : (((σ : ℂ) + (t : ℂ) * I) - (q.1 : ℂ)).re = σ - (q.1 : ℂ).re := by simp
  have hre2 : (((σ : ℂ) + (t : ℂ) * I) - 1 + (q.1 : ℂ)).re = σ - 1 + (q.1 : ℂ).re := by simp
  have hp1 : 0 < (((σ : ℂ) + (t : ℂ) * I) - (q.1 : ℂ)).re := by rw [hre1]; linarith
  have hp2 : 0 < (((σ : ℂ) + (t : ℂ) * I) - 1 + (q.1 : ℂ)).re := by rw [hre2]; linarith
  rw [Complex.add_re]
  exact add_nonneg (re_inv_pos_of_re_pos hp1).le (re_inv_pos_of_re_pos hp2).le

/-- A zero within unit height of `t` contributes at least `1/5` at the point `2 + it`. -/
theorem re_xiPairTerm_ge_of_near {t : ℝ} {q : XiZeroCopy} (hq : |(q.1 : ℂ).im - t| ≤ 1) :
    (1 : ℝ) / 5 ≤ ((((2 : ℂ) + (t : ℂ) * I) - (q.1 : ℂ))⁻¹
      + (((2 : ℂ) + (t : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  set ρ : ℂ := (q.1 : ℂ) with hρ
  set z : ℂ := ((2 : ℂ) + (t : ℂ) * I) - ρ with hz
  have hzre : z.re = 2 - ρ.re := by rw [hz]; simp
  have hzim : z.im = t - ρ.im := by rw [hz]; simp
  have hp2 : 0 < (((2 : ℂ) + (t : ℂ) * I) - 1 + ρ).re := by
    have : (((2 : ℂ) + (t : ℂ) * I) - 1 + ρ).re = 1 + ρ.re := by simp; ring
    rw [this]; linarith
  have hnormSq : Complex.normSq z ≤ 5 := by
    rw [Complex.normSq_apply, hzre, hzim]
    have habs : |t - ρ.im| ≤ 1 := by
      rw [abs_sub_comm]
      exact hq
    have hsq : (t - ρ.im) * (t - ρ.im) ≤ 1 := by
      have := abs_le.1 habs
      nlinarith [this.1, this.2]
    nlinarith [h0, h1]
  have hzre1 : (1 : ℝ) ≤ z.re := by rw [hzre]; linarith
  have hpos : 0 < Complex.normSq z := by
    refine Complex.normSq_pos.2 ?_
    intro h
    rw [h] at hzre1
    simp at hzre1
    linarith
  have hfirst : (1 : ℝ) / 5 ≤ (z⁻¹).re := by
    rw [Complex.inv_re, le_div_iff₀ hpos]
    nlinarith [hnormSq, hzre1, hpos]
  rw [Complex.add_re]
  have := (re_inv_pos_of_re_pos hp2).le
  linarith

/-! ## The bound on the logarithmic derivative at abscissa two -/

theorem exists_norm_logDeriv_riemannZeta_two_line :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  have hsum2 : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
  have hs : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by rw [hre]; norm_num
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((2 : ℂ) + (t : ℂ) * I) n‖
        = ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre]
    norm_num
  rw [logDeriv_riemannZeta_eq_neg_LSeries hs, norm_neg, LSeries]
  refine le_trans (norm_tsum_le_tsum_norm (hsum2.congr fun n => (hterm n).symm)) ?_
  exact le_of_eq (tsum_congr hterm)

/-! ## The logarithmic derivative at abscissa two is `O(log t)` -/

theorem exists_re_logDeriv_xi_two_line_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re ≤ C * Real.log t := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_logDeriv_riemannZeta_two_line
  set C : ℝ := 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 2 with hCdef
  have hC0 : 0 < C := by
    rw [hCdef]
    positivity
  refine ⟨C, hC0, ?_⟩
  have hdig : ∀ᶠ u : ℝ in atTop,
      ‖Complex.digamma ((1 : ℂ) + (u : ℂ) * I)‖ ≤ 2 * Real.log u :=
    GaloisForLFunctions.norm_digamma_vertical_le_two_log (by norm_num)
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  have hdig' : ∀ᶠ t : ℝ in atTop,
      ‖Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤ 2 * Real.log (t / 2) :=
    hhalf.eventually hdig
  filter_upwards [hdig', Filter.eventually_ge_atTop (3 : ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))] with t hdt ht3 hlog1
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 2 := by rw [hs]; simp
  have hsplit : logDeriv xi s = s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s
      + logDeriv riemannZeta s := logDeriv_xi_split (by rw [hre]; norm_num)
  have hsnorm : (2 : ℝ) ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hre] at this
    simpa using this
  have hs1norm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre1 : (s - 1).re = 1 := by rw [Complex.sub_re, hre]; norm_num
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1] at this
    simpa using this
  have hinv1 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, one_div]
    gcongr
  have hinv2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one_iff₀]
    right
    exact hs1norm
  have hgamma : ‖logDeriv Complex.Gammaℝ s‖ ≤ |Real.log Real.pi| / 2 + Real.log t := by
    have hsre : (0 : ℝ) < s.re := by rw [hre]; norm_num
    have hhalfs : s / 2 = (1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      rw [hs]
      push_cast
      ring
    rw [logDeriv_Gammaℝ_eq hsre, hhalfs]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖-((Real.log Real.pi : ℂ) / 2)‖ = |Real.log Real.pi| / 2 := by
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have h2 : ‖Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖
        ≤ Real.log t := by
      rw [norm_div]
      have hlog : Real.log (t / 2) ≤ Real.log t := by
        refine Real.log_le_log (by linarith) (by linarith)
      have : ‖Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤ 2 * Real.log t := by
        linarith
      have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2norm]
      linarith
    linarith
  have hzeta : ‖logDeriv riemannZeta s‖ ≤ C₀ := hC₀ t
  have hfinal : (logDeriv xi s).re ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [hsplit]
    calc ‖s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s‖
        ≤ ‖s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s‖ + ‖logDeriv riemannZeta s‖ :=
          norm_add_le _ _
      _ ≤ (‖s⁻¹ + (s - 1)⁻¹‖ + ‖logDeriv Complex.Gammaℝ s‖) + ‖logDeriv riemannZeta s‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖s⁻¹‖ + ‖(s - 1)⁻¹‖) + ‖logDeriv Complex.Gammaℝ s‖)
            + ‖logDeriv riemannZeta s‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by linarith
  have hCpos : (0 : ℝ) ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 1 := by positivity
  have hmul : 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t ≤ C * Real.log t := by
    rw [hCdef]
    nlinarith [hlog1, hCpos]
  linarith

/-! ## The local zero count -/

/-- **`N(t+1) − N(t) = O(log t)`.**  Every finite packet of divisor copies within unit height of
`t` has at most `C log t` members. -/
theorem exists_card_near_xi_zeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ 1) → (F.card : ℝ) ≤ C * Real.log t := by
  obtain ⟨C, hC0, hC⟩ := exists_re_logDeriv_xi_two_line_le
  refine ⟨10 * C, by positivity, ?_⟩
  filter_upwards [hC] with t ht F hF
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs
  have hxi : xi s ≠ 0 := by
    refine xi_ne_zero_of_one_le_re ?_
    rw [hs]
    simp
  set f : XiZeroCopy → ℂ := fun q => ((s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) with hf
  have hsum : Summable f := summable_xiPairTerm hxi
  have hsumre : Summable (fun q => (f q).re) :=
    hsum.map Complex.reAddGroupHom Complex.continuous_re
  have hnonneg : ∀ q : XiZeroCopy, 0 ≤ (f q).re := by
    intro q
    rw [hf, hs]
    exact re_xiPairTerm_nonneg (by norm_num) q
  have hnear : ∀ q ∈ F, (1 : ℝ) / 5 ≤ (f q).re := by
    intro q hq
    rw [hf, hs]
    exact re_xiPairTerm_ge_of_near (hF q hq)
  have hcard : (F.card : ℝ) * (1 / 5) ≤ ∑ q ∈ F, (f q).re := by
    have := Finset.card_nsmul_le_sum F (fun q => (f q).re) (1 / 5) hnear
    rw [nsmul_eq_mul] at this
    exact this
  have hle : (∑ q ∈ F, (f q).re) ≤ ∑' q, (f q).re :=
    hsumre.sum_le_tsum F (fun q _ => hnonneg q)
  have hval : (∑' q, (f q).re) = 2 * (logDeriv xi s).re := by
    rw [← Complex.re_tsum hsum]
    rw [hf]
    rw [← two_logDeriv_xi_eq_pair_tsum hxi]
    simp
  have hfinal : (F.card : ℝ) * (1 / 5) ≤ 2 * (C * Real.log t) := by
    refine le_trans hcard (le_trans hle ?_)
    rw [hval]
    have := ht
    linarith
  linarith

/-! ## The weighted density -/

theorem re_xiPairTerm_ge_weighted {t : ℝ} (q : XiZeroCopy) :
    (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))
      ≤ ((((2 : ℂ) + (t : ℂ) * I) - (q.1 : ℂ))⁻¹
        + (((2 : ℂ) + (t : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  set ρ : ℂ := (q.1 : ℂ) with hρ
  set z : ℂ := ((2 : ℂ) + (t : ℂ) * I) - ρ with hz
  have hzre : z.re = 2 - ρ.re := by rw [hz]; simp
  have hzim : z.im = t - ρ.im := by rw [hz]; simp
  have hp2 : 0 < (((2 : ℂ) + (t : ℂ) * I) - 1 + ρ).re := by
    have hval : (((2 : ℂ) + (t : ℂ) * I) - 1 + ρ).re = 1 + ρ.re := by simp; ring
    rw [hval]; linarith
  have hden : Complex.normSq z = (2 - ρ.re) ^ (2 : ℕ) + (t - ρ.im) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hpos : (0 : ℝ) < Complex.normSq z := by
    rw [hden]
    nlinarith [sq_nonneg (t - ρ.im), h1]
  have hfirst : (1 : ℝ) / 4 / (1 + (t - ρ.im) ^ (2 : ℕ)) ≤ (z⁻¹).re := by
    rw [Complex.inv_re, hzre, hden]
    have hd2 : (0 : ℝ) < (2 - ρ.re) ^ (2 : ℕ) + (t - ρ.im) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (t - ρ.im), h1]
    rw [div_le_div_iff₀ (by positivity) hd2]
    nlinarith [sq_nonneg (t - ρ.im), h0, h1]
  rw [Complex.add_re]
  have h2 := (re_inv_pos_of_re_pos hp2).le
  linarith

/-- **The weighted local density.**  `Σ_ρ 1/(1+(t−γ)²) = O(log t)`. -/
theorem exists_tsum_weighted_density_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      Summable (fun q : XiZeroCopy => (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) ∧
      ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤ C * Real.log t := by
  obtain ⟨C, hC0, hC⟩ := exists_re_logDeriv_xi_two_line_le
  refine ⟨8 * C, by positivity, ?_⟩
  filter_upwards [hC] with t ht
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs
  have hxi : xi s ≠ 0 := by
    refine xi_ne_zero_of_one_le_re ?_
    rw [hs]
    simp
  set f : XiZeroCopy → ℂ := fun q => ((s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹) with hf
  have hsum : Summable f := summable_xiPairTerm hxi
  have hsumre : Summable (fun q => (f q).re) :=
    hsum.map Complex.reAddGroupHom Complex.continuous_re
  have hcomp : ∀ q : XiZeroCopy,
      (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤ (f q).re := by
    intro q
    rw [hf, hs]
    exact re_xiPairTerm_ge_weighted q
  have hnn : ∀ q : XiZeroCopy, 0 ≤ (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) := by
    intro q
    positivity
  have hsumq : Summable (fun q : XiZeroCopy =>
      (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) :=
    Summable.of_nonneg_of_le hnn hcomp hsumre
  have hsumfull : Summable (fun q : XiZeroCopy => (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) := by
    have := hsumq.mul_left 4
    refine this.congr fun q => ?_
    field_simp
  refine ⟨hsumfull, ?_⟩
  have hle : (∑' q : XiZeroCopy, (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)))
      ≤ ∑' q, (f q).re := hsumq.tsum_le_tsum hcomp hsumre
  have hval : (∑' q, (f q).re) = 2 * (logDeriv xi s).re := by
    rw [← Complex.re_tsum hsum, hf, ← two_logDeriv_xi_eq_pair_tsum hxi]
    simp
  have hquarter : (∑' q : XiZeroCopy, (1 : ℝ) / 4 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)))
      = (1 / 4) * ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    field_simp
  rw [hquarter, hval] at hle
  linarith

end

end RHTower
