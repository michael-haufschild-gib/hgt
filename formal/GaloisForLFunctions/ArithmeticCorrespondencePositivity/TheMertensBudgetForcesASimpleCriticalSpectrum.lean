import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensEnergyPaysItsCriticalResidues
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The Mertens budget forces a simple critical spectrum

A **Mertens budget** is a linear log-energy: `∫_0^L e^{−u} M(⌊e^u⌋)² du ≤ S L + B` for all `L ≥ 0`,
i.e. `∫_1^X M(⌊x⌋)²/x² dx ≤ S log X + B`. P40 showed that the slope `S` pays the residue masses
`‖1/(ρ ζ′(ρ))‖²` of finitely many simple critical zeros. Here the budget is shown to decide the
whole spectrum:

* **Purity** (`riemannZeta_ne_zero_of_mertens_budget`, `riemannHypothesis_of_mertens_budget`). On
  every line `Re s = ½ + e` the Mellin pairing of `M` converges and inverts `ζ`, so `ζ` has no zero
  right of the critical line.
* **Simplicity** (`deriv_riemannZeta_ne_zero_of_mertens_budget`). A critical zero with `ζ′(ρ) = 0`
  gives `|ζ(s)| ≤ K|s − ρ|²` near `ρ`, so on the window `|y − Im ρ| ≤ e` of the line `Re s = ½ + e`
  the symbol `1/(sζ(s))` has size `≳ e^{−2}`; the window mass `e ∫ ‖G‖² ≳ e^{−2}` then outgrows the
  Abelian bound `π S + 2π e B` (`mul_integral_norm_sq_lineSymbol_le_of_linear`).
* **The whole spectrum is paid** (`summable_and_tsum_le_of_mertens_budget`).
  `Σ_ρ ‖1/(ρ ζ′(ρ))‖² ≤ S` over all critical zeros.

So a Mertens budget is purity together with a simple spectrum and a summable residue mass — the
`ℤ`-form of the `𝔽_q` budget law (P42), where a finite prime-error slope is purity and counts the
spectrum with squared multiplicity: the Mertens budget sees multiplicity as a divergence.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)

/-- A Mertens budget has nonnegative slope and may be taken with `B ≥ 0`. -/
theorem mertens_budget_normalize {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B) :
    0 ≤ S ∧
      ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + max B 0 := by
  refine ⟨?_, fun L hL => (hlin L hL).trans (by linarith [le_max_left B 0])⟩
  by_contra h
  exact not_forall_logEnergy_le_of_neg mertensRow (not_le.mp h) hlin

/-- **Purity.** Under a Mertens budget `ζ` has no zero right of the critical line. -/
theorem riemannZeta_ne_zero_of_mertens_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B)
    {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  obtain ⟨hS0, hlin'⟩ := mertens_budget_normalize hlin
  by_cases hs1 : s = 1
  · rw [hs1]; exact riemannZeta_one_ne_zero
  have he : 0 < s.re - 1 / 2 := by linarith
  have hsdef : s = ((s.re - 1 / 2 + 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hsdef] at hs1 ⊢
  exact (lineSymbol_mertens_eq_of_linear hS0 (le_max_right B 0) hlin' he s.im hs1).1

/-- **A Mertens budget implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_mertens_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B) :
    RiemannHypothesis :=
  _root_.RHTower.riemannHypothesis_iff_forall_zero_re_le_half.mpr fun _ hz => by
    by_contra h
    exact riemannZeta_ne_zero_of_mertens_budget hlin (not_le.mp h) hz

/-- At a zero where the derivative vanishes too, `‖f(s)‖ ≤ K ‖s − ρ‖²` near `ρ` (two `dslope`s). -/
theorem exists_norm_le_sq_of_deriv_eq_zero {f : ℂ → ℂ} {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball ρ r)) (h0 : f ρ = 0) (h1 : deriv f ρ = 0) :
    ∃ η > 0, ∃ K > 0, ∀ s : ℂ, ‖s - ρ‖ < η → ‖f s‖ ≤ K * ‖s - ρ‖ ^ 2 := by
  have hU : Metric.ball ρ r ∈ 𝓝 ρ := Metric.ball_mem_nhds ρ hr
  have hd₁ : DifferentiableOn ℂ (dslope f ρ) (Metric.ball ρ r) :=
    (Complex.differentiableOn_dslope hU).mpr hf
  have hd₁0 : dslope f ρ ρ = 0 := by rw [dslope_same, h1]
  have hd₂ : DifferentiableOn ℂ (dslope (dslope f ρ) ρ) (Metric.ball ρ r) :=
    (Complex.differentiableOn_dslope hU).mpr hd₁
  have hc : ContinuousAt (dslope (dslope f ρ) ρ) ρ := (hd₂.differentiableAt hU).continuousAt
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  refine ⟨η, hη, ‖dslope (dslope f ρ) ρ ρ‖ + 1, by positivity, fun s hs => ?_⟩
  have e1 : f s = (s - ρ) * dslope f ρ s := by
    have := sub_smul_dslope f ρ s
    rw [h0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have e2 : dslope f ρ s = (s - ρ) * dslope (dslope f ρ) ρ s := by
    have := sub_smul_dslope (dslope f ρ) ρ s
    rw [hd₁0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hb : ‖dslope (dslope f ρ) ρ s‖ ≤ ‖dslope (dslope f ρ) ρ ρ‖ + 1 := by
    have h := hη' (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at h
    linarith [norm_sub_norm_le (dslope (dslope f ρ) ρ s) (dslope (dslope f ρ) ρ ρ)]
  rw [e1, e2, norm_mul, norm_mul]
  calc ‖s - ρ‖ * (‖s - ρ‖ * ‖dslope (dslope f ρ) ρ s‖)
      = ‖s - ρ‖ ^ 2 * ‖dslope (dslope f ρ) ρ s‖ := by ring
    _ ≤ ‖s - ρ‖ ^ 2 * (‖dslope (dslope f ρ) ρ ρ‖ + 1) := by gcongr
    _ = (‖dslope (dslope f ρ) ρ ρ‖ + 1) * ‖s - ρ‖ ^ 2 := by ring

/-- Near a zero with `‖ζ(s)‖ ≤ K‖s − ρ‖²` the Mertens symbol is large on the window
`|y − Im ρ| ≤ e`: `‖G(e + iy)‖² ≥ 1/(16 K² e⁴ (‖ρ‖ + 1)²)`. -/
theorem norm_sq_lineSymbol_mertens_ge {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) {η K : ℝ} (hK : 0 < K)
    (hbound : ∀ s : ℂ, ‖s - ρ‖ < η → ‖riemannZeta s‖ ≤ K * ‖s - ρ‖ ^ 2)
    {e : ℝ} (he : 0 < e) (heη : e < η / 2) (he2 : e < 1 / 2) {y : ℝ}
    (hy : y ∈ Icc (ρ.im - e) (ρ.im + e)) :
    1 / (16 * K ^ 2 * e ^ 4 * (‖ρ‖ + 1) ^ 2) ≤ ‖lineSymbol (logProfile mertensRow) e y‖ ^ 2 := by
  have hss : (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - ρ = (e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hnorm : ‖(((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - ρ‖ ≤ 2 * e := by
    rw [hss]
    have h2 : |y - ρ.im| ≤ e := abs_sub_le_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    calc ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖ ≤ ‖(e : ℂ)‖ + ‖((y - ρ.im : ℝ) : ℂ) * I‖ :=
          norm_add_le _ _
      _ = |e| + |y - ρ.im| := by
          simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * e := by rw [abs_of_pos he]; linarith
  have hs1 : (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs0 : (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨hζ, hG⟩ := lineSymbol_mertens_eq_of_linear hS0 hB0 hlin he y hs1
  generalize (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = s at hnorm hs0 hζ hG
  have hζb : ‖riemannZeta s‖ ≤ 4 * K * e ^ 2 := by
    calc ‖riemannZeta s‖ ≤ K * ‖s - ρ‖ ^ 2 := hbound s (by linarith)
      _ ≤ K * (2 * e) ^ 2 := by gcongr
      _ = 4 * K * e ^ 2 := by ring
  have hsb : ‖s‖ ≤ ‖ρ‖ + 1 := by
    calc ‖s‖ = ‖ρ + (s - ρ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖ρ‖ + ‖s - ρ‖ := norm_add_le _ _
      _ ≤ ‖ρ‖ + 1 := by linarith
  have hpos : 0 < ‖s‖ * ‖riemannZeta s‖ := mul_pos (norm_pos_iff.mpr hs0) (norm_pos_iff.mpr hζ)
  have hprod : ‖s‖ * ‖riemannZeta s‖ ≤ (‖ρ‖ + 1) * (4 * K * e ^ 2) :=
    mul_le_mul hsb hζb (norm_nonneg _) (by positivity)
  rw [hG, norm_div, norm_one, norm_mul, div_pow, one_pow]
  apply one_div_le_one_div_of_le (pow_pos hpos 2)
  calc (‖s‖ * ‖riemannZeta s‖) ^ 2 ≤ ((‖ρ‖ + 1) * (4 * K * e ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hpos.le hprod 2
    _ = 16 * K ^ 2 * e ^ 4 * (‖ρ‖ + 1) ^ 2 := by ring

/-- The window mass near such a zero: `e ∫ ‖G(e + iy)‖² dy ≥ 1/(8 K² e² (‖ρ‖ + 1)²)`. -/
theorem mul_integral_norm_sq_lineSymbol_mertens_ge {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) {η K : ℝ} (hK : 0 < K)
    (hbound : ∀ s : ℂ, ‖s - ρ‖ < η → ‖riemannZeta s‖ ≤ K * ‖s - ρ‖ ^ 2)
    {e : ℝ} (he : 0 < e) (heη : e < η / 2) (he2 : e < 1 / 2) :
    1 / (8 * K ^ 2 * e ^ 2 * (‖ρ‖ + 1) ^ 2) ≤
      e * ∫ y, ‖lineSymbol (logProfile mertensRow) e y‖ ^ 2 := by
  have hdata := integrable_and_memLp_dampedProfile_logProfile (c := e) mertensRow_zero
    (add_nonneg (div_nonneg hS0 he.le) hB0) he.le
    (fun T => pronic_energy_le_of_linear hS0 hB0 hlin he T) (by linarith)
  have hint : Integrable (fun y => ‖lineSymbol (logProfile mertensRow) e y‖ ^ 2) :=
    _root_.RHTower.integrable_norm_sq_laplaceBoundary hdata.1.ofReal hdata.2.ofReal
  have h1 := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Icc
    (by simp [Real.volume_Icc])
    (fun y hy => norm_sq_lineSymbol_mertens_ge hS0 hB0 hlin hre hK hbound he heη he2 hy)
    hint.integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith)] at h1
  have h2 := h1.trans (setIntegral_le_integral hint (Eventually.of_forall fun y => sq_nonneg _))
  have hP : 0 < ‖ρ‖ + 1 := by positivity
  calc 1 / (8 * K ^ 2 * e ^ 2 * (‖ρ‖ + 1) ^ 2)
      = e * (1 / (16 * K ^ 2 * e ^ 4 * (‖ρ‖ + 1) ^ 2) * (ρ.im + e - (ρ.im - e))) := by
        field_simp; ring
    _ ≤ e * ∫ y, ‖lineSymbol (logProfile mertensRow) e y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 he.le

/-- A small positive parameter: `0 < e < a`, `e < ½`, `Q e² < 1`. -/
theorem exists_small_pos {a Q : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q) :
    ∃ e : ℝ, 0 < e ∧ e < a ∧ e < 1 / 2 ∧ Q * e ^ 2 < 1 := by
  refine ⟨min (a / 2) (1 / (2 * (Q + 2))), lt_min (by linarith) (by positivity),
    (min_le_left _ _).trans_lt (by linarith), ?_, ?_⟩
  · refine (min_le_right _ _).trans_lt ?_
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  · have h0 : 0 < min (a / 2) (1 / (2 * (Q + 2))) := lt_min (by linarith) (by positivity)
    have h1 : min (a / 2) (1 / (2 * (Q + 2))) * (2 * (Q + 2)) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have h2 : min (a / 2) (1 / (2 * (Q + 2))) ≤ 1 / 2 := by
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith

/-- **Simplicity.** Under a Mertens budget every zero of `ζ` on the critical line is simple. -/
theorem deriv_riemannZeta_ne_zero_of_mertens_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : ρ.re = 1 / 2) : deriv riemannZeta ρ ≠ 0 := by
  intro hd
  obtain ⟨hS0, hlin'⟩ := mertens_budget_normalize hlin
  have hB0 : 0 ≤ max B 0 := le_max_right B 0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre; norm_num at hre
  have hr : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)
  have hdiff : DifferentiableOn ℂ riemannZeta (Metric.ball ρ ‖ρ - 1‖) := fun s hs =>
    (differentiableAt_riemannZeta fun h => by
      rw [Metric.mem_ball, h, dist_comm, dist_eq_norm] at hs
      exact lt_irrefl _ hs).differentiableWithinAt
  obtain ⟨η, hη, K, hK, hbound⟩ := exists_norm_le_sq_of_deriv_eq_zero hr hdiff hz hd
  have hA0 : 0 ≤ Real.pi * S + 2 * Real.pi * max B 0 := by have := Real.pi_pos; positivity
  obtain ⟨e, he, heη, he2, hsmall⟩ := exists_small_pos (a := η / 2)
    (Q := 8 * K ^ 2 * (‖ρ‖ + 1) ^ 2 * (Real.pi * S + 2 * Real.pi * max B 0)) (by linarith)
    (by positivity)
  have hlow := mul_integral_norm_sq_lineSymbol_mertens_ge hS0 hB0 hlin' hre hK hbound he heη he2
  have hup := mul_integral_norm_sq_lineSymbol_le_of_linear mertensRow_zero zero_le_one
    abs_mertensRow_le_sq hS0 hB0 hlin' he
  have hup' : Real.pi * S + 2 * Real.pi * e * max B 0 ≤ Real.pi * S + 2 * Real.pi * max B 0 := by
    have := Real.pi_pos
    have : e * max B 0 ≤ max B 0 := by nlinarith
    nlinarith
  have hfin := (hlow.trans hup).trans hup'
  rw [div_le_iff₀ (by positivity)] at hfin
  nlinarith

/-- **The whole critical spectrum is paid.** Under a Mertens budget of slope `S`,
`Σ_ρ ‖1/(ρ ζ′(ρ))‖² ≤ S` over all zeros of `ζ` on the critical line. -/
theorem summable_and_tsum_le_of_mertens_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} =>
        ‖1 / ((ρ : ℂ) * deriv riemannZeta ρ)‖ ^ 2) ∧
      ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2},
        ‖1 / ((ρ : ℂ) * deriv riemannZeta ρ)‖ ^ 2 ≤ S := by
  have hfin : ∀ F : Finset {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2},
      ∑ ρ ∈ F, ‖1 / ((ρ : ℂ) * deriv riemannZeta ρ)‖ ^ 2 ≤ S := by
    intro F
    by_contra h
    refine not_forall_mertens_energy_le_linear (F.map (Function.Embedding.subtype _)) ?_
      ?_ hlin
    · intro ρ hρ
      obtain ⟨ρ', -, rfl⟩ := Finset.mem_map.mp hρ
      exact ⟨ρ'.2.1, deriv_riemannZeta_ne_zero_of_mertens_budget hlin ρ'.2.1 ρ'.2.2, ρ'.2.2⟩
    · rw [Finset.sum_map]; exact not_le.mp h
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfin⟩

/-- **The Mertens budget law.** A linear Mertens log-energy of slope `S` forces the Riemann
hypothesis, simplicity of every critical zero, and `Σ_ρ ‖1/(ρ ζ′(ρ))‖² ≤ S`. -/
theorem mertens_budget_forces_simple_critical_spectrum {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B) :
    RiemannHypothesis ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → deriv riemannZeta ρ ≠ 0) ∧
      Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} =>
        ‖1 / ((ρ : ℂ) * deriv riemannZeta ρ)‖ ^ 2) ∧
      ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2},
        ‖1 / ((ρ : ℂ) * deriv riemannZeta ρ)‖ ^ 2 ≤ S :=
  ⟨riemannHypothesis_of_mertens_budget hlin,
    fun _ hz hre => deriv_riemannZeta_ne_zero_of_mertens_budget hlin hz hre,
    summable_and_tsum_le_of_mertens_budget hlin⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
