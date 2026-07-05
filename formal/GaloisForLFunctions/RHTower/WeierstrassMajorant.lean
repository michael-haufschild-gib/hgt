/-
Weierstrass step-majorant against the law of a bounded random variable.

For a `[0,R]`-valued random variable `Y` on a probability space, a threshold `θ`, and a
tolerance `δ > 0`, there is a polynomial `q` majorizing the step `1_{[0,θ]}` — value `≥ 1`
on `[0,θ]`, `≥ 0` on `[0,R]` — whose expectation `E q(Y)` is within `δ` of `P(Y ≤ θ)`. The
construction: continuity from above picks `ε` with `P(Y ≤ θ+ε) ≤ P(Y ≤ θ) + δ/3`; a
continuous tent `h` (1 on `[0,θ]`, 0 above `θ+ε`) satisfies `E h(Y) ≤ P(Y ≤ θ+ε)`;
Weierstrass gives a polynomial `P` within `δ/3` of `h` on `[0,R]`; and `q := P + δ/3`
majorizes and integrates within the budget. This is the analytic input that drives a
polynomial-moment density bound to the exact small-ball measure.
-/
import Mathlib

open MeasureTheory Set Filter Topology

namespace RHTower

/-- Abstract Weierstrass step-majorant: for a `[0,R]`-valued random variable `Y` on a
probability space, a threshold `θ`, and `δ > 0`, there is a polynomial `q` majorizing the
step `1_{[0,θ]}` (value `≥ 1` on `[0,θ]`, `≥ 0` on `[0,R]`) whose expectation `E q(Y)` is
within `δ` of `P(Y ≤ θ)`. -/
theorem exists_poly_majorant_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) {R θ : ℝ} (hθ0 : 0 ≤ θ) (hθR : θ ≤ R)
    (hYR : ∀ ω, Y ω ∈ Set.Icc (0:ℝ) R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Polynomial ℝ,
      (∀ u ∈ Set.Icc (0:ℝ) θ, 1 ≤ q.eval u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) R, 0 ≤ q.eval u) ∧
      ∫ ω, q.eval (Y ω) ∂μ ≤ (μ {ω | Y ω ≤ θ}).toReal + δ := by
  have hδ3 : 0 < δ / 3 := by positivity
  -- Step A: continuity from above picks ε with P(Y ≤ θ+ε) ≤ P(Y ≤ θ) + δ/3.
  obtain ⟨ε, hε0, hεmeas⟩ :
      ∃ ε : ℝ, 0 < ε ∧
        (μ {ω | Y ω ≤ θ + ε}).toReal ≤ (μ {ω | Y ω ≤ θ}).toReal + δ / 3 := by
    set s : ℕ → Set Ω := fun n => {ω | Y ω ≤ θ + 1 / (n + 1)} with hs
    have hmeas : ∀ n, NullMeasurableSet (s n) μ := fun n =>
      (measurableSet_le hY measurable_const).nullMeasurableSet
    have hanti : Antitone s := by
      intro m n hmn ω hω
      simp only [hs, mem_setOf_eq] at hω ⊢
      have hle : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hmn 1
      linarith
    have hiInter : (⋂ n, s n) = {ω | Y ω ≤ θ} := by
      ext ω
      simp only [hs, mem_iInter, mem_setOf_eq]
      constructor
      · intro hall
        by_contra hgt
        rw [not_le] at hgt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
        have := hall n
        linarith
      · intro hle n
        have : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
    have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
    rw [hiInter] at htend
    have htendR : Tendsto (fun n => (μ (s n)).toReal) atTop
        (𝓝 (μ {ω | Y ω ≤ θ}).toReal) :=
      (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend
    have hev : ∀ᶠ n in atTop, (μ (s n)).toReal < (μ {ω | Y ω ≤ θ}).toReal + δ / 3 :=
      htendR.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨N, hN⟩ := hev.exists
    exact ⟨1 / (N + 1), by positivity, le_of_lt hN⟩
  -- Step B: the tent majorant.
  set h : ℝ → ℝ := fun u => max 0 (min 1 ((θ + ε - u) / ε)) with hh
  have hcont : Continuous h := by rw [hh]; fun_prop (disch := assumption)
  have hh1 : ∀ u : ℝ, u ≤ θ → h u = 1 := by
    intro u hu
    simp only [hh]
    have : (1 : ℝ) ≤ (θ + ε - u) / ε := by rw [le_div_iff₀ hε0]; linarith
    rw [min_eq_left this, max_eq_right zero_le_one]
  have hh0 : ∀ u : ℝ, 0 ≤ h u := by intro u; simp only [hh]; exact le_max_left _ _
  have hhle1 : ∀ u : ℝ, h u ≤ 1 := by
    intro u; simp only [hh]; exact max_le zero_le_one (min_le_left _ _)
  have hhstep : ∀ u : ℝ, h u ≤ (if u ≤ θ + ε then 1 else 0) := by
    intro u
    by_cases hc : u ≤ θ + ε
    · rw [if_pos hc]; exact hhle1 u
    · rw [if_neg hc]
      rw [not_le] at hc
      have hx : (θ + ε - u) / ε ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hε0); linarith
      simp only [hh]
      rw [max_eq_left (le_trans (min_le_right _ _) hx)]
  -- Step C: Weierstrass polynomial P within δ/3 of h on [0,R].
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0:ℝ) R, |P.eval x - h x| ≤ δ / 3 := by
    have hRnn : (0:ℝ) ≤ R := le_trans hθ0 hθR
    set hC : C(Set.Icc (0:ℝ) R, ℝ) := ⟨fun x => h x, hcont.comp continuous_subtype_val⟩ with hhC
    have hmemset : hC ∈ closure
        (↑(polynomialFunctions (Set.Icc (0:ℝ) R)) : Set C(Set.Icc (0:ℝ) R, ℝ)) := by
      have hcoe : (↑((polynomialFunctions (Set.Icc (0:ℝ) R)).topologicalClosure)
            : Set C(Set.Icc (0:ℝ) R, ℝ))
          = closure ↑(polynomialFunctions (Set.Icc (0:ℝ) R)) :=
        Subalgebra.topologicalClosure_coe _
      rw [← hcoe, polynomialFunctions_closure_eq_top]
      trivial
    rw [Metric.mem_closure_iff] at hmemset
    obtain ⟨g, hgmem, hgdist⟩ := hmemset (δ / 3) hδ3
    rw [polynomialFunctions_coe, Set.mem_range] at hgmem
    obtain ⟨P, hPg⟩ := hgmem
    refine ⟨P, ?_⟩
    intro x hx
    have hxle : dist (hC ⟨x, hx⟩) (g ⟨x, hx⟩) ≤ dist hC g :=
      ContinuousMap.dist_apply_le_dist _
    have hgx : g ⟨x, hx⟩ = P.eval x := by
      rw [← hPg]
      simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply]
    have hCx : hC ⟨x, hx⟩ = h x := rfl
    rw [hCx, hgx, Real.dist_eq] at hxle
    rw [abs_sub_comm]
    exact le_of_lt (lt_of_le_of_lt hxle hgdist)
  -- Step D: assemble q = P + δ/3.
  refine ⟨P + Polynomial.C (δ / 3), ?_, ?_, ?_⟩
  · -- ≥ 1 on [0,θ]
    intro u hu
    have huR : u ∈ Set.Icc (0:ℝ) R := ⟨hu.1, le_trans hu.2 hθR⟩
    have := hP u huR
    rw [hh1 u hu.2] at this
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    rw [abs_le] at this
    linarith [this.1]
  · -- ≥ 0 on [0,R]
    intro u hu
    have := hP u hu
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    rw [abs_le] at this
    linarith [this.1, hh0 u]
  · -- expectation bound
    have hRnn : (0:ℝ) ≤ R := le_trans hθ0 hθR
    obtain ⟨CP, hCP⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_bound_of_continuousOn
      (P.continuous.continuousOn)
    have hPYint : Integrable (fun ω => P.eval (Y ω)) μ := by
      apply (integrable_const CP).mono'
        (P.continuous.measurable.comp hY).aestronglyMeasurable
      filter_upwards with ω
      exact hCP (Y ω) (hYR ω)
    have hhYint : Integrable (fun ω => h (Y ω)) μ := by
      apply (integrable_const (1:ℝ)).mono' (hcont.measurable.comp hY).aestronglyMeasurable
      filter_upwards with ω
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (hh0 (Y ω))]
      exact hhle1 (Y ω)
    have hmeasset : MeasurableSet {ω | Y ω ≤ θ + ε} := measurableSet_le hY measurable_const
    have hqeval : (fun ω => (P + Polynomial.C (δ / 3)).eval (Y ω))
        = (fun ω => P.eval (Y ω) + δ / 3) := by
      funext ω; simp [Polynomial.eval_add, Polynomial.eval_C]
    have hPle : ∫ ω, P.eval (Y ω) ∂μ ≤ (∫ ω, h (Y ω) ∂μ) + δ / 3 := by
      have hpt : (fun ω => P.eval (Y ω)) ≤ (fun ω => h (Y ω) + δ / 3) := by
        intro ω
        have := hP (Y ω) (hYR ω)
        rw [abs_le] at this
        linarith [this.2]
      calc ∫ ω, P.eval (Y ω) ∂μ
          ≤ ∫ ω, (h (Y ω) + δ / 3) ∂μ :=
            integral_mono hPYint (hhYint.add (integrable_const _)) hpt
        _ = (∫ ω, h (Y ω) ∂μ) + δ / 3 := by
            rw [integral_add hhYint (integrable_const _), integral_const]
            simp
    have hhle : ∫ ω, h (Y ω) ∂μ ≤ (μ {ω | Y ω ≤ θ + ε}).toReal := by
      have hpt : (fun ω => h (Y ω)) ≤ Set.indicator {ω | Y ω ≤ θ + ε} (1 : Ω → ℝ) := by
        intro ω
        rw [Set.indicator_apply]
        simp only [mem_setOf_eq, Pi.one_apply]
        exact hhstep (Y ω)
      calc ∫ ω, h (Y ω) ∂μ
          ≤ ∫ ω, Set.indicator {ω | Y ω ≤ θ + ε} (1 : Ω → ℝ) ω ∂μ :=
            integral_mono hhYint ((integrable_const (1:ℝ)).indicator hmeasset) hpt
        _ = (μ {ω | Y ω ≤ θ + ε}).toReal := by
            rw [integral_indicator_one hmeasset, measureReal_def]
    rw [hqeval, integral_add hPYint (integrable_const _), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    linarith [hPle, hhle, hεmeas]

end RHTower
