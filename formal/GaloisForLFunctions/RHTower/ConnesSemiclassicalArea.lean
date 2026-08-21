import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Connes' semiclassical phase-space area

Formalization of §VIII (35)-(43) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

At the end of §VIII Connes counts the quantum states of the scaling Hamiltonian `H = qp` that are
confined to `|q| ≤ Λ`, `|p| ≤ Λ`, `|H| ≤ E`, and finds that the count falls short of the free count
`(1/2π)(2E)(2 log Λ)` by exactly the leading term of the Riemann-von Mangoldt formula

  `⟨N(E)⟩ = (E/2π)(log(E/2π) - 1)`,

with a **minus** sign.  That minus sign is the whole point of the paper: the zeros appear as an
absorption spectrum (§II (C)), not an emission spectrum.

The mathematical content is the exact area of the corner region

  `D'_+ = {(P,Q) : 0 ≤ P ≤ Λ, 0 ≤ Q ≤ Λ, PQ ≤ c}`,

computed here as a genuine two-dimensional Lebesgue measure:

  `vol D'_+ = c (1 + 2 log Λ - log c)`   whenever `0 < c ≤ Λ²`.

* `connes_volume_phaseRegion` - the two-dimensional statement.
* `connes_integral_sliceLength` - the Fubini slice computation, which is literally Connes'
  "rectangle with sides `c/Λ`, `Λ`, plus the subgraph of the hyperbola from `c/Λ` to `Λ`".
* `connes_area_eqn39`, `connes_area_eqn43` - the two displayed formulas of the paper.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set intervalIntegral Real

/-- Connes' semiclassical phase-space region `D'_+` of §VIII (37)/(42): the corner of the square
`[0,Λ]²` under the hyperbola `PQ = c`. -/
def connesPhaseRegion (Λ c : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (0:ℝ) Λ ∧ z.2 ∈ Icc (0:ℝ) Λ ∧ z.1 * z.2 ≤ c}

theorem measurableSet_connesPhaseRegion (Λ c : ℝ) :
    MeasurableSet (connesPhaseRegion Λ c) := by
  have h1 : MeasurableSet {z : ℝ × ℝ | z.1 ∈ Icc (0:ℝ) Λ} :=
    measurable_fst measurableSet_Icc
  have h2 : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Icc (0:ℝ) Λ} :=
    measurable_snd measurableSet_Icc
  have h3 : MeasurableSet {z : ℝ × ℝ | z.1 * z.2 ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  have : connesPhaseRegion Λ c =
      ({z : ℝ × ℝ | z.1 ∈ Icc (0:ℝ) Λ} ∩ {z : ℝ × ℝ | z.2 ∈ Icc (0:ℝ) Λ})
        ∩ {z : ℝ × ℝ | z.1 * z.2 ≤ c} := by
    ext z; simp [connesPhaseRegion, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

/-- The vertical slice of the region above `p`. -/
theorem connesPhaseRegion_slice (Λ c : ℝ) {p : ℝ} (hp : 0 < p) :
    Prod.mk p ⁻¹' connesPhaseRegion Λ c =
      if p ≤ Λ then Icc (0:ℝ) (min Λ (c / p)) else (∅ : Set ℝ) := by
  by_cases hpΛ : p ≤ Λ
  · simp only [hpΛ, if_true]
    ext q
    simp only [connesPhaseRegion, mem_preimage, mem_setOf_eq, mem_Icc, le_min_iff]
    constructor
    · rintro ⟨-, ⟨hq0, hqΛ⟩, hprod⟩
      exact ⟨hq0, hqΛ, (le_div_iff₀' hp).mpr hprod⟩
    · rintro ⟨hq0, hqΛ, hqc⟩
      exact ⟨⟨le_of_lt hp, hpΛ⟩, ⟨hq0, hqΛ⟩, (le_div_iff₀' hp).mp hqc⟩
  · simp only [hpΛ, if_false]
    ext q
    simp only [connesPhaseRegion, mem_preimage, mem_setOf_eq, mem_Icc, mem_empty_iff_false,
      iff_false, not_and]
    rintro ⟨-, h⟩
    exact absurd h hpΛ

/-- The slice length `min Λ (c/p)` is measurable. -/
theorem measurable_connesSliceLength (Λ c : ℝ) :
    Measurable fun p : ℝ => min Λ (c / p) := by fun_prop

theorem connesSliceLength_integrableOn (Λ c : ℝ) (hΛ : 0 < Λ) (hc : 0 < c) :
    IntegrableOn (fun p : ℝ => min Λ (c / p)) (Ioc (0:ℝ) Λ) := by
  refine Integrable.mono' (g := fun _ : ℝ => Λ) ?_
    (measurable_connesSliceLength Λ c).aestronglyMeasurable ?_
  · exact integrableOn_const (hs := by simp [Real.volume_Ioc])
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := Λ))] with p hp
    have hp0 : 0 < p := hp.1
    have hnn : 0 ≤ min Λ (c / p) := le_min hΛ.le (div_nonneg hc.le hp0.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact min_le_left _ _

/-- **§VIII (39)/(43).**  The exact area of the semiclassical region.  Connes' `D'_+` is the union
of the rectangle with sides `c/Λ` and `Λ` with the subgraph of the hyperbola `PQ = c` from
`Q = c/Λ` to `Q = Λ`; its area is `c(1 + 2 log Λ - log c)`.  With `c = E/2π` this is exactly
`(2E/2π) log Λ - (E/2π)(log(E/2π) - 1)`, whose second summand is the leading term
`⟨N(E)⟩ = (E/2π)(log(E/2π) - 1)` of the Riemann-von Mangoldt counting function, entering with a
minus sign — the absorption-spectrum signature of §II (C). -/
theorem connes_integral_sliceLength (Λ c : ℝ) (hΛ : 0 < Λ) (hc : 0 < c) (hcΛ : c ≤ Λ ^ 2) :
    ∫ p in (0:ℝ)..Λ, min Λ (c / p) = c * (1 + 2 * Real.log Λ - Real.log c) := by
  set a : ℝ := c / Λ with ha
  have ha0 : 0 < a := div_pos hc hΛ
  have haΛ : a ≤ Λ := by
    rw [ha, div_le_iff₀ hΛ]; nlinarith
  have hint : IntegrableOn (fun p : ℝ => min Λ (c / p)) (Ioc (0:ℝ) Λ) :=
    connesSliceLength_integrableOn Λ c hΛ hc
  have hii1 : IntervalIntegrable (fun p : ℝ => min Λ (c / p)) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le]
    exact hint.mono_set (Ioc_subset_Ioc_right haΛ)
  have hii2 : IntervalIntegrable (fun p : ℝ => min Λ (c / p)) volume a Λ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haΛ]
    exact hint.mono_set (Ioc_subset_Ioc_left ha0.le)
  rw [← integral_add_adjacent_intervals hii1 hii2]
  have h1 : ∫ p in (0:ℝ)..a, min Λ (c / p) = Λ * a := by
    have : ∫ p in (0:ℝ)..a, min Λ (c / p) = ∫ _p in (0:ℝ)..a, Λ := by
      refine integral_congr_ae ?_
      filter_upwards with p hp
      rw [uIoc_of_le ha0.le] at hp
      have hp0 : 0 < p := hp.1
      have : Λ ≤ c / p := by
        rw [le_div_iff₀ hp0]
        have := hp.2
        calc Λ * p ≤ Λ * a := by nlinarith
          _ = c := by rw [ha]; field_simp
      exact min_eq_left this
    rw [this]
    simp [mul_comm]
  have h2 : ∫ p in a..Λ, min Λ (c / p) = c * (Real.log Λ - Real.log a) := by
    have hcongr : ∫ p in a..Λ, min Λ (c / p) = ∫ p in a..Λ, c * p⁻¹ := by
      refine integral_congr_ae ?_
      filter_upwards with p hp
      rw [uIoc_of_le haΛ] at hp
      have hp0 : 0 < p := lt_trans ha0 hp.1
      have hle : c / p ≤ Λ := by
        rw [div_le_iff₀ hp0]
        have := le_of_lt hp.1
        calc c = Λ * a := by rw [ha]; field_simp
          _ ≤ Λ * p := by nlinarith
      rw [min_eq_right hle, div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hΛ,
      Real.log_div (ne_of_gt hΛ) (ne_of_gt ha0)]
  rw [h1, h2, ha, Real.log_div (ne_of_gt hc) (ne_of_gt hΛ)]
  field_simp
  ring

/-- The exact two-dimensional Lebesgue measure of `D'_+`. -/
theorem connes_volume_phaseRegion (Λ c : ℝ) (hΛ : 0 < Λ) (hc : 0 < c) (hcΛ : c ≤ Λ ^ 2) :
    volume (connesPhaseRegion Λ c)
      = ENNReal.ofReal (c * (1 + 2 * Real.log Λ - Real.log c)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_connesPhaseRegion Λ c)]
  have hslice : ∀ᵐ p : ℝ,
      volume (Prod.mk p ⁻¹' connesPhaseRegion Λ c)
        = (Ioc (0:ℝ) Λ).indicator (fun p => ENNReal.ofReal (min Λ (c / p))) p := by
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0:ℝ)))] with p hp
    simp only [mem_compl_iff, mem_singleton_iff] at hp
    rcases lt_trichotomy p 0 with hneg | h0 | hpos
    · have : Prod.mk p ⁻¹' connesPhaseRegion Λ c = (∅ : Set ℝ) := by
        ext q
        simp only [connesPhaseRegion, mem_preimage, mem_setOf_eq, mem_Icc, mem_empty_iff_false,
          iff_false, not_and]
        rintro ⟨h, -⟩
        exact absurd h (not_le.2 hneg)
      rw [this, indicator_of_notMem (by simp [not_lt.2 hneg.le]), measure_empty]
    · exact absurd h0 hp
    · rw [connesPhaseRegion_slice Λ c hpos]
      by_cases hpΛ : p ≤ Λ
      · rw [if_pos hpΛ, Real.volume_Icc, sub_zero,
          indicator_of_mem (by exact ⟨hpos, hpΛ⟩)]
      · rw [if_neg hpΛ, measure_empty,
          indicator_of_notMem (by simp only [mem_Ioc, not_and, not_le]; intro _; exact not_le.1 hpΛ)]
  rw [lintegral_congr_ae hslice, lintegral_indicator measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (connesSliceLength_integrableOn Λ c hΛ hc) ?_]
  · rw [← integral_of_le hΛ.le, connes_integral_sliceLength Λ c hΛ hc hcΛ]
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := Λ))] with p hp
    exact le_min hΛ.le (div_nonneg hc.le hp.1.le)


/-- **§VIII (39).**  Connes' first normalization: basic character `α(x) = exp(ix)`, symplectic form
`ω = (1/2π) dp ∧ dq`, hyperbola `pq = E`. -/
theorem connes_area_eqn39 (Λ E : ℝ) (hΛ : 0 < Λ) (hE : 0 < E) (hEΛ : E ≤ Λ ^ 2) :
    (volume (connesPhaseRegion Λ E)).toReal / (2 * Real.pi)
      = E / (2 * Real.pi) + (2 * E) / (2 * Real.pi) * Real.log Λ
        - E / (2 * Real.pi) * Real.log E := by
  rw [connes_volume_phaseRegion Λ E hΛ hE hEΛ, ENNReal.toReal_ofReal]
  · ring
  · have hlog : Real.log E ≤ 2 * Real.log Λ := by
      have h := Real.log_le_log hE hEΛ
      rwa [Real.log_pow] at h
      
    nlinarith [hE.le]

/-- **§VIII (43).**  Connes' second normalization: basic character `α₀(x) = exp(-2πix)`, symplectic
form `ω = dP ∧ dQ`, hyperbola `PQ = E/2π`.  The right-hand side exhibits the leading term
`⟨N(E)⟩ = (E/2π)(log(E/2π) - 1)` of the Riemann-von Mangoldt counting function entering with a
minus sign. -/
theorem connes_area_eqn43 (Λ E : ℝ) (hΛ : 0 < Λ) (hE : 0 < E)
    (hEΛ : E / (2 * Real.pi) ≤ Λ ^ 2) :
    (volume (connesPhaseRegion Λ (E / (2 * Real.pi)))).toReal
      = (2 * E) / (2 * Real.pi) * Real.log Λ
        - E / (2 * Real.pi) * (Real.log (E / (2 * Real.pi)) - 1) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hc : (0:ℝ) < E / (2 * Real.pi) := div_pos hE hpi
  rw [connes_volume_phaseRegion Λ _ hΛ hc hEΛ, ENNReal.toReal_ofReal]
  · ring
  · have hlog : Real.log (E / (2 * Real.pi)) ≤ 2 * Real.log Λ := by
      have h := Real.log_le_log hc hEΛ
      rwa [Real.log_pow] at h
    nlinarith [hc.le]


end

end GaloisForLFunctions.RHTower
