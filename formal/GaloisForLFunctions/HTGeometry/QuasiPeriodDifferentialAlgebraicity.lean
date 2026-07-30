import GaloisForLFunctions.HTGeometry.EntireFacetRealizationCodimension
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.SmallTranslationDerivInvariance

/-!
# Constant multipliers supply no analytic freedom

Weakening invariance to *quasi*-invariance with constant multipliers,

`f (z + ω₁) = a · f z`,  `f (z + ω₂) = b · f z`,  `a, b ≠ 0`,

does not weaken the period-rank law.  The multipliers cancel in the logarithmic derivative
`logDeriv f = f' / f`, which therefore has `ω₁` and `ω₂` as genuine periods, and the two-step
rigidity already proved for periods applies to it: for an entire nowhere-vanishing `f` it is
constant, whether the two steps are `ℝ`-dependent (non-discrete period group) or `ℝ`-independent
(Liouville on the lattice).  A constant logarithmic derivative is the order-one relation
`y₁ − c·y₀ = 0`, so `f` itself is differentially algebraic.

* `periodic_logDeriv_of_quasiperiodic` — a quasi-period of `f` is a period of `logDeriv f`;
* **`differentiallyAlgebraic_of_quasiperiods`** — the quasi-period rank law;
* `eq_zero_iff_of_mem_span_range` and `ne_zero_of_quasiperiods_realDependent` — when the two steps
  are `ℝ`-dependent such a carrier has no zeros at all: the zero set is invariant under a
  non-discrete group, so one zero would be an accumulation point of zeros and the identity theorem
  would kill the function;
* `differentiallyAlgebraic_of_quasiperiods_realDependent` — on that branch the law needs neither
  nonvanishing nor nonzero multipliers, being the one-dimensional case of
  `differentiallyAlgebraic_of_quasiperiods_of_not_discrete`;
* `QuasiPeriodFacetRealization` — the constant-multiplier facet datum, with
  `ScalarFacetRealization.toQuasiPeriod` exhibiting the invariant datum as the case "all multipliers
  `1`".  The facet-codimension law it obeys is proved in `QuasiPeriodLatticeNoZeros`, where the
  lattice branch is closed.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-! ### Quasi-periods are periods of the logarithmic derivative -/

/-- **The multiplier cancels in `f' / f`.**  A constant-multiplier quasi-period of a differentiable
`f` is a genuine period of `logDeriv f`. -/
theorem periodic_logDeriv_of_quasiperiodic {f : ℂ → ℂ} {w a : ℂ} (ha : a ≠ 0)
    (hd : Differentiable ℂ f) (h : ∀ z, f (z + w) = a * f z) :
    Function.Periodic (logDeriv f) w := by
  have hshift : ∀ z, deriv f (z + w) = a * deriv f z := by
    intro z
    have hfun : (fun u : ℂ => f (u + w)) = fun u => a * f u := funext h
    have h1 : deriv (fun u : ℂ => f (u + w)) z = deriv f (z + w) := deriv_comp_add_const f w z
    have h2 : deriv (fun u : ℂ => a * f u) z = a * deriv f z := deriv_const_mul a (hd z)
    rw [← h1, hfun, h2]
  intro z
  rw [logDeriv_apply, logDeriv_apply, hshift z, h z, mul_div_mul_left _ _ ha]

/-! ### The quasi-period rank law -/

/-- **The quasi-period rank law in its sharp form.**  An entire nowhere-vanishing function with two
`ℚ`-independent constant-multiplier quasi-periods satisfies a first-order equation `f' = c·f` with a
*constant* coefficient.  The logarithmic derivative is entire and doubly periodic, hence constant —
by non-discreteness of the period group when the two steps are `ℝ`-dependent, and by Liouville on
the lattice when they are `ℝ`-independent. -/
theorem exists_deriv_eq_const_mul_of_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ∃ c : ℂ, ∀ z, deriv f z = c * f z := by
  have hd' : Differentiable ℂ (deriv f) := fun z =>
    ((hd.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ (logDeriv f) := by
    have : Differentiable ℂ fun z => deriv f z / f z := fun z => (hd' z).div (hd z) (hne z)
    simpa [logDeriv] using! this
  have hspan : ∀ p ∈ Submodule.span ℤ (Set.range ![w₁, w₂]),
      Function.Periodic (logDeriv f) p := by
    refine periodic_of_mem_span_range ![w₁, w₂] (fun i => ?_)
    fin_cases i
    · exact periodic_logDeriv_of_quasiperiodic ha hd h₁
    · exact periodic_logDeriv_of_quasiperiodic hb hd h₂
  have hconst : ∀ x y, logDeriv f x = logDeriv f y := by
    by_cases hdep : LinearIndependent ℝ ![w₁, w₂]
    · refine const_of_lattice_periodic_differentiable ⟨w₁, w₂, hdep⟩ hL (fun p hp => hspan p ?_)
      rw [range_cons_two]
      exact hp
    · exact meromorphicNF_constant_of_rankTwo_realDependent_periods (logDeriv f)
        (fun z _ => (hL.analyticAt z).meromorphicNFAt) ![w₁, w₂] hindep hdep hspan
  refine ⟨logDeriv f 0, fun z => ?_⟩
  have hz : deriv f z / f z = logDeriv f 0 := by
    rw [← logDeriv_apply]
    exact hconst z 0
  exact (div_eq_iff (hne z)).mp hz

/-- **The quasi-period rank law.**  An entire nowhere-vanishing function with two `ℚ`-independent
constant-multiplier quasi-periods is differentially algebraic: it satisfies the first-order equation
`f' = c·f` with a constant coefficient. -/
theorem differentiallyAlgebraic_of_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    DifferentiallyAlgebraic f := by
  obtain ⟨c, hc⟩ := exists_deriv_eq_const_mul_of_quasiperiods hd hne hindep ha hb h₁ h₂
  refine differentiallyAlgebraic_of_firstOrder_poly_ode (Polynomial.C c) 1 one_ne_zero (fun z => ?_)
  simpa using hc z

/-- An entire nowhere-vanishing function with two `ℚ`-independent constant-multiplier quasi-periods
is not hypertranscendental. -/
theorem not_hypertranscendental_of_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ¬ Hypertranscendental f :=
  fun hf => hf (differentiallyAlgebraic_of_quasiperiods hd hne hindep ha hb h₁ h₂)

/-! ### Real-dependent steps make the nonvanishing hypothesis automatic -/

/-- **The zero set is invariant under the whole integer span of the steps.**  A nonzero multiplier
cannot create or destroy a zero, and the property is stable under sums and integer multiples. -/
theorem eq_zero_iff_of_mem_span_range {ι : Type*} {f : ℂ → ℂ} (w : ι → ℂ)
    (h : ∀ i, ∃ c : ℂ, c ≠ 0 ∧ ∀ z, f (z + w i) = c * f z) :
    ∀ p ∈ Submodule.span ℤ (Set.range w), ∀ z, (f (z + p) = 0 ↔ f z = 0) := by
  have hadd : ∀ q r : ℂ, (∀ z, f (z + q) = 0 ↔ f z = 0) → (∀ z, f (z + r) = 0 ↔ f z = 0) →
      ∀ z, (f (z + (q + r)) = 0 ↔ f z = 0) := by
    intro q r hq hr z
    have hz : z + (q + r) = (z + r) + q := by ring
    rw [hz, hq (z + r), hr z]
  have hneg : ∀ q : ℂ, (∀ z, f (z + q) = 0 ↔ f z = 0) → ∀ z, (f (z + -q) = 0 ↔ f z = 0) := by
    intro q hq z
    have hz : (z + -q) + q = z := by ring
    have hshift := hq (z + -q)
    rw [hz] at hshift
    exact hshift.symm
  have hzsmul : ∀ (a : ℤ) (q : ℂ), (∀ z, f (z + q) = 0 ↔ f z = 0) →
      ∀ z, (f (z + a • q) = 0 ↔ f z = 0) := by
    intro a q hq
    induction a using Int.induction_on with
    | zero => intro z; simp
    | succ n ih =>
        intro z
        have hs : ((n : ℤ) + 1) • q = (n : ℤ) • q + q := by rw [add_smul, one_smul]
        rw [hs]
        exact hadd _ _ ih hq z
    | pred n ih =>
        intro z
        have hs : (-(n : ℤ) - 1) • q = (-(n : ℤ)) • q + -q := by rw [sub_smul, one_smul]; ring
        rw [hs]
        exact hadd _ _ ih (hneg q hq) z
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨c, hc, hcw⟩ := h i
      intro z
      rw [hcw z]
      simp [hc]
  | zero => intro z; simp
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hzsmul a x hx

/-- **An entire quasi-periodic function with `ℝ`-dependent steps has no zeros at all.**  The zero set
is invariant under the integer span of the two steps, which is not discrete, so a single zero would
be an accumulation point of zeros and the identity theorem would make the function vanish
identically. -/
theorem ne_zero_of_quasiperiods_realDependent {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (hdep : ¬ LinearIndependent ℝ ![w₁, w₂]) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z)
    {z₁ : ℂ} (hz₁ : f z₁ ≠ 0) : ∀ z, f z ≠ 0 := by
  intro z₀ hz₀
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_rankTwo_realDependent_periods ![w₁, w₂]
    hindep hdep
  have hspan := eq_zero_iff_of_mem_span_range ![w₁, w₂] (fun i => by
    fin_cases i
    · exact ⟨a, ha, h₁⟩
    · exact ⟨b, hb, h₂⟩)
  have hzero : ∀ n, f (z₀ + p n) = 0 := fun n => (hspan (p n) (hp_mem n) z₀).mpr hz₀
  have hpz : Filter.Tendsto (fun n => z₀ + p n) Filter.atTop (nhdsWithin z₀ {z₀}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using (tendsto_const_nhds.add hp_zero :
      Filter.Tendsto (fun n => z₀ + p n) Filter.atTop (nhds (z₀ + 0))), ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp [hp_ne n]
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 :=
    hpz.frequently (Filter.Eventually.of_forall hzero).frequently
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hd.analyticAt z
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z₀) hfreq
  exact hz₁ (hall (Set.mem_univ z₁))

/-- **The quasi-period rank law with `ℝ`-dependent steps needs neither a nonvanishing hypothesis nor
nonzero multipliers.**  The `ℝ`-dependent step group is not discrete, so the span of `f` is a
one-dimensional space of entire functions stable under arbitrarily small translations, hence stable
under differentiation, and the constant-coefficient annihilator is immediate. -/
theorem differentiallyAlgebraic_of_quasiperiods_realDependent {f : ℂ → ℂ}
    (hd : Differentiable ℂ f) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (hdep : ¬ LinearIndependent ℝ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    DifferentiallyAlgebraic f :=
  differentiallyAlgebraic_of_quasiperiods_of_not_discrete hd ![w₁, w₂] ![a, b]
    (fun i z => by
      fin_cases i
      · simpa using h₁ z
      · simpa using h₂ z)
    (not_discrete_intSpan_fin_two_of_not_linearIndependent_real ![w₁, w₂] hindep hdep)

/-- An entire function with two `ℚ`-independent, `ℝ`-dependent constant-multiplier quasi-periods is
not hypertranscendental. -/
theorem not_hypertranscendental_of_quasiperiods_realDependent {f : ℂ → ℂ}
    (hd : Differentiable ℂ f) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (hdep : ¬ LinearIndependent ℝ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ¬ Hypertranscendental f :=
  fun hf => hf (differentiallyAlgebraic_of_quasiperiods_realDependent hd hindep hdep h₁ h₂)

/-! ### The facet-codimension law for constant-multiplier data -/

/-- **A constant-multiplier facet datum.**  `ℚ`-independent translation steps together with, for
every facet, an entire hypertranscendental carrier which each omitted translation reproduces up to a
constant factor.  Taking all multipliers `1` recovers the invariant datum
`ScalarFacetRealization`. -/
structure QuasiPeriodFacetRealization (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers. -/
  carrier : Finset α → (ℂ → ℂ)
  /-- Each carrier is entire. -/
  carrier_entire : ∀ F ∈ facets, Differentiable ℂ (carrier F)
  /-- Each omitted translation reproduces the carrier up to a constant multiplier. -/
  carrier_multiplier : ∀ F ∈ facets, ∀ v ∈ V \ F,
    ∃ a : ℂ, ∀ z, carrier F (z + ω v) = a * carrier F z
  /-- Each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, Hypertranscendental (carrier F)

/-- An entire invariant datum is the constant-multiplier datum with all multipliers `1`. -/
def ScalarFacetRealization.toQuasiPeriod {V : Finset α} {facets : Set (Finset α)}
    (R : ScalarFacetRealization V facets)
    (hentire : ∀ F ∈ facets, Differentiable ℂ (R.carrier F)) :
    QuasiPeriodFacetRealization V facets where
  ω := R.ω
  indep := R.indep
  carrier := R.carrier
  carrier_entire := hentire
  carrier_multiplier := fun F hF v hv =>
    ⟨1, fun z => by rw [R.carrier_periodic F hF v hv z, one_mul]⟩
  carrier_hypertranscendental := R.carrier_hypertranscendental

end GaloisForLFunctions.HTGeometry
