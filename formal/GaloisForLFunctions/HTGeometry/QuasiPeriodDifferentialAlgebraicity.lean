import GaloisForLFunctions.HTGeometry.EntireFacetRealizationCodimension

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

* `differentiallyAlgebraic_of_deriv_eq_const_mul` — a constant logarithmic derivative is an
  algebraic differential equation;
* `periodic_logDeriv_of_quasiperiodic` — a quasi-period of `f` is a period of `logDeriv f`;
* **`differentiallyAlgebraic_of_quasiperiods`** — the quasi-period rank law;
* `QuasiPeriodFacetRealization` and **`facetComplementRankOne_of_quasiPeriodRealization`** — the
  facet-codimension law for constant-multiplier data: every facet still omits at most one ambient
  vertex, so scalar quasiperiodicity is no escape from the principalization theorem.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-! ### A constant logarithmic derivative is an algebraic differential equation -/

/-- A function whose derivative is a fixed constant multiple of itself satisfies the order-one
relation `y₁ − c·y₀ = 0`. -/
theorem differentiallyAlgebraic_of_deriv_eq_const_mul {f : ℂ → ℂ} {c : ℂ}
    (h : ∀ z, deriv f z = c * f z) : DifferentiallyAlgebraic f := by
  refine ⟨1, MvPolynomial.X 2 - MvPolynomial.C c * MvPolynomial.X 1, ?_, ?_⟩
  · intro hzero
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single 2 1)) hzero
    simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul,
      Finsupp.single_eq_single_iff] at hco
  · intro z
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero, h z]
    ring

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

/-- **The quasi-period rank law.**  An entire nowhere-vanishing function with two `ℚ`-independent
constant-multiplier quasi-periods is differentially algebraic.  The logarithmic derivative is
entire and doubly periodic, hence constant — by non-discreteness of the period group when the two
steps are `ℝ`-dependent, and by Liouville on the lattice when they are `ℝ`-independent — so `f`
satisfies `f' = c·f`. -/
theorem differentiallyAlgebraic_of_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    DifferentiallyAlgebraic f := by
  have hd' : Differentiable ℂ (deriv f) := fun z =>
    ((hd.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ (logDeriv f) := by
    have : Differentiable ℂ fun z => deriv f z / f z := fun z => (hd' z).div (hd z) (hne z)
    simpa [logDeriv] using this
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
  refine differentiallyAlgebraic_of_deriv_eq_const_mul (c := logDeriv f 0) (fun z => ?_)
  have hz : deriv f z / f z = logDeriv f 0 := by
    rw [← logDeriv_apply]
    exact hconst z 0
  exact (div_eq_iff (hne z)).mp hz

/-- An entire nowhere-vanishing function with two `ℚ`-independent constant-multiplier quasi-periods
is not hypertranscendental. -/
theorem not_hypertranscendental_of_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℚ ![w₁, w₂])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ¬ Hypertranscendental f :=
  fun hf => hf (differentiallyAlgebraic_of_quasiperiods hd hne hindep ha hb h₁ h₂)

/-! ### The facet-codimension law for constant-multiplier data -/

/-- **A constant-multiplier facet datum.**  `ℚ`-independent translation steps together with, for
every facet, an entire nowhere-vanishing hypertranscendental carrier which each omitted translation
reproduces up to a nonzero constant factor.  Taking all multipliers `1` recovers the invariant
datum `ScalarFacetRealization`. -/
structure QuasiPeriodFacetRealization (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers. -/
  carrier : Finset α → (ℂ → ℂ)
  /-- Each carrier is entire. -/
  carrier_entire : ∀ F ∈ facets, Differentiable ℂ (carrier F)
  /-- Each carrier is nowhere zero. -/
  carrier_ne_zero : ∀ F ∈ facets, ∀ z, carrier F z ≠ 0
  /-- Each omitted translation reproduces the carrier up to a nonzero constant multiplier. -/
  carrier_multiplier : ∀ F ∈ facets, ∀ v ∈ V \ F,
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, carrier F (z + ω v) = a * carrier F z
  /-- Each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, Hypertranscendental (carrier F)

/-- An entire nowhere-vanishing invariant datum is the constant-multiplier datum with all
multipliers `1`. -/
def ScalarFacetRealization.toQuasiPeriod {V : Finset α} {facets : Set (Finset α)}
    (R : ScalarFacetRealization V facets)
    (hentire : ∀ F ∈ facets, Differentiable ℂ (R.carrier F))
    (hne : ∀ F ∈ facets, ∀ z, R.carrier F z ≠ 0) :
    QuasiPeriodFacetRealization V facets where
  ω := R.ω
  indep := R.indep
  carrier := R.carrier
  carrier_entire := hentire
  carrier_ne_zero := hne
  carrier_multiplier := fun F hF v hv =>
    ⟨1, one_ne_zero, fun z => by rw [R.carrier_periodic F hF v hv z, one_mul]⟩
  carrier_hypertranscendental := R.carrier_hypertranscendental

/-- **Two omitted vertices kill a constant-multiplier carrier.**  Their steps are two
`ℚ`-independent quasi-periods, so the quasi-period rank law makes the carrier differentially
algebraic. -/
theorem no_quasiPeriodFacetRealization_of_two_omitted {V : Finset α} {facets : Set (Finset α)}
    (R : QuasiPeriodFacetRealization V facets) {F : Finset α} (hF : F ∈ facets) {u v : α}
    (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False := by
  obtain ⟨a, ha, hau⟩ := R.carrier_multiplier F hF u hu
  obtain ⟨b, hb, hbv⟩ := R.carrier_multiplier F hF v hv
  have hindep : LinearIndependent ℚ ![R.ω u, R.ω v] := by
    rw [← comp_cons_two]
    exact R.indep.comp _ (injective_cons_two huv)
  exact R.carrier_hypertranscendental F hF
    (differentiallyAlgebraic_of_quasiperiods (R.carrier_entire F hF) (R.carrier_ne_zero F hF)
      hindep ha hb hau hbv)

/-- **The facet-codimension law for constant-multiplier data.**  Every facet omits at most one
ambient vertex: scalar quasiperiodicity with constant multipliers supplies no extra analytic
direction. -/
theorem facetComplementRankOne_of_quasiPeriodRealization {V : Finset α} {facets : Set (Finset α)}
    (R : QuasiPeriodFacetRealization V facets) (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  exact no_quasiPeriodFacetRealization_of_two_omitted R hF hu hv huv

end GaloisForLFunctions.HTGeometry
