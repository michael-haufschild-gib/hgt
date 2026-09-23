import GaloisForLFunctions.HTGeometry.QuasiPeriodLatticeZeros
import GaloisForLFunctions.HTGeometry.QuasiPeriodDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

/-!
# An entire function with constant multipliers over a lattice has no zeros

A single zero would propagate to the whole lattice coset, giving `(2N+1)²` zeros in a disc whose
radius is linear in `N` (`card_latticeBox`, `eq_zero_of_mem_latticeBox`).  But the multiplier
relations bound the function by `K exp(c‖z‖)` (`exists_exp_growth_bound_of_quasiperiods`), and
Jensen's inequality bounds the zero count of a function of exponential type linearly in the radius
(`RHTower.exponentialType_zeroCount_linear`).  Quadratic beats linear, so there is no zero.

With the zeros excluded, the logarithmic derivative is entire and the quasi-period rank law applies
in the lattice case as well.  Together with the real-dependent case this removes every hypothesis
beyond entirety:

* **`ne_zero_of_quasiperiods_lattice`** — no zeros;
* **`differentiallyAlgebraic_of_quasiperiods_entire`** — an entire function reproduced by two
  `ℚ`-independent translations up to constant multipliers is differentially algebraic.  No
  nonvanishing hypothesis, no nonzero-multiplier hypothesis, no elliptic input.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

/-- **A quasi-periodic entire function with `ℝ`-independent steps has no zeros.**  A zero would
produce quadratically many zeros in a disc of radius `r`, while a function of exponential type has
only linearly many. -/
theorem ne_zero_of_quasiperiods_lattice {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z)
    {c : ℂ} (hc : f c ≠ 0) : ∀ z, f z ≠ 0 := by
  classical
  intro z₀ hz₀
  obtain ⟨K₀, A, hK₀, hA, hgrow⟩ :=
    exists_exp_growth_bound_of_quasiperiods hd.continuous hindep ha hb h₁ h₂
  have hCmax : ∀ z : ℂ, ‖f z‖ ≤ max K₀ 1 * Real.exp (A * ‖z‖) := fun z =>
    le_trans (hgrow z)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  obtain ⟨K, hK, hlinear⟩ :=
    RHTower.exponentialType_zeroCount_linear hd hc hA (le_max_right K₀ 1) hCmax
  have hS0 : (0 : ℝ) ≤ ‖w₁‖ + ‖w₂‖ := by positivity
  have hD0 : (0 : ℝ) ≤ ‖z₀ - c‖ := norm_nonneg _
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (K * (‖w₁‖ + ‖w₂‖) + K * (2 + ‖z₀ - c‖)) 1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hNgt : K * (‖w₁‖ + ‖w₂‖) + K * (2 + ‖z₀ - c‖) < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hball : ∀ u ∈ latticeBox z₀ w₁ w₂ N,
      id u ∈ closedBall c (1 + ‖z₀ - c‖ + (N : ℝ) * (‖w₁‖ + ‖w₂‖)) := by
    intro u hu
    rw [id, mem_closedBall_iff_norm]
    have hb' := norm_sub_le_of_mem_latticeBox (c := c) hu
    linarith
  have hzero : ∀ u ∈ latticeBox z₀ w₁ w₂ N, f (id u) = 0 :=
    fun u hu => eq_zero_of_mem_latticeBox ha hb h₁ h₂ hz₀ N hu
  have hcount := RHTower.card_le_sum_divisor_of_finite_zeros hd hc
    (latticeBox z₀ w₁ w₂ N) id (Set.injOn_id _) hball hzero
  rw [card_latticeBox hindep z₀ N] at hcount
  have hr1 : (1 : ℝ) ≤ 1 + ‖z₀ - c‖ + (N : ℝ) * (‖w₁‖ + ‖w₂‖) := by
    have hns : (0 : ℝ) ≤ (N : ℝ) * (‖w₁‖ + ‖w₂‖) := by positivity
    linarith
  have hup := hlinear (1 + ‖z₀ - c‖ + (N : ℝ) * (‖w₁‖ + ‖w₂‖)) hr1
  have hlow : (((2 * N + 1) ^ (2 : ℕ) : ℕ) : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor f
        (closedBall c (1 + ‖z₀ - c‖ + (N : ℝ) * (‖w₁‖ + ‖w₂‖)))) u) : ℝ) := by
    exact_mod_cast hcount
  have hcomb : (((2 * N + 1) ^ (2 : ℕ) : ℕ) : ℝ)
      ≤ K * (1 + (1 + ‖z₀ - c‖ + (N : ℝ) * (‖w₁‖ + ‖w₂‖))) := le_trans hlow hup
  push_cast at hcomb
  have hKD : K * (2 + ‖z₀ - c‖) < (N : ℝ) := by nlinarith
  have hKS : K * (‖w₁‖ + ‖w₂‖) < (N : ℝ) := by nlinarith
  have hprod : K * (‖w₁‖ + ‖w₂‖) * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hKS.le (by linarith)
  nlinarith

/-- **Sharp form of the entire quasi-period law.**  The function satisfies `f' = c·f` with a
*constant* coefficient, on both branches: `ℝ`-dependent steps give a one-dimensional
derivation-invariant span, `ℝ`-independent steps give a zero-free `f` with constant logarithmic
derivative. -/
theorem exists_deriv_eq_const_mul_of_quasiperiods_entire {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ∃ c : ℂ, ∀ z, deriv f z = c * f z := by
  by_cases hdep : LinearIndependent ℝ ![w₁, w₂]
  · by_cases hf0 : ∀ z, f z = 0
    · refine ⟨0, fun z => ?_⟩
      have hfe : f = fun _ => (0 : ℂ) := funext hf0
      subst hfe
      simp
    obtain ⟨c₀, hc₀⟩ := not_forall.mp hf0
    have ha : a ≠ 0 := by
      intro h
      apply hc₀
      have hval := h₁ (c₀ - w₁)
      rw [show c₀ - w₁ + w₁ = c₀ by ring, h, zero_mul] at hval
      exact hval
    have hb : b ≠ 0 := by
      intro h
      apply hc₀
      have hval := h₂ (c₀ - w₂)
      rw [show c₀ - w₂ + w₂ = c₀ by ring, h, zero_mul] at hval
      exact hval
    exact exists_deriv_eq_const_mul_of_quasiperiods hd
      (ne_zero_of_quasiperiods_lattice hd hdep ha hb h₁ h₂ hc₀) hindepQ ha hb h₁ h₂
  · refine exists_deriv_eq_const_mul_of_quasiperiods_of_not_discrete hd ![w₁, w₂] ![a, b]
      (fun i z => ?_)
      (not_discrete_intSpan_fin_two_of_not_linearIndependent_real ![w₁, w₂] hindepQ hdep)
    fin_cases i
    · simpa using h₁ z
    · simpa using h₂ z

/-- **The scalar quasi-period rank law for entire functions, unconditionally.**  An entire function
reproduced by two `ℚ`-independent translations up to constant multipliers is differentially
algebraic — it satisfies a first-order equation with constant coefficient. -/
theorem differentiallyAlgebraic_of_quasiperiods_entire {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    DifferentiallyAlgebraic f := by
  obtain ⟨c, hc⟩ := exists_deriv_eq_const_mul_of_quasiperiods_entire hd hindepQ h₁ h₂
  refine differentiallyAlgebraic_of_firstOrder_poly_ode (Polynomial.C c) 1 one_ne_zero (fun z => ?_)
  simpa using hc z

/-- **The normal form.**  Such a function is `f 0 · exp (c·z)`: in particular it is nowhere zero
unless it vanishes identically, and its multipliers are `exp (c·w₁)` and `exp (c·w₂)`. -/
theorem eq_mul_exp_of_quasiperiods_entire {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ∃ c : ℂ, ∀ z, f z = f 0 * Complex.exp (c * z) := by
  obtain ⟨c, hc⟩ := exists_deriv_eq_const_mul_of_quasiperiods_entire hd hindepQ h₁ h₂
  refine ⟨c, fun z => ?_⟩
  have hgd : ∀ u : ℂ, HasDerivAt (fun v : ℂ => f v * Complex.exp (-(c * v)))
      (deriv f u * Complex.exp (-(c * u)) + f u * (Complex.exp (-(c * u)) * (-c))) u := by
    intro u
    have hfu : HasDerivAt f (deriv f u) u := (hd u).hasDerivAt
    have hev : HasDerivAt (fun v : ℂ => Complex.exp (-(c * v)))
        (Complex.exp (-(c * u)) * (-c)) u := by
      have hbase := (((hasDerivAt_id u).const_mul c).neg).cexp
      simpa using hbase
    exact hfu.mul hev
  have hdiff : Differentiable ℂ fun v : ℂ => f v * Complex.exp (-(c * v)) :=
    fun u => (hgd u).differentiableAt
  have hzero : ∀ u : ℂ, deriv (fun v : ℂ => f v * Complex.exp (-(c * v))) u = 0 := by
    intro u
    rw [(hgd u).deriv, hc u]
    ring
  have hconst := is_const_of_deriv_eq_zero hdiff hzero z 0
  simp only [mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [Complex.exp_neg, ← div_eq_mul_inv, div_eq_iff (Complex.exp_ne_zero (c * z))] at hconst
  exact hconst

/-- An entire function with two `ℚ`-independent constant-multiplier quasi-periods is never
hypertranscendental. -/
theorem not_hypertranscendental_of_quasiperiods_entire {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {w₁ w₂ a b : ℂ} (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ¬ Hypertranscendental f :=
  fun hf => hf (differentiallyAlgebraic_of_quasiperiods_entire hd hindepQ h₁ h₂)


/-! ### The facet-codimension law for constant-multiplier data, unconditionally -/

/-- **Two omitted vertices kill a constant-multiplier carrier.**  Their steps are two
`ℚ`-independent quasi-periods of an entire carrier, so the unconditional quasi-period rank law makes
it differentially algebraic. -/
theorem no_quasiPeriodFacetRealization_of_two_omitted {α : Type*} [DecidableEq α] {V : Finset α}
    {facets : Set (Finset α)} (R : QuasiPeriodFacetRealization V facets) {F : Finset α}
    (hF : F ∈ facets) {u v : α} (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False := by
  obtain ⟨a, hau⟩ := R.carrier_multiplier F hF u hu
  obtain ⟨b, hbv⟩ := R.carrier_multiplier F hF v hv
  have hindep : LinearIndependent ℚ ![R.ω u, R.ω v] := by
    rw [← comp_cons_two]
    exact R.indep.comp _ (injective_cons_two huv)
  exact R.carrier_hypertranscendental F hF
    (differentiallyAlgebraic_of_quasiperiods_entire (R.carrier_entire F hF) hindep hau hbv)

/-- **The facet-codimension law for constant-multiplier data.**  Every facet omits at most one
ambient vertex.  Unconditional: neither nonvanishing of the carriers, nor invertibility of the
multipliers, nor any elliptic input is assumed. -/
theorem facetComplementRankOne_of_quasiPeriodRealization {α : Type*} [DecidableEq α] {V : Finset α}
    {facets : Set (Finset α)} (R : QuasiPeriodFacetRealization V facets)
    (hsub : ∀ F ∈ facets, F ⊆ V) : FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  exact no_quasiPeriodFacetRealization_of_two_omitted R hF hu hv huv

end GaloisForLFunctions.HTGeometry
