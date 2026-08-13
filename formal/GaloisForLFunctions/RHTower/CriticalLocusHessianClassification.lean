import Mathlib
import GaloisForLFunctions.RHTower.CriticalLocusQuadrupleEvenness
import GaloisForLFunctions.RHTower.CrystallineShadowTransversality
import GaloisForLFunctions.RHTower.SuzukiInteriorExcursionSpectralTurningPoint

/-!
# Hessian classification of spectral-type criteria at the critical locus

The relative value of a spectral test `F` on one off-line splitting quadruple is
`φ_γ(t) = ∑_{quadruple} F − 2F(1/2+iγ) − 2F(1/2−iγ)`.  This module certifies the
second-order theory of these functionals at the critical locus `t = 0`:

* **exact separation** — a finite multi-splitting's value is the sum of its per-ordinate
  relative quadruple values, with no cross-terms, because summing a function over a
  multiset join is additive;
* **the weight** — the second central jet of the quadruple functional equals
  `2(F''(1/2+iγ) + F''(1/2−iγ))`, and under the reality symmetry `F(s̄) = conj (F s)` it
  is the real weight `4 Re F''(1/2+iγ)`;
* **per-zero necessity** — a detector (a test whose real part is locally maximal at the
  undisplaced configuration along one real splitting parameter) has nonpositive weight
  at that ordinate;
* **mixture/determination** — the Hessian of a scaled multi-splitting is the diagonal
  form `∑_j w_j t_j²`, and two spectral tests are second-order equivalent at every real
  ordinate exactly when their real weight functions agree;
* **composite criteria** — on a one-parameter stratum through the critical locus every
  first derivative vanishes, so a smooth composite `g(φ₁,…,φₙ)` has stratum second
  derivative `∑_i ∂_i g · φ_i''(0)`: the finite-rank chain-rule correction dies on
  strata and per-zero necessity survives composition;
* **the shadow pairing** — for the explicit-formula line kernel
  `F_h(ρ) = ∫ h(x) e^{(ρ−1/2)x} dx` of a continuous compactly supported test `h`, the
  relative quadruple value is exactly `∫ h(x)·4cos(γx)(cosh(tx)−1) dx`, so the
  deformation shadow is the absolutely continuous measure with the transversality
  density of `shadowDensity`.

The conjugation bridge `deriv F (s̄) = conj (deriv F s)` for reality-symmetric tests is
proved from the slope characterization of the derivative and iterated to second order.
-/

namespace RHTower

noncomputable section

open Complex MeasureTheory ComplexConjugate Filter

/-! ## The relative quadruple functional and exact separation -/

/-- The relative quadruple functional `φ_γ(t)`: the value of the splitting quadruple minus
its on-line collapse (two conjugate double zeros). -/
def relativeQuadrupleValue (F : ℂ → ℂ) (γ t : ℂ) : ℂ :=
  criticalQuadrupleSum F γ t - criticalQuadrupleSum F γ 0

theorem relativeQuadrupleValue_zero (F : ℂ → ℂ) (γ : ℂ) :
    relativeQuadrupleValue F γ 0 = 0 := sub_self _

/-- Evenness of the relative quadruple functional in the displacement. -/
theorem relativeQuadrupleValue_neg (F : ℂ → ℂ) (γ t : ℂ) :
    relativeQuadrupleValue F γ (-t) = relativeQuadrupleValue F γ t := by
  unfold relativeQuadrupleValue
  rw [criticalQuadrupleSum_neg]

/-- The scalar quadruple functional is the sum of `F` over the quadruple multiset. -/
theorem criticalQuadrupleSum_eq_map_sum (F : ℂ → ℂ) (γ t : ℂ) :
    ((criticalQuadruple γ t).map F).sum = criticalQuadrupleSum F γ t := by
  simp only [criticalQuadruple, criticalQuadrupleSum, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-- A finite multi-splitting configuration: the multiset join of its quadruples. -/
def multiQuadruple {ι : Type*} (s : Finset ι) (gam t : ι → ℂ) : Multiset ℂ :=
  ∑ j ∈ s, criticalQuadruple (gam j) (t j)

/-- Multi-splitting evenness: flipping every displacement sign leaves the configuration
unchanged as a multiset. -/
theorem multiQuadruple_neg {ι : Type*} (s : Finset ι) (gam t : ι → ℂ) :
    multiQuadruple s gam (fun j => -(t j)) = multiQuadruple s gam t := by
  unfold multiQuadruple
  exact Finset.sum_congr rfl fun j _ => criticalQuadruple_neg (gam j) (t j)

/-- **Exact separation, absolute form.**  Summing a spectral test over a finite
multi-splitting is the sum of the per-ordinate quadruple functionals — exactly, not merely
to second order.  Cross-terms between distinct ordinates are identically zero. -/
theorem multiQuadruple_map_sum {ι : Type*} (s : Finset ι) (gam t : ι → ℂ) (F : ℂ → ℂ) :
    ((multiQuadruple s gam t).map F).sum = ∑ j ∈ s, criticalQuadrupleSum F (gam j) (t j) := by
  classical
  unfold multiQuadruple
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih,
        criticalQuadrupleSum_eq_map_sum]

/-- **Exact separation, relative form.**  The relative value of a finite multi-splitting
against its on-line collapse is the sum of the per-ordinate relative quadruple values. -/
theorem multiQuadruple_relative_separation {ι : Type*} (s : Finset ι) (gam t : ι → ℂ)
    (F : ℂ → ℂ) :
    ((multiQuadruple s gam t).map F).sum - ((multiQuadruple s gam (fun _ => 0)).map F).sum
      = ∑ j ∈ s, relativeQuadrupleValue F (gam j) (t j) := by
  rw [multiQuadruple_map_sum, multiQuadruple_map_sum, ← Finset.sum_sub_distrib]
  rfl

/-! ## Analyticity of the quadruple functional -/

/-- The quadruple functional of a test analytic at the two conjugate line points is
analytic at the critical locus. -/
theorem analyticAt_criticalQuadrupleSum (F : ℂ → ℂ) (γ : ℂ)
    (h₊ : AnalyticAt ℂ F (1 / 2 + γ * I)) (h₋ : AnalyticAt ℂ F (1 / 2 - γ * I)) :
    AnalyticAt ℂ (criticalQuadrupleSum F γ) 0 := by
  have a₁ : AnalyticAt ℂ (fun t : ℂ => F (t + (1 / 2 + γ * I))) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => t + (1 / 2 + γ * I)) 0 :=
      analyticAt_id.add analyticAt_const
    have houter : AnalyticAt ℂ F ((fun t : ℂ => t + (1 / 2 + γ * I)) 0) := by simpa using h₊
    simpa [Function.comp_def] using houter.comp inner
  have a₂ : AnalyticAt ℂ (fun t : ℂ => F ((1 / 2 + γ * I) - t)) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => (1 / 2 + γ * I) - t) 0 :=
      analyticAt_const.sub analyticAt_id
    have houter : AnalyticAt ℂ F ((fun t : ℂ => (1 / 2 + γ * I) - t) 0) := by simpa using h₊
    simpa [Function.comp_def] using houter.comp inner
  have a₃ : AnalyticAt ℂ (fun t : ℂ => F (t + (1 / 2 - γ * I))) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => t + (1 / 2 - γ * I)) 0 :=
      analyticAt_id.add analyticAt_const
    have houter : AnalyticAt ℂ F ((fun t : ℂ => t + (1 / 2 - γ * I)) 0) := by simpa using h₋
    simpa [Function.comp_def] using houter.comp inner
  have a₄ : AnalyticAt ℂ (fun t : ℂ => F ((1 / 2 - γ * I) - t)) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => (1 / 2 - γ * I) - t) 0 :=
      analyticAt_const.sub analyticAt_id
    have houter : AnalyticAt ℂ F ((fun t : ℂ => (1 / 2 - γ * I) - t) 0) := by simpa using h₋
    simpa [Function.comp_def] using houter.comp inner
  exact ((a₁.add a₂).add a₃).add a₄

/-! ## The weight: the second central jet -/

private theorem iteratedDeriv_two_eq_deriv_deriv (f : ℂ → ℂ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem iteratedDeriv_two_shift (F : ℂ → ℂ) (c : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => F (t + c)) 0 = iteratedDeriv 2 F c := by
  simpa using congrFun (iteratedDeriv_comp_add_const 2 F c) 0

private theorem iteratedDeriv_two_reflect (F : ℂ → ℂ) (c : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => F (c - t)) 0 = iteratedDeriv 2 F c := by
  have h1 : (fun t : ℂ => F (c - t)) = fun t : ℂ => F (-t + c) := by
    funext t; exact congrArg F (by ring)
  have h4 := iteratedDeriv_comp_neg 2 (fun z : ℂ => F (z + c)) 0
  have h5 : iteratedDeriv 2 (fun t : ℂ => F (-t + c)) 0
      = ((-1 : ℂ)) ^ 2 • iteratedDeriv 2 (fun z : ℂ => F (z + c)) 0 := by
    simpa using h4
  rw [h1, h5]
  have h6 := congrFun (iteratedDeriv_comp_add_const 2 F c) 0
  simp only [zero_add] at h6
  rw [h6]
  simp [neg_one_sq]

/-- **The weight (Θ2(ii)).**  The second central jet of the quadruple functional of a test
analytic at the two conjugate line points is twice the sum of the second derivatives
there. -/
theorem iteratedDeriv_two_criticalQuadrupleSum (F : ℂ → ℂ) (γ : ℂ)
    (h₊ : AnalyticAt ℂ F (1 / 2 + γ * I)) (h₋ : AnalyticAt ℂ F (1 / 2 - γ * I)) :
    iteratedDeriv 2 (criticalQuadrupleSum F γ) 0
      = 2 * (iteratedDeriv 2 F (1 / 2 + γ * I) + iteratedDeriv 2 F (1 / 2 - γ * I)) := by
  have a₁ : AnalyticAt ℂ (fun t : ℂ => F (t + (1 / 2 + γ * I))) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => t + (1 / 2 + γ * I)) 0 :=
      analyticAt_id.add analyticAt_const
    have houter : AnalyticAt ℂ F ((fun t : ℂ => t + (1 / 2 + γ * I)) 0) := by simpa using h₊
    simpa [Function.comp_def] using houter.comp inner
  have a₂ : AnalyticAt ℂ (fun t : ℂ => F ((1 / 2 + γ * I) - t)) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => (1 / 2 + γ * I) - t) 0 :=
      analyticAt_const.sub analyticAt_id
    have houter : AnalyticAt ℂ F ((fun t : ℂ => (1 / 2 + γ * I) - t) 0) := by simpa using h₊
    simpa [Function.comp_def] using houter.comp inner
  have a₃ : AnalyticAt ℂ (fun t : ℂ => F (t + (1 / 2 - γ * I))) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => t + (1 / 2 - γ * I)) 0 :=
      analyticAt_id.add analyticAt_const
    have houter : AnalyticAt ℂ F ((fun t : ℂ => t + (1 / 2 - γ * I)) 0) := by simpa using h₋
    simpa [Function.comp_def] using houter.comp inner
  have a₄ : AnalyticAt ℂ (fun t : ℂ => F ((1 / 2 - γ * I) - t)) 0 := by
    have inner : AnalyticAt ℂ (fun t : ℂ => (1 / 2 - γ * I) - t) 0 :=
      analyticAt_const.sub analyticAt_id
    have houter : AnalyticAt ℂ F ((fun t : ℂ => (1 / 2 - γ * I) - t) 0) := by simpa using h₋
    simpa [Function.comp_def] using houter.comp inner
  have hfun : criticalQuadrupleSum F γ
      = ((fun t : ℂ => F (t + (1 / 2 + γ * I))) + fun t : ℂ => F ((1 / 2 + γ * I) - t))
        + ((fun t : ℂ => F (t + (1 / 2 - γ * I))) + fun t : ℂ => F ((1 / 2 - γ * I) - t)) := by
    funext t
    simp only [criticalQuadrupleSum, Pi.add_apply]
    ring
  have c₁ : ContDiffAt ℂ 2 (fun t : ℂ => F (t + (1 / 2 + γ * I))) 0 := a₁.contDiffAt
  have c₂ : ContDiffAt ℂ 2 (fun t : ℂ => F ((1 / 2 + γ * I) - t)) 0 := a₂.contDiffAt
  have c₃ : ContDiffAt ℂ 2 (fun t : ℂ => F (t + (1 / 2 - γ * I))) 0 := a₃.contDiffAt
  have c₄ : ContDiffAt ℂ 2 (fun t : ℂ => F ((1 / 2 - γ * I) - t)) 0 := a₄.contDiffAt
  rw [hfun, iteratedDeriv_add (c₁.add c₂) (c₃.add c₄), iteratedDeriv_add c₁ c₂,
    iteratedDeriv_add c₃ c₄, iteratedDeriv_two_shift, iteratedDeriv_two_reflect,
    iteratedDeriv_two_shift, iteratedDeriv_two_reflect]
  ring

/-! ## The conjugation bridge for reality-symmetric tests -/

/-- Reality-symmetric derivative bridge: if `F(w̄) = conj (F w)` holds near `z` and `F`
has derivative `d` at `z`, then `F` has derivative `d̄` at `z̄`. -/
theorem hasDerivAt_conj_of_eventually_conj {F : ℂ → ℂ} {z d : ℂ}
    (hsym : ∀ᶠ w in nhds z, F (conj w) = conj (F w))
    (h : HasDerivAt F d z) : HasDerivAt F (conj d) (conj z) := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  have hconj : Filter.Tendsto (fun w : ℂ => conj w)
      (nhdsWithin (conj z) {conj z}ᶜ) (nhdsWithin z {z}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Filter.Tendsto (fun w : ℂ => conj w) (nhds (conj z)) (nhds z) := by
        simpa using Complex.continuous_conj.tendsto (conj z)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      intro hcontra
      apply hw
      have := congrArg (fun u : ℂ => conj u) hcontra
      simpa using this
  have hmain : Filter.Tendsto (fun w : ℂ => conj (slope F z (conj w)))
      (nhdsWithin (conj z) {conj z}ᶜ) (nhds (conj d)) :=
    (Complex.continuous_conj.tendsto d).comp (h.comp hconj)
  refine hmain.congr' ?_
  have hz : F (conj z) = conj (F z) := hsym.self_of_nhds
  have hpull : ∀ᶠ w in nhdsWithin (conj z) {conj z}ᶜ, F (conj (conj w)) = conj (F (conj w)) :=
    (hconj.mono_right nhdsWithin_le_nhds).eventually hsym
  filter_upwards [hpull] with w hw
  rw [Complex.conj_conj] at hw
  rw [slope_def_field, slope_def_field, map_div₀, map_sub, map_sub, ← hw, hz,
    Complex.conj_conj, Complex.conj_conj]

/-- Value form of the conjugation bridge for an analytic point. -/
theorem deriv_conj_eq_of_eventually_conj {F : ℂ → ℂ} {z : ℂ}
    (hsym : ∀ᶠ w in nhds z, F (conj w) = conj (F w)) (hA : AnalyticAt ℂ F z) :
    deriv F (conj z) = conj (deriv F z) :=
  (hasDerivAt_conj_of_eventually_conj hsym hA.differentiableAt.hasDerivAt).deriv

/-- Analyticity transfers to the conjugate point under the reality symmetry. -/
theorem analyticAt_conj_point {F : ℂ → ℂ} {z : ℂ}
    (hκ : ∀ s, F (conj s) = conj (F s)) (hA : AnalyticAt ℂ F z) :
    AnalyticAt ℂ F (conj z) := by
  obtain ⟨U, hUopen, hUmem, hU⟩ : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, AnalyticAt ℂ F w := by
    have hev := hA.eventually_analyticAt
    rw [Filter.eventually_iff_exists_mem] at hev
    obtain ⟨v, hv, hva⟩ := hev
    obtain ⟨U, hUv, hUopen, hzU⟩ := mem_nhds_iff.mp hv
    exact ⟨U, hUopen, hzU, fun w hw => hva w (hUv hw)⟩
  have hUconj : IsOpen ((fun w : ℂ => conj w) ⁻¹' U) :=
    hUopen.preimage Complex.continuous_conj
  have hdiff : DifferentiableOn ℂ F ((fun w : ℂ => conj w) ⁻¹' U) := by
    intro w hw
    have hw' : AnalyticAt ℂ F (conj w) := hU _ hw
    have hd : HasDerivAt F (conj (deriv F (conj w))) (conj (conj w)) :=
      hasDerivAt_conj_of_eventually_conj (Filter.Eventually.of_forall hκ)
        hw'.differentiableAt.hasDerivAt
    rw [Complex.conj_conj] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hmem : conj z ∈ (fun w : ℂ => conj w) ⁻¹' U := by
    simpa [Complex.conj_conj] using hUmem
  exact hdiff.analyticAt (hUconj.mem_nhds hmem)

/-- Second-order conjugation bridge at an analytic point of a reality-symmetric test. -/
theorem iteratedDeriv_two_conj_eq {F : ℂ → ℂ} {z : ℂ}
    (hκ : ∀ s, F (conj s) = conj (F s)) (hA : AnalyticAt ℂ F z) :
    iteratedDeriv 2 F (conj z) = conj (iteratedDeriv 2 F z) := by
  have hder : ∀ᶠ w in nhds z, deriv F (conj w) = conj (deriv F w) := by
    filter_upwards [hA.eventually_analyticAt] with w hw
    exact deriv_conj_eq_of_eventually_conj (Filter.Eventually.of_forall hκ) hw
  have h2 : HasDerivAt (deriv F) (conj (deriv (deriv F) z)) (conj z) :=
    hasDerivAt_conj_of_eventually_conj hder hA.deriv.differentiableAt.hasDerivAt
  rw [iteratedDeriv_two_eq_deriv_deriv, iteratedDeriv_two_eq_deriv_deriv]
  exact h2.deriv

/-- **The real weight.**  For a reality-symmetric test analytic at `1/2 + iγ` with `γ`
real, the second central jet of the quadruple functional is the real number
`4 Re F''(1/2 + iγ)` — the weight `w_F(γ)` of the Hessian classification. -/
theorem iteratedDeriv_two_criticalQuadrupleSum_re (F : ℂ → ℂ) (γ : ℝ)
    (hκ : ∀ s, F (conj s) = conj (F s))
    (h₊ : AnalyticAt ℂ F (1 / 2 + (γ : ℂ) * I)) :
    iteratedDeriv 2 (criticalQuadrupleSum F (γ : ℂ)) 0
      = ((4 * (iteratedDeriv 2 F (1 / 2 + (γ : ℂ) * I)).re : ℝ) : ℂ) := by
  have hpt : ((1 : ℂ) / 2 - (γ : ℂ) * I) = conj (1 / 2 + (γ : ℂ) * I) := by
    simp [Complex.ext_iff]
  have h₋ : AnalyticAt ℂ F (1 / 2 - (γ : ℂ) * I) := by
    rw [hpt]; exact analyticAt_conj_point hκ h₊
  rw [iteratedDeriv_two_criticalQuadrupleSum F (γ : ℂ) h₊ h₋]
  have hconj2 : iteratedDeriv 2 F (1 / 2 - (γ : ℂ) * I)
      = conj (iteratedDeriv 2 F (1 / 2 + (γ : ℂ) * I)) := by
    rw [hpt]; exact iteratedDeriv_two_conj_eq hκ h₊
  rw [hconj2, Complex.add_conj]
  push_cast
  ring

/-! ## Per-zero necessity -/

/-- **Per-zero necessity (Θ2(iii)).**  If the real part of the quadruple functional is
locally maximal at the undisplaced configuration along the real splitting parameter — the
detector property on one admissible splitting — then the second central jet has
nonpositive real part.  Detection is per-zero of necessity. -/
theorem re_iteratedDeriv_two_nonpos_of_detector (F : ℂ → ℂ) (γ : ℂ)
    (h₊ : AnalyticAt ℂ F (1 / 2 + γ * I)) (h₋ : AnalyticAt ℂ F (1 / 2 - γ * I))
    (hdet : ∀ᶠ x : ℝ in nhds 0,
      (criticalQuadrupleSum F γ (x : ℂ)).re ≤ (criticalQuadrupleSum F γ 0).re) :
    (iteratedDeriv 2 (criticalQuadrupleSum F γ) 0).re ≤ 0 := by
  set Φ := criticalQuadrupleSum F γ with hΦdef
  have hA : AnalyticAt ℂ Φ 0 := analyticAt_criticalQuadrupleSum F γ h₊ h₋
  set g : ℝ → ℝ := fun x => (Φ (x : ℂ)).re with hgdef
  have hofReal : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds 0) (nhds 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have hEvℝ : ∀ᶠ x : ℝ in nhds 0, AnalyticAt ℂ Φ (x : ℂ) :=
    hofReal.eventually hA.eventually_analyticAt
  have hgderiv : ∀ᶠ x : ℝ in nhds 0, HasDerivAt g (deriv Φ (x : ℂ)).re x := by
    filter_upwards [hEvℝ] with x hx
    exact hx.differentiableAt.hasDerivAt.real_of_complex
  have hderivg_eq : deriv g =ᶠ[nhds (0 : ℝ)] fun x => (deriv Φ (x : ℂ)).re := by
    filter_upwards [hgderiv] with x hx using hx.deriv
  have hΦ' : AnalyticAt ℂ (deriv Φ) 0 := hA.deriv
  have h2c : HasDerivAt (deriv Φ) (deriv (deriv Φ) 0) (((0 : ℝ) : ℂ)) := by
    simpa using hΦ'.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => (deriv Φ (x : ℂ)).re) (deriv (deriv Φ) 0).re 0 :=
    h2c.real_of_complex
  have hgg : deriv (deriv g) 0 = (deriv (deriv Φ) 0).re := by
    rw [hderivg_eq.deriv_eq]
    exact h2.deriv
  have hmax : IsLocalMax g 0 := by
    filter_upwards [hdet] with x hx
    simpa [hgdef] using hx
  have hcont : ContinuousAt g 0 := by
    have hΦc : ContinuousAt (fun x : ℝ => Φ (x : ℂ)) 0 := by
      have := hA.continuousAt.comp (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ)))
      simpa [Function.comp_def] using this
    exact Complex.continuous_re.continuousAt.comp hΦc
  have hsuzuki := suzukiSecondDeriv_nonpos_of_isLocalMax hmax hcont
  rw [hgg] at hsuzuki
  rw [iteratedDeriv_two_eq_deriv_deriv]
  exact hsuzuki

/-- **Per-zero necessity, weight form.**  A reality-symmetric detector has nonpositive real
weight `Re F''(1/2 + iγ) ≤ 0` at every real ordinate where it penalizes the splitting. -/
theorem weight_nonpos_of_detector (F : ℂ → ℂ) (γ : ℝ)
    (hκ : ∀ s, F (conj s) = conj (F s))
    (h₊ : AnalyticAt ℂ F (1 / 2 + (γ : ℂ) * I))
    (hdet : ∀ᶠ x : ℝ in nhds 0,
      (criticalQuadrupleSum F (γ : ℂ) (x : ℂ)).re ≤ (criticalQuadrupleSum F (γ : ℂ) 0).re) :
    (iteratedDeriv 2 F (1 / 2 + (γ : ℂ) * I)).re ≤ 0 := by
  have hpt : ((1 : ℂ) / 2 - (γ : ℂ) * I) = conj (1 / 2 + (γ : ℂ) * I) := by
    simp [Complex.ext_iff]
  have h₋ : AnalyticAt ℂ F (1 / 2 - (γ : ℂ) * I) := by
    rw [hpt]; exact analyticAt_conj_point hκ h₊
  have hnec := re_iteratedDeriv_two_nonpos_of_detector F (γ : ℂ) h₊ h₋ hdet
  rw [iteratedDeriv_two_criticalQuadrupleSum_re F γ hκ h₊] at hnec
  simp only [Complex.ofReal_re] at hnec
  linarith

/-! ## Mixture and determination -/

private theorem iteratedDeriv_two_sub_const (Φ : ℂ → ℂ) (c : ℂ) :
    iteratedDeriv 2 (fun τ : ℂ => Φ τ - c) 0 = iteratedDeriv 2 Φ 0 := by
  rw [iteratedDeriv_two_eq_deriv_deriv, iteratedDeriv_two_eq_deriv_deriv]
  have h1 : deriv (fun τ : ℂ => Φ τ - c) = deriv Φ := by
    funext τ
    exact deriv_sub_const c
  rw [h1]

private theorem iteratedDeriv_two_scaled (Φ : ℂ → ℂ) (hA : AnalyticAt ℂ Φ 0) (c : ℂ) :
    iteratedDeriv 2 (fun τ : ℂ => Φ (c * τ)) 0 = c ^ 2 * iteratedDeriv 2 Φ 0 := by
  have hmul : Filter.Tendsto (fun τ : ℂ => c * τ) (nhds 0) (nhds 0) := by
    have := (continuous_const.mul continuous_id (M₀ := ℂ)).tendsto 0
    simpa using this
  have hEv : ∀ᶠ τ : ℂ in nhds 0, AnalyticAt ℂ Φ (c * τ) :=
    hmul.eventually hA.eventually_analyticAt
  have hd1 : ∀ᶠ τ : ℂ in nhds 0,
      HasDerivAt (fun τ : ℂ => Φ (c * τ)) (c * deriv Φ (c * τ)) τ := by
    filter_upwards [hEv] with τ hτ
    have hinner : HasDerivAt (fun τ : ℂ => c * τ) c τ := by
      simpa using (hasDerivAt_id τ).const_mul c
    have houter : HasDerivAt Φ (deriv Φ (c * τ)) (c * τ) := hτ.differentiableAt.hasDerivAt
    have := houter.comp τ hinner
    simpa [Function.comp_def, mul_comm] using this
  have hderiv_eq : deriv (fun τ : ℂ => Φ (c * τ)) =ᶠ[nhds (0 : ℂ)]
      fun τ => c * deriv Φ (c * τ) := by
    filter_upwards [hd1] with τ hτ using hτ.deriv
  have hΦ' : AnalyticAt ℂ (deriv Φ) 0 := hA.deriv
  have hsecond : HasDerivAt (fun τ : ℂ => c * deriv Φ (c * τ))
      (c * (c * deriv (deriv Φ) 0)) 0 := by
    have hinner : HasDerivAt (fun τ : ℂ => c * τ) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
    have houter : HasDerivAt (deriv Φ) (deriv (deriv Φ) 0) ((fun τ : ℂ => c * τ) 0) := by
      simpa using hΦ'.differentiableAt.hasDerivAt
    have hchain := houter.comp (0 : ℂ) hinner
    have : HasDerivAt (fun τ : ℂ => deriv Φ (c * τ)) (c * deriv (deriv Φ) 0) 0 := by
      simpa [Function.comp_def, mul_comm] using hchain
    exact this.const_mul c
  rw [iteratedDeriv_two_eq_deriv_deriv, hderiv_eq.deriv_eq, hsecond.deriv,
    iteratedDeriv_two_eq_deriv_deriv]
  ring

/-- **The diagonal Hessian (Θ2(iv), mixture form).**  Along the scaled multi-splitting
stratum `τ ↦ (t_j τ)_j` the second central jet is the diagonal quadratic form
`∑_j t_j² · w_j` in the per-ordinate weights: the Hessian of a spectral-type criterion at
the critical locus is an element of the simplicial cone spanned by the single-ordinate
forms. -/
theorem iteratedDeriv_two_multiSplitting {ι : Type*} (s : Finset ι) (F : ℂ → ℂ)
    (gam t : ι → ℂ)
    (h₊ : ∀ j ∈ s, AnalyticAt ℂ F (1 / 2 + gam j * I))
    (h₋ : ∀ j ∈ s, AnalyticAt ℂ F (1 / 2 - gam j * I)) :
    iteratedDeriv 2 (fun τ : ℂ => ∑ j ∈ s, relativeQuadrupleValue F (gam j) (t j * τ)) 0
      = ∑ j ∈ s, (t j) ^ 2 * iteratedDeriv 2 (criticalQuadrupleSum F (gam j)) 0 := by
  classical
  have hterm : ∀ j ∈ s, ContDiffAt ℂ 2
      (fun τ : ℂ => relativeQuadrupleValue F (gam j) (t j * τ)) 0 := by
    intro j hj
    have hAj : AnalyticAt ℂ (criticalQuadrupleSum F (gam j)) 0 :=
      analyticAt_criticalQuadrupleSum F (gam j) (h₊ j hj) (h₋ j hj)
    have hinner : AnalyticAt ℂ (fun τ : ℂ => t j * τ) 0 :=
      analyticAt_const.mul analyticAt_id
    have hcomp : AnalyticAt ℂ (fun τ : ℂ => criticalQuadrupleSum F (gam j) (t j * τ)) 0 := by
      have houter : AnalyticAt ℂ (criticalQuadrupleSum F (gam j))
          ((fun τ : ℂ => t j * τ) 0) := by simpa using hAj
      simpa [Function.comp_def] using houter.comp hinner
    exact (hcomp.sub analyticAt_const).contDiffAt
  have hfun : (fun τ : ℂ => ∑ j ∈ s, relativeQuadrupleValue F (gam j) (t j * τ))
      = ∑ j ∈ s, fun τ : ℂ => relativeQuadrupleValue F (gam j) (t j * τ) := by
    funext τ
    rw [Finset.sum_apply]
  rw [hfun, iteratedDeriv_sum hterm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hAj : AnalyticAt ℂ (criticalQuadrupleSum F (gam j)) 0 :=
    analyticAt_criticalQuadrupleSum F (gam j) (h₊ j hj) (h₋ j hj)
  have hsub : (fun τ : ℂ => relativeQuadrupleValue F (gam j) (t j * τ))
      = fun τ : ℂ => (fun σ : ℂ => criticalQuadrupleSum F (gam j) (t j * σ)) τ
          - criticalQuadrupleSum F (gam j) 0 := rfl
  rw [hsub, iteratedDeriv_two_sub_const, iteratedDeriv_two_scaled _ hAj]

/-- **Determination (Θ2(iv)).**  Two reality-symmetric spectral tests are second-order
equivalent at every real ordinate exactly when their real weight functions agree: the
second-order jet at the critical locus determines the weight and nothing else. -/
theorem secondOrder_jets_eq_iff_weights_eq (F G : ℂ → ℂ)
    (hκF : ∀ s, F (conj s) = conj (F s)) (hκG : ∀ s, G (conj s) = conj (G s))
    (hF : ∀ γ : ℝ, AnalyticAt ℂ F (1 / 2 + (γ : ℂ) * I))
    (hG : ∀ γ : ℝ, AnalyticAt ℂ G (1 / 2 + (γ : ℂ) * I)) :
    (∀ γ : ℝ, iteratedDeriv 2 (criticalQuadrupleSum F (γ : ℂ)) 0
        = iteratedDeriv 2 (criticalQuadrupleSum G (γ : ℂ)) 0)
      ↔ ∀ γ : ℝ, (iteratedDeriv 2 F (1 / 2 + (γ : ℂ) * I)).re
        = (iteratedDeriv 2 G (1 / 2 + (γ : ℂ) * I)).re := by
  constructor
  · intro hjets γ
    have h := hjets γ
    rw [iteratedDeriv_two_criticalQuadrupleSum_re F γ hκF (hF γ),
      iteratedDeriv_two_criticalQuadrupleSum_re G γ hκG (hG γ)] at h
    have := Complex.ofReal_inj.mp h
    linarith
  · intro hweights γ
    rw [iteratedDeriv_two_criticalQuadrupleSum_re F γ hκF (hF γ),
      iteratedDeriv_two_criticalQuadrupleSum_re G γ hκG (hG γ), hweights γ]

/-! ## Composite criteria -/

private theorem pi_single_eq_smul {n : ℕ} (i : Fin n) (c : ℝ) :
    Pi.single (M := fun _ : Fin n => ℝ) i c = c • Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- **Composite criteria (Θ2(v)).**  On a one-parameter stratum through the critical locus
every component first derivative vanishes, so the second derivative of a smooth composite
is the gradient-weighted sum of the component second jets: the finite-rank Hessian
correction of the chain rule dies on strata. -/
theorem deriv_deriv_comp_of_first_derivs_zero {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (φ : ℝ → Fin n → ℝ)
    (hg : ContDiffAt ℝ 2 g (φ 0))
    (hφ : ∀ i, AnalyticAt ℝ (fun y => φ y i) 0)
    (hcrit : ∀ i, deriv (fun y => φ y i) 0 = 0) :
    deriv (deriv (fun x => g (φ x))) 0
      = ∑ i, fderiv ℝ g (φ 0) (Pi.single i 1) * deriv (deriv (fun y => φ y i)) 0 := by
  classical
  -- eventual joint differentiability of the components
  have hφev : ∀ᶠ x in nhds (0 : ℝ), ∀ i,
      HasDerivAt (fun y => φ y i) (deriv (fun y => φ y i) x) x := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(hφ i).eventually_analyticAt] with x hx
    exact hx.differentiableAt.hasDerivAt
  -- eventual differentiability of g along the curve
  have hφcont : ContinuousAt φ 0 := by
    rw [continuousAt_pi]
    intro i
    exact (hφ i).continuousAt
  have hgev : ∀ᶠ x in nhds (0 : ℝ), DifferentiableAt ℝ g (φ x) := by
    have hgev' : ∀ᶠ w in nhds (φ 0), DifferentiableAt ℝ g w := by
      filter_upwards [hg.eventually (by norm_num)] with w hw
      exact hw.differentiableAt (by norm_num)
    exact hφcont.tendsto.eventually hgev'
  -- the first-derivative formula near the critical point
  have hψ : ∀ᶠ x in nhds (0 : ℝ), HasDerivAt (fun y => g (φ y))
      (∑ i, deriv (fun y => φ y i) x * fderiv ℝ g (φ x) (Pi.single i 1)) x := by
    filter_upwards [hφev, hgev] with x hx hgx
    have hcurve : HasDerivAt φ (fun i => deriv (fun y => φ y i) x) x :=
      hasDerivAt_pi.mpr fun i => hx i
    have hchain := hgx.hasFDerivAt.comp_hasDerivAt x hcurve
    have hexpand : fderiv ℝ g (φ x) (fun i => deriv (fun y => φ y i) x)
        = ∑ i, deriv (fun y => φ y i) x * fderiv ℝ g (φ x) (Pi.single i 1) := by
      have hbasis : (fun i => deriv (fun y => φ y i) x)
          = ∑ i, Pi.single (M := fun _ : Fin n => ℝ) i (deriv (fun y => φ y i) x) :=
        (Finset.univ_sum_single _).symm
      rw [hbasis, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pi_single_eq_smul, map_smul, smul_eq_mul]
    rw [← hexpand]
    exact hchain
  have hψeq : deriv (fun y => g (φ y)) =ᶠ[nhds (0 : ℝ)]
      fun x => ∑ i, deriv (fun y => φ y i) x * fderiv ℝ g (φ x) (Pi.single i 1) := by
    filter_upwards [hψ] with x hx using hx.deriv
  -- differentiate the formula at the critical point
  have hPdiff : ∀ i : Fin n,
      DifferentiableAt ℝ (fun x => fderiv ℝ g (φ x) (Pi.single i 1)) 0 := by
    intro i
    have hfder : DifferentiableAt ℝ (fderiv ℝ g) (φ 0) :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hφ0 : DifferentiableAt ℝ φ 0 :=
      (hasDerivAt_pi.mpr fun i => (hφ i).differentiableAt.hasDerivAt).differentiableAt
    have happly : DifferentiableAt ℝ
        (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (fderiv ℝ g (φ 0)) :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).differentiableAt
    exact (happly.comp _ (hfder.comp _ hφ0))
  have hD2 : ∀ i : Fin n, DifferentiableAt ℝ (deriv (fun y => φ y i)) 0 :=
    fun i => (hφ i).deriv.differentiableAt
  have hterm : ∀ i ∈ Finset.univ, HasDerivAt
      (fun x => deriv (fun y => φ y i) x * fderiv ℝ g (φ x) (Pi.single i 1))
      (deriv (deriv (fun y => φ y i)) 0 * fderiv ℝ g (φ 0) (Pi.single i 1)) 0 := by
    intro i _
    have hDi : HasDerivAt (deriv (fun y => φ y i)) (deriv (deriv (fun y => φ y i)) 0) 0 :=
      (hD2 i).hasDerivAt
    have hPi : HasDerivAt (fun x => fderiv ℝ g (φ x) (Pi.single i 1))
        (deriv (fun x => fderiv ℝ g (φ x) (Pi.single i 1)) 0) 0 :=
      (hPdiff i).hasDerivAt
    have := hDi.mul hPi
    rw [hcrit i] at this
    simpa using this
  have hsum := HasDerivAt.sum hterm
  rw [hψeq.deriv_eq, hsum.deriv]

/-- **Composite per-zero necessity.**  A smooth composite of stratum functionals that is
locally maximal at the critical locus has nonpositive gradient-weighted total weight:
per-zero necessity survives composition with smooth outer functions. -/
theorem composite_detector_necessity {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (φ : ℝ → Fin n → ℝ)
    (hg : ContDiffAt ℝ 2 g (φ 0))
    (hφ : ∀ i, AnalyticAt ℝ (fun y => φ y i) 0)
    (hcrit : ∀ i, deriv (fun y => φ y i) 0 = 0)
    (hmax : IsLocalMax (fun x => g (φ x)) 0) :
    ∑ i, fderiv ℝ g (φ 0) (Pi.single i 1) * deriv (deriv (fun y => φ y i)) 0 ≤ 0 := by
  rw [← deriv_deriv_comp_of_first_derivs_zero g φ hg hφ hcrit]
  refine suzukiSecondDeriv_nonpos_of_isLocalMax hmax ?_
  have hφcont : ContinuousAt φ 0 := by
    rw [continuousAt_pi]
    intro i
    exact (hφ i).continuousAt
  exact hg.continuousAt.comp hφcont

/-! ## The shadow pairing: the explicit-formula kernel of the deformation -/

/-- The explicit-formula line kernel of a test `h`: `F_h(ρ) = ∫ h(x) e^{(ρ−1/2)x} dx`. -/
def lineTestTransform (h : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  ∫ x : ℝ, h x * Complex.exp ((ρ - 1 / 2) * x)

theorem lineTestTransform_shift (h : ℝ → ℂ) (a : ℂ) :
    lineTestTransform h (1 / 2 + a) = ∫ x : ℝ, h x * Complex.exp (a * x) := by
  unfold lineTestTransform
  congr 1
  funext x
  congr 2
  ring

theorem integrable_lineTest_kernel {h : ℝ → ℂ} (hc : Continuous h)
    (hs : HasCompactSupport h) (a : ℂ) :
    Integrable (fun x : ℝ => h x * Complex.exp (a * x)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hs.mul_right
  exact hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

private theorem exp_line_pair (γ x : ℂ) :
    Complex.exp ((γ * I) * x) + Complex.exp ((-(γ * I)) * x) = 2 * Complex.cos (γ * x) := by
  rw [Complex.cos]
  ring_nf

/-- **The shadow of one splitting (Θ3.1).**  For the explicit-formula line kernel of a
continuous compactly supported test, the relative quadruple value is the integral of the
test against the transversality density `4cos(γx)(cosh(tx)−1)`: the deformation shadow is
absolutely continuous with real-analytic density, never atomic. -/
theorem relativeQuadrupleValue_lineTestTransform (h : ℝ → ℂ) (hc : Continuous h)
    (hs : HasCompactSupport h) (γ t : ℂ) :
    relativeQuadrupleValue (lineTestTransform h) γ t
      = ∫ x : ℝ, h x * (4 * Complex.cos (γ * ↑x) * (Complex.cosh (t * ↑x) - 1)) := by
  have I₀ : ∀ a : ℂ, Integrable (fun x : ℝ => h x * Complex.exp (a * ↑x)) :=
    fun a => integrable_lineTest_kernel hc hs a
  unfold relativeQuadrupleValue criticalQuadrupleSum
  rw [show t + (1 / 2 + γ * I) = 1 / 2 + (t + γ * I) by ring, lineTestTransform_shift,
    show (1 / 2 + γ * I) - t = 1 / 2 + (-t + γ * I) by ring, lineTestTransform_shift,
    show t + (1 / 2 - γ * I) = 1 / 2 + (t - γ * I) by ring, lineTestTransform_shift,
    show (1 / 2 - γ * I) - t = 1 / 2 + (-t - γ * I) by ring, lineTestTransform_shift,
    show (0 : ℂ) + (1 / 2 + γ * I) = 1 / 2 + γ * I by ring,
    show (1 / 2 + γ * I) - (0 : ℂ) = 1 / 2 + γ * I by ring,
    show (0 : ℂ) + (1 / 2 - γ * I) = 1 / 2 + -(γ * I) by ring,
    show (1 / 2 - γ * I) - (0 : ℂ) = 1 / 2 + -(γ * I) by ring,
    show (1 : ℂ) / 2 + γ * I = 1 / 2 + γ * I from rfl, lineTestTransform_shift,
    lineTestTransform_shift]
  rw [← integral_add (I₀ (t + γ * I)) (I₀ (-t + γ * I)),
    ← integral_add ((I₀ (t + γ * I)).add (I₀ (-t + γ * I))) (I₀ (t - γ * I)),
    ← integral_add (((I₀ (t + γ * I)).add (I₀ (-t + γ * I))).add (I₀ (t - γ * I)))
      (I₀ (-t - γ * I)),
    ← integral_add (I₀ (γ * I)) (I₀ (γ * I)),
    ← integral_add ((I₀ (γ * I)).add (I₀ (γ * I))) (I₀ (-(γ * I))),
    ← integral_add (((I₀ (γ * I)).add (I₀ (γ * I))).add (I₀ (-(γ * I)))) (I₀ (-(γ * I))),
    ← integral_sub
      ((((I₀ (t + γ * I)).add (I₀ (-t + γ * I))).add (I₀ (t - γ * I))).add (I₀ (-t - γ * I)))
      ((((I₀ (γ * I)).add (I₀ (γ * I))).add (I₀ (-(γ * I)))).add (I₀ (-(γ * I))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hq := quadrupleExp_sub_undisplaced γ t (x : ℂ)
  have hp := exp_line_pair γ (x : ℂ)
  linear_combination (h x) * hq - 2 * (h x) * hp

/-- **Θ3.1 over the reals.**  The single-splitting shadow of a real test is the real
integral against the density `4cos(γx)(cosh(tx)−1)`. -/
theorem relativeQuadrupleValue_lineTestTransform_real (h : ℝ → ℝ) (hc : Continuous h)
    (hs : HasCompactSupport h) (γ t : ℝ) :
    relativeQuadrupleValue (lineTestTransform fun x => (h x : ℂ)) (γ : ℂ) (t : ℂ)
      = ((∫ x : ℝ, h x * (4 * Real.cos (γ * x) * (Real.cosh (t * x) - 1)) : ℝ) : ℂ) := by
  have hcC : Continuous fun x : ℝ => (h x : ℂ) := Complex.continuous_ofReal.comp hc
  have hsC : HasCompactSupport fun x : ℝ => (h x : ℂ) :=
    hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  rw [relativeQuadrupleValue_lineTestTransform _ hcC hsC (γ : ℂ) (t : ℂ)]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  push_cast [← Complex.ofReal_cos, ← Complex.ofReal_cosh]
  ring_nf
  norm_cast

/-- **The multi-splitting shadow is the transversality density (Θ3.1 + Θ3.2 pairing).**
The total shadow of a finite multi-splitting of a real test is the integral of the test
against `shadowDensity`, the density whose nonvanishing is finite crystalline
transversality. -/
theorem multiSplitting_shadow_integral {ι : Type*} [Fintype ι] (h : ℝ → ℝ)
    (hc : Continuous h) (hs : HasCompactSupport h) (gam t : ι → ℝ) :
    ∑ j, relativeQuadrupleValue (lineTestTransform fun x => (h x : ℂ)) (gam j : ℂ) (t j : ℂ)
      = ((∫ x : ℝ, h x * shadowDensity gam t x : ℝ) : ℂ) := by
  classical
  have hterm : ∀ j : ι,
      relativeQuadrupleValue (lineTestTransform fun x => (h x : ℂ)) (gam j : ℂ) (t j : ℂ)
        = ((∫ x : ℝ, h x * (4 * Real.cos (gam j * x) * (Real.cosh (t j * x) - 1)) : ℝ) : ℂ) :=
    fun j => relativeQuadrupleValue_lineTestTransform_real h hc hs (gam j) (t j)
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Complex.ofReal_sum]
  congr 1
  have hint : ∀ j ∈ Finset.univ, Integrable
      (fun x : ℝ => h x * (4 * Real.cos (gam j * x) * (Real.cosh (t j * x) - 1))) := by
    intro j _
    refine Continuous.integrable_of_hasCompactSupport ?_ hs.mul_right
    exact hc.mul (by fun_prop)
  rw [← MeasureTheory.integral_finset_sum Finset.univ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold shadowDensity
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

end RHTower
