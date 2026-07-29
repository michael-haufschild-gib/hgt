/-
# The field→function reduction for Böttcher transcendence (natural-boundary route, algebra side)

The connected-case input `Transcendental (RatFunc ℂ) (phiMero c)` (the `hGtr` of
`q62_independence_connected_of_inputs`) is reduced here to a purely **function-level** statement: that no
nonzero `q ∈ ℂ[z][Y]` makes `z ↦ q(z, φ_c(z))` vanish on `U`. The geometry (natural boundary at the
Julia set) refutes that function-level relation; this file does the algebra connecting it to the
field-theoretic `Transcendental`.

Two bricks:
* `eval₂_polyToAnalytic_val` — the bivariate eval-germ identity: evaluating `q ∈ ℂ[z][Y]` at the analytic
  germ `phiAnalytic c` (over the polynomial base) has representative function `z ↦ q.eval₂ (eval-at-z)
  (φ_c z) = Σ_i (q.coeff i)(z)·φ_c(z)ⁱ`. Pure `Polynomial.hom_eval₂` threading through the subring
  inclusion and the germ coercion.
* `phiMero_transcendental_of_no_function_relation` — the reduction itself. `IsFractionRing.isAlgebraic_iff`
  turns `IsAlgebraic (RatFunc ℂ)` into `IsAlgebraic (ℂ[X])` (no manual denominator clearing — a `ℂ[X]`
  -algebraic witness *is* an element of `ℂ[z][Y]`); the eval-germ identity plus `meroField` faithfulness
  then make that witness a vanishing function, contradicting the hypothesis.

The output `(fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z))` is exactly the polynomial
relation `Σ_i (q.coeff i)(z)·φ_c(z)ⁱ` that `AlgebraicBranch.exists_analyticAt_branch_poly` /
`branch_unique_poly` consume (`eval₂` over `q.support` = the `aeval`-sum, since over `ℂ` `aeval = eval`).
-/
import GaloisForLFunctions.Bottcher.Q62Field
import GaloisForLFunctions.Bottcher.ZeroSet
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Integral

open Polynomial Filter Topology Set

namespace Bottcher

variable {U : Set ℂ}

/-- **Bivariate eval-germ identity.** Evaluating `q ∈ ℂ[z][Y]` at the analytic germ `phiAnalytic c hU`
(over the polynomial base ring `ℂ[z]` via `polyToAnalytic`) yields the analytic germ whose representative
is the genuine function `z ↦ q.eval₂ (eval-at-z) (φ_c z) = Σ_i (q.coeff i)(z)·φ_c(z)ⁱ`. Proof: thread
`Polynomial.hom_eval₂` through the subring inclusion `(analyticSubring U).subtype`, the pointwise
`Pi.evalRingHom`, and the germ coercion `Germ.coeRingHom`. -/
theorem eval₂_polyToAnalytic_val (c : ℂ) (hU : U ⊆ escapeOpen c) (q : Polynomial (Polynomial ℂ)) :
    (q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) : analyticSubring U).val
      = (↑(fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) : Germ (𝓟 U) ℂ) := by
  rw [show ((q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) : analyticSubring U).val)
        = (analyticSubring U).subtype (q.eval₂ (polyToAnalytic U) (phiAnalytic c hU)) from rfl]
  rw [hom_eval₂ q (polyToAnalytic U) (analyticSubring U).subtype (phiAnalytic c hU)]
  have hpi : (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z))
      = q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) (bottcherCoord c) := by
    funext z
    change eval₂ (evalRingHom z) (bottcherCoord c z) q
      = Pi.evalRingHom (fun _ : ℂ => ℂ) z
          (eval₂ (RingHom.pi fun z : ℂ => evalRingHom z) (bottcherCoord c) q)
    rw [hom_eval₂ q (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z))
      (Pi.evalRingHom (fun _ : ℂ => ℂ) z) (bottcherCoord c)]
    rfl
  rw [hpi]
  rw [show (↑(q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) (bottcherCoord c))
        : Germ (𝓟 U) ℂ)
      = Germ.coeRingHom (𝓟 U)
          (q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) (bottcherCoord c)) from rfl]
  rw [hom_eval₂ q (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) (Germ.coeRingHom (𝓟 U))
    (bottcherCoord c)]
  rfl

/-- **Transcendence from the function-level no-relation (the field→function reduction).** If no nonzero
`q ∈ ℂ[z][Y]` makes the genuine function `z ↦ q(z, φ_c(z)) = Σ_i (q.coeff i)(z)·φ_c(z)ⁱ` vanish on `U`,
then `φ_c = phiMero c` is transcendental over `ℂ(z) = RatFunc ℂ` in the carrier `M = meroField U` (with
the base-field algebra structure from `ratfuncToMero`). This is the precise `hGtr` input of
`q62_independence_connected_of_inputs`, reduced to a statement the natural-boundary geometry refutes. -/
theorem phiMero_transcendental_of_no_function_relation {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  letI algK : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI algA : Algebra (Polynomial ℂ) (meroField U) := (polyToMero U).toAlgebra
  haveI hst : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField U) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show polyToMero U p = ratfuncToMero U hUo hUc hUne hUinf (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [ratfuncToMero_algebraMap_polynomial]
  haveI := isDomain_analyticSubring U hUo hUc hUne
  show ¬ IsAlgebraic (RatFunc ℂ) (phiMero c hU)
  rw [← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ) (meroField U)]
  rintro ⟨q, hq0, hqe⟩
  apply hno q hq0
  rw [aeval_def] at hqe
  have halg : (algebraMap (Polynomial ℂ) (meroField U)) = polyToMero U := rfl
  rw [halg] at hqe
  rw [show q.eval₂ (polyToMero U) (phiMero c hU)
        = algebraMap (analyticSubring U) (meroField U)
            (q.eval₂ (polyToAnalytic U) (phiAnalytic c hU)) from by
    rw [hom_eval₂ q (polyToAnalytic U) (algebraMap (analyticSubring U) (meroField U))
      (phiAnalytic c hU)]
    rfl] at hqe
  rw [meroField_algebraMap_eq_zero_iff U hUo hUc hUne] at hqe
  have hval := eval₂_polyToAnalytic_val c hU q
  rw [hqe, ZeroMemClass.coe_zero] at hval
  have hFzero : (↑(fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) : Germ (𝓟 U) ℂ)
      = 0 := hval.symm
  rw [← Germ.coe_zero, Germ.coe_eq] at hFzero
  exact fun z hz => eventually_principal.mp hFzero z hz

/-- `z ↦ R.eval₂ (eval-at-z) (φ_c z) = Σ_i (R.coeff i)(z)·φ_c(z)ⁱ` is analytic on `U ⊆ escapeOpen c`
(a finite sum of analytic `(R.coeff i)(z)·φ_c(z)ⁱ`). The analytic input shared by every step of the
natural-boundary argument (countability of the simple-root failure set, the branch continuation). -/
theorem analyticOnNhd_eval₂_bottcher (c : ℂ) (hU : U ⊆ escapeOpen c)
    (R : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (fun z => R.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) U := by
  have hfun : (fun z => R.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z))
      = (fun z => ∑ i ∈ Finset.range (R.natDegree + 1),
          (R.coeff i).eval z * (bottcherCoord c z) ^ i) := by
    funext z; rw [eval₂_eq_sum_range]; rfl
  rw [hfun]
  apply Finset.analyticOnNhd_fun_sum
  intro i _
  have h1 : AnalyticOnNhd ℂ (fun z => (R.coeff i).eval z) U := analyticOnNhd_polyEval U (R.coeff i)
  have h2 : AnalyticOnNhd ℂ (fun z => (bottcherCoord c z) ^ i) U := by
    have := ((analyticOnNhd_bottcherCoord_full c).mono hU).pow i
    rw [show (fun z => (bottcherCoord c z) ^ i) = bottcherCoord c ^ i by
      funext z
      rfl]
    exact this
  exact h1.mul h2

/-- **Minimal-degree relation ⟹ cofinitely-many simple-root points.** From *any* nonzero `q ∈ ℂ[z][Y]`
with `z ↦ q(z, φ_c(z))` vanishing on `U` (infinite, preconnected), extract a nonzero `P` of minimal
`Y`-degree (`≥ 1`) with the same vanishing relation, whose `Y`-derivative relation `z ↦ ∂_Y P(z, φ_c z)`
has a **countable** zero set on `U`. So `φ_c` is a *simple* root of `P(z,·)` at cofinitely many points of
`U` — the simple-root data the branch-continuation (`exists_analyticAt_branch_poly` + `branch_unique_poly`)
needs. Proof: `Nat.find` on the `Y`-degree; minimality forces `∂_Y P` (lower degree, nonzero by char 0)
to not vanish identically, so `analyticOnNhd_zeros_countable` applies. -/
theorem exists_simpleRoot_relation (hUc : IsPreconnected U) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (q : Polynomial (Polynomial ℂ)) (hq0 : q ≠ 0)
    (hqrel : Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U) :
    ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧ 1 ≤ P.natDegree ∧
      Set.EqOn (fun z => P.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U ∧
      {z ∈ U | (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z)
          (bottcherCoord c z) = 0}.Countable := by
  classical
  set Pr : ℕ → Prop := fun n => ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧ Q.natDegree = n ∧
    Set.EqOn (fun z => Q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U with hPr
  have hex : ∃ n, Pr n := ⟨q.natDegree, q, hq0, rfl, hqrel⟩
  obtain ⟨P, hP0, hPnd, hPrel⟩ := Nat.find_spec hex
  set n₀ := Nat.find hex with hn0
  have hmin : ∀ Q : Polynomial (Polynomial ℂ), Q ≠ 0 →
      Set.EqOn (fun z => Q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U →
      n₀ ≤ Q.natDegree :=
    fun Q hQ0 hQrel => Nat.find_min' hex ⟨Q, hQ0, rfl, hQrel⟩
  have hdeg1 : 1 ≤ P.natDegree := by
    by_contra h
    push Not at h
    have hnd0 : P.natDegree = 0 := by omega
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hnd0
    have hazero : ∀ z ∈ U, a.eval z = 0 := by
      intro z hz
      have hthis := hPrel hz
      simp only [← ha, Pi.zero_apply] at hthis
      rw [eval₂_C] at hthis
      simpa using hthis
    have hsub : U ⊆ {x | Polynomial.IsRoot a x} := fun z hz => hazero z hz
    have : a = 0 := Polynomial.eq_zero_of_infinite_isRoot a (hUinf.mono hsub)
    rw [this, map_zero] at ha
    exact hP0 ha.symm
  have hD0 : Polynomial.derivative P ≠ 0 := by
    intro hD
    have hc := coeff_derivative P (P.natDegree - 1)
    rw [hD, Polynomial.coeff_zero] at hc
    have hnd : (P.natDegree - 1) + 1 = P.natDegree := by omega
    rw [hnd] at hc
    have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    have hcast : ((P.natDegree - 1 : ℕ) : Polynomial ℂ) + 1 ≠ 0 := by
      have heq : ((P.natDegree - 1 : ℕ) : Polynomial ℂ) + 1 = ((P.natDegree : ℕ) : Polynomial ℂ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ P.natDegree), Nat.cast_one]; ring
      rw [heq]
      exact Nat.cast_ne_zero.mpr (by omega)
    exact (mul_ne_zero hlc hcast) hc.symm
  refine ⟨P, hP0, hdeg1, hPrel, ?_⟩
  have hgan : AnalyticOnNhd ℂ
      (fun z => (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) U :=
    analyticOnNhd_eval₂_bottcher c hU (Polynomial.derivative P)
  have hgne : ∃ x ∈ U,
      (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom x) (bottcherCoord c x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hDrel : Set.EqOn
        (fun z => (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U :=
      fun x hx => by simpa using hcon x hx
    have hlt : (Polynomial.derivative P).natDegree < P.natDegree :=
      natDegree_derivative_lt (by omega)
    have hge := hmin (Polynomial.derivative P) hD0 hDrel
    omega
  obtain ⟨x₀, hx₀U, hx₀⟩ := hgne
  exact analyticOnNhd_zeros_countable hgan hUc hx₀U hx₀

/-- `z ↦ R.eval₂ (eval-at-z)(g z) = Σ_i (R.coeff i)(z)·g(z)ⁱ` is analytic on `V` whenever `g` is — the
general analytic-branch form (`analyticOnNhd_eval₂_bottcher` is the case `g = φ_c`). Needed to carry the
relation along a basin branch, where `g` is the continued Böttcher coordinate, not `bottcherCoord` itself. -/
theorem analyticOnNhd_eval₂_of_analyticOnNhd {V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g V) (R : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (fun z => R.eval₂ (Polynomial.evalRingHom z) (g z)) V := by
  have hfun : (fun z => R.eval₂ (Polynomial.evalRingHom z) (g z))
      = (fun z => ∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).eval z * (g z) ^ i) := by
    funext z; rw [eval₂_eq_sum_range]; rfl
  rw [hfun]
  apply Finset.analyticOnNhd_fun_sum
  intro i _
  exact (analyticOnNhd_polyEval V (R.coeff i)).mul (hg.pow i)

/-- **Relation propagation (identity theorem).** If `g` is analytic on a preconnected `V` and the
polynomial relation `P(z, g z) = 0` holds in a neighbourhood of one point `w₀ ∈ V`, it holds on all of
`V`. This is the step that carries the algebraic relation `P(z, φ_c z) = 0` from the deep exterior
(`deepBall`, where `g = φ_c = bottcherCoord c`) into the whole connected basin along the continued branch
`g` — the propagation half of the remaining continuation core. -/
theorem eval₂_relation_propagate {V : Set ℂ} (hVc : IsPreconnected V)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g V) (P : Polynomial (Polynomial ℂ))
    {w₀ : ℂ} (hw₀V : w₀ ∈ V)
    (hloc : ∀ᶠ z in 𝓝 w₀, P.eval₂ (Polynomial.evalRingHom z) (g z) = 0) :
    Set.EqOn (fun z => P.eval₂ (Polynomial.evalRingHom z) (g z)) 0 V := by
  have han : AnalyticOnNhd ℂ (fun z => P.eval₂ (Polynomial.evalRingHom z) (g z)) V :=
    analyticOnNhd_eval₂_of_analyticOnNhd hg P
  have hev : (fun z => P.eval₂ (Polynomial.evalRingHom z) (g z)) =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
    filter_upwards [hloc] with z hz using hz
  exact han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc hw₀V hev

/-- **Transcendence from the impossibility of a minimal simple-root relation.** The single clean entry
point the natural-boundary geometry plugs into: if no nonzero `P ∈ ℂ[z][Y]` of minimal `Y`-degree
(`≥ 1`) whose `Y`-derivative relation has a countable zero set can make `z ↦ P(z, φ_c z)` vanish on `U`,
then `φ_c = phiMero c` is transcendental over `ℂ(z)`. Composes `exists_simpleRoot_relation` (extract the
minimal relation) with `phiMero_transcendental_of_no_function_relation` (field→function). The hypothesis
`hgeom` is exactly what `NaturalBoundaryContradiction.false_of_basin_branch_dendrite` (+ a dendrite Julia
point and the basin branch `β`) discharges. -/
theorem phiMero_transcendental_of_no_minimal_relation {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hgeom : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        Set.EqOn (fun z => P.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U →
        {z ∈ U | (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z)
            (bottcherCoord c z) = 0}.Countable →
        False) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_function_relation hUo hUc hUne hUinf c hU
  intro q hq0 hqrel
  obtain ⟨P, hP0, hdeg, hPrel, hcount⟩ := exists_simpleRoot_relation hUc hUinf c hU q hq0 hqrel
  exact hgeom P hP0 hdeg hPrel hcount

/-- **Böttcher functional-equation propagation (identity theorem).** If a branch `g` is analytic on a
preconnected `V`, the composite `g ∘ f_c^[p]` is analytic on `V`, and the functional equation
`g(f_c^[p] z) = g(z)^{2^p}` holds near one point `w₁ ∈ V`, then it holds on all of `V`. Where `g = φ_c`
(near the deep exterior) the equation holds by `bottcherCoord_quadratic` iterated; this carries it across
the whole continuation domain, supplying the `g ∘ F =ᶠ g^d` hypothesis that
`ResonanceOrder.const_of_no_resonance` (the local natural-boundary obstruction at a non-resonant repelling
periodic point) consumes — the resonance route's analogue of `eval₂_relation_propagate`. -/
theorem eqOn_funEq_of_eventuallyEq (c : ℂ) {V : Set ℂ} (hVc : IsPreconnected V)
    {g : ℂ → ℂ} {p : ℕ}
    (hg : AnalyticOnNhd ℂ g V)
    (hgF : AnalyticOnNhd ℂ (fun z => g ((quadratic c)^[p] z)) V)
    {w₁ : ℂ} (hw₁V : w₁ ∈ V)
    (hloc : ∀ᶠ z in 𝓝 w₁, g ((quadratic c)^[p] z) = (g z) ^ (2 ^ p)) :
    Set.EqOn (fun z => g ((quadratic c)^[p] z)) (fun z => (g z) ^ (2 ^ p)) V :=
  hgF.eqOn_of_preconnected_of_eventuallyEq (hg.pow _) hVc hw₁V hloc

end Bottcher
