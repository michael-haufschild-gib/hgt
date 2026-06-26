/-
# Connected-case Böttcher transcendence — end-to-end verified skeleton

This file threads the entire verified infrastructure of the connected-case transcendence into a single
theorem, reducing `Transcendental (RatFunc ℂ) (phiMero c)` to exactly the two remaining deep dynamical
inputs (packaged as one hypothesis `hinput`):

  `phiMero_transcendental_of_no_minimal_relation`   (TranscendenceReduction — the algebra reduction)
    ∘ `false_of_funEq_at_nonresonant`               (NaturalBoundaryContradiction — the resonance finisher)

`hinput` says: for each minimal simple-root relation, there is a single-valued continuation `g` of `φ_c`
— analytic on a preconnected `V`, satisfying the Böttcher functional equation `g ∘ f_c^[p] = g^{2^p}`,
non-constant — reaching a non-resonant periodic point `z₀ ∈ V`. Those are exactly: (1) the continuation
`g` (basin-construction lane) and (2) a non-resonant repelling periodic point, dense in `J_c`
(Montel/periodic lane). Given them, the connected-case transcendence closes by one application — every
connective brick between the two inputs and the field-theoretic conclusion is proven here.
-/
import GaloisForLFunctions.Bottcher.NaturalBoundaryContradiction
import GaloisForLFunctions.Bottcher.TranscendenceReduction
import GaloisForLFunctions.Bottcher.BranchContinuation
import GaloisForLFunctions.Bottcher.SquareFree

open Polynomial Filter Topology Set

namespace Bottcher

/-- **Connected-case transcendence, end-to-end skeleton.** Given `hinput` — for each minimal simple-root
relation, a single-valued continuation `g` of `φ_c` (analytic on a preconnected `V`, satisfying the
Böttcher functional equation, non-constant) reaching a non-resonant periodic point `z₀ ∈ V` — the
coordinate `φ_c = phiMero c` is transcendental over `ℂ(z) = RatFunc ℂ`. Composes the algebra reduction
`phiMero_transcendental_of_no_minimal_relation` with the resonance finisher `false_of_funEq_at_nonresonant`;
every brick between the two deep inputs and the conclusion is verified. -/
theorem phiMero_transcendental_of_resonance_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        Set.EqOn (fun z => P.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U →
        {z ∈ U | (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z)
            (bottcherCoord c z) = 0}.Countable →
        ∃ (lam : ℂ) (p : ℕ) (V : Set ℂ) (g : ℂ → ℂ) (z₀ : ℂ),
          IsPreconnected V ∧ IsOpen V ∧ z₀ ∈ V ∧ AnalyticOnNhd ℂ g V ∧
          Set.EqOn (fun z => g ((quadratic c)^[p] z)) (fun z => (g z) ^ (2 ^ p)) V ∧
          (quadratic c)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          g z₀ ≠ 0 ∧ (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) ∧
          (∃ z ∈ V, g z ≠ g z₀)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_minimal_relation hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hrel hcount
  obtain ⟨lam, p, V, g, z₀, hVc, hVo, hz₀V, hgan, hgfe, hFz, hlam, hζ0, hres, hnoncon⟩ :=
    hinput P hP0 hdeg hrel hcount
  exact false_of_funEq_at_nonresonant hVc hVo hz₀V hgan hgfe hFz hlam hζ0 hres hnoncon

/-- **Divisibility-route contradiction at a non-resonant periodic simple root.** The end-to-end spine of
the divisibility route: from a minimal relation `P` (vanishing on `U`, with `Q = compRelPoly c p P` also
vanishing) and a non-resonant periodic point `z₀` (`f_c^[p] z₀ = z₀`, multiplier `λ` with `λ^m ≠ 2^p`)
that is a *simple root* `(z₀, w₀)` of `P` with `w₀^{2^p} = w₀`, `w₀ ≠ 0`, and `(X - C(C w₀)) ∤ P` (the
branch is non-constant), one derives `False` — needing NO global continuation. The local algebraic branch
`g` (`exists_analyticAt_branch_poly`) satisfies the Böttcher functional equation near `z₀` via the
divisibility gateway (`divides_relation_up_to_denom` → `funEq_hdiv_of_divides` → `funEq_of_branch`); the
resonance obstruction (`false_of_eventually_funEq_at_nonresonant`) then forces `g` locally constant,
contradicting `(X - C(C w₀)) ∤ P` via `relation_at_const`. The remaining input is purely dynamical: such a
periodic non-resonant simple-root point (repelling periodic points dense in `J_c`, off the finite branch
locus of `P` and the finite zero set of the denominator `e`). -/
theorem false_of_periodic_simpleroot {U : Set ℂ} (c : ℂ) (p : ℕ) {lam w₀ d : ℂ} {z₀ : ℂ}
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
        ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hFz : (quadratic c)^[p] z₀ = z₀) (hlam : HasDerivAt ((quadratic c)^[p]) lam z₀)
    (hw₀ : w₀ ^ (2 ^ p) = w₀) (hw0ne : w₀ ≠ 0)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))
    (hndvd : ¬ ((Polynomial.X - Polynomial.C (Polynomial.C w₀)) ∣ P)) :
    False := by
  obtain ⟨g, hgAt, hgz, hgrel⟩ := exists_analyticAt_branch_poly P hroot hpartial hd
  obtain ⟨e, S, he0, hPS⟩ :=
    divides_relation_up_to_denom c P (compRelPoly c p P) hP0 hPmin hPrel hQrel
  have hdiv := funEq_hdiv_of_divides c p P he0 hPS hgAt.continuousAt hgrel
  have hF : ContinuousAt ((quadratic c)^[p]) z₀ := hlam.continuousAt
  have heq : ∀ᶠ z in 𝓝 z₀, g ((quadratic c)^[p] z) = (g z) ^ (2 ^ p) :=
    funEq_of_branch P hpartial hd hgAt hgz hgrel hF hFz hw₀ hdiv
  have hnoncon : ¬ (∀ᶠ z in 𝓝 z₀, g z = g z₀) := by
    intro hcon
    apply hndvd
    rw [Polynomial.dvd_iff_isRoot]
    have hrelw0 : ∀ᶠ z in 𝓝 z₀, (P.eval (Polynomial.C w₀)).eval z = 0 := by
      filter_upwards [hgrel, hcon] with z hgr hc
      rw [hgz] at hc
      rw [← relation_at_const, ← hc]; exact hgr
    obtain ⟨t, htsub, htopen, hz0t⟩ := eventually_nhds_iff.mp hrelw0
    have htinf : t.Infinite := infinite_of_mem_nhds z₀ (htopen.mem_nhds hz0t)
    by_contra hne
    exact (htinf.mono (fun x hx => htsub x hx)) (Polynomial.finite_setOf_isRoot hne)
  exact false_of_eventually_funEq_at_nonresonant hgAt heq hFz hlam
    (by rw [hgz]; exact hw0ne) hres hnoncon

/-- Bridge: the `eval₂` relation form equals the explicit support-sum form,
`R.eval₂ (eval-at-z) w = ∑ᵢ (R.coeff i)(z)·wⁱ`. Lets the `eval₂`-based reduction
(`TranscendenceReduction`) and the support-sum-based divisibility machinery (`BranchContinuation`) talk. -/
theorem eval₂_eq_relation (R : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    R.eval₂ (Polynomial.evalRingHom z) w = ∑ i ∈ R.support, (R.coeff i).aeval z * w ^ i := by
  rw [Polynomial.eval₂_eq_eval_map, ← relation_eq_eval_map]

/-- **Minimal-degree simple-root relation, with minimality EXPOSED (support-sum form).** Like
`TranscendenceReduction.exists_simpleRoot_relation` but additionally returns the minimality predicate
`hPmin` that the divisibility gateway `divides_relation_up_to_denom` needs — and everything in the
support-sum form the divisibility machinery uses. Built from `BranchContinuation.exists_minimal_relation`
(which exposes minimality) plus the countability-of-`∂P`-zeros argument (minimality ⟹ `∂_Y P` not
identically zero ⟹ `analyticOnNhd_zeros_countable`). -/
theorem exists_simpleRoot_minimal_relation {U : Set ℂ} (hUc : IsPreconnected U) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (q : Polynomial (Polynomial ℂ)) (hq0 : q ≠ 0)
    (hqrel : ∀ z ∈ U, ∑ i ∈ q.support, (q.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧ 1 ≤ P.natDegree ∧
      (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) ∧
      (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree) ∧
      {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
        ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable := by
  obtain ⟨P, hP0, hdeg1, hPrel, hPmin⟩ := exists_minimal_relation hUinf c q hq0 hqrel
  refine ⟨P, hP0, hdeg1, hPrel, hPmin, ?_⟩
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
      rw [heq]; exact Nat.cast_ne_zero.mpr (by omega)
    exact (mul_ne_zero hlc hcast) hc.symm
  set f := fun z => ∑ i ∈ (Polynomial.derivative P).support,
    ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i with hf
  have hfeq : f = fun z => (Polynomial.derivative P).eval₂ (Polynomial.evalRingHom z)
      (bottcherCoord c z) := by funext z; rw [hf, eval₂_eq_relation]
  have hgan : AnalyticOnNhd ℂ f U := by
    rw [hfeq]; exact analyticOnNhd_eval₂_bottcher c hU (Polynomial.derivative P)
  have hgne : ∃ x ∈ U, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hge := hPmin (Polynomial.derivative P) hD0 hcon
    have hlt : (Polynomial.derivative P).natDegree < P.natDegree := natDegree_derivative_lt (by omega)
    omega
  obtain ⟨x₀, hx₀U, hx₀⟩ := hgne
  exact analyticOnNhd_zeros_countable hgan hUc hx₀U hx₀

/-- **Transcendence entry with minimality exposed.** Variant of
`TranscendenceReduction.phiMero_transcendental_of_no_minimal_relation` whose obligation `hgeom` ALSO
receives the minimality predicate `hPmin` (and works entirely in the support-sum form). This is the entry
the divisibility route consumes: pair `hgeom := fun P _ _ hPrel hPmin hcount => false_of_periodic_simpleroot …`
to reduce connected-case `φ_c`-transcendence to the purely dynamical existence of a non-resonant periodic
simple-root point. -/
theorem phiMero_transcendental_of_no_minimal_relation_min {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hgeom : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        False) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_function_relation hUo hUc hUne hUinf c hU
  intro q hq0 hqe
  have hqrel : ∀ z ∈ U, ∑ i ∈ q.support, (q.coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz; rw [← eval₂_eq_relation]; simpa using hqe hz
  obtain ⟨P, hP0, hdeg, hPrel, hPmin, hcount⟩ :=
    exists_simpleRoot_minimal_relation hUc hUinf c hU q hq0 hqrel
  exact hgeom P hP0 hdeg hPrel hPmin hcount

/-- **A relation vanishing on a nonempty open `U ⊆ escapeOpen c` vanishes on all of `escapeOpen c`**
(identity theorem). The relation `z ↦ ∑ᵢ (P.coeff i)(z)·φ_c(z)ⁱ` is analytic on the *connected*
`escapeOpen c` (`analyticOnNhd_eval₂_bottcher`, `isConnected_escapeOpen`) and vanishes on the open `U`,
hence everywhere. Upgrades `hPrel` (on `U`) to the `escapeOpen`-wide hypothesis that
`relation_iterate_eq_zero` (forward-invariance of `escapeOpen`) needs to conclude `compRelPoly` vanishes. -/
theorem relation_vanishes_escapeOpen {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ)
    (hU : U ⊆ escapeOpen c) (P : Polynomial (Polynomial ℂ))
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∀ z ∈ escapeOpen c, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
  obtain ⟨u, huU⟩ := hUne
  have han : AnalyticOnNhd ℂ
      (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i) (escapeOpen c) := by
    have h := analyticOnNhd_eval₂_bottcher c (subset_refl (escapeOpen c)) P
    have hfe : (fun z => P.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z))
        = (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i) := by
      funext z; rw [eval₂_eq_relation]
    rwa [hfe] at h
  have hev : (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i)
      =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [hUo.mem_nhds huU] with z hz using hPrel z hz
  have heqon : Set.EqOn (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i)
      (fun _ => (0 : ℂ)) (escapeOpen c) :=
    han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (isConnected_escapeOpen c).isPreconnected (hU huU) hev
  intro z hz; exact heqon hz

/-- **Connected-case `φ_c`-transcendence reduced to the purely dynamical input (divisibility route).**
The capstone reduction: `φ_c = phiMero c` is transcendental over `ℂ(z)` provided that for each minimal
simple-root relation `P` there is a non-resonant periodic point `z₀` (`f_c^[p] z₀ = z₀`, multiplier `λ`
with `λ^m ≠ 2^p`) that is a *simple root* `(z₀, w₀)` of `P`, with `w₀^{2^p} = w₀`, `w₀ ≠ 0`, and
`(X - C(C w₀)) ∤ P` (non-constant branch). Every algebraic and analytic step — minimal-relation
extraction (`phiMero_transcendental_of_no_minimal_relation_min`), the `escapeOpen` identity-theorem
upgrade, the iterated-relation vanishing (`relation_iterate_eq_zero` + `compRelPoly_relation`), the
`P ∣ P(f^[p]·, ·^{2^p})` divisibility gateway, the Böttcher functional equation, and the resonance
obstruction — is now proven (`false_of_periodic_simpleroot`). The residue `hinput` is exactly the
dynamics: repelling periodic points are dense in `J_c`; a generic one avoids the finite branch locus of
`P` (simple root, non-constant branch) and is non-resonant. No global analytic continuation is required. -/
theorem phiMero_transcendental_of_periodic_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) ∧
          ¬ ((Polynomial.X - Polynomial.C (Polynomial.C w₀)) ∣ P)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_minimal_relation_min hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, lam, w₀, d, z₀, hroot, hpartial, hd, hFz, hlam, hw₀, hw0ne, hres, hndvd⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  exact false_of_periodic_simpleroot c p P hP0 hPmin hPrel hQrel hroot hpartial hd hFz hlam
    hw₀ hw0ne hres hndvd

/-- **`φ_c` is non-constant on any nonempty open `U ⊆ escapeOpen c`**: there is `x₀ ∈ U` with
`bottcherCoord c x₀ ≠ w₀`. If `φ_c ≡ w₀` on `U` then (identity theorem) `φ_c ≡ w₀` on the connected
`escapeOpen c`; the functional equation `φ_c(z²+c) = φ_c(z)²` forces `w₀ = w₀²`, contradicting
`‖φ_c‖ > 1` (`one_lt_norm_bottcherCoord`). -/
theorem exists_bottcherCoord_ne {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ)
    (hU : U ⊆ escapeOpen c) (w₀ : ℂ) :
    ∃ x₀ ∈ U, bottcherCoord c x₀ ≠ w₀ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, huU⟩ := hUne
  have hφan : AnalyticOnNhd ℂ (bottcherCoord c) (escapeOpen c) := analyticOnNhd_bottcherCoord_full c
  have hev : bottcherCoord c =ᶠ[𝓝 u] (fun _ => w₀) := by
    filter_upwards [hUo.mem_nhds huU] with z hz using hcon z hz
  have heqon : Set.EqOn (bottcherCoord c) (fun _ => w₀) (escapeOpen c) :=
    hφan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (isConnected_escapeOpen c).isPreconnected (hU huU) hev
  have hu_esc : u ∈ escapeOpen c := hU huU
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hu_esc
  have hfu_esc : quadratic c u ∈ escapeOpen c := by
    have hge := norm_iterate_ge hc hz2 1
    rw [Function.iterate_one] at hge
    simp only [escapeOpen, Set.mem_setOf_eq] at hu_esc ⊢
    linarith
  have hfe := bottcherCoord_quadratic hc hz2
  have h1 : bottcherCoord c u = w₀ := heqon hu_esc
  have h2 : bottcherCoord c (quadratic c u) = w₀ := heqon hfu_esc
  rw [h2, h1] at hfe
  have hnorm : 1 < ‖w₀‖ := by rw [← h1]; exact one_lt_norm_bottcherCoord hc hz2
  have hns : ‖w₀‖ = ‖w₀‖ ^ 2 := by rw [← norm_pow]; exact congrArg norm hfe
  nlinarith [hnorm, hns]

/-- **Non-divisibility from minimality** (discharges `hndvd`). For the minimal vanishing relation `P`
(degree `≥ 1`) and any `w₀`, `(X - C(C w₀)) ∤ P`. Otherwise `P = (X - C(C w₀))·P'` with `P' ≠ 0` of degree
`natDegree P − 1`; `relation(P)(z,φ_c z) = (φ_c z − w₀)·relation(P')(z,φ_c z) = 0` on `U` and `φ_c ≢ w₀`
(`exists_bottcherCoord_ne`), so the identity theorem gives `relation(P') ≡ 0` on `U` — a lower-degree
vanishing relation, contradicting minimality. Removes the `hndvd` hypothesis from the divisibility input. -/
theorem factor_not_dvd_of_minimal {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (w₀ : ℂ) :
    ¬ ((Polynomial.X - Polynomial.C (Polynomial.C w₀)) ∣ P) := by
  rintro ⟨P', hPeq⟩
  have hXne : (Polynomial.X - Polynomial.C (Polynomial.C w₀)) ≠ 0 :=
    (Polynomial.monic_X_sub_C (Polynomial.C w₀)).ne_zero
  have hP'0 : P' ≠ 0 := by rintro rfl; rw [mul_zero] at hPeq; exact hP0 hPeq
  have hdeglt : P'.natDegree < P.natDegree := by
    rw [hPeq, Polynomial.natDegree_mul hXne hP'0, Polynomial.natDegree_X_sub_C]
    omega
  have hrelfac : ∀ z w : ℂ,
      (∑ i ∈ (Polynomial.X - Polynomial.C (Polynomial.C w₀)).support,
        ((Polynomial.X - Polynomial.C (Polynomial.C w₀)).coeff i).aeval z * w ^ i) = w - w₀ := by
    intro z w
    rw [relation_eq_eval_map, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.coe_evalRingHom, Polynomial.eval_C,
      Polynomial.eval_C]
  set g := fun z => ∑ i ∈ P'.support, (P'.coeff i).aeval z * (bottcherCoord c z) ^ i with hgdef
  have hfactor : ∀ z ∈ U, (bottcherCoord c z - w₀) * g z = 0 := by
    intro z hz
    have hmul := relation_mul (Polynomial.X - Polynomial.C (Polynomial.C w₀)) P' z (bottcherCoord c z)
    rw [← hPeq, hrelfac] at hmul
    rw [hgdef, ← hmul]; exact hPrel z hz
  obtain ⟨x₀, hx₀U, hx₀ne⟩ := exists_bottcherCoord_ne hUo hUne c hU w₀
  have hgan : AnalyticOnNhd ℂ g U := by
    have h := analyticOnNhd_eval₂_bottcher c hU P'
    have hfe : (fun z => P'.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) = g := by
      funext z; rw [hgdef, eval₂_eq_relation]
    rwa [hfe] at h
  have hφc : ContinuousAt (bottcherCoord c) x₀ :=
    ((analyticOnNhd_bottcherCoord_full c) x₀ (hU hx₀U)).continuousAt
  have hgloc : g =ᶠ[𝓝 x₀] (fun _ => (0 : ℂ)) := by
    have hUx : ∀ᶠ z in 𝓝 x₀, z ∈ U := hUo.mem_nhds hx₀U
    have hne : ∀ᶠ z in 𝓝 x₀, bottcherCoord c z - w₀ ≠ 0 := by
      have := (hφc.sub continuousAt_const).eventually_ne (by simpa using sub_ne_zero.mpr hx₀ne)
      simpa using this
    filter_upwards [hUx, hne] with z hzU hzne
    exact (mul_eq_zero.mp (hfactor z hzU)).resolve_left hzne
  have hg0 : ∀ z ∈ U, g z = 0 := by
    have heqon : Set.EqOn g (fun _ => (0 : ℂ)) U :=
      hgan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hx₀U hgloc
    intro z hz; exact heqon hz
  have hge := hPmin P' hP'0 hg0
  omega

/-- **Connected-case `φ_c`-transcendence reduced to the PURELY DYNAMICAL input.** The cleanest capstone:
the algebraic non-divisibility side-condition `hndvd` of `phiMero_transcendental_of_periodic_input` is now
discharged internally (`factor_not_dvd_of_minimal`), so `hinput` requires ONLY a non-resonant periodic
point `z₀` (`f_c^[p] z₀ = z₀`, multiplier `λ` with `λ^m ≠ 2^p`) that is a *simple root* `(z₀, w₀)` of the
minimal relation `P` with `w₀^{2^p} = w₀` and `w₀ ≠ 0`. Every algebraic/analytic step is proven; the
residue is exactly dynamics — repelling periodic points dense in `J_c`, a generic one off the finite branch
locus of `P` (simple root), non-resonant, with the squaring-fixed value (`exists_periodic_of_finite_mapsTo`
on the root set, closed under `w ↦ w^{2^p}` at the periodic point). -/
theorem phiMero_transcendental_of_periodic_input' {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_periodic_input hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, lam, w₀, d, z₀, hroot, hpartial, hd, hFz, hlam, hw₀, hw0ne, hres⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount
  exact ⟨p, lam, w₀, d, z₀, hroot, hpartial, hd, hFz, hlam, hw₀, hw0ne, hres,
    factor_not_dvd_of_minimal hUo hUc hUne c hU P hP0 hdeg hPrel hPmin w₀⟩

/-- **Transcendence from a STRONGLY-REPELLING periodic simple root** — the divisibility route in its most
dynamically-natural form. The abstract non-resonance `∀m, λ^m ≠ 2^p` of
`phiMero_transcendental_of_periodic_input'` is replaced by the single modulus inequality `2^p < ‖λ‖`
(`nonresonant_of_norm_gt`): a strongly-repelling cycle is automatically non-resonant. So `φ_c` is
transcendental over `ℂ(z)` provided that for each minimal relation `P` there is a periodic point `z₀`
(`f_c^[p] z₀ = z₀`, multiplier `λ`, `2^p < ‖λ‖`) that is a simple root `(z₀,w₀)` of `P` with `w₀^{2^p}=w₀`,
`w₀≠0`. The cleanest dynamical target — and (via `nonresonant_of_norm_gt`, `hasDerivAt_iterate_periodic`,
`exists_pow_fixed_root`) the modulus bound transfers through the squaring-orbit exponent, so it suffices to
exhibit ANY strongly-repelling cycle (`∏‖orbit‖ > 1`, i.e. `‖λ‖ > 2^p`) meeting `P`'s nonzero simple-root
locus. -/
theorem phiMero_transcendental_of_repelling_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_periodic_input' hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, lam, w₀, d, z₀, hroot, hpartial, hd, hFz, hlam, hw₀, hw0ne, hnorm⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount
  exact ⟨p, lam, w₀, d, z₀, hroot, hpartial, hd, hFz, hlam, hw₀, hw0ne,
    nonresonant_of_norm_gt hnorm⟩

end Bottcher
