/-
# Connected-pair `NoRelation` via the natural boundary, with `hinput` discharged internally

Combining the assembled `hinput` (`Q62HinputAssembly`) with the minimal-relation reduction
(`exists_separable_relation_of_relation`) discharges the natural-boundary engine's `hinput` **inside**
the `NoRelation` proof.  The engine's `hinput` names the *original* relation's continued fibre, which
need not be squarefree; reducing to the minimal `T'` first (a genuine relation, squarefree by
construction) supplies the separable-fibre witness for free — the separability transfers from
`bottcherCoord c₂` to `γ` at the witness `w ∈ U`.  The natural-boundary contradiction (branch family,
`β` follows a single branch, the branch continues `β` across the frontier, contradicting the natural
boundary `hnb`) is then replicated on `T'`.

Result: the connected-pair `NoRelation` via the natural-boundary route needs only the standard
exposure data (`β`, `γ` analytic across the frontier and matching on `U`), the natural boundary `hnb`
(proven unconditionally for connected `c₁` by `hnb_of_mem_mandelbrot_connected`), and the single
topological input `UncountableLocallyConnectedFrontier c₁` (co-countable for connected `c₁`).  No
`hinput`, no separable-witness hypothesis.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.Q62HinputAssembly
import GaloisForLFunctions.Bottcher.RelativeMinimalRelation
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb
open Polynomial Filter Topology Set Metric U0NaturalBoundary
namespace Bottcher
variable {U : Set ℂ}

theorem noRelation_phiMero_of_naturalBoundary_of_uncountableLC
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hunc : UncountableLocallyConnectedFrontier c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  rcases Nat.lt_or_ge (bivarPoly Q s).natDegree 1 with hdeg0 | hpos
  · have hdeg0' : (bivarPoly Q s).natDegree = 0 := by omega
    have hQzero : ∀ i ∈ s, i ≠ 0 → Q i = 0 := by
      intro i hi hi0
      have hcoeff : (bivarPoly Q s).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [bivarPoly, Polynomial.finsetSum_coeff] at hcoeff
      simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
      rw [Finset.sum_ite_eq] at hcoeff
      rw [if_pos hi] at hcoeff
      exact hcoeff
    obtain ⟨i₀, hi₀s, hi₀ne⟩ := hnt
    have hi₀0 : i₀ = 0 := by
      by_contra h
      apply hi₀ne
      rw [hQzero i₀ hi₀s h]; simp
    rw [hi₀0] at hi₀ne hi₀s
    have hfun : ∀ z ∈ U, (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) = 0 := by
      intro z hzU
      have h1 := hEqOn hzU
      simp only [Pi.zero_apply] at h1
      have h2 : ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i
          = (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
        rw [Finset.sum_eq_single_of_mem 0 hi₀s]
        · simp
        · intro b hb hb0; rw [hQzero b hb hb0]; simp
      rw [h2] at h1; exact h1
    apply hi₀ne
    have hval : ((Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) : analyticSubring U).val
        = ((0 : analyticSubring U) : Germ (Filter.principal U) ℂ) := by
      rw [eval₂_polyToAnalytic_val, ZeroMemClass.coe_zero, ← Filter.Germ.coe_zero,
        Filter.Germ.coe_eq]
      exact Filter.eventually_principal.mpr fun z hz => hfun z hz
    exact Subtype.ext hval
  · obtain ⟨T', wfar, hdeg', hwU, hwJ, hlead, hsepw, hrel', hnoζ⟩ :=
      exists_separable_relation_of_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG Q s hpos hEqOn
    have hsupp : T'.support ⊆ Finset.range (T'.natDegree + 1) :=
      Polynomial.supp_subset_range_natDegree_succ
    have hT'ne : T' ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hdeg'; omega
    have hN : T'.natDegree ∈ T'.support := Polynomial.natDegree_mem_support_of_nonzero hT'ne
    have hwfarK₁ : wfar ∈ (filledJulia c₁)ᶜ := escapeOpen_subset_compl_filledJulia c₁ (hU₁ hwU)
    have hleadγ : (T'.coeff T'.natDegree).eval₂ (Polynomial.evalRingHom wfar) (γ wfar) ≠ 0 := by
      rw [show γ wfar = bottcherCoord c₂ wfar from hγmatch wfar hwU]; exact hlead
    have hsepγ : (fibrePoly (fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z))
        T'.support wfar).Separable := by
      have hval : ∀ i, (T'.coeff i).eval₂ (Polynomial.evalRingHom wfar) (γ wfar)
          = (T'.coeff i).eval₂ (Polynomial.evalRingHom wfar) (bottcherCoord c₂ wfar) :=
        fun i => by rw [hγmatch wfar hwU]
      have heq : (fibrePoly (fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z))
            T'.support wfar)
          = (fibrePoly (fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z)
              (bottcherCoord c₂ z)) T'.support wfar) := by
        simp only [fibrePoly]
        apply Finset.sum_congr rfl
        intro i _; rw [hval i]
      rw [heq]; exact hsepw
    obtain ⟨z₀, w₀, hsep, hfront, hβlim⟩ :=
      hinput_tuple_of_engine_relation hUo hUne hU₁ hβan hβesc hγan hγfront hγmatch hsupp hN
        hdeg' hrel' hwfarK₁ hleadγ hsepγ hunc
    set a : ℕ → ℂ → ℂ := fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z) with hadef
    have haAt : ∀ i ∈ T'.support, AnalyticAt ℂ (a i) z₀ :=
      fun i _ => analyticAt_eval₂_of_analyticAt (hγfront z₀ hfront) (T'.coeff i)
    have ha : ∀ i ∈ T'.support, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ :=
      fun i _ => analyticOnNhd_eval₂_of_analyticOnNhd hγan (T'.coeff i)
    have hmatch : ∀ i ∈ T'.support, ∀ z ∈ U,
        a i z = (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
      intro i _ z hz
      show (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z)
          = (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)
      rw [hγmatch z hz]
    have hrelU : ∀ z ∈ U, ∑ i ∈ T'.support, a i z * (β z) ^ i = 0 := by
      intro z hz
      calc ∑ i ∈ T'.support, a i z * (β z) ^ i
          = ∑ i ∈ T'.support, ((T'.coeff i).eval₂ (Polynomial.evalRingHom z)
              (bottcherCoord c₂ z)) * (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi; rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
        _ = 0 := hrel' hz
    have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ T'.support, a i z * (β z) ^ i = 0 :=
      relation_eq_zero_basin_analytic_of_open hUo hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
    have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ T'.support, a i z * (β z) ^ i = 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
    have hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
      nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront
    have hrootSum : ∑ i ∈ T'.support, a i z₀ * w₀ ^ i = 0 :=
      relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := T'.support)
        (fun i hi => (haAt i hi).continuousAt) hNeBot hβlim hβrel
    have hrootPoly : (fibrePoly a T'.support z₀).eval w₀ = 0 := by rwa [eval_fibrePoly]
    have hderiv : (fibrePoly a T'.support z₀).derivative.eval w₀ ≠ 0 :=
      eval_derivative_ne_zero_of_separable hsep hrootPoly
    obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic
      (fun i hi => (haAt i hi).contDiffAt) hrootSum
      (relation_hasDerivAt_w_analytic a T'.support z₀ w₀) hderiv
    have hmatchβ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z :=
      branch_unique_within_analytic (fun i hi => (haAt i hi).continuousAt)
        (relation_hasDerivAt_w_analytic a T'.support z₀ w₀) hderiv hgAt.continuousAt hgz₀ hβlim
        (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
    exact (hnb z₀ hfront) ⟨g, hgAt, hmatchβ⟩

/-- **Both-connected pair `NoRelation`, `hnb` and `hinput` both discharged.**  For a connected
`c₁ ∈ mandelbrot ∖ {0,-2}`, the natural boundary `hnb` is supplied by `hnb_of_branch_matching` and the
`hinput` producer is discharged by the minimal reduction, so the both-connected pair
`NoRelation (phiMero c₁) (phiMero c₂)` follows from the transcendence `hG` (proven elsewhere), the
exposure data (`γ = bottcherCoord c₂` analytic on `K₁ᶜ` and across `∂K₁`, matching on `U` — the #124
collar), and the single topological input `UncountableLocallyConnectedFrontier c₁`.  No `hnb`, no
`hinput`, no separable-witness hypothesis. -/
theorem noRelation_phiMero_bothConnected_of_uncountableLC
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hunc : UncountableLocallyConnectedFrontier c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_naturalBoundary_of_uncountableLC hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
    β γ hβan hβesc hγan hγfront hγmatch
    (hnb_of_branch_matching hc₁M hc₁0 hc₁2 hconn₁ hβan hβesc) hunc

end Bottcher
