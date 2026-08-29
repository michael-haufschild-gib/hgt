import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDefectCountability
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.AutonomousReciprocalAperture

/-!
# Multiplicative translation-spectrum countability for a meromorphic source

The additive theorem transfers through the logarithmic derivative.  On an arbitrary open,
preconnected, nonempty, infinite domain the meromorphic jet-field bridge is available, so a
nonvanishing analytic function satisfies an algebraic differential equation exactly when its
logarithmic derivative does.  Consequently a hypertranscendental source analytic off a closed
countable set has only countably many differentially algebraic multiplicative translation defects.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open Complex Set Filter Topology
open scoped Differential

noncomputable section

/-! ## The field derivation on a general domain -/

/-- **The field derivation is the ordinary derivative**, on an arbitrary domain. -/
theorem deriv_analyticMeroElementOn {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    (analyticMeroElement f hf)′ = analyticMeroElement (deriv f) hf.deriv := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroFieldDifferential hUo hUc hUne
  have h1 : differentialJet 1 (analyticMeroElement f hf)
      = analyticMeroElement (deriv f) hf.deriv := by
    rw [differentialJet_analyticMeroElement hUo hUc hUne, analyticMeroElement, analyticJetElement,
      analyticFunctionElement]
    congr 1
    apply Subtype.ext
    exact congrArg
      (fun h : ℂ → ℂ => (Filter.Germ.coeRingHom (Filter.principal U) h))
      (iteratedDeriv_one (f := f))
  rw [← h1, differentialJet_succ, differentialJet_zero]

/-! ## Logarithmic-derivative equivalence on a domain -/

/-- **Domain logarithmic-derivative equivalence.**  A nonvanishing analytic function on an open
preconnected infinite domain satisfies an algebraic differential equation there exactly when its
logarithmic derivative does. -/
theorem differentiallyAlgebraicOn_logDeriv_iff {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G U) (hGne : ∀ z ∈ U, G z ≠ 0) :
    DifferentiallyAlgebraicOn (fun z => deriv G z / G z) U ↔ DifferentiallyAlgebraicOn G U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := U) hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  have hL : AnalyticOnNhd ℂ (fun z => deriv G z / G z) U := hG.deriv.div hG hGne
  have hGmero_ne : analyticMeroElement G hG ≠ 0 := by
    rw [Ne, analyticMeroElement_eq_zero_iff hG]
    intro hzero
    obtain ⟨z, hz⟩ := hUne
    exact hGne z hz (hzero z hz)
  have hprod : analyticMeroElement (fun z => deriv G z / G z) hL * analyticMeroElement G hG
      = (analyticMeroElement G hG)′ := by
    rw [← analyticMeroElement_mul hL hG, deriv_analyticMeroElementOn hUo hUc hUne G hG]
    refine analyticMeroElement_congrOn _ _ ?_
    intro z hz
    exact div_mul_cancel₀ (deriv G z) (hGne z hz)
  have hmero : analyticMeroElement (fun z => deriv G z / G z) hL =
      (analyticMeroElement G hG)′ / analyticMeroElement G hG := (eq_div_iff hGmero_ne).2 hprod
  constructor
  · intro h
    refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hG).1 ?_
    have h' := (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hL).2 h
    rw [hmero] at h'
    exact (GaloisForLFunctions.differentialAlgebraicOver_deriv_div_self_iff _).1 h'
  · intro h
    refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hL).1 ?_
    rw [hmero]
    exact (GaloisForLFunctions.differentialAlgebraicOver_deriv_div_self_iff _).2
      ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hG).2 h)

/-! ## Extending a relation from a subdomain -/

/-- A relation valid on a nonempty open subdomain propagates to the whole preconnected domain. -/
theorem differentiallyAlgebraicOn_of_subdomain {f : ℂ → ℂ} {U V : Set ℂ}
    (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U) (hVU : V ⊆ U) (hVopen : IsOpen V)
    (hVne : V.Nonempty) (h : DifferentiallyAlgebraicOn f V) :
    DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP0, hPv⟩ := h
  refine ⟨n, P, hP0, ?_⟩
  have hanal : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (entireJetVector f n z) P) U :=
    analyticOnNhd_eval_mvPolynomial (fun i => fun z => entireJetVector f n z i)
      (fun i => analyticOnNhd_entireJetVector_component hf n i) P
  obtain ⟨v, hv⟩ := hVne
  have hev : (fun z => MvPolynomial.eval (entireJetVector f n z) P) =ᶠ[nhds v] 0 := by
    filter_upwards [hVopen.mem_nhds hv] with w hw
    exact hPv w hw
  have hzero := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hVU hv) hev
  intro z hz
  exact hzero hz

/-! ## The multiplicative countability theorem -/

/-- The set of shifts whose multiplicative translation defect satisfies an algebraic differential
equation. -/
def multDefectDAStabilizer (G : ℂ → ℂ) (S : Set ℂ) : Set ℂ :=
  {h : ℂ | DifferentiallyAlgebraicOn (fun z => G (z + h) / G z) (defectDomain S h)}

/-- **Meromorphic multiplicative translation-spectrum countability.**  A source analytic off a
closed countable set and satisfying no algebraic differential equation there has at most countably
many differentially algebraic multiplicative translation defects, after the zero divisor is added
to the singular set. -/
theorem countable_multDefectDAStabilizer {G : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable)
    (hG : AnalyticOnNhd ℂ G Sᶜ)
    (hGht : ¬ DifferentiallyAlgebraicOn G Sᶜ) :
    ∃ S' : Set ℂ, IsClosed S' ∧ S'.Countable ∧ S ⊆ S' ∧
      (∀ z ∈ S'ᶜ, G z ≠ 0) ∧ (multDefectDAStabilizer G S').Countable := by
  classical
  -- a point of the domain where `G` does not vanish
  obtain ⟨z₁, hz₁, hGz₁⟩ : ∃ z ∈ Sᶜ, G z ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hGht ⟨0, MvPolynomial.X 1, by
      intro hzero
      have := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) hzero
      simp [MvPolynomial.coeff_X] at this, by
      intro z hz
      have hval : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) G z) : Fin 2 → ℂ) 1
          = G z := by
        rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
        simp [iteratedDeriv_zero]
      simp only [MvPolynomial.eval_X, hval]
      exact hno z hz⟩
  have hconnS : IsPreconnected (Sᶜ) := isPreconnected_compl_of_countable hScount hz₁
  -- the enlarged singular set
  set Z : Set ℂ := {z | z ∈ Sᶜ ∧ G z = 0} with hZdef
  set S' : Set ℂ := S ∪ Z with hS'def
  have hZcount : Z.Countable := by
    have := Bottcher.analyticOnNhd_zeros_countable hG hconnS hz₁ hGz₁
    refine this.mono ?_
    intro z hz
    exact ⟨hz.1, hz.2⟩
  have hS'count : S'.Countable := hScount.union hZcount
  have hS'compl : S'ᶜ = {z | z ∈ Sᶜ ∧ G z ≠ 0} := by
    ext z
    simp only [hS'def, hZdef, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or,
      not_and]
    constructor
    · rintro ⟨hzS, hzZ⟩
      exact ⟨hzS, hzZ hzS⟩
    · rintro ⟨hzS, hzG⟩
      exact ⟨hzS, fun _ => hzG⟩
  have hS'open : IsOpen (S'ᶜ) := by
    rw [hS'compl]
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    have hzS : z ∈ Sᶜ := hz.1
    have hGz : G z ≠ 0 := hz.2
    have hcont : ContinuousAt G z := (hG z hzS).continuousAt
    have h1 : {w : ℂ | G w ≠ 0} ∈ nhds z := hcont.eventually_ne hGz
    have h2 : Sᶜ ∈ nhds z := hSclosed.isOpen_compl.mem_nhds hzS
    exact Filter.inter_mem h2 h1
  have hS'closed : IsClosed S' := by
    rw [← isOpen_compl_iff]
    exact hS'open
  have hSsub : S ⊆ S' := Set.subset_union_left
  have hGne' : ∀ z ∈ S'ᶜ, G z ≠ 0 := by
    intro z hz
    rw [hS'compl] at hz
    exact hz.2
  have hS'sub : S'ᶜ ⊆ Sᶜ := Set.compl_subset_compl.2 hSsub
  have hGS' : AnalyticOnNhd ℂ G S'ᶜ := fun z hz => hG z (hS'sub hz)
  -- the logarithmic derivative is hypertranscendental on the enlarged domain
  set L : ℂ → ℂ := fun z => deriv G z / G z with hLdef
  have hz₁' : z₁ ∈ S'ᶜ := by
    rw [hS'compl]
    exact ⟨hz₁, hGz₁⟩
  have hS'ne : (S'ᶜ).Nonempty := ⟨z₁, hz₁'⟩
  have hS'conn : IsPreconnected (S'ᶜ) := isPreconnected_compl_of_countable hS'count hz₁'
  have hS'inf : (S'ᶜ).Infinite := infinite_compl_of_countable hS'count
  have hLanal : AnalyticOnNhd ℂ L S'ᶜ := hGS'.deriv.div hGS' hGne'
  have hLht : ¬ DifferentiallyAlgebraicOn L S'ᶜ := by
    intro hLDA
    have hGDA' : DifferentiallyAlgebraicOn G S'ᶜ :=
      (differentiallyAlgebraicOn_logDeriv_iff hS'open hS'conn hS'ne hS'inf hGS' hGne').1 hLDA
    exact hGht (differentiallyAlgebraicOn_of_subdomain hconnS hG hS'sub hS'open hS'ne hGDA')
  refine ⟨S', hS'closed, hS'count, hSsub, hGne', ?_⟩
  refine Set.Countable.mono ?_ (countable_defectDAStabilizer hS'closed hS'count hLanal hLht)
  intro h hh
  set D : Set ℂ := defectDomain S' h with hDdef
  have hDopen : IsOpen D := isOpen_defectDomain hS'closed h
  have hDcount : (defectSingularSet S' h).Countable := countable_defectSingularSet hS'count h
  obtain ⟨w₀, hw₀⟩ : D.Nonempty := nonempty_compl_of_countable hDcount
  have hDconn : IsPreconnected D := isPreconnected_compl_of_countable hDcount hw₀
  have hDinf : D.Infinite := infinite_compl_of_countable hDcount
  have hmemS' : ∀ z ∈ D, z ∈ S'ᶜ := fun z hz => defectDomain_subset_compl S' h hz
  have hmemS'shift : ∀ z ∈ D, z + h ∈ S'ᶜ := fun z hz => defectDomain_shift_mem_compl hz
  set Q : ℂ → ℂ := fun z => G (z + h) / G z with hQdef
  have hGshift : AnalyticOnNhd ℂ (fun z => G (z + h)) D := by
    intro z hz
    have h1 : AnalyticAt ℂ G (z + h) := hGS' _ (hmemS'shift z hz)
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (𝕜 := ℂ) (g := G) (f := fun w : ℂ => w + h) (x := z) h1 hinner
  have hGD : AnalyticOnNhd ℂ G D := fun z hz => hGS' _ (hmemS' z hz)
  have hGneD : ∀ z ∈ D, G z ≠ 0 := fun z hz => hGne' _ (hmemS' z hz)
  have hGneDshift : ∀ z ∈ D, G (z + h) ≠ 0 := fun z hz => hGne' _ (hmemS'shift z hz)
  have hQanal : AnalyticOnNhd ℂ Q D := hGshift.div hGD hGneD
  have hQne : ∀ z ∈ D, Q z ≠ 0 := fun z hz => div_ne_zero (hGneDshift z hz) (hGneD z hz)
  have hlogQ : DifferentiallyAlgebraicOn (fun z => deriv Q z / Q z) D :=
    (differentiallyAlgebraicOn_logDeriv_iff hDopen hDconn ⟨w₀, hw₀⟩ hDinf hQanal hQne).2 hh
  have hEq : Set.EqOn (fun z => deriv Q z / Q z) (fun z => L (z + h) - L z) D := by
    intro z hz
    have hGz : DifferentiableAt ℂ G z := (hGD z hz).differentiableAt
    have hGzh : DifferentiableAt ℂ G (z + h) :=
      (hGS' _ (hmemS'shift z hz)).differentiableAt
    have hQderiv := deriv_div
      (hGzh.comp z (differentiableAt_id.add_const h)) hGz (hGneD z hz)
    change deriv (fun u => G (u + h) / G u) z =
      (deriv (fun u => G (u + h)) z * G z - G (z + h) * deriv G z) / G z ^ 2
      at hQderiv
    show deriv (fun u => G (u + h) / G u) z / (G (z + h) / G z) =
      deriv G (z + h) / G (z + h) - deriv G z / G z
    rw [hQderiv, deriv_comp_add_const]
    field_simp [hGneD z hz, hGneDshift z hz]
  obtain ⟨n, P, hP0, hPv⟩ := hlogQ
  refine ⟨n, P, hP0, fun z hz => ?_⟩
  have hev : (fun z => deriv Q z / Q z) =ᶠ[nhds z] (fun z => L (z + h) - L z) := by
    filter_upwards [hDopen.mem_nhds hz] with w hw using hEq hw
  have hjet : (Fin.cons z (fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun z => L (z + h) - L z) z) : Fin (n + 2) → ℂ)
      = Fin.cons z (fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun z => deriv Q z / Q z) z) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        simp only [Fin.cons_succ]
        exact (Filter.EventuallyEq.iteratedDeriv_eq (j : ℕ) hev).symm
  rw [hjet]
  exact hPv z hz

end

end GaloisForLFunctions.HTGeometry
