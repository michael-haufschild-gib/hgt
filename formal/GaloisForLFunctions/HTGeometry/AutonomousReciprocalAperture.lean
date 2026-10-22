import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.InverseJetIndependence
import GaloisForLFunctions.HTGeometry.AllJetLevelSet

/-!
# Autonomous differential order is invariant under reciprocals; finite Euler products

For a nonzero element `u` of a differential field extension, the jets `u, u', ..., u^(n)` are
algebraically independent over the base exactly when the jets of `u⁻¹` are, since both generate the same
jet field at each order. Transported to analytic functions through the field of meromorphic functions
on a domain, this shows that a nonvanishing analytic `f` satisfies a nonzero autonomous algebraic
differential equation of order `n` along the real axis if and only if `1/f` does, so the minimal
autonomous order of `f` and `1/f` coincide. Applied to the finite Euler product
`t ↦ Π_(p ∈ S) (1 - p^(-1 - i t))⁻¹`, written as the reciprocal of a polynomial phase observable on the
strip `|Im t| < 1`, its minimal autonomous order equals the number of primes in `S`.

## Main results

- `algebraicIndependent_fin_jets_inv_iff`: for `u ≠ 0`, the jets of `u⁻¹` up to order `n` are
  algebraically independent iff those of `u` are.
- `exists_realAutonomousAnnihilator_inv_iff`: a nonvanishing analytic `f` has a nonzero order-`n`
  autonomous real-axis annihilator iff `1/f` has one.
- `autonomousMinimalOrder_inv_eq`: `autonomousMinimalOrder (1/f) = autonomousMinimalOrder f`.
- `autonomousMinimalOrder_finiteEulerProductPhase_eq`: the finite Euler product phase over a finite set
  `S` of primes has minimal autonomous order `|S|`.

## Hypotheses

The results are unconditional. The analytic statements assume that the domain `U` is open, preconnected,
contains `0` (and, for the converse direction, the whole real axis), and that `f` is analytic and
nonvanishing on `U`. The Euler product result has no hypotheses beyond the finite set of primes.
-/

open Complex Set Filter Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section


/-- For `u ≠ 0` in a differential field extension, algebraic independence of the jets of `u` of order
at most `n` implies that of the jets of `u⁻¹`; the inductive step uses that `u` and `u⁻¹` have the same
jet field at every order. -/
theorem algebraicIndepOn_jets_inv_Iic_of
    {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    {u : K} (hu : u ≠ 0) : ∀ n : ℕ,
    AlgebraicIndepOn F (fun i : ℕ => differentialJet i u) (Set.Iic n) →
      AlgebraicIndepOn F (fun i : ℕ => differentialJet i u⁻¹) (Set.Iic n) := by
  intro n
  induction n with
  | zero =>
      intro h
      have hset : (Set.Iic 0 : Set ℕ) = {0} := by
        ext m
        simp
      rw [hset] at h ⊢
      have htrans : Transcendental F (differentialJet 0 u⁻¹) := by
        rw [differentialJet_zero]
        intro halg
        have hu0 : IsAlgebraic F u := IsAlgebraic.inv_iff.mp halg
        have htransu : Transcendental F (differentialJet 0 u) :=
          (algebraicIndependent_unique_type_iff
            (x := fun i : ↥({0} : Set ℕ) => differentialJet (i : ℕ) u)).mp h
        rw [differentialJet_zero] at htransu
        exact htransu hu0
      exact (algebraicIndependent_unique_type_iff
        (x := fun i : ↥({0} : Set ℕ) => differentialJet (i : ℕ) u⁻¹)).mpr htrans
  | succ n ih =>
      intro h
      have hset : (Set.Iic (n + 1) : Set ℕ) = insert (n + 1) (Set.Iic n) := by
        ext m
        simp [Nat.le_succ_iff_eq_or_le, or_comm]
      have hnot : (n + 1) ∉ (Set.Iic n : Set ℕ) := by simp
      rw [hset] at h ⊢
      rw [AlgebraicIndepOn.insert_iff hnot] at h ⊢
      refine ⟨ih h.1, ?_⟩
      have hu_trans : Transcendental
          (Algebra.adjoin F ((fun i : ℕ => differentialJet i u) '' Set.Iic n))
          (differentialJet (n + 1) u) := h.2
      rw [transcendental_algebraAdjoin_iff]
      rw [transcendental_algebraAdjoin_iff] at hu_trans
      have hfield : IntermediateField.adjoin F
          ((fun i : ℕ => differentialJet i u⁻¹) '' Set.Iic n) = jetFieldLe F u n := by
        show jetFieldLe F u⁻¹ n = jetFieldLe F u n
        exact jetFieldLe_inv F hu n
      rw [hfield]
      intro halg
      exact hu_trans ((isAlgebraic_differentialJet_succ_inv_iff hu n).mp halg)

/-- For `u ≠ 0`, the jets `u⁻¹, (u⁻¹)', ..., (u⁻¹)^(n)` are algebraically independent over `F` if and
only if `u, u', ..., u^(n)` are. -/
theorem algebraicIndependent_fin_jets_inv_iff
    {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    {u : K} (hu : u ≠ 0) (n : ℕ) :
    AlgebraicIndependent F (fun i : Fin (n + 1) => differentialJet (i : ℕ) u⁻¹) ↔
      AlgebraicIndependent F (fun i : Fin (n + 1) => differentialJet (i : ℕ) u) := by
  constructor
  · intro h
    have hinv : u⁻¹ ≠ 0 := inv_ne_zero hu
    let e : ↥(Set.Iic n) → Fin (n + 1) := fun i =>
      ⟨(i : ℕ), Nat.lt_succ_of_le i.2⟩
    have he : Function.Injective e := by
      intro i j hij
      exact Subtype.ext (congrArg Fin.val hij)
    have hIic : AlgebraicIndepOn F
        (fun i : ℕ => differentialJet i u⁻¹) (Set.Iic n) := by
      simpa [AlgebraicIndepOn, Function.comp_def, e] using h.comp e he
    have hback := algebraicIndepOn_jets_inv_Iic_of hinv n hIic
    let r : Fin (n + 1) → ↥(Set.Iic n) := fun i =>
      ⟨(i : ℕ), Nat.le_of_lt_succ i.2⟩
    have hr : Function.Injective r := by
      intro i j hij
      exact Fin.ext (congrArg Subtype.val hij)
    have := hback.comp r hr
    simpa [Function.comp_def, r] using this
  · intro h
    let e : ↥(Set.Iic n) → Fin (n + 1) := fun i =>
      ⟨(i : ℕ), Nat.lt_succ_of_le i.2⟩
    have he : Function.Injective e := by
      intro i j hij
      exact Subtype.ext (congrArg Fin.val hij)
    have hIic : AlgebraicIndepOn F
        (fun i : ℕ => differentialJet i u) (Set.Iic n) := by
      simpa [AlgebraicIndepOn, Function.comp_def, e] using h.comp e he
    have hforward := algebraicIndepOn_jets_inv_Iic_of hu n hIic
    let r : Fin (n + 1) → ↥(Set.Iic n) := fun i =>
      ⟨(i : ℕ), Nat.le_of_lt_succ i.2⟩
    have hr : Function.Injective r := by
      intro i j hij
      exact Fin.ext (congrArg Subtype.val hij)
    have := hforward.comp r hr
    simpa [Function.comp_def, r] using this

variable {U : Set ℂ}

/-- On an open preconnected nonempty `U`, a polynomial vanishes on the jets of the meromorphic element
of an analytic `f` iff the same polynomial in the iterated derivatives of `f` vanishes at every point
of `U`. -/
theorem aeval_analyticMero_jets_eq_zero_iff
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
    letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
    letI := meroFieldDifferential hUo hUc hUne
    MvPolynomial.aeval
        (fun j : Fin m => differentialJet (j : ℕ) (analyticMeroElement f hf)) P = 0 ↔
      ∀ z ∈ U, MvPolynomial.eval
        (fun j : Fin m => iteratedDeriv (j : ℕ) f z) P = 0 := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI := meroFieldDifferential hUo hUc hUne
  rw [MvPolynomial.aeval_def]
  have hjets : (fun j : Fin m =>
      differentialJet (j : ℕ) (analyticMeroElement f hf)) =
      fun j : Fin m => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ)) := by
    funext j
    exact differentialJet_analyticMeroElement hUo hUc hUne f hf (j : ℕ)
  rw [hjets]
  have hmeroJets : (fun j : Fin m =>
      algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) =
      fun j : Fin m => analyticMeroElement (iteratedDeriv (j : ℕ) f)
        (analyticOnNhd_iteratedDeriv hf (j : ℕ)) := by
    funext j
    rfl
  rw [hmeroJets]
  have hconst : (algebraMap ℂ (meroField U)) = constToMero U := by
    rfl
  rw [hconst]
  rw [← analyticMeroElement_eval_mvPolynomial
    (fun j : Fin m => iteratedDeriv (j : ℕ) f)
    (fun j => analyticOnNhd_iteratedDeriv hf (j : ℕ)) P]
  exact analyticMeroElement_eq_zero_iff
    (analyticOnNhd_eval_mvPolynomial
      (fun j : Fin m => iteratedDeriv (j : ℕ) f)
      (fun j => analyticOnNhd_iteratedDeriv hf (j : ℕ)) P)

theorem analyticMeroElement_congrOn
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hfg : Set.EqOn f g U) :
    analyticMeroElement f hf = analyticMeroElement g hg := by
  unfold analyticMeroElement
  congr 1
  apply Subtype.ext
  change ((f : ℂ → ℂ) : Germ (Filter.principal U) ℂ) =
    ((g : ℂ → ℂ) : Germ (Filter.principal U) ℂ)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr hfg

/-- For `f` analytic and nonvanishing on `U`, the meromorphic element of `1/f` is the inverse of the
meromorphic element of `f`. -/
theorem analyticMeroElement_inv
    [IsDomain (analyticSubring U)]
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ z ∈ U, f z ≠ 0) :
    analyticMeroElement (fun z => (f z)⁻¹)
        (fun z hz => (hf z hz).inv (hne z hz)) =
      (analyticMeroElement f hf)⁻¹ := by
  let g : ℂ → ℂ := fun z => (f z)⁻¹
  have hg : AnalyticOnNhd ℂ g U := fun z hz => (hf z hz).inv (hne z hz)
  have hmul : analyticMeroElement f hf * analyticMeroElement g hg = 1 := by
    rw [← analyticMeroElement_mul hf hg]
    rw [analyticMeroElement_congrOn (hf.mul hg) analyticOnNhd_const
      (fun z hz => mul_inv_cancel₀ (hne z hz))]
    rw [analyticMeroElement_const]
    exact map_one (constToMero U)
  simpa [g] using eq_inv_of_mul_eq_one_right hmul

/-- Identity principle on the real axis: an analytic function on a preconnected `U ∋ 0` that vanishes at
every real point vanishes on all of `U`. -/
theorem eqOn_zero_of_analyticOnNhd_of_eq_ofReal
    {E : ℂ → ℂ} (hUc : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (hE : AnalyticOnNhd ℂ E U) (hreal : ∀ t : ℝ, E (t : ℂ) = 0) :
    ∀ z ∈ U, E z = 0 := by
  have hbase : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (nhds (0 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    rw [Complex.ofReal_zero] at hc
    exact hc
  have hpunc : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase ?_
    filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  have hfreq : ∃ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, E w = 0 :=
    hpunc.frequently (Filter.Frequently.of_forall fun n => hreal _)
  exact hE.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hzero hfreq

/-- A nonzero autonomous algebraic differential relation of order `n` satisfied by `f` along the real
axis makes the jets of `f` up to order `n` algebraically dependent over `ℂ` in the meromorphic function
field of `U`. -/
theorem not_algebraicIndependent_analyticMero_jets_of_realAutonomousAnnihilator
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hP : P ≠ 0)
    (hann : RealAutonomousAnnihilator f n P) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc ⟨0, hzero⟩
    letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
    letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
    letI := meroFieldDifferential hUo hUc ⟨0, hzero⟩
    ¬ AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (analyticMeroElement f hf)) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc ⟨0, hzero⟩
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI := meroFieldDifferential hUo hUc ⟨0, hzero⟩
  let H := lastVariableJetLift P
  have hH : H ≠ 0 := lastVariableJetLift_ne_zero hP
  have hpoint : ∀ z ∈ U, MvPolynomial.eval
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) H = 0 := by
    apply eqOn_zero_of_analyticOnNhd_of_eq_ofReal hUc hzero
      (analyticOnNhd_eval_mvPolynomial
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f)
        (fun j => analyticOnNhd_iteratedDeriv hf (j : ℕ)) H)
    intro t
    rw [eval_jetLift]
    simpa using hann t
  have hfield := (aeval_analyticMero_jets_eq_zero_iff hUo hUc ⟨0, hzero⟩ hf H).mpr hpoint
  intro hAI
  apply hH
  exact (algebraicIndependent_iff.mp hAI) H hfield

/-- Conversely, if `U` contains the real axis and the jets of `f` up to order `n` are algebraically
dependent in the meromorphic function field, then `f` has a nonzero autonomous real-axis annihilator of
order `n`. -/
theorem exists_realAutonomousAnnihilator_of_not_algebraicIndependent_analyticMero_jets
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {n : ℕ}
    (hdep :
      letI := Bottcher.isDomain_analyticSubring U hUo hUc ⟨0, hzero⟩
      letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
      letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
      letI := meroFieldDifferential hUo hUc ⟨0, hzero⟩
      ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ)
          (analyticMeroElement f hf))) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator f n P := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc ⟨0, hzero⟩
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI := meroFieldDifferential hUo hUc ⟨0, hzero⟩
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨H, hfield, hH⟩ := hdep
  have hpoint := (aeval_analyticMero_jets_eq_zero_iff hUo hUc ⟨0, hzero⟩ hf H).mp hfield
  refine ⟨jetUnlift H, jetUnlift_ne_zero hH, ?_⟩
  intro t
  let a : Fin (n + 1) → ℂ :=
    fun j => iteratedDeriv (j : ℕ) f (t : ℂ)
  change Polynomial.eval₂ (MvPolynomial.eval fun j : Fin n => a j.castSucc)
    (a (Fin.last n)) (jetUnlift H) = 0
  rw [← eval_jetLift a, lastVariableJetLift_jetUnlift]
  exact hpoint (t : ℂ) (hreal t)

/-- Constants have zero derivative in the differential field of meromorphic functions on `U`. -/
theorem meroField_deriv_constToMero_eq_zero
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c : ℂ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
    letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
    letI := meroFieldDifferential hUo hUc hUne
    (algebraMap ℂ (meroField U) c)′ = 0 := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  change (algebraMap (analyticSubring U) (meroField U)
    (constToAnalytic U c))′ = 0
  rw [meroFieldDifferential_algebraMap hUo hUc hUne]
  have hconst : analyticSubringDeriv hUo (constToAnalytic U c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    let f : ℂ → ℂ := fun _ => c
    calc
      Germ.coeRingHom (Filter.principal U) (deriv f) =
          Germ.coeRingHom (Filter.principal U) (0 : ℂ → ℂ) := by
        congr 1
        funext z
        simp [f]
      _ = 0 := (Germ.coeRingHom (Filter.principal U)).map_zero
  rw [hconst, map_zero]

/-- Reciprocal invariance of autonomous relations: for `f` analytic and nonvanishing on an open
preconnected `U` containing the real axis, `1/f` satisfies a nonzero autonomous algebraic differential
equation of order `n` along the real axis iff `f` does. -/
theorem exists_realAutonomousAnnihilator_inv_iff
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ z ∈ U, f z ≠ 0) (n : ℕ) :
    (∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
        RealAutonomousAnnihilator (fun z => (f z)⁻¹) n P) ↔
      ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
        RealAutonomousAnnihilator f n P := by
  let hUne : U.Nonempty := ⟨0, hzero⟩
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI : Differential ℂ := ⟨0⟩
  letI := meroFieldDifferential hUo hUc hUne
  letI : DifferentialAlgebra ℂ (meroField U) :=
    ⟨fun c => by
      rw [meroField_deriv_constToMero_eq_zero hUo hUc hUne]
      change (0 : meroField U) = algebraMap ℂ (meroField U) 0
      rw [map_zero]⟩
  let g : ℂ → ℂ := fun z => (f z)⁻¹
  have hg : AnalyticOnNhd ℂ g U := fun z hz => (hf z hz).inv (hne z hz)
  let u : meroField U := analyticMeroElement f hf
  let v : meroField U := analyticMeroElement g hg
  have hu : u ≠ 0 := by
    intro hu0
    have hall := (analyticMeroElement_eq_zero_iff hf).mp hu0
    exact hne 0 hzero (hall 0 hzero)
  have hv : v = u⁻¹ := by
    simpa [u, v, g] using analyticMeroElement_inv hf hne
  constructor
  · rintro ⟨P, hP, hann⟩
    have hdepv : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) v) := by
      simpa [v, g] using
        (not_algebraicIndependent_analyticMero_jets_of_realAutonomousAnnihilator
          hUo hUc hzero hg hP hann)
    have hdepinv : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) u⁻¹) := by
      simpa only [hv] using hdepv
    have hdepu : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) u) :=
      (not_congr (algebraicIndependent_fin_jets_inv_iff hu n)).mp hdepinv
    exact exists_realAutonomousAnnihilator_of_not_algebraicIndependent_analyticMero_jets
      hUo hUc hzero hreal hf (by simpa [u] using hdepu)
  · rintro ⟨P, hP, hann⟩
    have hdepu : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) u) := by
      simpa [u] using
        (not_algebraicIndependent_analyticMero_jets_of_realAutonomousAnnihilator
          hUo hUc hzero hf hP hann)
    have hdepinv : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) u⁻¹) :=
      (not_congr (algebraicIndependent_fin_jets_inv_iff hu n)).mpr hdepu
    have hdepv : ¬ AlgebraicIndependent ℂ
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) v) := by
      simpa only [hv] using hdepinv
    exact exists_realAutonomousAnnihilator_of_not_algebraicIndependent_analyticMero_jets
      hUo hUc hzero hreal hg (by simpa [v, g] using hdepv)

/-- Under the same domain and nonvanishing hypotheses, the minimal autonomous order of `1/f` equals that
of `f`. -/
theorem autonomousMinimalOrder_inv_eq
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ z ∈ U, f z ≠ 0) :
    autonomousMinimalOrder (fun z => (f z)⁻¹) = autonomousMinimalOrder f := by
  unfold autonomousMinimalOrder
  congr 1
  ext n
  exact exists_realAutonomousAnnihilator_inv_iff
    hUo hUc hzero hreal hf hne n

/-- The polyannulus radii `log p` attached to the primes of a finite set `S`. -/
def finitePrimeRadius (S : Finset Nat.Primes) :
    Fin (Fintype.card ↥S) → ℝ :=
  fun i => Real.log ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ))

theorem finitePrimeRadius_pos (S : Finset Nat.Primes)
    (i : Fin (Fintype.card ↥S)) : 0 < finitePrimeRadius S i := by
  apply Real.log_pos
  exact_mod_cast (finitePrimeAt S i).2.one_lt

/-- On the phase strip, the inverse Euler factor product `Π_(p ∈ S) (1 - p^(-1) p^(-i t))` never vanishes,
since each term `p^(-1) p^(-i t)` has modulus less than one there. -/
theorem finiteEulerInverseAnchorPhase_ne_zero
    (S : Finset Nat.Primes) :
    ∀ z ∈ phaseStrip (finitePrimeRadius S) (finitePrimeFrequency S),
      phaseFunction (finitePrimeFrequency S)
        (polynomialPhaseObservable
          (eulerInverseAnchorPolynomial (finitePrimeDamping S))) z ≠ 0 := by
  intro z hz
  simp only [phaseFunction, polynomialPhaseObservable,
    eulerInverseAnchorPolynomial, map_prod, map_sub, map_one, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply sub_ne_zero.mpr
  intro heq
  have hphase : ‖phasePoint (finitePrimeFrequency S) z i‖ <
      Real.exp (finitePrimeRadius S i) := by
    have hi := hz i
    have hi' : |-(finitePrimeFrequency S i * z.im)| < finitePrimeRadius S i := by
      simpa only [abs_neg] using hi
    rw [norm_phasePoint]
    exact Real.exp_lt_exp.mpr (lt_of_le_of_lt (le_abs_self _) hi')
  have hexp : Real.exp (finitePrimeRadius S i) =
      ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) := by
    rw [finitePrimeRadius, Real.exp_log]
    exact_mod_cast (finitePrimeAt S i).2.pos
  have hp0 : (0 : ℝ) < ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) := by
    exact_mod_cast (finitePrimeAt S i).2.pos
  have hdamp : ‖finitePrimeDamping S i‖ =
      ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ))⁻¹ := by
    simp [finitePrimeDamping]
  have hnorm : ‖finitePrimeDamping S i *
      phasePoint (finitePrimeFrequency S) z i‖ < 1 := by
    rw [hexp] at hphase
    rw [norm_mul, hdamp]
    rwa [inv_mul_lt_one₀ hp0]
  rw [← heq, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- The finite Euler product `t ↦ Π_(p ∈ S) (1 - p^(-1 - i t))⁻¹`, written as the reciprocal of the phase
function of the polynomial `Π_i (1 - X_i / p_i)` along the frequencies `-log p`. -/
def finiteEulerProductPhase (S : Finset Nat.Primes) : ℂ → ℂ :=
  fun z =>
    (phaseFunction (finitePrimeFrequency S)
      (polynomialPhaseObservable
        (eulerInverseAnchorPolynomial (finitePrimeDamping S))) z)⁻¹

/-- The finite Euler product phase over `S` has minimal autonomous order exactly `|S|`: the polynomial
phase has order `|S|` by rational independence of the `log p`, and reciprocals preserve the order. -/
theorem autonomousMinimalOrder_finiteEulerProductPhase_eq
    (S : Finset Nat.Primes) :
    autonomousMinimalOrder (finiteEulerProductPhase S) = Fintype.card ↥S := by
  let rho := finitePrimeRadius S
  let omega := finitePrimeFrequency S
  let F := polynomialPhaseObservable
    (eulerInverseAnchorPolynomial (finitePrimeDamping S))
  have hrho : ∀ i, 0 < rho i := finitePrimeRadius_pos S
  have hF : AnalyticOnNhd ℂ F (polyannulus rho) :=
    analyticOnNhd_polynomialPhaseObservable _ _
  have hinv := autonomousMinimalOrder_inv_eq
    (U := phaseStrip rho omega)
    (isOpen_phaseStrip rho omega)
    (isPreconnected_phaseStrip rho omega)
    (zero_mem_phaseStrip hrho)
    (ofReal_mem_phaseStrip hrho)
    (analyticOnNhd_phaseFunction hF)
    (finiteEulerInverseAnchorPhase_ne_zero S)
  rw [show finiteEulerProductPhase S =
      fun z => (phaseFunction omega F z)⁻¹ by rfl]
  rw [hinv]
  exact autonomousMinimalOrder_eulerInverseAnchorPhase_eq
    hrho omega
    (finitePrimeFrequency_rationallyIndependent S)
    (finitePrimeFrequency_injective S)
    (finitePrimeDamping S)
    (finitePrimeDamping_ne_zero S)

end
end GaloisForLFunctions.HTGeometry
