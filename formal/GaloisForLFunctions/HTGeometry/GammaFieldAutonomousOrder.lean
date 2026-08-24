import GaloisForLFunctions.HTGeometry.GammaFieldLawInstanceFree
import GaloisForLFunctions.HTGeometry.MvPolynomialDiagonalScaleDomain
import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture
import GaloisForLFunctions.HTGeometry.SpectralAffineGauge
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.VerticalPhaseRank
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.GammaCoefficientLawWitness
import GaloisForLFunctions.HTGeometry.FiniteEulerApertureCompletion
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth

open Complex Set Filter Topology
open scoped Differential BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaOrderDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaOrderIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaOrderDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaOrderComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaOrderRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

def verticalLineComplex (σ : ℝ) (Φ : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Φ (Complex.I * z + (σ : ℂ))

def verticalJetScale {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  mvPolynomialDiagonalScaleRing
    (fun i : Fin (n + 1) => (-Complex.I) ^ (i : ℕ)) Q

theorem verticalJetScale_ne_zero {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) ℂ}
    (hQ : Q ≠ 0) : verticalJetScale Q ≠ 0 := by
  apply mvPolynomialDiagonalScaleRing_ne_zero_field _ _ hQ
  intro i
  exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)

theorem eval_verticalJetScale {n : ℕ} (a : Fin (n + 1) → ℂ)
    (Q : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval a (verticalJetScale Q) =
      MvPolynomial.eval
        (fun i : Fin (n + 1) => (-Complex.I) ^ (i : ℕ) * a i) Q := by
  rw [verticalJetScale, mvPolynomialDiagonalScaleRing,
    GaloisForLFunctions.eval_bind₁]
  have hfun :
      (fun i : Fin (n + 1) => MvPolynomial.eval a
        (MvPolynomial.C ((-Complex.I) ^ (i : ℕ)) * MvPolynomial.X i)) =
      fun i : Fin (n + 1) => (-Complex.I) ^ (i : ℕ) * a i := by
    funext i
    simp
  rw [hfun]

theorem iteratedDeriv_verticalLineComplex (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ)
    (σ : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (verticalLineComplex σ Φ) z =
      Complex.I ^ k * iteratedDeriv k Φ (Complex.I * z + (σ : ℂ)) := by
  let g : Fin 1 → ℂ → ℂ := fun _ => Φ
  have h := iteratedDeriv_comp_affine_eq
    (U := Set.univ) (V := Set.univ) (g := g) isOpen_univ
    (fun _ _ _ => hΦ.contDiff.contDiffAt) isOpen_univ
    (a := Complex.I) (b := (σ : ℂ)) (fun _ _ => Set.mem_univ _) 0 k z (Set.mem_univ z)
  change iteratedDeriv k (fun v => Φ (Complex.I * v + (σ : ℂ))) z = _
  exact h

theorem exists_realAutonomousAnnihilator_verticalLineComplex_of_stripRelation
    {n : ℕ} {σ R : ℝ} {Φ : ℂ → ℂ} (hR : 0 < R) (hΦ : Differentiable ℂ Φ)
    {Q : MvPolynomial (Fin (n + 1)) ℂ} (hQ : Q ≠ 0)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) Q = 0) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (verticalLineComplex σ Φ) n P := by
  let Qv := verticalJetScale Q
  refine ⟨jetUnlift Qv, jetUnlift_ne_zero (verticalJetScale_ne_zero hQ), ?_⟩
  intro t
  let a : Fin (n + 1) → ℂ :=
    fun i => iteratedDeriv (i : ℕ) (verticalLineComplex σ Φ) (t : ℂ)
  have hlift := eval_jetLift a (jetUnlift Qv)
  rw [lastVariableJetLift_jetUnlift] at hlift
  have htwo : Polynomial.eval₂
      (MvPolynomial.eval fun j : Fin n =>
        iteratedDeriv (j : ℕ) (verticalLineComplex σ Φ) (t : ℂ))
      (iteratedDeriv n (verticalLineComplex σ Φ) (t : ℂ)) (jetUnlift Qv) =
      MvPolynomial.eval a Qv := by
    simpa [a] using hlift.symm
  rw [htwo]
  rw [eval_verticalJetScale]
  have hjets : (fun i : Fin (n + 1) => (-Complex.I) ^ (i : ℕ) * a i) =
      fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ
        ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext i
    rw [show a i = Complex.I ^ (i : ℕ) * iteratedDeriv (i : ℕ) Φ
        (Complex.I * (t : ℂ) + (σ : ℂ)) by
      exact iteratedDeriv_verticalLineComplex Φ hΦ σ (i : ℕ) (t : ℂ)]
    have hpow : (-Complex.I) ^ (i : ℕ) * Complex.I ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [← mul_assoc, hpow, one_mul]
    congr 1
    ring
  rw [hjets]
  exact hrel _ (by simpa [verticalStrip] using hR)

theorem autonomousMinimalOrder_verticalLineComplex_le_of_gammaField_relation
    {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0)
    (hrel : ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
      (differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun y => f y)) (hftb : HasTotallyBoundedOrbit (fun y => f y)) :
    autonomousMinimalOrder (verticalLineComplex σ Φ) ≤ n := by
  obtain ⟨β, d, hdβ, hdrel, hd0, _⟩ :=
    finite_phase_law_of_gammaField_relation' hσ hN hr hρ hrρ hR
      (hΦ.differentiableOn) hap e he Ψ hΨ x hxmem hx0 hrel hf hfu hftb
  let Q : MvPolynomial (Fin (n + 1)) ℂ :=
    ∑ α : Fin N, MvPolynomial.C (d α) *
      ∏ i : Fin (n + 1), (MvPolynomial.X i) ^ (e α i)
  apply autonomousMinimalOrder_le
  apply exists_realAutonomousAnnihilator_verticalLineComplex_of_stripRelation hR hΦ hd0
  intro z hz
  rw [← jetPoly_eq_mvEval]
  exact hdrel z hz

/-- A nonzero differential-polynomial relation of a specified order over
`ℂ(s)⟨Γ⟩`.  Distinct exponent vectors prevent duplicate monomial bookkeeping. -/
def GammaFieldRelationAtOrder (Ψ : upperEndAnalyticSubring) (n : ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ (e : Fin N → Fin (n + 1) → ℕ), Function.Injective e ∧
    ∃ x : Fin N → upperEndMeroField,
      (∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) ∧
      (∀ α, x α ≠ 0) ∧
      ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i) = 0

/-- Orders of nonzero autonomous relations over `ℂ(s)⟨Γ⟩`. -/
def gammaFieldOrderSet (Ψ : upperEndAnalyticSubring) : Set ℕ :=
  {n | GammaFieldRelationAtOrder Ψ n}

/-- Least autonomous differential order over the Euler--Gamma coefficient field. -/
def gammaFieldMinimalOrder (Ψ : upperEndAnalyticSubring) : ℕ :=
  sInf (gammaFieldOrderSet Ψ)

theorem gammaFieldMinimalOrder_le {Ψ : upperEndAnalyticSubring} {n : ℕ}
    (h : GammaFieldRelationAtOrder Ψ n) : gammaFieldMinimalOrder Ψ ≤ n :=
  Nat.sInf_le h

theorem gammaFieldRelationAtOrder_minimal {Ψ : upperEndAnalyticSubring} {n : ℕ}
    (h : GammaFieldRelationAtOrder Ψ n) :
    GammaFieldRelationAtOrder Ψ (gammaFieldMinimalOrder Ψ) :=
  by
    change gammaFieldMinimalOrder Ψ ∈ gammaFieldOrderSet Ψ
    exact Nat.sInf_mem ⟨n, h⟩

theorem autonomousMinimalOrder_verticalLineComplex_le_of_gammaFieldRelationAtOrder
    {n : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (hrel : GammaFieldRelationAtOrder Ψ n) :
    autonomousMinimalOrder (verticalLineComplex σ Φ) ≤ n := by
  obtain ⟨N, hN, e, he, x, hxmem, hx0, hrelation⟩ := hrel
  classical
  set f : ℝ →ᵇ ℂ := verticalRestriction Φ hR hΦ.differentiableOn hap
  have hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I) := fun _ => rfl
  have hfun : (fun y : ℝ => (f y : ℂ)) =
      fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I) := funext hf
  have hapline : _root_.HTGeometry.IsBohrAlmostPeriodic (fun y : ℝ => (f y : ℂ)) := by
    rw [hfun]
    exact isBohrAlmostPeriodic_line hR hap
  exact autonomousMinimalOrder_verticalLineComplex_le_of_gammaField_relation
    hσ hN hr hρ hrρ hR hΦ hap e he Ψ hΨ x hxmem hx0 hrelation hf
    (uniformContinuous_of_isBohrAlmostPeriodic f.continuous hapline)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic f.continuous hapline)

/-- Exact Gamma-relative order from one same-order relation and exact constant order.
The projective-boundary theorem supplies the lower inequality without loss of order. -/
theorem gammaFieldMinimalOrder_eq_of_autonomousMinimalOrder_eq
    {k : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (hconst : autonomousMinimalOrder (verticalLineComplex σ Φ) = k)
    (hex : GammaFieldRelationAtOrder Ψ k) :
    gammaFieldMinimalOrder Ψ = k := by
  apply le_antisymm (gammaFieldMinimalOrder_le hex)
  have hmin := gammaFieldRelationAtOrder_minimal hex
  rw [← hconst]
  exact autonomousMinimalOrder_verticalLineComplex_le_of_gammaFieldRelationAtOrder
    hσ hr hρ hrρ hR hΦ hap Ψ hΨ hmin

theorem exists_globalJetRelation_of_realAutonomousAnnihilator_verticalLineComplex
    {n : ℕ} {σ : ℝ} {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hP0 : P ≠ 0)
    (hP : RealAutonomousAnnihilator (verticalLineComplex σ Φ) n P) :
    ∃ Q : MvPolynomial (Fin (n + 1)) ℂ, Q ≠ 0 ∧
      ∀ s : ℂ, MvPolynomial.eval
        (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ s) Q = 0 := by
  let Qv := lastVariableJetLift P
  let Q : MvPolynomial (Fin (n + 1)) ℂ :=
    mvPolynomialDiagonalScaleRing
      (fun i : Fin (n + 1) => Complex.I ^ (i : ℕ)) Qv
  have hQv0 : Qv ≠ 0 := lastVariableJetLift_ne_zero hP0
  have hQ0 : Q ≠ 0 := by
    apply mvPolynomialDiagonalScaleRing_ne_zero_field _ _ hQv0
    intro i
    exact pow_ne_zero _ Complex.I_ne_zero
  refine ⟨Q, hQ0, fun s => ?_⟩
  let G : ℂ → ℂ := fun z => MvPolynomial.eval
    (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) (verticalLineComplex σ Φ) z) Qv
  have hgdiff : Differentiable ℂ (verticalLineComplex σ Φ) := by
    unfold verticalLineComplex
    fun_prop
  have hGreal : ∀ t : ℝ, MvPolynomial.eval
      (fun i : Fin (n + 1) =>
        iteratedDeriv (i : ℕ) (verticalLineComplex σ Φ) (t : ℂ)) Qv = 0 := by
    intro t
    let a : Fin (n + 1) → ℂ := fun i =>
      iteratedDeriv (i : ℕ) (verticalLineComplex σ Φ) (t : ℂ)
    have hlift := eval_jetLift a P
    change MvPolynomial.eval a Qv = 0
    rw [hlift]
    simpa [a] using hP t
  have hGdiff : Differentiable ℂ G := by
    intro z
    let Rz : ℝ := |z.re| + 1
    have hz : z ∈ verticalStrip 0 Rz := by
      simp only [verticalStrip, sub_zero]
      dsimp [Rz]
      linarith [le_abs_self z.re]
    have hd := (differentiableOn_mvEval_jets
      (σ := 0) (R := Rz) hgdiff.differentiableOn Qv) z hz
    exact hd.differentiableAt
      ((GaloisForLFunctions.isOpen_verticalStrip 0 Rz).mem_nhds hz)
  have hGanalytic : ∀ z, AnalyticAt ℂ G z := by
    have hGa : AnalyticOnNhd ℂ G Set.univ :=
      hGdiff.differentiableOn.analyticOnNhd isOpen_univ
    exact fun z => hGa z (Set.mem_univ z)
  have hGzero : ∀ z : ℂ, G z = 0 :=
    fun z => eq_zero_of_analytic_of_eqOn_real hGanalytic
      (fun t => by simpa [G] using hGreal t) z
  change MvPolynomial.eval
    (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ s)
      (mvPolynomialDiagonalScaleRing
        (fun i : Fin (n + 1) => Complex.I ^ (i : ℕ)) Qv) = 0
  rw [mvPolynomialDiagonalScaleRing, GaloisForLFunctions.eval_bind₁]
  have heval :
      (fun i : Fin (n + 1) => MvPolynomial.eval
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Φ s)
          (MvPolynomial.C (Complex.I ^ (i : ℕ)) * MvPolynomial.X i)) =
      fun i : Fin (n + 1) => Complex.I ^ (i : ℕ) * iteratedDeriv (i : ℕ) Φ s := by
    funext i
    simp
  rw [heval]
  let z : ℂ := -Complex.I * (s - (σ : ℂ))
  have hs : Complex.I * z + (σ : ℂ) = s := by
    dsimp [z]
    ring_nf
    norm_num
  have hjets :
      (fun i : Fin (n + 1) => Complex.I ^ (i : ℕ) * iteratedDeriv (i : ℕ) Φ s) =
      fun i : Fin (n + 1) =>
        iteratedDeriv (i : ℕ) (verticalLineComplex σ Φ) z := by
    funext i
    rw [iteratedDeriv_verticalLineComplex Φ hΦ σ (i : ℕ) z, hs]
  rw [hjets]
  simpa [G] using hGzero z

def upperEndComplexToAnalytic : ℂ →+* upperEndAnalyticSubring :=
  upperEndPolyToAnalytic.comp Polynomial.C

theorem upperEndComplexToAnalytic_subtype (c : ℂ) :
    upperEndAnalyticSubring.subtype (upperEndComplexToAnalytic c) =
      Germ.coeRingHom upperEndFilter (fun _ : ℂ => c) := by
  rw [upperEndComplexToAnalytic, RingHom.comp_apply, polyToAnalytic_subtype]
  congr 1
  funext z
  simp

theorem mvPolynomial_eval₂_upperEnd_eq_zero_of_globalJetRelation
    {n : ℕ} {Φ : ℂ → ℂ} (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : ∀ s : ℂ, MvPolynomial.eval
      (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ s) Q = 0) :
    MvPolynomial.eval₂ upperEndComplexToMero
      (fun i : Fin (n + 1) => differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) Q = 0 := by
  let A : upperEndAnalyticSubring :=
    MvPolynomial.eval₂ upperEndComplexToAnalytic
      (fun i : Fin (n + 1) => (upperEndAnalyticDeriv^[(i : ℕ)] Ψ)) Q
  have hjet : ∀ i : Fin (n + 1),
      upperEndAnalyticSubring.subtype (upperEndAnalyticDeriv^[(i : ℕ)] Ψ) =
        Germ.coeRingHom upperEndFilter
          (fun z : ℂ => iteratedDeriv (i : ℕ) Φ z) := by
    intro i
    exact upperEndAnalyticDeriv_iterate_repr (i : ℕ) Ψ Φ hΨ
  have hrepr : ∀ T : MvPolynomial (Fin (n + 1)) ℂ,
      upperEndAnalyticSubring.subtype
        (MvPolynomial.eval₂ upperEndComplexToAnalytic
          (fun i : Fin (n + 1) => (upperEndAnalyticDeriv^[(i : ℕ)] Ψ)) T) =
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => MvPolynomial.eval
          (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) T) := by
    intro T
    induction T using MvPolynomial.induction_on with
    | C c =>
        rw [MvPolynomial.eval₂_C, upperEndComplexToAnalytic_subtype]
        congr 1
        funext z
        simp
    | add P Q hP hQ =>
        rw [MvPolynomial.eval₂_add, map_add, hP, hQ, ← map_add]
        congr 1
        funext z
        simp
    | mul_X P i hP =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, hP, hjet i, ← map_mul]
        congr 1
        funext z
        simp
  have hA0 : A = 0 := by
    apply Subtype.ext
    change upperEndAnalyticSubring.subtype A = upperEndAnalyticSubring.subtype 0
    rw [show upperEndAnalyticSubring.subtype A =
        Germ.coeRingHom upperEndFilter
          (fun z : ℂ => MvPolynomial.eval
            (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) Q) by
      exact hrepr Q]
    rw [map_zero]
    have hfun : (fun z : ℂ => MvPolynomial.eval
        (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) Q) = 0 := by
      funext z
      exact hrel z
    rw [hfun, map_zero]
  have hmap := congrArg
    (algebraMap upperEndAnalyticSubring upperEndMeroField) hA0
  rw [map_zero] at hmap
  change MvPolynomial.eval₂ upperEndComplexToMero
      (fun i : Fin (n + 1) => differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) Q = 0
  rw [← hmap]
  dsimp [A]
  rw [MvPolynomial.hom_eval₂]
  congr 1
  · funext i
    exact differentialJet_algebraMap (i : ℕ) Ψ

theorem gammaFieldRelationAtOrder_of_mvPolynomial
    {n : ℕ} (Ψ : upperEndAnalyticSubring)
    (Q : MvPolynomial (Fin (n + 1)) ℂ) (hQ : Q ≠ 0)
    (hrel : MvPolynomial.eval₂ upperEndComplexToMero
      (fun i : Fin (n + 1) => differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) Q = 0) :
    GammaFieldRelationAtOrder Ψ n := by
  classical
  let M : ℕ := Q.support.card
  let d : Fin M → (Fin (n + 1) →₀ ℕ) := fun α =>
    ((Q.support.equivFin.symm α : {m // m ∈ Q.support}) : Fin (n + 1) →₀ ℕ)
  let e : Fin M → Fin (n + 1) → ℕ := fun α i => d α i
  let x : Fin M → upperEndMeroField := fun α => upperEndComplexToMero (Q.coeff (d α))
  have hsupp : Q.support.Nonempty := by
    by_contra hempty
    apply hQ
    rw [← MvPolynomial.support_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hempty
  have hM : 0 < M := by
    dsimp [M]
    exact Finset.card_pos.mpr hsupp
  refine ⟨M, hM, e, ?_, x, ?_, ?_, ?_⟩
  · intro α β hαβ
    apply Q.support.equivFin.symm.injective
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrFun hαβ i
  · intro α
    exact upperEndComplexToMero_mem_gammaAdjoin _
  · intro α
    apply upperEndComplexToMero_ne_zero
    exact MvPolynomial.mem_support_iff.mp
      (Q.support.equivFin.symm α).2
  · let y : Fin (n + 1) → upperEndMeroField := fun i =>
      differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)
    dsimp [x, e, d, M]
    calc
      (∑ α : Fin Q.support.card,
          upperEndComplexToMero
            (Q.coeff ((Q.support.equivFin.symm α : {m // m ∈ Q.support}) :
              Fin (n + 1) →₀ ℕ)) *
          ∏ i : Fin (n + 1), y i ^
            (((Q.support.equivFin.symm α : {m // m ∈ Q.support}) :
              Fin (n + 1) →₀ ℕ) i)) =
          ∑ m ∈ Q.support,
            upperEndComplexToMero (Q.coeff m) *
              ∏ i : Fin (n + 1), y i ^ m i := by
        rw [← Finset.sum_attach Q.support]
        refine Fintype.sum_equiv Q.support.equivFin.symm _ _ fun α => ?_
        rfl
      _ = MvPolynomial.eval₂ upperEndComplexToMero y Q := by
        rw [MvPolynomial.eval₂_eq]
        apply Finset.sum_congr rfl
        intro m hm
        congr 1
        exact (Finsupp.prod_fintype m (fun i k => y i ^ k) (fun i => pow_zero (y i))).symm
      _ = 0 := hrel

theorem gammaFieldRelationAtOrder_of_realAutonomousAnnihilator_verticalLineComplex
    {n : ℕ} {σ : ℝ} {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hP0 : P ≠ 0)
    (hP : RealAutonomousAnnihilator (verticalLineComplex σ Φ) n P) :
    GammaFieldRelationAtOrder Ψ n := by
  obtain ⟨Q, hQ, hglobal⟩ :=
    exists_globalJetRelation_of_realAutonomousAnnihilator_verticalLineComplex hΦ hP0 hP
  exact gammaFieldRelationAtOrder_of_mvPolynomial Ψ Q hQ
    (mvPolynomial_eval₂_upperEnd_eq_zero_of_globalJetRelation Ψ hΨ Q hglobal)

def monomialRealFrequency {d : Type} (omega : d → ℝ) (m : d →₀ ℕ) : ℝ :=
  ∑ i ∈ m.support, (m i : ℝ) * omega i

theorem prod_phasePoint_vertical_eq_exp_monomialRealFrequency
    {d : Type} [Fintype d] [DecidableEq d]
    (omega : d → ℝ) (m : d →₀ ℕ) (s : ℂ) :
    (∏ i ∈ m.support, phasePoint omega (-Complex.I * (s - 1)) i ^ m i) =
      Complex.exp ((monomialRealFrequency omega m : ℝ) * (s - 1)) := by
  have hterm : ∀ i : d, phasePoint omega (-Complex.I * (s - 1)) i ^ m i =
      Complex.exp ((((m i : ℝ) * omega i : ℝ) : ℂ) * (s - 1)) := by
    intro i
    rw [phasePoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
    norm_num
  rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.exp_sum]
  congr 1
  rw [monomialRealFrequency]
  push_cast
  rw [Finset.sum_mul]

def polynomialVerticalExpCoeff {d : Type} [Fintype d] [DecidableEq d]
    (omega : d → ℝ) (Q : MvPolynomial d ℂ) : Fin Q.support.card → ℂ :=
  fun α =>
    let m : d →₀ ℕ := ((Q.support.equivFin.symm α : {m // m ∈ Q.support}) : d →₀ ℕ)
    Q.coeff m * Complex.exp (-(monomialRealFrequency omega m : ℂ))

def polynomialVerticalExpFrequency {d : Type} [Fintype d] [DecidableEq d]
    (omega : d → ℝ) (Q : MvPolynomial d ℂ) : Fin Q.support.card → ℝ :=
  fun α =>
    monomialRealFrequency omega
      ((Q.support.equivFin.symm α : {m // m ∈ Q.support}) : d →₀ ℕ)

theorem phaseFunction_vertical_eq_expSum
    {d : Type} [Fintype d] [DecidableEq d]
    (omega : d → ℝ) (Q : MvPolynomial d ℂ) :
    (fun s : ℂ => phaseFunction omega (polynomialPhaseObservable Q)
      (-Complex.I * (s - 1))) =
      expSum (polynomialVerticalExpCoeff omega Q)
        (polynomialVerticalExpFrequency omega Q) := by
  funext s
  unfold phaseFunction polynomialPhaseObservable expSum
  rw [MvPolynomial.eval_eq]
  rw [← Finset.sum_attach Q.support]
  refine Fintype.sum_equiv Q.support.equivFin _ _ fun m => ?_
  simp only [Equiv.symm_apply_apply, polynomialVerticalExpCoeff,
    polynomialVerticalExpFrequency]
  rw [prod_phasePoint_vertical_eq_exp_monomialRealFrequency]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem isStripAlmostPeriodic_phaseFunction_vertical
    {d : Type} [Fintype d] [DecidableEq d]
    (omega : d → ℝ) (Q : MvPolynomial d ℂ) (σ R : ℝ) :
    IsStripAlmostPeriodic
      (fun s : ℂ => phaseFunction omega (polynomialPhaseObservable Q)
        (-Complex.I * (s - 1))) σ R := by
  rw [phaseFunction_vertical_eq_expSum]
  exact isStripAlmostPeriodic_expSum _ _ _ _

def finiteEulerAnchorEntire (S : Finset Nat.Primes) : ℂ → ℂ :=
  fun s => finiteEulerCharacteristicDet S (-Complex.I * (s - 1))

theorem differentiable_finiteEulerAnchorEntire (S : Finset Nat.Primes) :
    Differentiable ℂ (finiteEulerAnchorEntire S) := by
  unfold finiteEulerAnchorEntire
  rw [finiteEulerCharacteristicDet_eq_inverseAnchor]
  unfold phaseFunction polynomialPhaseObservable phasePoint
  let coords : ℂ → (Fin (Fintype.card ↥S) → ℂ) := fun s j =>
    Complex.exp
      (Complex.I * (finitePrimeFrequency S j : ℂ) * (-Complex.I * (s - 1)))
  change Differentiable ℂ (fun s => MvPolynomial.eval (coords s)
    (eulerInverseAnchorPolynomial (finitePrimeDamping S)))
  have hc : Differentiable ℂ coords := by
    dsimp [coords]
    fun_prop
  intro s
  exact ((differentiable_mvPolynomial_eval
    (eulerInverseAnchorPolynomial (finitePrimeDamping S))) (coords s)).comp s (hc s)

theorem finiteEulerAnchorEntire_eq_phaseVertical (S : Finset Nat.Primes) :
    finiteEulerAnchorEntire S =
      fun s : ℂ => phaseFunction (finitePrimeFrequency S)
        (polynomialPhaseObservable
        (eulerInverseAnchorPolynomial (finitePrimeDamping S)))
        (-Complex.I * (s - 1)) := by
  unfold finiteEulerAnchorEntire
  rw [finiteEulerCharacteristicDet_eq_inverseAnchor]

theorem isStripAlmostPeriodic_finiteEulerAnchorEntire
    (S : Finset Nat.Primes) (σ R : ℝ) :
    IsStripAlmostPeriodic (finiteEulerAnchorEntire S) σ R := by
  rw [finiteEulerAnchorEntire_eq_phaseVertical]
  exact isStripAlmostPeriodic_phaseFunction_vertical _ _ _ _

theorem verticalLineComplex_finiteEulerAnchorEntire_eq_characteristicDet
    (S : Finset Nat.Primes) :
    verticalLineComplex 1 (finiteEulerAnchorEntire S) =
      finiteEulerCharacteristicDet S := by
  funext z
  unfold verticalLineComplex finiteEulerAnchorEntire
  congr 1
  ring_nf
  norm_num

theorem autonomousMinimalOrder_verticalLineComplex_finiteEulerAnchorEntire_eq
    (S : Finset Nat.Primes) :
    autonomousMinimalOrder (verticalLineComplex 1 (finiteEulerAnchorEntire S)) =
      Fintype.card ↥S := by
  rw [verticalLineComplex_finiteEulerAnchorEntire_eq_characteristicDet]
  exact autonomousMinimalOrder_finiteEulerCharacteristicDet_eq S

def finiteEulerAnchorUpperEndAnalytic (S : Finset Nat.Primes) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (finiteEulerAnchorEntire S),
    ⟨finiteEulerAnchorEntire S, 0,
      ((differentiable_finiteEulerAnchorEntire S).differentiableOn.analyticOnNhd
        isOpen_univ).mono (Set.subset_univ _), rfl⟩⟩

theorem finiteEulerAnchorUpperEndAnalytic_repr (S : Finset Nat.Primes) :
    upperEndAnalyticSubring.subtype (finiteEulerAnchorUpperEndAnalytic S) =
      Germ.coeRingHom upperEndFilter (finiteEulerAnchorEntire S) := rfl

theorem exists_realAutonomousAnnihilator_verticalLineComplex_finiteEulerAnchorEntire
    (S : Finset Nat.Primes) :
    ∃ P : Polynomial (MvPolynomial (Fin (Fintype.card ↥S)) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator
        (verticalLineComplex 1 (finiteEulerAnchorEntire S)) (Fintype.card ↥S) P := by
  rw [verticalLineComplex_finiteEulerAnchorEntire_eq_characteristicDet,
    finiteEulerCharacteristicDet_eq_inverseAnchor]
  exact exists_polynomialPhase_realAutonomousAnnihilator
    (rho := fun _ => 1) (fun _ => zero_lt_one)
    (finitePrimeFrequency S)
    (eulerInverseAnchorPolynomial (finitePrimeDamping S))

theorem gammaFieldRelationAtOrder_finiteEulerAnchorEntire
    (S : Finset Nat.Primes) :
    GammaFieldRelationAtOrder (finiteEulerAnchorUpperEndAnalytic S)
      (Fintype.card ↥S) := by
  obtain ⟨P, hP0, hP⟩ :=
    exists_realAutonomousAnnihilator_verticalLineComplex_finiteEulerAnchorEntire S
  exact gammaFieldRelationAtOrder_of_realAutonomousAnnihilator_verticalLineComplex
    (differentiable_finiteEulerAnchorEntire S)
    (finiteEulerAnchorUpperEndAnalytic S)
    (finiteEulerAnchorUpperEndAnalytic_repr S) hP0 hP

theorem gammaFieldMinimalOrder_finiteEulerAnchorEntire_eq
    (S : Finset Nat.Primes) :
    gammaFieldMinimalOrder (finiteEulerAnchorUpperEndAnalytic S) = Fintype.card ↥S := by
  apply gammaFieldMinimalOrder_eq_of_autonomousMinimalOrder_eq
    (σ := 1) (R := 1) (rr := 1 / 4) (ρ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (differentiable_finiteEulerAnchorEntire S)
    (isStripAlmostPeriodic_finiteEulerAnchorEntire S 1 1)
    (finiteEulerAnchorUpperEndAnalytic S)
    (finiteEulerAnchorUpperEndAnalytic_repr S)
    (autonomousMinimalOrder_verticalLineComplex_finiteEulerAnchorEntire_eq S)
    (gammaFieldRelationAtOrder_finiteEulerAnchorEntire S)

end

end GaloisForLFunctions.HTGeometry
