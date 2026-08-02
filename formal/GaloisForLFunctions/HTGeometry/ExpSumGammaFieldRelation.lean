import GaloisForLFunctions.HTGeometry.ExpSumPhaseRankSharp
import GaloisForLFunctions.HTGeometry.UpperEndGammaElement
import GaloisForLFunctions.HTGeometry.UpperEndJetTransport
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogCarrier

/-!
# The exponential sum as a solution of a Gamma-field relation

A sum of exponentials satisfies the constant-coefficient linear differential equation whose
characteristic roots are its frequencies.  Constants lie in `ℂ(s) ⊆ ℂ(s)⟨Γ⟩`, so that equation is a
relation of the kind the finite phase law consumes: linear in the jets, with coefficients nonzero
elements of the Gamma field — the coefficients of the annihilator that actually occur.

Together with the rank computation this exhibits, for every `r`, a solution of a Gamma-field relation
whose rational phase rank is exactly `r`.
-/

open Filter Set Topology Function

open scoped Differential

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance expSumDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance expSumIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance expSumDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance expSumComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance expSumRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

variable {r : ℕ}

/-- An exponential sum is entire, hence analytic on every upper half-plane. -/
theorem analyticOnNhd_expSum_upperTail (a : Fin r → ℂ) (μ : Fin r → ℝ) :
    AnalyticOnNhd ℂ (expSum a μ) (upperTail 0) :=
  DifferentiableOn.analyticOnNhd (differentiable_expSum a μ).differentiableOn
    (isOpen_upperTail 0)

/-- The exponential sum as an upper-end analytic germ. -/
def expSumUpperAnalytic (a : Fin r → ℂ) (μ : Fin r → ℝ) : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter (expSum a μ)),
    ⟨expSum a μ, 0, analyticOnNhd_expSum_upperTail a μ, rfl⟩⟩

@[simp] theorem expSumUpperAnalytic_coe (a : Fin r → ℂ) (μ : Fin r → ℝ) :
    ((expSumUpperAnalytic a μ : upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
      = ((expSum a μ : ℂ → ℂ) : Germ upperEndFilter ℂ) := rfl

/-- The characteristic polynomial of the exponential sum. -/
def expSumChar (μ : Fin r → ℝ) : Polynomial ℂ :=
  expSumAnnihilator Finset.univ (fun k : Fin r => ((μ k : ℝ) : ℂ))

/-- **The annihilating equation in the carrier.** -/
theorem expSum_analytic_ode (a : Fin r → ℂ) (μ : Fin r → ℝ) :
    ∑ j ∈ Finset.range ((expSumChar μ).natDegree + 1),
        upperEndPolyToAnalytic (Polynomial.C ((expSumChar μ).coeff j))
          * upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ) = 0 := by
  classical
  refine Subtype.ext ?_
  rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum]
  have hterm : ∀ j ∈ Finset.range ((expSumChar μ).natDegree + 1),
      ((upperEndPolyToAnalytic (Polynomial.C ((expSumChar μ).coeff j))
          * upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ) :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
        = ((((fun _ : ℂ => (expSumChar μ).coeff j) * iteratedDeriv j (expSum a μ)) :
            ℂ → ℂ) : Germ upperEndFilter ℂ) := by
    intro j _
    rw [MulMemClass.coe_mul]
    have hrepr : ((upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ) :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
        = ((iteratedDeriv j (expSum a μ) : ℂ → ℂ) : Germ upperEndFilter ℂ) :=
      upperEndAnalyticDeriv_iterate_repr j _ _ rfl
    have hconst : ((upperEndPolyToAnalytic (Polynomial.C ((expSumChar μ).coeff j)) :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
        = ((fun _ : ℂ => (expSumChar μ).coeff j : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
      have hev : ((upperEndPolyToAnalytic (Polynomial.C ((expSumChar μ).coeff j)) :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
          = ((fun z : ℂ => (Polynomial.C ((expSumChar μ).coeff j)).eval z : ℂ → ℂ) :
            Germ upperEndFilter ℂ) := rfl
      rw [hev]
      refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
      simp
    rw [hrepr, hconst, ← Germ.coe_mul]
  rw [Finset.sum_congr rfl hterm, ← Germ.coe_sum]
  refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  have hfun : expSum a μ = fun x : ℂ => ∑ k ∈ (Finset.univ : Finset (Fin r)),
      a k * Complex.exp (((μ k : ℝ) : ℂ) * x) := by
    funext x
    rw [expSum]
  show (∑ j ∈ Finset.range ((expSumChar μ).natDegree + 1),
      ((fun _ : ℂ => (expSumChar μ).coeff j) * iteratedDeriv j (expSum a μ))) z = 0
  rw [Finset.sum_apply]
  show ∑ j ∈ Finset.range ((expSumChar μ).natDegree + 1),
      (expSumChar μ).coeff j * iteratedDeriv j (expSum a μ) z = 0
  rw [hfun]
  exact expSumAnnihilator_ode Finset.univ a (fun k : Fin r => ((μ k : ℝ) : ℂ)) z

/-- **The exponential sum solves a Gamma-field relation.**  The relation is linear in the jets, its
exponents are distinct, and its coefficients are nonzero elements of `ℂ(s)⟨Γ⟩`. -/
theorem exists_gammaField_relation_expSum (a : Fin r → ℂ) (μ : Fin r → ℝ) :
    ∃ (N : ℕ) (e : Fin N → Fin ((expSumChar μ).natDegree + 1) → ℕ)
      (x : Fin N → upperEndMeroField),
      0 < N ∧ Function.Injective e ∧
      (∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) ∧
      (∀ α, x α ≠ 0) ∧
      ∑ α : Fin N, x α * ∏ i : Fin ((expSumChar μ).natDegree + 1),
          (differentialJet (i : ℕ)
            (algebraMap upperEndAnalyticSubring upperEndMeroField
              (expSumUpperAnalytic a μ))) ^ (e α i) = 0 := by
  classical
  set P : Polynomial ℂ := expSumChar μ with hP
  set S : Finset ℕ := P.support with hS
  set N : ℕ := S.card with hN
  set en : Fin N → ℕ := fun α => ((S.equivFin.symm α : {x // x ∈ S}) : ℕ) with hen
  have hmem : ∀ α, en α ∈ S := fun α => (S.equivFin.symm α).2
  have heninj : Function.Injective en := by
    intro α β hab
    have : (S.equivFin.symm α) = (S.equivFin.symm β) := Subtype.ext hab
    exact S.equivFin.symm.injective this
  have hle : ∀ α, en α < P.natDegree + 1 := by
    intro α
    have := Polynomial.le_natDegree_of_mem_supp (en α) (hmem α)
    omega
  have hNpos : 0 < N := by
    rw [hN, Finset.card_pos]
    refine ⟨P.natDegree, ?_⟩
    rw [hS, Polynomial.mem_support_iff]
    have hmonic : P.Monic := by
      rw [hP, expSumChar, expSumAnnihilator]
      exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    rw [hmonic.coeff_natDegree]
    exact one_ne_zero
  set idx : Fin N → Fin (P.natDegree + 1) := fun α => ⟨en α, hle α⟩ with hidx
  refine ⟨N, fun α i => if i = idx α then 1 else 0,
    fun α => algebraMap (RatFunc ℂ) upperEndMeroField
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff (en α)))),
    hNpos, ?_, ?_, ?_, ?_⟩
  · -- distinct exponent vectors
    intro α β hab
    have h : (if idx α = idx α then (1 : ℕ) else 0) = (if idx α = idx β then (1 : ℕ) else 0) :=
      congrFun hab (idx α)
    rw [if_pos rfl] at h
    have hidxeq : idx α = idx β := by
      by_contra hne
      rw [if_neg hne] at h
      exact absurd h one_ne_zero
    have : en α = en β := congrArg Fin.val hidxeq
    exact heninj this
  · -- the coefficients lie in the Gamma field
    intro α
    exact IntermediateField.algebraMap_mem _ _
  · -- the coefficients are nonzero
    intro α
    have hcoeff : P.coeff (en α) ≠ 0 := by
      have := hmem α
      rw [hS, Polynomial.mem_support_iff] at this
      exact this
    have hC : (Polynomial.C (P.coeff (en α))) ≠ 0 := by
      simpa using hcoeff
    have h1 : (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff (en α)))) ≠ 0 := by
      intro h0
      exact hC (by
        have := (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)) (by
          rw [h0, map_zero] : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff (en α)))
            = algebraMap (Polynomial ℂ) (RatFunc ℂ) 0)
        exact this)
    intro h0
    have h0' : upperEndRatfuncToMero
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff (en α)))) = 0 := h0
    exact h1 (upperEndRatfuncToMero_injective (by rw [h0', map_zero]))
  · -- the relation
    have hprod : ∀ α : Fin N,
        (∏ i : Fin (P.natDegree + 1),
          (differentialJet (i : ℕ)
            (algebraMap upperEndAnalyticSubring upperEndMeroField
              (expSumUpperAnalytic a μ))) ^ (if i = idx α then 1 else 0))
        = differentialJet (en α)
            (algebraMap upperEndAnalyticSubring upperEndMeroField
              (expSumUpperAnalytic a μ)) := by
      intro α
      rw [Finset.prod_eq_single (idx α)]
      · rw [if_pos rfl, pow_one]
      · intro i _ hi
        rw [if_neg hi, pow_zero]
      · intro h
        exact absurd (Finset.mem_univ (idx α)) h
    rw [Finset.sum_congr rfl fun α _ => by rw [hprod α]]
    -- reindex onto the support and extend to the full range
    have hjet : ∀ j : ℕ, differentialJet j
        (algebraMap upperEndAnalyticSubring upperEndMeroField (expSumUpperAnalytic a μ))
        = algebraMap upperEndAnalyticSubring upperEndMeroField
            (upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ)) :=
      fun j => differentialJet_algebraMap j _
    have hcoe : ∀ j : ℕ,
        algebraMap (RatFunc ℂ) upperEndMeroField
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff j)))
          = algebraMap upperEndAnalyticSubring upperEndMeroField
              (upperEndPolyToAnalytic (Polynomial.C (P.coeff j))) := by
      intro j
      show upperEndRatfuncToMero _ = _
      rw [upperEndRatfuncToMero_algebraMap_polynomial, upperEndPolyToMero]
      rfl
    have hterm : ∀ α : Fin N,
        algebraMap (RatFunc ℂ) upperEndMeroField
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.coeff (en α))))
          * differentialJet (en α)
              (algebraMap upperEndAnalyticSubring upperEndMeroField (expSumUpperAnalytic a μ))
        = algebraMap upperEndAnalyticSubring upperEndMeroField
            (upperEndPolyToAnalytic (Polynomial.C (P.coeff (en α)))
              * upperEndAnalyticDeriv^[en α] (expSumUpperAnalytic a μ)) := by
      intro α
      rw [hjet, hcoe, map_mul]
    rw [Finset.sum_congr rfl fun α _ => hterm α, ← map_sum]
    -- the analytic identity
    have hsum : ∑ α : Fin N, upperEndPolyToAnalytic (Polynomial.C (P.coeff (en α)))
          * upperEndAnalyticDeriv^[en α] (expSumUpperAnalytic a μ)
        = ∑ j ∈ Finset.range (P.natDegree + 1),
            upperEndPolyToAnalytic (Polynomial.C (P.coeff j))
              * upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ) := by
      have hS' : ∑ α : Fin N, upperEndPolyToAnalytic (Polynomial.C (P.coeff (en α)))
            * upperEndAnalyticDeriv^[en α] (expSumUpperAnalytic a μ)
          = ∑ j ∈ S, upperEndPolyToAnalytic (Polynomial.C (P.coeff j))
              * upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ) := by
        rw [← Finset.sum_coe_sort S (fun j => upperEndPolyToAnalytic (Polynomial.C (P.coeff j))
          * upperEndAnalyticDeriv^[j] (expSumUpperAnalytic a μ))]
        exact Fintype.sum_equiv S.equivFin.symm _ _ fun α => rfl
      rw [hS']
      refine Finset.sum_subset ?_ ?_
      · intro j hj
        rw [Finset.mem_range]
        have := Polynomial.le_natDegree_of_mem_supp j (by rwa [← hS])
        omega
      · intro j _ hj
        have hzero : P.coeff j = 0 := by
          by_contra hne
          exact hj (by rw [hS, Polynomial.mem_support_iff]; exact hne)
        simp [hzero]
    rw [hsum, expSum_analytic_ode a μ, map_zero]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance expSumWitDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance expSumWitIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance expSumWitDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance expSumWitComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance expSumWitRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **The law's hypotheses are inhabited at every rank.**  For every rationally independent frequency
packet of size `r` there is a function holomorphic and almost periodic on the strip, satisfying a
relation with distinct jet exponents and nonzero coefficients in `ℂ(s)⟨Γ⟩`, whose Bohr–Fourier
expansion along the line carries exactly `r` rationally independent frequencies. -/
theorem exists_gammaField_solution_rank_eq {r : ℕ} {μ : Fin r → ℝ} (hμ : LinearIndependent ℚ μ)
    {a : Fin r → ℂ} (ha : ∀ k, a k ≠ 0) (σ R : ℝ) :
    ∃ (Φ : ℂ → ℂ) (Ψ : upperEndAnalyticSubring) (m N : ℕ)
      (e : Fin N → Fin (m + 1) → ℕ) (x : Fin N → upperEndMeroField),
      DifferentiableOn ℂ Φ (verticalStrip σ R) ∧ IsStripAlmostPeriodic Φ σ R ∧
      upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ ∧
      0 < N ∧ Function.Injective e ∧
      (∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) ∧
      (∀ α, x α ≠ 0) ∧
      (∑ α : Fin N, x α * ∏ i : Fin (m + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i) = 0) ∧
      Module.rank ℚ
          (bohrFrequencyModule fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I))
        = (r : Cardinal) := by
  obtain ⟨N, e, x, hN, he, hxmem, hx0, hrel⟩ := exists_gammaField_relation_expSum a μ
  refine ⟨expSum a μ, expSumUpperAnalytic a μ, (expSumChar μ).natDegree, N, e, x,
    (differentiable_expSum a μ).differentiableOn, isStripAlmostPeriodic_expSum a μ σ R, rfl,
    hN, he, hxmem, hx0, hrel, ?_⟩
  exact rank_bohrFrequencyModule_expSum_line ha hμ σ

end

end GaloisForLFunctions.HTGeometry
