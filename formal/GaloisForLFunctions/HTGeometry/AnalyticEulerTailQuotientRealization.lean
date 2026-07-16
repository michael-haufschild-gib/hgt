import GaloisForLFunctions.HTGeometry.AnalyticEulerExponentialTailBase

/-!
# Canonical analytic realization of the bounded prime tail quotient

Bounded complex prime streams form a vector space.  Quotienting by the subspace of finitely
supported streams produces the intrinsic cofinite-tail source space.  At every differential
order, the actual analytic Dirichlet realization descends to a linear map from this source
quotient into meromorphic jets modulo the Euler-exponential base.  Taking all orders gives one
canonical all-jet realization whose injectivity is the sharply isolated analytic faithfulness
problem.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

/-- The complex vector space of uniformly bounded prime coefficient streams. -/
def boundedPrimeSourceSubmodule : Submodule ℂ (Nat.Primes → ℂ) where
  carrier := {c | ∃ M : ℝ, ∀ p, ‖c p‖ ≤ M}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro c d ⟨M, hc⟩ ⟨N, hd⟩
    refine ⟨M + N, fun p ↦ (norm_add_le (c p) (d p)).trans ?_⟩
    exact add_le_add (hc p) (hd p)
  smul_mem' := by
    rintro z c ⟨M, hc⟩
    refine ⟨‖z‖ * M, ?_⟩
    intro p
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hc p) (norm_nonneg z)

/-- A bounded prime source, bundled with the existence of a uniform bound. -/
abbrev BoundedPrimeSource := boundedPrimeSourceSubmodule

/-- The linear gauge subspace of bounded sources supported on finitely many primes. -/
def boundedPrimeFiniteSupportSubmodule : Submodule ℂ BoundedPrimeSource where
  carrier := {c | (Function.support (c : Nat.Primes → ℂ)).Finite}
  zero_mem' := by simp [Function.support]
  add_mem' := by
    intro c d hc hd
    apply (hc.union hd).subset
    intro p hp
    simp only [Function.support, Set.mem_union, Set.mem_setOf_eq,
      Submodule.coe_add, Pi.add_apply] at hp ⊢
    by_cases hcp : (c : Nat.Primes → ℂ) p = 0
    · exact Or.inr fun hdp ↦ hp (by rw [hcp, hdp, add_zero])
    · exact Or.inl hcp
  smul_mem' := by
    intro z c hc
    apply hc.subset
    intro p hp
    simp only [Function.support, Set.mem_setOf_eq, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at hp ⊢
    intro hcp
    exact hp (by rw [hcp, mul_zero])

/-- The canonical complex source space of bounded prime coefficients modulo finite support. -/
abbrev BoundedPrimeTailSpace :=
  BoundedPrimeSource ⧸ boundedPrimeFiniteSupportSubmodule

/-- Equality in the bounded prime tail space is exactly finite support of the difference. -/
@[simp]
theorem boundedPrimeTailClass_eq_iff (c d : BoundedPrimeSource) :
    (Submodule.Quotient.mk c : BoundedPrimeTailSpace) =
        Submodule.Quotient.mk d ↔
      (Function.support
        (((c - d : BoundedPrimeSource) : Nat.Primes → ℂ))).Finite := by
  rw [Submodule.Quotient.eq]
  rfl

/-- The Euler-exponential base regarded as a complex vector subspace of the ambient meromorphic
field. -/
def analyticEulerExponentialBaseComplexSubmodule (a : ℂ) :
    Submodule ℂ upperEndMeroField where
  carrier := analyticEulerExponentialBase a
  zero_mem' := IntermediateField.zero_mem _
  add_mem' := IntermediateField.add_mem _
  smul_mem' := by
    intro z f hf
    rw [Algebra.smul_def]
    apply IntermediateField.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField upperEndMeroField]
      exact IntermediateField.algebraMap_mem _
        (algebraMap ℂ upperEndRationalCoordinateField z)
    · exact hf

/-- Analytic meromorphic jets modulo the localized single-prime Euler modes. -/
abbrev AnalyticEulerJetTailSpace (a : ℂ) :=
  upperEndMeroField ⧸ analyticEulerExponentialBaseComplexSubmodule a

/-- A canonical choice of one convergence bound for a bundled bounded source. -/
def boundedPrimeSourceBound (c : BoundedPrimeSource) : ℝ :=
  Classical.choose c.property

theorem boundedPrimeSourceBound_spec (c : BoundedPrimeSource) (p : Nat.Primes) :
    ‖(c : Nat.Primes → ℂ) p‖ ≤ boundedPrimeSourceBound c :=
  (Classical.choose_spec c.property) p

/-- The actual analytic carrier selected from a bundled bounded prime source. -/
def analyticBoundedPrimeShiftCarrier (a : ℂ) (c : BoundedPrimeSource) :
    upperEndMeroField :=
  analyticPrimeObservableShiftCarrier (c : Nat.Primes → ℂ)
    (boundedPrimeSourceBound c) (boundedPrimeSourceBound_spec c) a

/-- Analytic jets of bounded prime carriers respect source addition exactly. -/
theorem differentialJet_analyticBoundedPrimeShiftCarrier_add
    (a : ℂ) (k : ℕ) (c d : BoundedPrimeSource) :
    GaloisForLFunctions.differentialJet k
        (analyticBoundedPrimeShiftCarrier a (c + d)) =
      GaloisForLFunctions.differentialJet k
          (analyticBoundedPrimeShiftCarrier a c) +
        GaloisForLFunctions.differentialJet k
          (analyticBoundedPrimeShiftCarrier a d) := by
  have hlin := differentialJet_analyticPrimeObservableShiftCarrier_linearCombination
    (J := Fin 2)
    (fun i ↦ if i = 0 then (c : Nat.Primes → ℂ) else (d : Nat.Primes → ℂ))
    (fun i ↦ if i = 0 then boundedPrimeSourceBound c else
      boundedPrimeSourceBound d)
    (by
      intro i p
      fin_cases i
      · simpa using boundedPrimeSourceBound_spec c p
      · simpa using boundedPrimeSourceBound_spec d p)
    (fun _ ↦ (1 : ℂ))
    ((c + d : BoundedPrimeSource) : Nat.Primes → ℂ)
    (boundedPrimeSourceBound (c + d))
    (boundedPrimeSourceBound_spec (c + d))
    (by intro p; simp [Fin.sum_univ_two]) a k
  simpa [analyticBoundedPrimeShiftCarrier, Fin.sum_univ_two] using hlin

/-- Analytic jets of bounded prime carriers respect complex source scaling exactly. -/
theorem differentialJet_analyticBoundedPrimeShiftCarrier_smul
    (a : ℂ) (k : ℕ) (z : ℂ) (c : BoundedPrimeSource) :
    GaloisForLFunctions.differentialJet k
        (analyticBoundedPrimeShiftCarrier a (z • c)) =
      z • GaloisForLFunctions.differentialJet k
        (analyticBoundedPrimeShiftCarrier a c) := by
  have hlin := differentialJet_analyticPrimeObservableShiftCarrier_linearCombination
    (J := Fin 1) (fun _ ↦ (c : Nat.Primes → ℂ))
    (fun _ ↦ boundedPrimeSourceBound c)
    (fun _ ↦ boundedPrimeSourceBound_spec c)
    (fun _ ↦ z) ((z • c : BoundedPrimeSource) : Nat.Primes → ℂ)
    (boundedPrimeSourceBound (z • c))
    (boundedPrimeSourceBound_spec (z • c))
    (by intro p; simp [Algebra.smul_def]) a k
  simpa [analyticBoundedPrimeShiftCarrier, Algebra.smul_def] using hlin

/-- At one differential order, analytic realization followed by quotienting out the Euler base is
a complex-linear source map. -/
def analyticBoundedPrimeJetQuotientMap (a : ℂ) (k : ℕ) :
    BoundedPrimeSource →ₗ[ℂ] AnalyticEulerJetTailSpace a where
  toFun c := Submodule.Quotient.mk
    (GaloisForLFunctions.differentialJet k
      (analyticBoundedPrimeShiftCarrier a c))
  map_add' := by
    intro c d
    change Submodule.Quotient.mk _ =
      Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add, differentialJet_analyticBoundedPrimeShiftCarrier_add]
  map_smul' := by
    intro z c
    change Submodule.Quotient.mk _ = z • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul, differentialJet_analyticBoundedPrimeShiftCarrier_smul]

/-- Every jet of a finitely supported bounded prime carrier lies in the Euler-exponential base. -/
theorem differentialJet_analyticBoundedPrimeShiftCarrier_mem_eulerBase_of_finiteSupport
    (a : ℂ) (k : ℕ) (c : BoundedPrimeSource)
    (hc : (Function.support (c : Nat.Primes → ℂ)).Finite) :
    GaloisForLFunctions.differentialJet k
        (analyticBoundedPrimeShiftCarrier a c) ∈
      analyticEulerExponentialBase a := by
  classical
  let u : Nat.Primes →₀ ℂ :=
    Finsupp.onFinset hc.toFinset (c : Nat.Primes → ℂ) (by
      intro p hp
      exact hc.mem_toFinset.mpr hp)
  have hu (p : Nat.Primes) : u p = (c : Nat.Primes → ℂ) p := by
    exact Finsupp.onFinset_apply
  have hsource : (fun p ↦ u p) = (c : Nat.Primes → ℂ) := funext hu
  have hchosen : ∀ p, ‖u p‖ ≤ boundedPrimeSourceBound c := by
    intro p
    rw [hu]
    exact boundedPrimeSourceBound_spec c p
  have heq := differentialJet_analyticPrimeObservableShiftCarrier_congr_bound
    (fun p ↦ u p) (finitePrimeSourceBound u) (boundedPrimeSourceBound c)
    (finitePrimeSource_norm_le_bound u) hchosen a k
  have hmem := differentialJet_analyticFinitePrimeShiftCarrier_mem_eulerBase a u k
  have htarget :
      GaloisForLFunctions.differentialJet k
          (analyticPrimeObservableShiftCarrier (c : Nat.Primes → ℂ)
            (boundedPrimeSourceBound c) (boundedPrimeSourceBound_spec c) a) =
        GaloisForLFunctions.differentialJet k
          (analyticPrimeObservableShiftCarrier (fun p ↦ u p)
            (boundedPrimeSourceBound c) hchosen a) := by
    congr
  change GaloisForLFunctions.differentialJet k
      (analyticPrimeObservableShiftCarrier (c : Nat.Primes → ℂ)
        (boundedPrimeSourceBound c) (boundedPrimeSourceBound_spec c) a) ∈ _
  rw [htarget, ← heq]
  exact hmem

/-- The finite-support gauge lies in the kernel at every jet order. -/
theorem boundedPrimeFiniteSupport_le_analyticBoundedPrimeJetQuotientMap_ker
    (a : ℂ) (k : ℕ) :
    boundedPrimeFiniteSupportSubmodule ≤
      (analyticBoundedPrimeJetQuotientMap a k).ker := by
  intro c hc
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact differentialJet_analyticBoundedPrimeShiftCarrier_mem_eulerBase_of_finiteSupport
    a k c hc

/-- **Canonical Euler-tail jet realization.**  Every differential order factors uniquely through
the bounded source quotient modulo finite prime support. -/
def analyticEulerTailJetRealization (a : ℂ) (k : ℕ) :
    BoundedPrimeTailSpace →ₗ[ℂ] AnalyticEulerJetTailSpace a :=
  boundedPrimeFiniteSupportSubmodule.liftQ
    (analyticBoundedPrimeJetQuotientMap a k)
    (boundedPrimeFiniteSupport_le_analyticBoundedPrimeJetQuotientMap_ker a k)

@[simp]
theorem analyticEulerTailJetRealization_mk
    (a : ℂ) (k : ℕ) (c : BoundedPrimeSource) :
    analyticEulerTailJetRealization a k
        (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (GaloisForLFunctions.differentialJet k
          (analyticBoundedPrimeShiftCarrier a c)) := by
  rfl

/-- **Canonical all-jet tail realization.**  The whole analytic differential tower is one linear
map out of the intrinsic bounded cofinite-tail source space. -/
def analyticEulerTailAllJetRealization (a : ℂ) :
    BoundedPrimeTailSpace →ₗ[ℂ] (ℕ → AnalyticEulerJetTailSpace a) :=
  LinearMap.pi fun k ↦ analyticEulerTailJetRealization a k

@[simp]
theorem analyticEulerTailAllJetRealization_apply
    (a : ℂ) (q : BoundedPrimeTailSpace) (k : ℕ) :
    analyticEulerTailAllJetRealization a q k =
      analyticEulerTailJetRealization a k q :=
  rfl

end


end GaloisForLFunctions.HTGeometry
