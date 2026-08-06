import GaloisForLFunctions.HTGeometry.SourceCoboundaryModule

/-!
# Operators against jet characters

A finite differential character of a family — a finitely supported family of constants indexed by
observable and jet order — is the same datum as a finitely supported family of constant-coefficient
differential operators.  Under that correspondence the two forms of the simultaneous coboundary
condition agree.

This is the dictionary between the source theorem, which is stated with jet characters, and the
source-boundary module, whose scalars are the differential operators.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K : Type u} [Field C] [Field K] [Algebra C K] [Differential K]

/-! ### Polynomials as finitely supported coefficient families -/

/-- The coefficient family of a polynomial. -/
def polyFinsupp (P : Polynomial C) : ℕ →₀ C :=
  Finsupp.onFinset P.support P.coeff fun _ hm => Polynomial.mem_support_iff.2 hm

@[simp] theorem polyFinsupp_apply (P : Polynomial C) (m : ℕ) : polyFinsupp P m = P.coeff m := rfl

@[simp] theorem polyFinsupp_zero : polyFinsupp (0 : Polynomial C) = 0 := by
  ext m
  rw [polyFinsupp_apply, Polynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem polyFinsupp_support (P : Polynomial C) : (polyFinsupp P).support = P.support := by
  ext m
  rw [Finsupp.mem_support_iff, polyFinsupp_apply, Polynomial.mem_support_iff]

theorem polyFinsupp_eq_zero_iff {P : Polynomial C} : polyFinsupp P = 0 ↔ P = 0 := by
  constructor
  · intro h
    ext m
    have := congrFun (congrArg (fun f : ℕ →₀ C => (f : ℕ → C)) h) m
    simpa using this
  · rintro rfl
    exact polyFinsupp_zero

/-- The polynomial with a prescribed coefficient family. -/
def finsuppPoly (f : ℕ →₀ C) : Polynomial C := f.sum fun m a => Polynomial.monomial m a

@[simp] theorem finsuppPoly_zero : finsuppPoly (0 : ℕ →₀ C) = 0 := by
  rw [finsuppPoly, Finsupp.sum_zero_index]

theorem polyFinsupp_finsuppPoly (f : ℕ →₀ C) : polyFinsupp (finsuppPoly f) = f := by
  ext m
  rw [polyFinsupp_apply, finsuppPoly, Finsupp.sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [Polynomial.coeff_monomial, if_neg hb]
  · intro hm
    rw [Finsupp.notMem_support_iff.1 hm, Polynomial.coeff_monomial, if_pos rfl]

theorem finsuppPoly_polyFinsupp (P : Polynomial C) : finsuppPoly (polyFinsupp P) = P := by
  rw [finsuppPoly, Finsupp.sum, polyFinsupp_support]
  show (∑ m ∈ P.support, Polynomial.monomial m (P.coeff m)) = P
  rw [← Polynomial.sum, Polynomial.sum_monomial_eq]

/-! ### The operator action as a jet character -/

theorem pow_derivC_apply (hC : ∀ c : C, (algebraMap C K c)′ = 0) (m : ℕ) :
    ∀ x : K, ((derivC hC) ^ m) x = differentialJet m x := by
  induction m with
  | zero => intro x; rw [pow_zero, differentialJet_zero]; rfl
  | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, ih, derivC_apply, differentialJet_succ]

theorem aeval_derivC_sum (hC : ∀ c : C, (algebraMap C K c)′ = 0) (P : Polynomial C) (x : K) :
    (Polynomial.aeval (derivC hC)) P x
      = (polyFinsupp P).sum fun m a => algebraMap C K a * differentialJet m x := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, LinearMap.coe_sum,
    Finset.sum_apply, Finsupp.sum]
  rw [polyFinsupp_support]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Module.End.mul_apply, pow_derivC_apply, Module.algebraMap_end_apply, Algebra.smul_def]
  rfl

/-! ### The correspondence between operators and jet characters -/

variable {I : Type u} (tau : I → K ≃+* K)

theorem finsupp_curry_zero {κ : Type u} :
    Finsupp.curry (0 : (κ × ℕ) →₀ C) = 0 := by
  ext p m
  rfl

theorem finsupp_uncurry_zero {κ : Type u} :
    Finsupp.uncurry (0 : κ →₀ (ℕ →₀ C)) = 0 := by
  ext q
  rfl

/-- The jet character attached to a family of operators. -/
def jetCharacterOfOperators {κ : Type u} (l : κ →₀ Polynomial C) : (κ × ℕ) →₀ C :=
  (l.mapRange polyFinsupp polyFinsupp_zero).uncurry

/-- The operator family attached to a jet character. -/
def operatorsOfJetCharacter {κ : Type u} (c : (κ × ℕ) →₀ C) : κ →₀ Polynomial C :=
  c.curry.mapRange finsuppPoly finsuppPoly_zero

theorem jetCharacterOfOperators_operatorsOfJetCharacter {κ : Type u} (c : (κ × ℕ) →₀ C) :
    jetCharacterOfOperators (operatorsOfJetCharacter c) = c := by
  have hmap : (c.curry.mapRange finsuppPoly finsuppPoly_zero).mapRange
      polyFinsupp polyFinsupp_zero = c.curry := by
    ext p m
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, polyFinsupp_finsuppPoly]
  rw [jetCharacterOfOperators, operatorsOfJetCharacter, hmap, Finsupp.uncurry_curry]

theorem jetCharacterOfOperators_ne_zero {κ : Type u} {l : κ →₀ Polynomial C} (hl : l ≠ 0) :
    jetCharacterOfOperators l ≠ 0 := by
  intro h
  apply hl
  have hcurry : l.mapRange polyFinsupp polyFinsupp_zero = 0 := by
    have hc := congrArg Finsupp.curry h
    rw [jetCharacterOfOperators, Finsupp.curry_uncurry, finsupp_curry_zero] at hc
    exact hc
  ext p
  have hp := congrFun (congrArg (fun f : κ →₀ (ℕ →₀ C) => (f : κ → (ℕ →₀ C))) hcurry) p
  rw [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at hp
  rw [polyFinsupp_eq_zero_iff.1 hp, Finsupp.coe_zero, Pi.zero_apply]

theorem operatorsOfJetCharacter_ne_zero {κ : Type u} {c : (κ × ℕ) →₀ C} (hc : c ≠ 0) :
    operatorsOfJetCharacter c ≠ 0 := by
  intro h
  apply hc
  rw [← jetCharacterOfOperators_operatorsOfJetCharacter c, h, jetCharacterOfOperators,
    Finsupp.mapRange_zero, finsupp_uncurry_zero]

/-- The operator sum against a family is the jet-character sum. -/
theorem operatorSum_eq_jetSum (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    {κ : Type u} (l : κ →₀ Polynomial C) (y : κ → K) :
    (∑ p ∈ l.support, (Polynomial.aeval (derivC hC)) (l p) (y p))
      = Finsupp.linearCombination K (fun q : κ × ℕ => differentialJet q.2 (y q.1))
        (Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K))
          (jetCharacterOfOperators l)) := by
  classical
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by intro q; rw [zero_smul]),
    jetCharacterOfOperators, Finsupp.sum_uncurry_index,
    Finsupp.sum_mapRange_index (by intro p; rw [Finsupp.sum_zero_index])]
  show (∑ p ∈ l.support, (Polynomial.aeval (derivC hC)) (l p) (y p))
    = l.sum fun p P => (polyFinsupp P).sum fun m a =>
        algebraMap C K a • differentialJet m (y p)
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [aeval_derivC_sum hC (l p) (y p)]
  refine Finset.sum_congr rfl fun m _ => ?_
  show algebraMap C K (polyFinsupp (l p) m) * differentialJet m (y p)
    = algebraMap C K (polyFinsupp (l p) m) • differentialJet m (y p)
  rw [smul_eq_mul]

/-- **The two forms of the simultaneous coboundary condition agree.** -/
theorem operator_criterion_iff_jet_criterion (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    {κ : Type u} (omega : I → κ → K) :
    (∀ l : κ →₀ Polynomial C, l ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠ ∑ p ∈ l.support, (Polynomial.aeval (derivC hC)) (l p) (omega i p)) ↔
      ∀ c : (κ × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          Finsupp.linearCombination K
            (fun q : κ × ℕ => differentialJet q.2 (omega i q.1))
            (Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c) := by
  constructor
  · intro hop c hc k
    obtain ⟨i, hi⟩ := hop (operatorsOfJetCharacter c) (operatorsOfJetCharacter_ne_zero hc) k
    refine ⟨i, ?_⟩
    rw [operatorSum_eq_jetSum hC _ (fun p => omega i p),
      jetCharacterOfOperators_operatorsOfJetCharacter] at hi
    exact hi
  · intro hjet l hl k
    obtain ⟨i, hi⟩ := hjet (jetCharacterOfOperators l) (jetCharacterOfOperators_ne_zero hl) k
    refine ⟨i, ?_⟩
    rwa [← operatorSum_eq_jetSum hC l (fun p => omega i p)] at hi

end

end GaloisForLFunctions.HTGeometry
