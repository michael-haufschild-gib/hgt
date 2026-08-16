import GaloisForLFunctions.HTGeometry.JetPrincipalSymbolExtraction
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder
import GaloisForLFunctions.HTGeometry.EigenLogDerivNormalization
import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule

/-!
# The rational substitution endomorphism of the free jet field

A nonconstant rational function `R` acts on the free differential rational field on one coordinate
by `y ↦ R(y)`: the coordinate `y^{(l)}` is sent to the `l`-th derivative of `R(y)`.  That the
prescription defines a field endomorphism at all is the statement that the jets of `R(y)` are
algebraically independent, which follows from the Jacobian criterion: the matrix of coordinate
partials is triangular with the constant diagonal `R'(y)`.

The endomorphism is the object whose stable range core is the orbifold tail of `R`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped Differential

noncomputable section

variable {C : Type*} [Field C]

/-! ## The substituted value and its jets -/

/-- The value of a rational function at the free generator. -/
def substitutionValue (R : RatFunc C) : JetField C Unit :=
  ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen R

/-- The jets of the substituted value: the prescribed images of the jet coordinates. -/
def substitutionJet (R : RatFunc C) (l : ℕ) : JetField C Unit :=
  differentialJet l (substitutionValue R)

/-- The derivative factor of the substitution. -/
def substitutionDeriv (R : RatFunc C) : JetField C Unit :=
  JetField.pd ((), 0) (substitutionValue R)

theorem substitutionValue_mem_adjoin (R : RatFunc C) :
    substitutionValue R ∈
      IntermediateField.adjoin C ({JetField.jet ((), 0)} : Set (JetField C Unit)) :=
  ratFuncEval_mem_adjoin _ R

theorem pd_substitutionValue_eq_zero (R : RatFunc C) {k : ℕ} (hk : k ≠ 0) :
    JetField.pd ((), k) (substitutionValue R) = 0 := by
  refine derivation_eq_zero_of_mem_adjoin _ _ ?_ (substitutionValue_mem_adjoin R)
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  refine JetField.pd_jet_of_ne ?_
  simp [Prod.ext_iff, hk]

/-- The substitution is triangular: the `l`-th jet does not meet any deeper coordinate. -/
theorem pd_substitutionJet_eq_zero_of_lt (R : RatFunc C) {l j : ℕ} (h : l < j) :
    JetField.pd ((), j) (substitutionJet R l) = 0 := by
  refine pd_differentialJet_eq_zero_of_gt (m := 0)
    (fun k hk => pd_substitutionValue_eq_zero R (by omega)) l j (by omega)

/-- The diagonal of the substitution Jacobian is the derivative factor. -/
theorem pd_substitutionJet_self (R : RatFunc C) (l : ℕ) :
    JetField.pd ((), l) (substitutionJet R l) = substitutionDeriv R := by
  have h := pd_differentialJet_top (u := substitutionValue R) (m := 0)
    (fun k hk => pd_substitutionValue_eq_zero R (by omega)) l
  rw [substitutionJet, substitutionDeriv, ← h]
  norm_num

/-! ## Algebraic independence of the substituted jets -/

theorem algebraicIndependent_substitutionJet_fin [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (n : ℕ) :
    AlgebraicIndependent C (fun i : Fin n => substitutionJet R (i : ℕ)) := by
  classical
  refine algebraicIndependent_of_domain_jacobian (K := C) (R := JetField C Unit)
    (fun i : Fin n => substitutionJet R (i : ℕ))
    (fun i => fun v => JetField.pd ((), (i : ℕ)) v)
    (fun i a b => map_add _ a b) (fun i a b => ?_) (fun i c => ?_)
    (Matrix.of fun i j => JetField.pd ((), (i : ℕ)) (substitutionJet R (j : ℕ))) ?_
    (fun i j => rfl)
  · have h := (JetField.pd ((), (i : ℕ)) : Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      a b
    simpa only [smul_eq_mul] using h
  · exact (JetField.pd ((), (i : ℕ)) :
      Derivation C (JetField C Unit) (JetField C Unit)).map_algebraMap c
  · have htri : (Matrix.of fun i j : Fin n =>
        JetField.pd ((), (i : ℕ)) (substitutionJet R (j : ℕ))).BlockTriangular id := by
      intro i j hij
      exact pd_substitutionJet_eq_zero_of_lt R (by exact_mod_cast hij)
    rw [Matrix.det_of_upperTriangular htri]
    have hdiag : ∀ i : Fin n, (Matrix.of fun i j : Fin n =>
        JetField.pd ((), (i : ℕ)) (substitutionJet R (j : ℕ))) i i = substitutionDeriv R :=
      fun i => pd_substitutionJet_self R (i : ℕ)
    rw [Finset.prod_congr rfl (fun i _ => hdiag i), Finset.prod_const]
    exact pow_ne_zero _ hR

theorem algebraicIndependent_substitutionJet [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) :
    AlgebraicIndependent C (fun p : Unit × ℕ => substitutionJet R p.2) := by
  classical
  refine algebraicIndependent_of_finite_type fun t ht => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ p ∈ t, p.2 < n := by
    obtain ⟨N, hN⟩ := (ht.image (fun p : Unit × ℕ => p.2)).bddAbove
    refine ⟨N + 1, fun p hp => ?_⟩
    have h : p.2 ≤ N := hN ⟨p, hp, rfl⟩
    omega
  refine (algebraicIndependent_substitutionJet_fin R hR n).comp
    (fun i : t => (⟨(i : Unit × ℕ).2, hn _ i.2⟩ : Fin n)) ?_
  intro a b hab
  have h2 : (a : Unit × ℕ).2 = (b : Unit × ℕ).2 := by
    simpa using congrArg Fin.val hab
  refine Subtype.ext ?_
  exact Prod.ext (Subsingleton.elim _ _) h2

/-! ## The endomorphism -/

/-- The substitution on the polynomial ring of jet coordinates. -/
def substitutionPolyHom (R : RatFunc C) : JetPoly C Unit →ₐ[C] JetField C Unit :=
  MvPolynomial.aeval (fun p : Unit × ℕ => substitutionJet R p.2)

theorem substitutionPolyHom_injective [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) : Function.Injective (substitutionPolyHom R) :=
  algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_substitutionJet R hR)

/-- **The rational substitution endomorphism** of the free jet field. -/
def jetSubstitution [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    JetField C Unit →ₐ[C] JetField C Unit :=
  IsFractionRing.liftAlgHom (substitutionPolyHom_injective R hR)

@[simp]
theorem jetSubstitution_jet [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (l : ℕ) :
    jetSubstitution R hR (JetField.jet ((), l)) = substitutionJet R l := by
  rw [jetSubstitution, JetField.jet, IsFractionRing.liftAlgHom_apply,
    IsFractionRing.lift_algebraMap]
  exact MvPolynomial.aeval_X _ _

theorem jetSubstitution_injective [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    Function.Injective (jetSubstitution R hR) :=
  (jetSubstitution R hR).toRingHom.injective

/-! ## The substitution is differential -/

/-- The locus where the substitution commutes with the derivation is an intermediate field. -/
def substitutionCommuteField [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    IntermediateField C (JetField C Unit) where
  carrier := {v | jetSubstitution R hR (JetField.jetDerivation v)
    = JetField.jetDerivation (jetSubstitution R hR v)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_add, hx, hy, map_add, map_add]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hx, hy,
      map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_setOf_eq]
    rw [Derivation.map_algebraMap, map_zero, AlgHom.commutes, Derivation.map_algebraMap]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_rhs => rw [map_inv₀]
    rw [Derivation.leibniz_inv, smul_eq_mul, map_mul, map_neg, map_pow, map_inv₀, hx,
      Derivation.leibniz_inv, smul_eq_mul]

theorem jet_mem_substitutionCommuteField [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (l : ℕ) :
    (JetField.jet ((), l) : JetField C Unit) ∈ substitutionCommuteField R hR := by
  show jetSubstitution R hR (JetField.jetDerivation (JetField.jet ((), l)))
      = JetField.jetDerivation (jetSubstitution R hR (JetField.jet ((), l)))
  rw [← JetField.deriv_eq, JetField.deriv_jet, jetSubstitution_jet, jetSubstitution_jet,
    ← JetField.deriv_eq, substitutionJet, substitutionJet, differentialJet_succ]

/-- **The substitution is a differential endomorphism.** -/
theorem jetSubstitution_jetDerivation [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (v : JetField C Unit) :
    jetSubstitution R hR (JetField.jetDerivation v)
      = JetField.jetDerivation (jetSubstitution R hR v) := by
  have htop : (⊤ : IntermediateField C (JetField C Unit)) ≤ substitutionCommuteField R hR := by
    rw [← differentialAdjoin_jet_zero_eq_top, differentialAdjoin,
      differentialJetSet_jet_zero, IntermediateField.adjoin_le_iff]
    rintro z ⟨⟨j, l⟩, rfl⟩
    have hj : j = () := rfl
    subst hj
    exact jet_mem_substitutionCommuteField R hR l
  exact htop (by trivial)

theorem jetSubstitution_deriv [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (v : JetField C Unit) :
    jetSubstitution R hR (v′) = (jetSubstitution R hR v)′ := by
  rw [JetField.deriv_eq, JetField.deriv_eq]
  exact jetSubstitution_jetDerivation R hR v

/-! ## The orbifold tail -/

@[simp]
theorem jetSubstitution_freeGen [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    jetSubstitution R hR (JetField.jet ((), 0)) = substitutionValue R := by
  rw [jetSubstitution_jet, substitutionJet, differentialJet_zero]

/-- **The orbifold tail of a rational map**: the differential field of observables surviving every
depth of the substitution tower. -/
def orbifoldTail [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    IntermediateField C (JetField C Unit) :=
  stableRangeCore (jetSubstitution R hR)

/-- The tail is closed under the ambient derivation, hence a differential field. -/
theorem derivationClosed_orbifoldTail [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) : DerivationClosed (orbifoldTail R hR) :=
  derivationClosed_stableRangeCore _ (jetSubstitution_deriv R hR)

/-- The substitution restricts to an automorphism of its own tail. -/
def orbifoldTailAlgEquiv [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    orbifoldTail R hR ≃ₐ[C] orbifoldTail R hR :=
  stableRangeCoreAlgEquiv (jetSubstitution R hR)

/-- **Eigen-current tail inclusion for a rational substitution.**  A current scaled by a nonzero
constant under the substitution generates a subfield of the tail. -/
theorem adjoin_le_orbifoldTail_of_eigenvector [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (q : JetField C Unit) (a : C) (ha : a ≠ 0)
    (hq : jetSubstitution R hR q = algebraMap C (JetField C Unit) a * q) :
    IntermediateField.adjoin C ({q} : Set (JetField C Unit)) ≤ orbifoldTail R hR :=
  adjoin_le_stableRangeCore_of_algebraMap_eigenvector _ q a ha hq

/-! ## The chain rule for the substitution -/

/-- The locus where the coordinate partial of the substituted element is the expected total
derivative. -/
def substitutionChainField [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (M N : ℕ) : IntermediateField C (JetField C Unit) where
  carrier := {v | JetField.pd ((), M) (jetSubstitution R hR v)
    = ∑ l ∈ Finset.range (N + 1),
        jetSubstitution R hR (JetField.pd ((), l) v) *
          JetField.pd ((), M) (substitutionJet R l)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add, map_add]
    ring
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hLHS : JetField.pd ((), M) (jetSubstitution R hR (x * y))
        = jetSubstitution R hR x * JetField.pd ((), M) (jetSubstitution R hR y)
          + jetSubstitution R hR y * JetField.pd ((), M) (jetSubstitution R hR x) := by
      rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [hLHS, hx, hy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    ring
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_setOf_eq]
    rw [AlgHom.commutes, Derivation.map_algebraMap]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [Derivation.map_algebraMap, map_zero, zero_mul]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_inv₀, Derivation.leibniz_inv, smul_eq_mul, hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Derivation.leibniz_inv, smul_eq_mul, map_mul, map_neg, map_pow, map_inv₀]
    ring

theorem jet_mem_substitutionChainField [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (M : ℕ) {N j : ℕ} (hj : j ≤ N) :
    (JetField.jet ((), j) : JetField C Unit) ∈ substitutionChainField R hR M N := by
  show JetField.pd ((), M) (jetSubstitution R hR (JetField.jet ((), j)))
      = ∑ l ∈ Finset.range (N + 1),
          jetSubstitution R hR (JetField.pd ((), l) (JetField.jet ((), j))) *
            JetField.pd ((), M) (substitutionJet R l)
  rw [jetSubstitution_jet, Finset.sum_eq_single j]
  · rw [JetField.pd_jet_self, map_one, one_mul]
  · intro l _ hlj
    rw [JetField.pd_jet_of_ne (by simp [Prod.ext_iff, hlj]), map_zero, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- **The chain rule.**  On elements of order at most `M` the top coordinate partial of the
substituted element is the substituted partial times the derivative factor. -/
theorem pd_jetSubstitution_top [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {v : JetField C Unit} {M : ℕ} (hv : ∀ j : ℕ, M < j → JetField.pd ((), j) v = 0) :
    JetField.pd ((), M) (jetSubstitution R hR v)
      = jetSubstitution R hR (JetField.pd ((), M) v) * substitutionDeriv R := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_jetObservableField_of_mem_differentialAdjoin
    (C := C) (y := (JetField.jet ((), 0) : JetField C Unit)) (z := v)
    (by rw [differentialAdjoin_jet_zero_eq_top]; trivial)
  set N : ℕ := max N₀ (M + 1) with hN
  have hvN : v ∈ jetObservableField C (JetField.jet ((), 0) : JetField C Unit) (N + 1) :=
    jetObservableField_mono _ (by omega) hN₀
  have hle : jetObservableField C (JetField.jet ((), 0) : JetField C Unit) (N + 1)
      ≤ substitutionChainField R hR M N := by
    rw [jetObservableField, IntermediateField.adjoin_le_iff]
    rintro z ⟨n, hn, rfl⟩
    show differentialJet n (JetField.jet ((), 0) : JetField C Unit)
      ∈ substitutionChainField R hR M N
    rw [JetField.differentialJet_jet_of_zero]
    exact jet_mem_substitutionChainField R hR M (by
      have : n < N + 1 := hn
      omega)
  have hsum : JetField.pd ((), M) (jetSubstitution R hR v)
      = ∑ l ∈ Finset.range (N + 1),
          jetSubstitution R hR (JetField.pd ((), l) v) *
            JetField.pd ((), M) (substitutionJet R l) := hle hvN
  rw [hsum, Finset.sum_eq_single M]
  · rw [pd_substitutionJet_self]
  · intro l _ hlM
    rcases lt_or_gt_of_ne hlM with hlt | hgt
    · rw [pd_substitutionJet_eq_zero_of_lt R hlt, mul_zero]
    · rw [hv l hgt, map_zero, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-! ## The principal-symbol eigen-relation -/

/-- Coordinate partials commute. -/
theorem pd_commutator {ι : Type*} (p q : ι × ℕ) :
    ⁅JetField.pd (C := C) (ι := ι) p, JetField.pd (C := C) (ι := ι) q⁆ = 0 := by
  refine JetField.derivation_ext fun r => ?_
  have h1 : JetField.pd p (JetField.pd q (JetField.jet r) : JetField C ι) = 0 := by
    by_cases hq : q = r
    · subst hq
      rw [JetField.pd_jet_self, Derivation.map_one_eq_zero]
    · rw [JetField.pd_jet_of_ne hq, map_zero]
  have h2 : JetField.pd q (JetField.pd p (JetField.jet r) : JetField C ι) = 0 := by
    by_cases hp : p = r
    · subst hp
      rw [JetField.pd_jet_self, Derivation.map_one_eq_zero]
    · rw [JetField.pd_jet_of_ne hp, map_zero]
  rw [Derivation.commutator_apply, h1, h2, sub_zero]
  rfl

theorem pd_comm {ι : Type*} (p q : ι × ℕ) (u : JetField C ι) :
    JetField.pd p (JetField.pd q u) = JetField.pd q (JetField.pd p u) := by
  have h := congrArg (fun D : Derivation C (JetField C ι) (JetField C ι) => D u)
    (pd_commutator (C := C) p q)
  simp only [Derivation.commutator_apply] at h
  have h0 : JetField.pd p (JetField.pd q u) - JetField.pd q (JetField.pd p u) = 0 := by
    simpa using h
  exact sub_eq_zero.mp h0

/-- The principal symbol of an element of order at most `M` again has order at most `M`. -/
theorem pd_order_le {M : ℕ} {u : JetField C Unit}
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0) :
    ∀ j : ℕ, M < j → JetField.pd ((), j) (JetField.pd ((), M) u) = 0 := by
  intro j hj
  rw [pd_comm, hu j hj, map_zero]

/-- **(T1).**  The principal symbol of an eigenvector of the substitution is an eigenvector with
the derivative factor attached. -/
theorem pd_eigen_of_jetSubstitution_eigen [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) {u : JetField C Unit} {M : ℕ}
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0) {lam : C}
    (heig : jetSubstitution R hR u = algebraMap C (JetField C Unit) lam * u) :
    jetSubstitution R hR (JetField.pd ((), M) u) * substitutionDeriv R
      = algebraMap C (JetField C Unit) lam * JetField.pd ((), M) u := by
  have h : JetField.pd ((), M) (jetSubstitution R hR u)
      = JetField.pd ((), M) (algebraMap C (JetField C Unit) lam * u) := by rw [heig]
  rw [pd_jetSubstitution_top R hR hu, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
    add_zero, smul_eq_mul] at h
  exact h

/-- **(T3).**  The logarithmic derivative of the principal symbol is an eigenvector with
eigenvalue one, whatever the original eigenvalue was. -/
theorem eigen_logDeriv_pd_of_jetSubstitution_eigen [CharZero C] (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) {u : JetField C Unit} {M : ℕ} (hM : 1 ≤ M)
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0) {lam : C} (hlam : lam ≠ 0)
    (hw0 : JetField.pd ((), M) u ≠ 0)
    (heig : jetSubstitution R hR u = algebraMap C (JetField C Unit) lam * u) :
    jetSubstitution R hR
        (JetField.pd ((), M) (JetField.pd ((), M) u) / JetField.pd ((), M) u) *
      substitutionDeriv R
      = JetField.pd ((), M) (JetField.pd ((), M) u) / JetField.pd ((), M) u := by
  have hchain : JetField.pd ((), M) (jetSubstitution R hR (JetField.pd ((), M) u))
      = jetSubstitution R hR (JetField.pd ((), M) (JetField.pd ((), M) u)) *
        substitutionDeriv R :=
    pd_jetSubstitution_top R hR (pd_order_le hu)
  have hρ : JetField.pd ((), M) (substitutionDeriv R) = 0 := by
    rw [substitutionDeriv, pd_comm, pd_substitutionValue_eq_zero R (by omega), map_zero]
  have hlam0 : algebraMap C (JetField C Unit) lam ≠ 0 := by
    have hinj : Function.Injective (algebraMap C (JetField C Unit)) :=
      (algebraMap C (JetField C Unit)).injective
    exact (map_ne_zero_iff _ hinj).mpr hlam
  exact eigen_logDeriv_of_chain_rule (JetField.pd ((), M))
    (jetSubstitution R hR).toRingHom hchain hρ hR
    (Derivation.map_algebraMap _ lam) hlam0 hw0
    (pd_eigen_of_jetSubstitution_eigen R hR hu heig)

/-! ## The first jet is scaled exactly -/

theorem pd_substitutionDeriv_eq_zero (R : RatFunc C) {k : ℕ} (hk : k ≠ 0) :
    JetField.pd ((), k) (substitutionDeriv R) = 0 := by
  rw [substitutionDeriv, pd_comm, pd_substitutionValue_eq_zero R hk, map_zero]

/-- The substitution scales the first jet coordinate by the derivative factor. -/
theorem substitutionJet_one (R : RatFunc C) :
    substitutionJet R 1 = JetField.jet ((), 1) * substitutionDeriv R := by
  classical
  have hmem : substitutionValue R ∈
      freeCoordinateField C (Unit × ℕ) (↑({((), 0)} : Finset (Unit × ℕ)) : Set (Unit × ℕ)) := by
    have h := substitutionValue_mem_adjoin R
    have hset : (freeCoordinate C (Unit × ℕ) '' (↑({((), 0)} : Finset (Unit × ℕ)) :
        Set (Unit × ℕ))) = ({JetField.jet ((), 0)} : Set (JetField C Unit)) := by
      ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hq0 : q = ((), 0) := by simpa using hq
        rw [hq0]
        rfl
      · rintro rfl
        exact ⟨((), 0), by simp, rfl⟩
    rw [freeCoordinateField, hset]
    exact h
  have h := freeCoordinate_chainRule ({((), 0)} : Finset (Unit × ℕ))
    (JetField.jetDerivation (C := C) (ι := Unit)) hmem
  rw [Finset.sum_singleton] at h
  calc substitutionJet R 1 = JetField.jetDerivation (substitutionValue R) := by
        rw [substitutionJet, differentialJet_succ, differentialJet_zero, JetField.deriv_eq]
    _ = JetField.jetDerivation (JetField.jet ((), 0) : JetField C Unit) *
          JetField.pd ((), 0) (substitutionValue R) := h
    _ = JetField.jet ((), 1) * substitutionDeriv R := by
        rw [JetField.jetDerivation_jet, substitutionDeriv]

theorem jetSubstitution_jet_one [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    jetSubstitution R hR (JetField.jet ((), 1))
      = JetField.jet ((), 1) * substitutionDeriv R := by
  rw [jetSubstitution_jet, substitutionJet_one]

/-! ## The Euler quotient of a first-order eigenvector is invariant -/

theorem mem_orbifoldTail_of_fixed [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {g : JetField C Unit} (hg : jetSubstitution R hR g = g) : g ∈ orbifoldTail R hR := by
  rw [orbifoldTail, mem_stableRangeCore_iff]
  intro n
  refine ⟨g, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [AlgHom.coe_pow, Function.iterate_succ_apply'] at ih ⊢
      rw [ih, hg]

/-- **The Euler quotient is an invariant.**  For a first-order eigenvector of the substitution
with the derivative factor as eigenvalue, the logarithmic Euler derivative in the first jet
coordinate is fixed by the substitution, hence lies in the tail. -/
theorem jetSubstitution_eulerQuotient [CharZero C] (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {v : JetField C Unit} (hv0 : v ≠ 0)
    (hv : ∀ j : ℕ, 1 < j → JetField.pd ((), j) v = 0)
    (heig : jetSubstitution R hR v * substitutionDeriv R = v) :
    jetSubstitution R hR (JetField.jet ((), 1) * JetField.pd ((), 1) v / v)
      = JetField.jet ((), 1) * JetField.pd ((), 1) v / v := by
  have hΦv : jetSubstitution R hR v = v / substitutionDeriv R := by
    field_simp
    linear_combination heig
  have hΦv0 : jetSubstitution R hR v ≠ 0 := by
    intro h
    exact hv0 (jetSubstitution_injective R hR (by rw [h, map_zero]))
  have hρ1 : JetField.pd ((), 1) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R one_ne_zero
  have hchain : JetField.pd ((), 1) (jetSubstitution R hR v)
      = jetSubstitution R hR (JetField.pd ((), 1) v) * substitutionDeriv R :=
    pd_jetSubstitution_top R hR hv
  have hpd : JetField.pd ((), 1) (jetSubstitution R hR v)
      = JetField.pd ((), 1) v / substitutionDeriv R := by
    rw [hΦv, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hρ1, smul_zero,
      smul_zero, zero_add, smul_eq_mul]
    field_simp
  have hΦpd : jetSubstitution R hR (JetField.pd ((), 1) v)
      = JetField.pd ((), 1) v / (substitutionDeriv R * substitutionDeriv R) := by
    rw [hpd] at hchain
    field_simp at hchain
    rw [eq_div_iff (mul_ne_zero hR hR)]
    linear_combination -hchain
  rw [map_div₀, map_mul, jetSubstitution_jet_one, hΦpd, hΦv]
  field_simp

end

end GaloisForLFunctions.HTGeometry
