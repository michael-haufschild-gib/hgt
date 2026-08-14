import GaloisForLFunctions.HTGeometry.ComplexTorusTail
import GaloisForLFunctions.HTGeometry.ComplexLatticeDensity
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# The phase tail of a complex torus protocol is the Maurer–Cartan velocity field

On the generic reparametrisation of the entire fraction field of `ℂ ^ n`, the invariants of every
deck translation of a degree-expanding isogeny protocol of a compact complex torus `ℂ ^ n / Λ` are
exactly the differential rational functions of the `n` velocities.

Nothing of the position survives, the surviving field has differential transcendence degree `n`, the
dimension of the group, and it meets the function field of the group only in the constants.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-! ### The constants of the entire fraction field -/

/-- The complex constants make the entire fraction field a `ℂ`-algebra. -/
noncomputable instance entireComplexAlgebra (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] : Algebra ℂ (EntireField V) :=
  (constEntire V).toAlgebra

theorem algebraMap_entireField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ) :
    algebraMap ℂ (EntireField V) c = constEntire V c := rfl

theorem algebraMap_entireField_injective {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] :
    Function.Injective (algebraMap ℂ (EntireField V)) := constEntire_injective

/-! ### The differential-generic carrier of a complex torus protocol -/

variable {n : ℕ}

/-- The standard coordinate frame of `ℂ ^ n`. -/
def stdFrame (n : ℕ) (j : Fin n) : Fin n → ℂ := Pi.single j 1

/-- The coordinate derivations of the entire fraction field of `ℂ ^ n`. -/
noncomputable def torusDeriv (n : ℕ) (j : Fin n) :
    Derivation ℤ (EntireField (Fin n → ℂ)) (EntireField (Fin n → ℂ)) :=
  fieldDirDerivation (stdFrame n j)

/-- The generic reparametrisation of the entire fraction field of `ℂ ^ n`: the carrier on which a
point of an `n`-dimensional complex torus is differential-generic. -/
abbrev TorusField (n : ℕ) : Type := MultiReparamField (EntireField (Fin n → ℂ)) n

/-- The chain-rule derivation of the reparametrised entire fraction field of `ℂ ^ n`. -/
noncomputable instance torusReparamDifferential (n : ℕ) : Differential (TorusField n) :=
  ⟨MultiReparamField.fieldDerivation (torusDeriv n)⟩

theorem torusField_deriv_eq (z : TorusField n) :
    z′ = MultiReparamField.fieldDerivation (torusDeriv n) z := rfl

@[simp] theorem torusField_deriv_jet (p : Fin n × ℕ) :
    (MultiReparamField.jet p : TorusField n)′ = MultiReparamField.jet (p.1, p.2 + 1) := by
  rw [torusField_deriv_eq, MultiReparamField.fieldDerivation_jet]

theorem torusField_deriv_algebraMap (a : EntireField (Fin n → ℂ)) :
    (algebraMap (EntireField (Fin n → ℂ)) (TorusField n) a)′
      = ∑ j : Fin n, algebraMap (EntireField (Fin n → ℂ)) (TorusField n) (torusDeriv n j a)
          * MultiReparamField.jet (j, 0) := by
  rw [torusField_deriv_eq, MultiReparamField.fieldDerivation_algebraMap]

/-! ### The constants as a differential subfield -/

local instance torusComplexDifferential : Differential ℂ where
  deriv := 0

noncomputable instance torusReparamComplexAlgebra (n : ℕ) : Algebra ℂ (TorusField n) :=
  inferInstanceAs (Algebra ℂ (FractionRing (MultiReparamPoly (EntireField (Fin n → ℂ)) n)))

instance torusReparamComplexTower (n : ℕ) :
    IsScalarTower ℂ (EntireField (Fin n → ℂ)) (TorusField n) :=
  inferInstanceAs (IsScalarTower ℂ (EntireField (Fin n → ℂ))
    (FractionRing (MultiReparamPoly (EntireField (Fin n → ℂ)) n)))

theorem algebraMap_torusField (c : ℂ) :
    algebraMap ℂ (TorusField n) c
      = algebraMap (EntireField (Fin n → ℂ)) (TorusField n) (constEntire (Fin n → ℂ) c) := by
  rw [IsScalarTower.algebraMap_apply ℂ (EntireField (Fin n → ℂ)) (TorusField n)]
  rfl

/-- The complex constants are differential constants of the reparametrised field. -/
theorem torusField_deriv_algebraMap_complex (c : ℂ) :
    (algebraMap ℂ (TorusField n) c)′ = 0 := by
  rw [algebraMap_torusField, torusField_deriv_algebraMap]
  have hzero : ∀ j : Fin n, torusDeriv n j (constEntire (Fin n → ℂ) c) = 0 := fun j =>
    fieldDirDerivation_constEntire (stdFrame n j) c
  simp only [hzero, map_zero, zero_mul, Finset.sum_const_zero]

local instance torusReparamComplexDifferentialAlgebra (n : ℕ) :
    DifferentialAlgebra ℂ (TorusField n) :=
  ⟨fun c => by
    rw [torusField_deriv_algebraMap_complex]
    show (0 : TorusField n) = algebraMap ℂ (TorusField n) (0 : ℂ)
    rw [map_zero]⟩

/-! ### The velocity field -/

/-- The jets of a coordinate of the reparametrisation are the derivatives of its velocity. -/
theorem differentialJet_torusJet (j : Fin n) (i : ℕ) :
    differentialJet i (MultiReparamField.jet (j, 0) : TorusField n)
      = MultiReparamField.jet (j, i) := by
  induction i with
  | zero => simp [differentialJet_zero]
  | succ i ih => rw [differentialJet_succ, ih, torusField_deriv_jet]

/-- **The velocity field of a complex torus protocol**: the differential rational functions of the
`n` Maurer–Cartan velocities. -/
noncomputable def complexTorusVelocityField (n : ℕ) : IntermediateField ℂ (TorusField n) :=
  differentialAdjoin ℂ
    (Set.range fun j : Fin n => (MultiReparamField.jet (j, 0) : TorusField n))

/-- Every jet lies in the velocity field. -/
theorem jet_mem_torusVelocityField (p : Fin n × ℕ) :
    (MultiReparamField.jet p : TorusField n) ∈ complexTorusVelocityField n := by
  have hmem := differentialJet_mem_differentialAdjoin ℂ
    (s := Set.range fun j : Fin n => (MultiReparamField.jet (j, 0) : TorusField n))
    (x := MultiReparamField.jet (p.1, 0)) ⟨p.1, rfl⟩ p.2
  rwa [differentialJet_torusJet] at hmem

/-- A jet polynomial with constant coefficients lies in the velocity field. -/
theorem algebraMap_mem_torusVelocityField_of_const_coeff
    {p : MultiReparamPoly (EntireField (Fin n → ℂ)) n}
    (hp : ∀ m, MvPolynomial.coeff m p ∈ (constEntire (Fin n → ℂ)).fieldRange) :
    algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n) p
      ∈ complexTorusVelocityField n := by
  classical
  have hsum : p = ∑ m ∈ p.support, MvPolynomial.monomial m (MvPolynomial.coeff m p) :=
    MvPolynomial.as_sum p
  rw [hsum, map_sum]
  refine sum_mem fun m _ => ?_
  rw [MvPolynomial.monomial_eq, map_mul]
  refine mul_mem ?_ ?_
  · obtain ⟨c, hc⟩ := hp m
    have hbase : algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)
          (MvPolynomial.C (MvPolynomial.coeff m p))
        = algebraMap ℂ (TorusField n) c := by
      rw [IsScalarTower.algebraMap_apply ℂ (EntireField (Fin n → ℂ)) (TorusField n), ← hc]
      rfl
    rw [hbase]
    exact IntermediateField.algebraMap_mem _ c
  · rw [Finsupp.prod, map_prod]
    refine prod_mem fun i _ => ?_
    rw [map_pow]
    exact pow_mem (jet_mem_torusVelocityField i) _

/-! ### The deck-invariant field -/

/-- The invariants of every deck translation of every depth of a complex torus protocol. -/
noncomputable def torusDeckInvariantField (L : PeriodLattice (Fin n → ℂ)) (M : ℕ → ℂ) :
    IntermediateField ℂ (TorusField n) where
  carrier := {x : TorusField n | ∀ k : ℕ, ∀ t : Fin n → ℂ, M k • t ∈ L.lattice →
    MultiReparamField.fieldEquiv (n := n) (fieldTranslateEquiv t) x = x}
  zero_mem' := by intro k t _; simp
  one_mem' := by intro k t _; simp
  add_mem' := by
    intro x y hx hy k t ht
    rw [map_add, hx k t ht, hy k t ht]
  mul_mem' := by
    intro x y hx hy k t ht
    rw [map_mul, hx k t ht, hy k t ht]
  inv_mem' := by
    intro x hx k t ht
    rw [map_inv₀, hx k t ht]
  algebraMap_mem' := by
    intro c k t _
    rw [algebraMap_torusField, MultiReparamField.fieldEquiv_base, fieldTranslateEquiv_constEntire]

theorem mem_torusDeckInvariantField_iff (L : PeriodLattice (Fin n → ℂ)) (M : ℕ → ℂ)
    {x : TorusField n} :
    x ∈ torusDeckInvariantField L M ↔ ∀ k : ℕ, ∀ t : Fin n → ℂ, M k • t ∈ L.lattice →
      MultiReparamField.fieldEquiv (n := n) (fieldTranslateEquiv t) x = x := Iff.rfl

/-- The deck-invariant field is closed under the chain-rule derivation. -/
theorem derivationClosed_torusDeckInvariantField (L : PeriodLattice (Fin n → ℂ)) (M : ℕ → ℂ) :
    DerivationClosed (torusDeckInvariantField L M) := by
  intro x hx k t ht
  have hcomm : ∀ (j : Fin n) (a : EntireField (Fin n → ℂ)),
      fieldTranslateEquiv t (torusDeriv n j a) = torusDeriv n j (fieldTranslateEquiv t a) :=
    fun j a => fieldTranslateEquiv_dirDerivation t (stdFrame n j) a
  have hstep := MultiReparamField.fieldEquiv_deriv (n := n) (torusDeriv n)
    (fieldTranslateEquiv t) hcomm x
  show MultiReparamField.fieldEquiv (n := n) (fieldTranslateEquiv t)
      (MultiReparamField.fieldDerivation (torusDeriv n) x) = _
  rw [hstep, hx k t ht]
  rfl

/-- **The phase tail of a complex torus protocol is the velocity field.**  For accumulated isogeny
degrees of unbounded norm on a compact complex torus `ℂ ^ n / Λ`, the elements of the generic
reparametrisation fixed by every deck translation of every depth are exactly the differential
rational functions of the `n` Maurer–Cartan velocities. -/
theorem torusDeckInvariantField_eq_torusVelocityField (L : PeriodLattice (Fin n → ℂ))
    (M : ℕ → ℂ) (hM : ∀ k, M k ≠ 0) (hMinf : Tendsto (fun k => ‖M k‖) atTop atTop) :
    torusDeckInvariantField L M = complexTorusVelocityField n := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨p, q, hq0, hpc, hqc, hrep⟩ :=
      exists_const_coeff_representation_of_dense_translation_fixed
        (dense_divisionPoints L M hM hMinf) x (by
          rintro t ⟨k, hk⟩
          exact hx k t hk)
    have hqne : algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n) q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (MultiReparamPoly (EntireField (Fin n → ℂ)) n)
        (TorusField n) (by rw [h, map_zero]))
    have hxval : x = algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n) p
        / algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n) q := by
      rw [eq_div_iff hqne, mul_comm]
      exact hrep
    rw [hxval]
    exact div_mem (algebraMap_mem_torusVelocityField_of_const_coeff hpc)
      (algebraMap_mem_torusVelocityField_of_const_coeff hqc)
  · refine differentialAdjoin_le ℂ ?_ (derivationClosed_torusDeckInvariantField L M)
    rintro y ⟨j, rfl⟩
    intro k t _
    exact MultiReparamField.fieldEquiv_jet (n := n) (fieldTranslateEquiv t) (j, 0)

/-! ### Differential transcendence of the velocity -/

/-- The jet coordinates are algebraically independent over the base. -/
theorem algebraicIndependent_torusJet :
    AlgebraicIndependent (EntireField (Fin n → ℂ))
      (fun p : Fin n × ℕ => (MultiReparamField.jet p : TorusField n)) := by
  have hX : AlgebraicIndependent (EntireField (Fin n → ℂ))
      (fun p : Fin n × ℕ =>
        (MvPolynomial.X p : MultiReparamPoly (EntireField (Fin n → ℂ)) n)) :=
    MvPolynomial.algebraicIndependent_X (Fin n × ℕ) (EntireField (Fin n → ℂ))
  have hinj : Function.Injective (IsScalarTower.toAlgHom (EntireField (Fin n → ℂ))
      (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)) :=
    IsFractionRing.injective (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)
  exact (AlgHom.algebraicIndependent_iff (IsScalarTower.toAlgHom (EntireField (Fin n → ℂ))
    (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)) hinj).2 hX

/-- **The `n` velocities are differentially independent over the constants.**  The phase tail of a
complex torus protocol therefore has differential transcendence degree `n`, the dimension of the
group. -/
theorem differentialIndependent_torusVelocity :
    DifferentialIndependent ℂ
      (fun j : Fin n => (MultiReparamField.jet (j, 0) : TorusField n)) := by
  have hbase : AlgebraicIndependent ℂ
      (fun p : Fin n × ℕ => (MultiReparamField.jet p : TorusField n)) :=
    algebraicIndependent_torusJet.restrictScalars algebraMap_entireField_injective
  show AlgebraicIndependent ℂ _
  have hfun : (fun p : Fin n × ℕ =>
      differentialJet p.2 ((fun j : Fin n => (MultiReparamField.jet (j, 0) : TorusField n)) p.1))
      = fun p : Fin n × ℕ => (MultiReparamField.jet p : TorusField n) := by
    funext p
    exact differentialJet_torusJet p.1 p.2
  rw [hfun]
  exact hbase

/-! ### The velocity carries no position -/

/-- The velocity field is generated by the jets. -/
theorem torusVelocityField_eq_adjoin_range_jet :
    complexTorusVelocityField n = IntermediateField.adjoin ℂ
      (Set.range (MultiReparamField.jet : Fin n × ℕ → TorusField n)) := by
  have hset : differentialJetSet
      (Set.range fun j : Fin n => (MultiReparamField.jet (j, 0) : TorusField n))
      = Set.range (MultiReparamField.jet : Fin n × ℕ → TorusField n) := by
    ext y
    constructor
    · rintro ⟨z, ⟨j, rfl⟩, i, rfl⟩
      exact ⟨(j, i), (differentialJet_torusJet j i).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨MultiReparamField.jet (p.1, 0), ⟨p.1, rfl⟩, p.2, differentialJet_torusJet p.1 p.2⟩
  rw [complexTorusVelocityField, differentialAdjoin, hset]

/-- Evaluating a complex jet polynomial is the image of its constant-coefficient lift. -/
theorem aeval_torusJet_eq_algebraMap (P : MvPolynomial (Fin n × ℕ) ℂ) :
    MvPolynomial.aeval (MultiReparamField.jet : Fin n × ℕ → TorusField n) P
      = algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)
        (MvPolynomial.map (constEntire (Fin n → ℂ)) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C]
      rw [IsScalarTower.algebraMap_apply ℂ (EntireField (Fin n → ℂ)) (TorusField n)]
      rfl
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]
      rfl

/-- **The velocity carries no position.**  An element of the base lying in the velocity field is a
constant, so the phase tail meets the function field of the torus only in the constants. -/
theorem eq_constEntire_of_algebraMap_mem_torusVelocityField {a : EntireField (Fin n → ℂ)}
    (ha : algebraMap (EntireField (Fin n → ℂ)) (TorusField n) a ∈ complexTorusVelocityField n) :
    ∃ c : ℂ, a = constEntire (Fin n → ℂ) c := by
  classical
  rw [torusVelocityField_eq_adjoin_range_jet, IntermediateField.mem_adjoin_iff] at ha
  obtain ⟨r, s, hrs⟩ := ha
  have hlift : ∀ u : MvPolynomial
      ↥(Set.range (MultiReparamField.jet : Fin n × ℕ → TorusField n)) ℂ,
      ∃ U : MvPolynomial (Fin n × ℕ) ℂ,
        MvPolynomial.aeval (MultiReparamField.jet : Fin n × ℕ → TorusField n) U
          = MvPolynomial.aeval Subtype.val u := by
    intro u
    have hfun : (MultiReparamField.jet : Fin n × ℕ → TorusField n) ∘
        (fun t : ↥(Set.range (MultiReparamField.jet : Fin n × ℕ → TorusField n)) =>
          t.2.choose) = Subtype.val := by
      funext t
      exact t.2.choose_spec
    refine ⟨MvPolynomial.rename (fun t : ↥(Set.range
      (MultiReparamField.jet : Fin n × ℕ → TorusField n)) => t.2.choose) u, ?_⟩
    rw [MvPolynomial.aeval_rename, hfun]
  obtain ⟨P, hP⟩ := hlift r
  obtain ⟨Q, hQ⟩ := hlift s
  rw [← hP, ← hQ, aeval_torusJet_eq_algebraMap, aeval_torusJet_eq_algebraMap] at hrs
  by_cases hQ0 : MvPolynomial.map (constEntire (Fin n → ℂ)) Q = 0
  · rw [hQ0, map_zero, div_zero] at hrs
    refine ⟨0, ?_⟩
    have ha0 : a = 0 :=
      (algebraMap (EntireField (Fin n → ℂ)) (TorusField n)).injective (by rw [hrs, map_zero])
    rw [ha0, map_zero]
  · have hQne : algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)
        (MvPolynomial.map (constEntire (Fin n → ℂ)) Q) ≠ 0 := by
      intro h
      exact hQ0 (IsFractionRing.injective (MultiReparamPoly (EntireField (Fin n → ℂ)) n)
        (TorusField n) (by rw [h, map_zero]))
    rw [eq_div_iff hQne] at hrs
    have hbase : algebraMap (EntireField (Fin n → ℂ)) (TorusField n) a
        = algebraMap (MultiReparamPoly (EntireField (Fin n → ℂ)) n) (TorusField n)
          (MvPolynomial.C a) := rfl
    rw [hbase, ← map_mul] at hrs
    have hpoly : MvPolynomial.C a * MvPolynomial.map (constEntire (Fin n → ℂ)) Q
        = MvPolynomial.map (constEntire (Fin n → ℂ)) P :=
      IsFractionRing.injective (MultiReparamPoly (EntireField (Fin n → ℂ)) n)
        (TorusField n) hrs
    obtain ⟨m, hm⟩ : ∃ m, MvPolynomial.coeff m
        (MvPolynomial.map (constEntire (Fin n → ℂ)) Q) ≠ 0 := by
      by_contra hcon
      refine hQ0 (MvPolynomial.ext _ _ fun m => ?_)
      simp only [MvPolynomial.coeff_zero]
      by_contra hnem
      exact hcon ⟨m, hnem⟩
    have hcoeff := congrArg (MvPolynomial.coeff m) hpoly
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map] at hcoeff
    refine ⟨MvPolynomial.coeff m P / MvPolynomial.coeff m Q, ?_⟩
    rw [MvPolynomial.coeff_map] at hm
    rw [map_div₀, eq_div_iff hm]
    exact hcoeff

end GaloisForLFunctions.HTGeometry
