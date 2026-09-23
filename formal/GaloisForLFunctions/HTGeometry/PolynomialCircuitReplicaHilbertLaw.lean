import GaloisForLFunctions.HTGeometry.TwoQubitGateParametrisation
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomial circuit images have dimension-controlled replica rank

Continuous circuit classes cannot be charged by endpoint cardinality.  Their
coordinates are polynomial functions of finitely many gate parameters, so
their replicated linear span is controlled instead by the Hilbert function of
that polynomial image.

This module proves a cardinality-free law: if every coordinate of a target
family is a degree-`d` polynomial in `k` parameters, its order-`r` replicated
span has rank at most `(r*d+1)^k`.  Finite unions pay only the number of
polynomial charts.  Complete exact-`s` two-qubit circuit classes, including all
continuous gate choices, then have normalized Choi replica rank at most

`(n*n)^s * (r*s+1)^(16*s)`.

No unitarity assumption is needed for the upper bound: allowing arbitrary
`4 × 4` local gate entries only enlarges the polynomial image.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev multilinearReplicaFeatureIndex (k r : ℕ) := Fin k → Fin (r + 1)

@[simp] theorem card_multilinearReplicaFeatureIndex (k r : ℕ) :
    Fintype.card (multilinearReplicaFeatureIndex k r) = (r + 1) ^ k := by
  simp [multilinearReplicaFeatureIndex]

def multilinearReplicaExponent {k r : ℕ}
    (e : multilinearReplicaFeatureIndex k r) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

def multilinearDegreeBound (k r : ℕ) : Multiset (Fin k) :=
  r • (Finset.univ : Finset (Fin k)).1

def multilinearBoundedCoeffLinearMap (k r : ℕ) :
    MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r) →ₗ[ℂ]
      (multilinearReplicaFeatureIndex k r → ℂ) where
  toFun p e := MvPolynomial.coeff (multilinearReplicaExponent e) p.1
  map_add' p q := by ext e; simp
  map_smul' c p := by ext e; simp

theorem multilinearBoundedCoeffLinearMap_injective (k r : ℕ) :
    Function.Injective (multilinearBoundedCoeffLinearMap k r) := by
  classical
  intro p q hpq
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.toMultiset ≤ multilinearDegreeBound k r
  · have hcoord : ∀ i : Fin k, d i ≤ r := by
      intro i
      have hi := (Multiset.le_iff_count.mp hd i)
      simpa [multilinearDegreeBound] using hi
    let e : multilinearReplicaFeatureIndex k r :=
      fun i => ⟨d i, Nat.lt_succ_iff.mpr (hcoord i)⟩
    have hexp : multilinearReplicaExponent e = d := by
      apply Finsupp.equivFunOnFinite.injective
      ext i
      rfl
    have he := congrFun hpq e
    simpa [multilinearBoundedCoeffLinearMap, hexp] using he
  · have hpzero : MvPolynomial.coeff d p.1 = 0 := by
      by_contra hne
      have hmem : d ∈ p.1.support := MvPolynomial.mem_support_iff.mpr hne
      have hddeg : d.toMultiset ≤ p.1.degrees := by
        rw [MvPolynomial.degrees_def]
        exact Finset.le_sup hmem
      exact hd (hddeg.trans p.2)
    have hqzero : MvPolynomial.coeff d q.1 = 0 := by
      by_contra hne
      have hmem : d ∈ q.1.support := MvPolynomial.mem_support_iff.mpr hne
      have hddeg : d.toMultiset ≤ q.1.degrees := by
        rw [MvPolynomial.degrees_def]
        exact Finset.le_sup hmem
      exact hd (hddeg.trans q.2)
    rw [hpzero, hqzero]

theorem finrank_multilinearDegreesLE_le_pow (k r : ℕ) :
    Module.finrank ℂ
        (MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r)) ≤
      (r + 1) ^ k := by
  let f := multilinearBoundedCoeffLinearMap k r
  letI : Module.Finite ℂ
      (MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r)) :=
    Module.Finite.of_injective f (multilinearBoundedCoeffLinearMap_injective k r)
  calc
    Module.finrank ℂ
        (MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r)) ≤
      Module.finrank ℂ (multilinearReplicaFeatureIndex k r → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective
          (multilinearBoundedCoeffLinearMap_injective k r)
    _ = (r + 1) ^ k := by simp

theorem multilinearPolynomial_eq_sum_coeff
    {k r : ℕ}
    (p : MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r)) :
    p.1 = ∑ e : multilinearReplicaFeatureIndex k r,
      MvPolynomial.monomial (multilinearReplicaExponent e)
        (MvPolynomial.coeff (multilinearReplicaExponent e) p.1) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.toMultiset ≤ multilinearDegreeBound k r
  · have hcoord : ∀ i : Fin k, d i ≤ r := by
      intro i
      have hi := (Multiset.le_iff_count.mp hd i)
      simpa [multilinearDegreeBound] using hi
    let e : multilinearReplicaFeatureIndex k r :=
      fun i => ⟨d i, Nat.lt_succ_iff.mpr (hcoord i)⟩
    have hexp : multilinearReplicaExponent e = d := by
      apply Finsupp.equivFunOnFinite.injective
      ext i
      rfl
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp [hexp]
    · intro b _ hbe
      have hbne : multilinearReplicaExponent b ≠ d := by
        intro hbd
        apply hbe
        funext i
        have hi := congrFun
          (congrArg (fun z : Fin k →₀ ℕ => (z : Fin k → ℕ)) hbd) i
        exact Fin.ext hi
      simp [hbne]
    · simp
  · have hpzero : MvPolynomial.coeff d p.1 = 0 := by
      by_contra hne
      have hmem : d ∈ p.1.support := MvPolynomial.mem_support_iff.mpr hne
      have hddeg : d.toMultiset ≤ p.1.degrees := by
        rw [MvPolynomial.degrees_def]
        exact Finset.le_sup hmem
      exact hd (hddeg.trans p.2)
    rw [hpzero]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    symm
    apply Finset.sum_eq_zero
    intro e _
    have hexpBound : (multilinearReplicaExponent e).toMultiset ≤
        multilinearDegreeBound k r := by
      rw [Multiset.le_iff_count]
      intro i
      simp [multilinearReplicaExponent, multilinearDegreeBound]
      exact Nat.lt_succ_iff.mp (e i).isLt
    have hne : multilinearReplicaExponent e ≠ d := by
      intro h
      apply hd
      simpa [h] using hexpBound
    simp [hne]

theorem aeval_multilinearPolynomial_eq_sum_coeff
    {k r : ℕ}
    (p : MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r))
    (u : Fin k → ℂ) :
    MvPolynomial.aeval u p.1 =
      ∑ e : multilinearReplicaFeatureIndex k r,
        MvPolynomial.coeff (multilinearReplicaExponent e) p.1 *
          ∏ i, u i ^ (e i : ℕ) := by
  conv_lhs => rw [multilinearPolynomial_eq_sum_coeff p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial]
  simp [multilinearReplicaExponent]

def multilinearCoordinateProduct
    {α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ) (r : ℕ)
    (x : Fin r → α) : MvPolynomial (Fin k) ℂ :=
  ∏ j, coord (x j)

theorem multilinearCoordinateProduct_mem_degreesLE
    {α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k 1))
    (r : ℕ) (x : Fin r → α) :
    multilinearCoordinateProduct coord r x ∈
      MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k r) := by
  classical
  let base : Multiset (Fin k) := (Finset.univ : Finset (Fin k)).1
  have hcoord' : ∀ a, (coord a).degrees ≤ base := by
    intro a
    simpa [base, multilinearDegreeBound] using hcoord a
  have hprod : ∀ S : Finset (Fin r),
      (∏ j ∈ S, coord (x j)).degrees ≤ S.card • base := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
        rw [Finset.prod_insert ha]
        apply MvPolynomial.degrees_mul_le.trans
        simpa [Finset.card_insert_of_notMem ha, Nat.succ_eq_add_one,
          add_nsmul, add_comm] using add_le_add (hcoord' (x a)) ih
  simpa [multilinearCoordinateProduct, multilinearDegreeBound, base] using
    hprod Finset.univ

theorem polynomialCoordinateProduct_mem_degreesLE
    {α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k degree))
    (r : ℕ) (x : Fin r → α) :
    multilinearCoordinateProduct coord r x ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k (r * degree)) := by
  classical
  let base : Multiset (Fin k) := (Finset.univ : Finset (Fin k)).1
  have hcoord' : ∀ a, (coord a).degrees ≤ degree • base := by
    intro a
    simpa [base, multilinearDegreeBound] using hcoord a
  have hprod : ∀ S : Finset (Fin r),
      (∏ j ∈ S, coord (x j)).degrees ≤ (S.card * degree) • base := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
        rw [Finset.prod_insert ha]
        apply MvPolynomial.degrees_mul_le.trans
        simpa [Finset.card_insert_of_notMem ha, Nat.succ_eq_add_one,
          Nat.add_mul, add_nsmul, add_comm] using
            add_le_add (hcoord' (x a)) ih
  simpa [multilinearCoordinateProduct, multilinearDegreeBound, base] using
    hprod Finset.univ

def multilinearReplicaCoefficientMap
    {α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ) (r : ℕ) :
    (multilinearReplicaFeatureIndex k r → ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun z := WithLp.toLp 2 fun x =>
    ∑ e, z e * MvPolynomial.coeff (multilinearReplicaExponent e)
      (multilinearCoordinateProduct coord r x)
  map_add' z w := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext x
    simp [mul_assoc, Finset.mul_sum]

def polynomialReplicaCoefficientMap
    {α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ) (r degree : ℕ) :
    (multilinearReplicaFeatureIndex k (r * degree) → ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun z := WithLp.toLp 2 fun x =>
    ∑ e, z e * MvPolynomial.coeff (multilinearReplicaExponent e)
      (multilinearCoordinateProduct coord r x)
  map_add' z w := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext x
    simp [mul_assoc, Finset.mul_sum]

theorem finitePureTensorPowerEuclidean_aeval_mem_multilinearReplicaCoefficientMap_range
    {C α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k 1))
    (param : C → Fin k → ℂ) (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r
        (fun a => MvPolynomial.aeval (param c) (coord a)) ∈
      (multilinearReplicaCoefficientMap coord r).range := by
  let z : multilinearReplicaFeatureIndex k r → ℂ :=
    fun e => ∏ i, param c i ^ (e i : ℕ)
  refine ⟨z, ?_⟩
  ext x
  symm
  change (∏ j, MvPolynomial.aeval (param c) (coord (x j))) = _
  have hp := multilinearCoordinateProduct_mem_degreesLE coord hcoord r x
  have heval := aeval_multilinearPolynomial_eq_sum_coeff
    (⟨multilinearCoordinateProduct coord r x, hp⟩) (param c)
  calc
    (∏ j, MvPolynomial.aeval (param c) (coord (x j))) =
        MvPolynomial.aeval (param c)
          (multilinearCoordinateProduct coord r x) := by
      rw [multilinearCoordinateProduct, map_prod]
    _ = _ := by
      simpa [multilinearReplicaCoefficientMap, z, mul_comm] using heval

theorem finitePureTensorPowerEuclidean_aeval_mem_polynomialReplicaCoefficientMap_range
    {C α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k degree))
    (param : C → Fin k → ℂ) (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r
        (fun a => MvPolynomial.aeval (param c) (coord a)) ∈
      (polynomialReplicaCoefficientMap coord r degree).range := by
  let z : multilinearReplicaFeatureIndex k (r * degree) → ℂ :=
    fun e => ∏ i, param c i ^ (e i : ℕ)
  refine ⟨z, ?_⟩
  ext x
  symm
  change (∏ j, MvPolynomial.aeval (param c) (coord (x j))) = _
  have hp := polynomialCoordinateProduct_mem_degreesLE coord hcoord r x
  have heval := aeval_multilinearPolynomial_eq_sum_coeff
    (⟨multilinearCoordinateProduct coord r x, hp⟩) (param c)
  calc
    (∏ j, MvPolynomial.aeval (param c) (coord (x j))) =
        MvPolynomial.aeval (param c)
          (multilinearCoordinateProduct coord r x) := by
      rw [multilinearCoordinateProduct, map_prod]
    _ = _ := by
      simpa [polynomialReplicaCoefficientMap, z, mul_comm] using heval

/-- Polynomial-image replica Hilbert law. A target family whose coordinates
are multilinear in `k` parameters has occupied order-`r` replica rank at
most `(r+1)^k`, regardless of target cardinality or ambient dimension. -/
theorem finrank_replicaTargetSpan_aeval_multilinear_le
    {C α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k) (multilinearDegreeBound k 1))
    (param : C → Fin k → ℂ) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      (r + 1) ^ k := by
  let L := multilinearReplicaCoefficientMap coord r
  have hle : replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a)) ≤ L.range := by
    apply Submodule.span_le.2
    rintro _ ⟨c, rfl⟩
    exact
      finitePureTensorPowerEuclidean_aeval_mem_multilinearReplicaCoefficientMap_range
        coord hcoord param r c
  calc
    Module.finrank ℂ (replicaTargetSpan r
        (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      Module.finrank ℂ L.range := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (multilinearReplicaFeatureIndex k r → ℂ) :=
      LinearMap.finrank_range_le L
    _ = (r + 1) ^ k := by simp

/-- Degree-`degree` polynomial-image replica Hilbert law. The complete
order-`r` occupied image has rank at most `(r*degree+1)^k`, with no target
cardinality or ambient-dimension factor. -/
theorem finrank_replicaTargetSpan_aeval_degree_le
    {C α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, coord a ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k degree))
    (param : C → Fin k → ℂ) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      (r * degree + 1) ^ k := by
  let L := polynomialReplicaCoefficientMap coord r degree
  have hle : replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a)) ≤ L.range := by
    apply Submodule.span_le.2
    rintro _ ⟨c, rfl⟩
    exact
      finitePureTensorPowerEuclidean_aeval_mem_polynomialReplicaCoefficientMap_range
        coord hcoord param r c
  calc
    Module.finrank ℂ (replicaTargetSpan r
        (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      Module.finrank ℂ L.range := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ
        (multilinearReplicaFeatureIndex k (r * degree) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = (r * degree + 1) ^ k := by simp

namespace TwoQubitCircuit

theorem genericTwoQubitGate_mem_multilinearDegreesLE
    {n s : ℕ} (pos : Fin s → Fin n × Fin n) (a : Fin s)
    (i j : Fin n → Bool) :
    MvPolynomial.map (Rat.castHom ℂ)
      (genericTwoQubitGate s (pos a).1 (pos a).2 a i j) ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) 1) := by
  classical
  unfold genericTwoQubitGate
  split_ifs
  · simp [MvPolynomial.mem_degreesLE, multilinearDegreeBound,
      MvPolynomial.degrees_X, Multiset.le_iff_count]
    intro b
    simp only [Multiset.count_singleton]
    split_ifs <;> omega
  · simp

theorem matrix_mul_mem_multilinearDegreesLE
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k a b : ℕ}
    {A B : Matrix ι ι (MvPolynomial (Fin k) ℂ)}
    (hA : ∀ i j, A i j ∈ MvPolynomial.degreesLE ℂ (Fin k)
      (multilinearDegreeBound k a))
    (hB : ∀ i j, B i j ∈ MvPolynomial.degreesLE ℂ (Fin k)
      (multilinearDegreeBound k b)) :
    ∀ i j, (A * B) i j ∈ MvPolynomial.degreesLE ℂ (Fin k)
      (multilinearDegreeBound k (a + b)) := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro x _
  rw [MvPolynomial.mem_degreesLE]
  apply MvPolynomial.degrees_mul_le.trans
  have hadd := add_le_add
    (MvPolynomial.mem_degreesLE.mp (hA i x))
    (MvPolynomial.mem_degreesLE.mp (hB x j))
  simpa [multilinearDegreeBound, add_nsmul] using hadd

theorem list_prod_matrix_mem_multilinearDegreesLE
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (A : List (Matrix ι ι (MvPolynomial (Fin k) ℂ)))
    (hA : ∀ M ∈ A, ∀ i j, M i j ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k 1)) :
    ∀ i j, A.prod i j ∈ MvPolynomial.degreesLE ℂ (Fin k)
      (multilinearDegreeBound k A.length) := by
  induction A with
  | nil =>
      intro i j
      rw [MvPolynomial.mem_degreesLE]
      simp only [List.prod_nil, Matrix.one_apply]
      split_ifs <;> simp [multilinearDegreeBound]
  | cons M A ih =>
      intro i j
      simpa [List.prod_cons, Nat.succ_eq_add_one, add_comm] using
        matrix_mul_mem_multilinearDegreesLE
          (a := 1) (b := A.length)
          (fun x y => hA M (by simp) x y)
          (ih (by
            intro N hN
            exact hA N (by simp [hN]))) i j

theorem twoQubitCircuitCoords_mem_degreeGateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) (i : Fin n → Bool) :
    MvPolynomial.map (Rat.castHom ℂ) (twoQubitCircuitCoords s pos v i) ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
  classical
  let A : List (Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin (s * 16)) ℚ)) :=
    List.ofFn fun a => genericTwoQubitGate s (pos a).1 (pos a).2 a
  let f : MvPolynomial (Fin (s * 16)) ℚ →+*
      MvPolynomial (Fin (s * 16)) ℂ :=
    MvPolynomial.map (Rat.castHom ℂ)
  have hA : ∀ M ∈ A, ∀ x y,
      f (M x y) ∈
        MvPolynomial.degreesLE ℂ (Fin (s * 16))
          (multilinearDegreeBound (s * 16) 1) := by
    intro M hM x y
    rw [List.mem_ofFn] at hM
    obtain ⟨a, rfl⟩ := hM
    simpa using genericTwoQubitGate_mem_multilinearDegreesLE pos a x y
  let Acomplex := A.map fun M => M.map f
  have hprod : ∀ x y, Acomplex.prod x y ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
    have hlen : Acomplex.length = s := by simp [Acomplex, A]
    simpa [hlen] using
      list_prod_matrix_mem_multilinearDegreesLE Acomplex (by
        intro M hM
        rw [List.mem_map] at hM
        obtain ⟨N, hNA, rfl⟩ := hM
        exact hA N hNA)
  have hprodmap :
      A.prod.map f = Acomplex.prod := by
    have hhom := List.prod_hom A (f.mapMatrix (m := (Fin n → Bool)))
    have hfun :
        ⇑(f.mapMatrix (m := (Fin n → Bool))) =
          fun M : Matrix (Fin n → Bool) (Fin n → Bool)
            (MvPolynomial (Fin (s * 16)) ℚ) => M.map f := by
      funext M
      rfl
    rw [hfun] at hhom
    simpa only [Acomplex] using hhom.symm
  rw [twoQubitCircuitCoords]
  change MvPolynomial.map (Rat.castHom ℂ)
      ((A.prod.mulVec (fun j => MvPolynomial.C (v j))) i) ∈ _
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_mul, MvPolynomial.map_C]
  have hij := congrArg (fun M => M i j) hprodmap
  change f (A.prod i j) = Acomplex.prod i j at hij
  change MvPolynomial.map (Rat.castHom ℂ) (A.prod i j) =
    Acomplex.prod i j at hij
  rw [hij]
  rw [MvPolynomial.mem_degreesLE]
  apply MvPolynomial.degrees_mul_le.trans
  have hC : (MvPolynomial.C ((v j : ℚ) : ℂ) :
      MvPolynomial (Fin (s * 16)) ℂ).degrees ≤ 0 :=
    (MvPolynomial.degrees_C _).le
  simpa using add_le_add (hprod i j) hC

def complexTwoQubitCircuitCoords
    {n : ℕ} (s : ℕ) (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) :
    (Fin n → Bool) → MvPolynomial (Fin (s * 16)) ℂ :=
  fun i => MvPolynomial.map (Rat.castHom ℂ)
    (twoQubitCircuitCoords s pos v i)

theorem complexTwoQubitCircuitCoords_mem_degreeGateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) (i : Fin n → Bool) :
    complexTwoQubitCircuitCoords s pos v i ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) :=
  twoQubitCircuitCoords_mem_degreeGateCount pos v i

theorem exists_param_aeval_complexTwoQubitCircuitCoords
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ)
    (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ k, IsTwoQubitGate (pos k).1 (pos k).2 (G k)) :
    ∃ u : Fin (s * 16) → ℂ, ∀ i,
      MvPolynomial.aeval u (complexTwoQubitCircuitCoords s pos v i) =
        ((List.ofFn G).prod.mulVec
          (fun j => algebraMap ℚ ℂ (v j))) i := by
  obtain ⟨u, hu⟩ := aeval_twoQubitCircuitCoords pos v G hG
  refine ⟨u, fun i => ?_⟩
  rw [complexTwoQubitCircuitCoords, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_map]
  have hcast : Rat.castHom ℂ = algebraMap ℚ ℂ := by
    ext q
    rfl
  rw [hcast]
  simpa [MvPolynomial.aeval_def] using hu i

def twoQubitCircuitBasisVector
    {n : ℕ} (j : Fin n → Bool) : (Fin n → Bool) → ℚ :=
  fun i => if i = j then 1 else 0

/-- Polynomial coordinates of the normalized Choi vector of a generic
two-qubit circuit.  Matrix entries have the same degree as prepared-state
coordinates; normalization is a parameter-independent scalar. -/
def complexTwoQubitCircuitChoiCoords
    {n : ℕ} (s : ℕ) (pos : Fin s → Fin n × Fin n) :
    ((Fin n → Bool) × (Fin n → Bool)) →
      MvPolynomial (Fin (s * 16)) ℂ :=
  fun p =>
    MvPolynomial.C
        ((Real.sqrt (Fintype.card (Fin n → Bool)) : ℂ)⁻¹) *
      complexTwoQubitCircuitCoords s pos
        (twoQubitCircuitBasisVector p.2) p.1

theorem complexTwoQubitCircuitChoiCoords_mem_degreeGateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (p : (Fin n → Bool) × (Fin n → Bool)) :
    complexTwoQubitCircuitChoiCoords s pos p ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
  rw [complexTwoQubitCircuitChoiCoords, MvPolynomial.mem_degreesLE]
  apply MvPolynomial.degrees_mul_le.trans
  have hC :
      (MvPolynomial.C
        ((Real.sqrt (Fintype.card (Fin n → Bool)) : ℂ)⁻¹) :
          MvPolynomial (Fin (s * 16)) ℂ).degrees ≤ 0 :=
    (MvPolynomial.degrees_C _).le
  simpa using add_le_add hC
    (complexTwoQubitCircuitCoords_mem_degreeGateCount
      pos (twoQubitCircuitBasisVector p.2) p.1)

theorem aeval_complexTwoQubitCircuitCoords_of_gateParam
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (u : Fin (s * 16) → ℂ)
    (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hu : ∀ k,
      (genericTwoQubitGate s (pos k).1 (pos k).2 k).map
          (MvPolynomial.aeval u) = G k)
    (v : (Fin n → Bool) → ℚ) (i : Fin n → Bool) :
    MvPolynomial.aeval u (complexTwoQubitCircuitCoords s pos v i) =
      ((List.ofFn G).prod.mulVec
        (fun j => algebraMap ℚ ℂ (v j))) i := by
  have hbase :
      MvPolynomial.aeval u (twoQubitCircuitCoords s pos v i) =
        ((List.ofFn G).prod.mulVec
          (fun j => algebraMap ℚ ℂ (v j))) i := by
    rw [twoQubitCircuitCoords, aeval_circuit' u]
    have hfun :
        ((fun N : Matrix (Fin n → Bool) (Fin n → Bool)
            (MvPolynomial (Fin (s * 16)) ℚ) =>
            Matrix.map N (MvPolynomial.aeval u)) ∘
          fun k => genericTwoQubitGate s (pos k).1 (pos k).2 k) = G :=
      funext hu
    rw [List.map_ofFn, hfun]
    congr 1
    funext j
    rw [MvPolynomial.aeval_C]
  rw [complexTwoQubitCircuitCoords, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_map]
  have hcast : Rat.castHom ℂ = algebraMap ℚ ℂ := by
    ext q
    rfl
  rw [hcast]
  simpa [MvPolynomial.aeval_def] using hbase

theorem exists_param_aeval_complexTwoQubitCircuitChoiCoords
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ k, IsTwoQubitGate (pos k).1 (pos k).2 (G k)) :
    ∃ u : Fin (s * 16) → ℂ, ∀ p,
      MvPolynomial.aeval u (complexTwoQubitCircuitChoiCoords s pos p) =
        (List.ofFn G).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool)) := by
  classical
  obtain ⟨u, hu⟩ := exists_param_of_twoQubitGates pos G hG
  refine ⟨u, fun p => ?_⟩
  rw [complexTwoQubitCircuitChoiCoords, map_mul, MvPolynomial.aeval_C,
    aeval_complexTwoQubitCircuitCoords_of_gateParam pos u G hu]
  simp [twoQubitCircuitBasisVector, Matrix.mulVec, dotProduct, div_eq_mul_inv,
    mul_comm]

/-- Fixed-architecture continuous-circuit Hilbert law. At replica order `r`,
all states prepared by one `s`-gate two-qubit architecture occupy rank at
most `(r*s+1)^(16s)`, independent of qubit Hilbert dimension and number of
gate choices. -/
theorem finrank_replicaTargetSpan_twoQubitCircuit_fixedArchitecture_le
    {C : Type*} {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate (pos k).1 (pos k).2 (G c k))
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c =>
      (List.ofFn (G c)).prod.mulVec
        (fun j => algebraMap ℚ ℂ (v j)))) ≤
      (r * s + 1) ^ (s * 16) := by
  classical
  have hexists : ∀ c, ∃ u : Fin (s * 16) → ℂ, ∀ i,
      MvPolynomial.aeval u (complexTwoQubitCircuitCoords s pos v i) =
        ((List.ofFn (G c)).prod.mulVec
          (fun j => algebraMap ℚ ℂ (v j))) i := by
    intro c
    exact exists_param_aeval_complexTwoQubitCircuitCoords
      pos v (G c) (hG c)
  choose param hparam using hexists
  have htarget : (fun c =>
      (List.ofFn (G c)).prod.mulVec
        (fun j => algebraMap ℚ ℂ (v j))) =
      (fun c i => MvPolynomial.aeval (param c)
        (complexTwoQubitCircuitCoords s pos v i)) := by
    funext c i
    exact (hparam c i).symm
  rw [htarget]
  exact finrank_replicaTargetSpan_aeval_degree_le
    (complexTwoQubitCircuitCoords s pos v)
    (complexTwoQubitCircuitCoords_mem_degreeGateCount pos v)
    param r

end TwoQubitCircuit

def polynomialFamilyReplicaCoefficientMap
    {A α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k : ℕ} (coord : A → α → MvPolynomial (Fin k) ℂ)
    (r degree : ℕ) :
    (A × multilinearReplicaFeatureIndex k (r * degree) → ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun z := WithLp.toLp 2 fun x =>
    ∑ a, ∑ e, z (a, e) *
      MvPolynomial.coeff (multilinearReplicaExponent e)
        (multilinearCoordinateProduct (coord a) r x)
  map_add' z w := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext x
    simp [mul_assoc, Finset.mul_sum]

theorem finitePureTensorPowerEuclidean_aeval_mem_polynomialFamilyReplicaCoefficientMap_range
    {A C α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k degree : ℕ}
    (coord : A → α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a i, coord a i ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k degree))
    (arch : C → A) (param : C → Fin k → ℂ) (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r
        (fun i => MvPolynomial.aeval (param c) (coord (arch c) i)) ∈
      (polynomialFamilyReplicaCoefficientMap coord r degree).range := by
  let z : A × multilinearReplicaFeatureIndex k (r * degree) → ℂ :=
    fun q => if q.1 = arch c then ∏ i, param c i ^ (q.2 i : ℕ) else 0
  refine ⟨z, ?_⟩
  ext x
  symm
  change (∏ j, MvPolynomial.aeval (param c) (coord (arch c) (x j))) = _
  have hp := polynomialCoordinateProduct_mem_degreesLE
    (coord (arch c)) (hcoord (arch c)) r x
  have heval := aeval_multilinearPolynomial_eq_sum_coeff
    (⟨multilinearCoordinateProduct (coord (arch c)) r x, hp⟩) (param c)
  calc
    (∏ j, MvPolynomial.aeval (param c) (coord (arch c) (x j))) =
        MvPolynomial.aeval (param c)
          (multilinearCoordinateProduct (coord (arch c)) r x) := by
      rw [multilinearCoordinateProduct, map_prod]
    _ = _ := by
      rw [heval]
      simp [polynomialFamilyReplicaCoefficientMap, z, mul_comm]

/-- Finite-union polynomial-image Hilbert law. Discrete architectures cost
only their actual count; each architecture's continuous parameter image costs
`(r*degree+1)^k`, independently of parameter cardinality and ambient space. -/
theorem finrank_replicaTargetSpan_aeval_finiteFamily_degree_le
    {A C α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k degree : ℕ}
    (coord : A → α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a i, coord a i ∈
      MvPolynomial.degreesLE ℂ (Fin k)
        (multilinearDegreeBound k degree))
    (arch : C → A) (param : C → Fin k → ℂ) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i))) ≤
      Fintype.card A * (r * degree + 1) ^ k := by
  let L := polynomialFamilyReplicaCoefficientMap coord r degree
  have hle : replicaTargetSpan r
      (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i)) ≤
      L.range := by
    apply Submodule.span_le.2
    rintro _ ⟨c, rfl⟩
    exact
      finitePureTensorPowerEuclidean_aeval_mem_polynomialFamilyReplicaCoefficientMap_range
        coord hcoord arch param r c
  calc
    Module.finrank ℂ (replicaTargetSpan r
        (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i))) ≤
      Module.finrank ℂ L.range := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ
        (A × multilinearReplicaFeatureIndex k (r * degree) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = Fintype.card A * (r * degree + 1) ^ k := by simp

namespace TwoQubitCircuit

abbrev twoQubitCircuitArchitectureIndex (n s : ℕ) :=
  Fin s → Fin n × Fin n

@[simp] theorem card_twoQubitCircuitArchitectureIndex (n s : ℕ) :
    Fintype.card (twoQubitCircuitArchitectureIndex n s) = (n * n) ^ s := by
  simp [twoQubitCircuitArchitectureIndex]

/-- Complete continuous two-qubit circuit-image Hilbert law. All exact
`s`-gate architectures and all continuous two-qubit gate choices together
occupy order-`r` replica rank at most
`(n^(2 : ℕ))^s * (r*s+1)^(16s)`. No net, word count, or gate discretization occurs. -/
theorem finrank_replicaTargetSpan_twoQubitCircuit_complete_le
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (v : (Fin n → Bool) → ℚ)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c =>
      (List.ofFn (G c)).prod.mulVec
        (fun j => algebraMap ℚ ℂ (v j)))) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  classical
  let coord : twoQubitCircuitArchitectureIndex n s →
      (Fin n → Bool) → MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitCoords s a v
  have hcoord : ∀ a i, coord a i ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
    intro a i
    exact complexTwoQubitCircuitCoords_mem_degreeGateCount a v i
  have hexists : ∀ c, ∃ u : Fin (s * 16) → ℂ, ∀ i,
      MvPolynomial.aeval u (coord (pos c) i) =
        ((List.ofFn (G c)).prod.mulVec
          (fun j => algebraMap ℚ ℂ (v j))) i := by
    intro c
    exact exists_param_aeval_complexTwoQubitCircuitCoords
      (pos c) v (G c) (hG c)
  choose param hparam using hexists
  have htarget : (fun c =>
      (List.ofFn (G c)).prod.mulVec
        (fun j => algebraMap ℚ ℂ (v j))) =
      (fun c i => MvPolynomial.aeval (param c) (coord (pos c) i)) := by
    funext c i
    exact (hparam c i).symm
  rw [htarget]
  simpa using finrank_replicaTargetSpan_aeval_finiteFamily_degree_le
    coord hcoord pos param r

/-- Complete continuous two-qubit Choi-image Hilbert law.  The normalized
Choi vectors of all exact `s`-gate architectures and all continuous gate
choices occupy order-`r` replica rank at most
`(n^(2 : ℕ))^s * (r*s+1)^(16s)`.  Continuous gate cardinality and Hilbert-space
dimension do not enter. -/
theorem finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_le
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c
        (p : (Fin n → Bool) × (Fin n → Bool)) =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool)))) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  classical
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  have hcoord : ∀ a p, coord a p ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
    intro a p
    exact complexTwoQubitCircuitChoiCoords_mem_degreeGateCount a p
  have hexists : ∀ c, ∃ u : Fin (s * 16) → ℂ, ∀ p,
      MvPolynomial.aeval u (coord (pos c) p) =
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool)) := by
    intro c
    exact exists_param_aeval_complexTwoQubitCircuitChoiCoords
      (pos c) (G c) (hG c)
  choose param hparam using hexists
  have htarget : (fun c p =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) =
      (fun c p => MvPolynomial.aeval (param c)
        (coord (pos c) p)) := by
    funext c p
    exact (hparam c p).symm
  rw [htarget]
  simpa using finrank_replicaTargetSpan_aeval_finiteFamily_degree_le
    coord hcoord pos param r

end TwoQubitCircuit

end

end GaloisForLFunctions.HTGeometry
