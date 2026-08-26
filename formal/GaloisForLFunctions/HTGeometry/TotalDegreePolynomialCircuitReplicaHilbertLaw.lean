import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Sum

/-!
# Total-degree Hilbert law for replicated polynomial circuit images

Coordinatewise degree treats admissible monomials as a box and overcounts a
degree-`N` polynomial by `(N+1)^k`.  Total degree identifies the exact simplex
of exponent vectors.  This module proves that a degree-`d` polynomial image in
`k` parameters has order-`r` replica span of rank at most

`Nat.choose (r * d + k) k`.

For every exact-`s` two-qubit architecture and every continuous choice of gate
entries, the complete normalized Choi target class therefore has replica rank
at most

`(n*n)^s * Nat.choose (r*s + 16*s) (16*s)`.

The result covers the entire continuous circuit image directly: no net,
selector, target cardinality, or discretization appears.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev totalDegreeReplicaFeatureIndex (k N : ℕ) :=
  Σ m : Fin (N + 1), Sym (Fin k) (m : ℕ)

@[simp] theorem card_totalDegreeReplicaFeatureIndex (k N : ℕ) :
    Fintype.card (totalDegreeReplicaFeatureIndex k N) =
      (N + k).choose k := by
  rw [Fintype.card_sigma]
  simp_rw [Sym.card_sym_eq_multichoose]
  rw [Fin.sum_univ_eq_sum_range]
  simpa using Nat.sum_range_multichoose N k

def totalDegreeReplicaExponent {k N : ℕ}
    (e : totalDegreeReplicaFeatureIndex k N) : Fin k →₀ ℕ :=
  Multiset.toFinsupp (e.2 : Multiset (Fin k))

theorem totalDegreeReplicaExponent_injective {k N : ℕ} :
    Function.Injective
      (totalDegreeReplicaExponent :
        totalDegreeReplicaFeatureIndex k N → Fin k →₀ ℕ) := by
  rintro ⟨m, a⟩ ⟨n, b⟩ hab
  have hmult : (a : Multiset (Fin k)) = (b : Multiset (Fin k)) := by
    have h := congrArg Finsupp.toMultiset hab
    simpa [totalDegreeReplicaExponent] using h
  have hfirst : m = n := by
    apply Fin.ext
    exact a.prop.symm.trans ((congrArg Multiset.card hmult).trans b.prop)
  subst n
  exact Sigma.ext rfl (heq_of_eq (Sym.ext hmult))

def totalDegreeReplicaFeatureOfExponent {k N : ℕ}
    (d : Fin k →₀ ℕ) (hd : d.sum (fun _ e => e) ≤ N) :
    totalDegreeReplicaFeatureIndex k N :=
  ⟨⟨d.sum (fun _ e => e), Nat.lt_succ_iff.mpr hd⟩,
    ⟨d.toMultiset, Finsupp.card_toMultiset d⟩⟩

@[simp] theorem totalDegreeReplicaExponent_featureOfExponent
    {k N : ℕ} (d : Fin k →₀ ℕ) (hd : d.sum (fun _ e => e) ≤ N) :
    totalDegreeReplicaExponent (totalDegreeReplicaFeatureOfExponent d hd) = d := by
  simp [totalDegreeReplicaExponent, totalDegreeReplicaFeatureOfExponent]

theorem totalDegreePolynomial_eq_sum_coeff
    {k N : ℕ} (p : MvPolynomial (Fin k) ℂ)
    (hp : p.totalDegree ≤ N) :
    p = ∑ e : totalDegreeReplicaFeatureIndex k N,
      MvPolynomial.monomial (totalDegreeReplicaExponent e)
        (MvPolynomial.coeff (totalDegreeReplicaExponent e) p) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ p.support
  · have hsum : d.sum (fun _ e => e) ≤ N :=
      (MvPolynomial.le_totalDegree hd).trans hp
    let e := totalDegreeReplicaFeatureOfExponent d hsum
    have hexp : totalDegreeReplicaExponent e = d :=
      totalDegreeReplicaExponent_featureOfExponent d hsum
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp [hexp]
    · intro b _ hbe
      have hbne : totalDegreeReplicaExponent b ≠ d := by
        intro hbd
        apply hbe
        apply totalDegreeReplicaExponent_injective
        exact hbd.trans hexp.symm
      simp [hbne]
    · simp
  · have hpzero : MvPolynomial.coeff d p = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hd
    rw [hpzero]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    symm
    apply Finset.sum_eq_zero
    intro e _
    by_cases h : totalDegreeReplicaExponent e = d
    · simp [h, hpzero]
    · simp [h]

theorem aeval_totalDegreePolynomial_eq_sum_coeff
    {k N : ℕ} (p : MvPolynomial (Fin k) ℂ)
    (hp : p.totalDegree ≤ N) (u : Fin k → ℂ) :
    MvPolynomial.aeval u p =
      ∑ e : totalDegreeReplicaFeatureIndex k N,
        MvPolynomial.coeff (totalDegreeReplicaExponent e) p *
          ∏ i, u i ^ totalDegreeReplicaExponent e i := by
  conv_lhs => rw [totalDegreePolynomial_eq_sum_coeff p hp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

theorem polynomialCoordinateProduct_totalDegree_le
    {α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, (coord a).totalDegree ≤ degree)
    (r : ℕ) (x : Fin r → α) :
    (multilinearCoordinateProduct coord r x).totalDegree ≤ r * degree := by
  classical
  calc
    (multilinearCoordinateProduct coord r x).totalDegree ≤
        ∑ j ∈ (Finset.univ : Finset (Fin r)),
          (coord (x j)).totalDegree := by
      simpa [multilinearCoordinateProduct] using
        MvPolynomial.totalDegree_finsetProd
          (Finset.univ : Finset (Fin r)) (fun j => coord (x j))
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin r)), degree := by
      apply Finset.sum_le_sum
      intro j _
      exact hcoord (x j)
    _ = r * degree := by simp

def totalDegreePolynomialReplicaCoefficientMap
    {α : Type*} [Fintype α] {k : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ) (r degree : ℕ) :
    (totalDegreeReplicaFeatureIndex k (r * degree) → ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun z := WithLp.toLp 2 fun x =>
    ∑ e, z e * MvPolynomial.coeff (totalDegreeReplicaExponent e)
      (multilinearCoordinateProduct coord r x)
  map_add' z w := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext x
    simp [mul_assoc, Finset.mul_sum]

theorem finitePureTensorPowerEuclidean_aeval_mem_totalDegreePolynomialReplicaCoefficientMap_range
    {C α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, (coord a).totalDegree ≤ degree)
    (param : C → Fin k → ℂ) (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r
        (fun a => MvPolynomial.aeval (param c) (coord a)) ∈
      (totalDegreePolynomialReplicaCoefficientMap coord r degree).range := by
  let z : totalDegreeReplicaFeatureIndex k (r * degree) → ℂ :=
    fun e => ∏ i, param c i ^ totalDegreeReplicaExponent e i
  refine ⟨z, ?_⟩
  ext x
  symm
  change (∏ j, MvPolynomial.aeval (param c) (coord (x j))) = _
  have hp := polynomialCoordinateProduct_totalDegree_le coord hcoord r x
  have heval := aeval_totalDegreePolynomial_eq_sum_coeff
    (multilinearCoordinateProduct coord r x) hp (param c)
  calc
    (∏ j, MvPolynomial.aeval (param c) (coord (x j))) =
        MvPolynomial.aeval (param c)
          (multilinearCoordinateProduct coord r x) := by
      rw [multilinearCoordinateProduct, map_prod]
    _ = _ := by
      simpa [totalDegreePolynomialReplicaCoefficientMap, z, mul_comm] using heval

/-- Exact total-degree polynomial-image replica Hilbert law. -/
theorem finrank_replicaTargetSpan_aeval_totalDegree_le
    {C α : Type*} [Fintype α] {k degree : ℕ}
    (coord : α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a, (coord a).totalDegree ≤ degree)
    (param : C → Fin k → ℂ) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      (r * degree + k).choose k := by
  let L := totalDegreePolynomialReplicaCoefficientMap coord r degree
  have hle : replicaTargetSpan r
      (fun c a => MvPolynomial.aeval (param c) (coord a)) ≤ L.range := by
    apply Submodule.span_le.2
    rintro _ ⟨c, rfl⟩
    exact
      finitePureTensorPowerEuclidean_aeval_mem_totalDegreePolynomialReplicaCoefficientMap_range
        coord hcoord param r c
  calc
    Module.finrank ℂ (replicaTargetSpan r
        (fun c a => MvPolynomial.aeval (param c) (coord a))) ≤
      Module.finrank ℂ L.range := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ
        (totalDegreeReplicaFeatureIndex k (r * degree) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = Fintype.card (totalDegreeReplicaFeatureIndex k (r * degree)) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = (r * degree + k).choose k :=
      card_totalDegreeReplicaFeatureIndex k (r * degree)

def totalDegreePolynomialFamilyReplicaCoefficientMap
    {A α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k : ℕ} (coord : A → α → MvPolynomial (Fin k) ℂ)
    (r degree : ℕ) :
    (A × totalDegreeReplicaFeatureIndex k (r * degree) → ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun z := WithLp.toLp 2 fun x =>
    ∑ a, ∑ e, z (a, e) *
      MvPolynomial.coeff (totalDegreeReplicaExponent e)
        (multilinearCoordinateProduct (coord a) r x)
  map_add' z w := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext x
    simp [mul_assoc, Finset.mul_sum]

theorem finitePureTensorPowerEuclidean_aeval_mem_totalDegreePolynomialFamilyReplicaCoefficientMap_range
    {A C α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k degree : ℕ}
    (coord : A → α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a i, (coord a i).totalDegree ≤ degree)
    (arch : C → A) (param : C → Fin k → ℂ) (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r
        (fun i => MvPolynomial.aeval (param c) (coord (arch c) i)) ∈
      (totalDegreePolynomialFamilyReplicaCoefficientMap coord r degree).range := by
  let z : A × totalDegreeReplicaFeatureIndex k (r * degree) → ℂ :=
    fun q => if q.1 = arch c then
      ∏ i, param c i ^ totalDegreeReplicaExponent q.2 i else 0
  refine ⟨z, ?_⟩
  ext x
  symm
  change (∏ j, MvPolynomial.aeval (param c) (coord (arch c) (x j))) = _
  have hp := polynomialCoordinateProduct_totalDegree_le
    (coord (arch c)) (hcoord (arch c)) r x
  have heval := aeval_totalDegreePolynomial_eq_sum_coeff
    (multilinearCoordinateProduct (coord (arch c)) r x) hp (param c)
  calc
    (∏ j, MvPolynomial.aeval (param c) (coord (arch c) (x j))) =
        MvPolynomial.aeval (param c)
          (multilinearCoordinateProduct (coord (arch c)) r x) := by
      rw [multilinearCoordinateProduct, map_prod]
    _ = _ := by
      rw [heval]
      simp [totalDegreePolynomialFamilyReplicaCoefficientMap, z, mul_comm]

/-- Finite-union exact total-degree replica Hilbert law. -/
theorem finrank_replicaTargetSpan_aeval_finiteFamily_totalDegree_le
    {A C α : Type*} [Fintype A] [DecidableEq A] [Fintype α]
    {k degree : ℕ}
    (coord : A → α → MvPolynomial (Fin k) ℂ)
    (hcoord : ∀ a i, (coord a i).totalDegree ≤ degree)
    (arch : C → A) (param : C → Fin k → ℂ) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i))) ≤
      Fintype.card A * (r * degree + k).choose k := by
  let L := totalDegreePolynomialFamilyReplicaCoefficientMap coord r degree
  have hle : replicaTargetSpan r
      (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i)) ≤
      L.range := by
    apply Submodule.span_le.2
    rintro _ ⟨c, rfl⟩
    exact
      finitePureTensorPowerEuclidean_aeval_mem_totalDegreePolynomialFamilyReplicaCoefficientMap_range
        coord hcoord arch param r c
  calc
    Module.finrank ℂ (replicaTargetSpan r
        (fun c i => MvPolynomial.aeval (param c) (coord (arch c) i))) ≤
      Module.finrank ℂ L.range := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ
        (A × totalDegreeReplicaFeatureIndex k (r * degree) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = Fintype.card (A × totalDegreeReplicaFeatureIndex k (r * degree)) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = Fintype.card A * (r * degree + k).choose k := by
      rw [Fintype.card_prod, card_totalDegreeReplicaFeatureIndex]

theorem totalDegree_map_le
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)

namespace TwoQubitCircuit

theorem genericTwoQubitGate_totalDegree_le_one
    {n s : ℕ} (pos : Fin s → Fin n × Fin n) (a : Fin s)
    (i j : Fin n → Bool) :
    (genericTwoQubitGate s (pos a).1 (pos a).2 a i j).totalDegree ≤ 1 := by
  classical
  unfold genericTwoQubitGate
  split_ifs <;> simp

theorem matrix_mul_totalDegree_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommSemiring R]
    {σ : Type*} {a b : ℕ}
    {A B : Matrix ι ι (MvPolynomial σ R)}
    (hA : ∀ i j, (A i j).totalDegree ≤ a)
    (hB : ∀ i j, (B i j).totalDegree ≤ b) :
    ∀ i j, ((A * B) i j).totalDegree ≤ a + b := by
  classical
  intro i j
  rw [Matrix.mul_apply]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro x _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (add_le_add (hA i x) (hB x j))

theorem list_prod_matrix_totalDegree_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommSemiring R]
    {σ : Type*}
    (A : List (Matrix ι ι (MvPolynomial σ R)))
    (hA : ∀ M ∈ A, ∀ i j, (M i j).totalDegree ≤ 1) :
    ∀ i j, (A.prod i j).totalDegree ≤ A.length := by
  induction A with
  | nil =>
      intro i j
      simp only [List.prod_nil, Matrix.one_apply, List.length_nil]
      split_ifs <;> simp
  | cons M A ih =>
      intro i j
      simpa [List.prod_cons, Nat.succ_eq_add_one, add_comm] using
        matrix_mul_totalDegree_le
          (a := 1) (b := A.length)
          (fun x y => hA M (by simp) x y)
          (ih (by
            intro N hN
            exact hA N (by simp [hN]))) i j

theorem twoQubitCircuitCoords_totalDegree_le_gateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) (i : Fin n → Bool) :
    (twoQubitCircuitCoords s pos v i).totalDegree ≤ s := by
  classical
  let A : List (Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin (s * 16)) ℚ)) :=
    List.ofFn fun a => genericTwoQubitGate s (pos a).1 (pos a).2 a
  have hA : ∀ M ∈ A, ∀ x y, (M x y).totalDegree ≤ 1 := by
    intro M hM x y
    rw [List.mem_ofFn] at hM
    obtain ⟨a, rfl⟩ := hM
    exact genericTwoQubitGate_totalDegree_le_one pos a x y
  have hprod : ∀ x y, (A.prod x y).totalDegree ≤ s := by
    have hlen : A.length = s := by simp [A]
    simpa [hlen] using list_prod_matrix_totalDegree_le A hA
  rw [twoQubitCircuitCoords]
  change ((A.prod.mulVec (fun j => MvPolynomial.C (v j))) i).totalDegree ≤ s
  simp only [Matrix.mulVec, dotProduct]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro j _
  have hC : (MvPolynomial.C (v j) :
      MvPolynomial (Fin (s * 16)) ℚ).totalDegree ≤ 0 := by simp
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa using add_le_add (hprod i j) hC)

theorem complexTwoQubitCircuitCoords_totalDegree_le_gateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) (i : Fin n → Bool) :
    (complexTwoQubitCircuitCoords s pos v i).totalDegree ≤ s := by
  exact (totalDegree_map_le (Rat.castHom ℂ)
    (twoQubitCircuitCoords s pos v i)).trans
      (twoQubitCircuitCoords_totalDegree_le_gateCount pos v i)

theorem complexTwoQubitCircuitChoiCoords_totalDegree_le_gateCount
    {n s : ℕ} (pos : Fin s → Fin n × Fin n)
    (p : (Fin n → Bool) × (Fin n → Bool)) :
    (complexTwoQubitCircuitChoiCoords s pos p).totalDegree ≤ s := by
  rw [complexTwoQubitCircuitChoiCoords]
  have hC : (MvPolynomial.C
      ((Real.sqrt (Fintype.card (Fin n → Bool)) : ℂ)⁻¹) :
      MvPolynomial (Fin (s * 16)) ℂ).totalDegree ≤ 0 := by simp
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa using add_le_add hC
      (complexTwoQubitCircuitCoords_totalDegree_le_gateCount
        pos (twoQubitCircuitBasisVector p.2) p.1))

/-- Complete exact-`s` Choi circuit class has simplex, rather than box,
replica Hilbert dimension. -/
theorem finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_totalDegree_le
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c
        (p : (Fin n → Bool) × (Fin n → Bool)) =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool)))) ≤
      (n * n) ^ s * (r * s + s * 16).choose (s * 16) := by
  classical
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  have hcoord : ∀ a p, (coord a p).totalDegree ≤ s := by
    intro a p
    exact complexTwoQubitCircuitChoiCoords_totalDegree_le_gateCount a p
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
  simpa using finrank_replicaTargetSpan_aeval_finiteFamily_totalDegree_le
    coord hcoord pos param r

/-- Explicit total-degree feature carrier for all exact-`s` two-qubit Choi
circuits at replica order `r`. -/
noncomputable def twoQubitCircuitChoiTotalDegreeReplicaCarrier
    (n s r : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ
      (Fin r → ((Fin n → Bool) × (Fin n → Bool)))) :=
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  (totalDegreePolynomialFamilyReplicaCoefficientMap coord r s).range

theorem finrank_twoQubitCircuitChoiTotalDegreeReplicaCarrier_le
    (n s r : ℕ) :
    Module.finrank ℂ
        (twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r) ≤
      (n * n) ^ s * (r * s + s * 16).choose (s * 16) := by
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  let L := totalDegreePolynomialFamilyReplicaCoefficientMap coord r s
  change Module.finrank ℂ L.range ≤ _
  calc
    Module.finrank ℂ L.range ≤ Module.finrank ℂ
        (twoQubitCircuitArchitectureIndex n s ×
          totalDegreeReplicaFeatureIndex (s * 16) (r * s) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = Fintype.card (twoQubitCircuitArchitectureIndex n s ×
          totalDegreeReplicaFeatureIndex (s * 16) (r * s)) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = (n * n) ^ s * (r * s + s * 16).choose (s * 16) := by
      rw [Fintype.card_prod, card_twoQubitCircuitArchitectureIndex,
        card_totalDegreeReplicaFeatureIndex]

theorem finitePureTensorPowerEuclidean_twoQubitCircuitChoi_mem_totalDegreeCarrier
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r (fun p =>
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool))) ∈
      twoQubitCircuitChoiTotalDegreeReplicaCarrier n s r := by
  classical
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  have hcoord : ∀ a p, (coord a p).totalDegree ≤ s := by
    intro a p
    exact complexTwoQubitCircuitChoiCoords_totalDegree_le_gateCount a p
  have hexists : ∀ c, ∃ u : Fin (s * 16) → ℂ, ∀ p,
      MvPolynomial.aeval u (coord (pos c) p) =
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool)) := by
    intro c
    exact exists_param_aeval_complexTwoQubitCircuitChoiCoords
      (pos c) (G c) (hG c)
  choose param hparam using hexists
  have hbase :=
    finitePureTensorPowerEuclidean_aeval_mem_totalDegreePolynomialFamilyReplicaCoefficientMap_range
      coord hcoord pos param r c
  have htarget : (fun p =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) =
      (fun p => MvPolynomial.aeval (param c) (coord (pos c) p)) := by
    funext p
    exact (hparam c p).symm
  rw [htarget]
  simpa only [twoQubitCircuitChoiTotalDegreeReplicaCarrier, coord] using hbase

end TwoQubitCircuit

end

end GaloisForLFunctions.HTGeometry
