import Mathlib
import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology
import GaloisForLFunctions.HTGeometry.PhysicalCharacteristicIncidence

/-!
# Simple-horizon rank-to-depth transmutation

At a simple common-normal horizon the underived constraint ideal saturates after one constraint,
while the observer's Smith staircase grows: the sheet-evaluation matrix factors as a Vandermonde of
the leading units times `diag(1, a, …, a^{N-1})`.  The orientation order is therefore `binom N 2`
and the discriminant order twice that, and adding one sheet appends a bar of length `N`.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix

/-! ## The underived ideal saturates -/

section Saturation

variable {R : Type*} [CommRing R] {N : ℕ}

/-- **Cards `(1)`, `(6)`.**  Constraints with a common uniformizer and unit leading coefficients
already generate the ideal of the uniformizer. -/
theorem span_constraints_eq (a : R) (u : Fin N → Rˣ) (hN : 0 < N) :
    Ideal.span (Set.range fun i : Fin N => a * (u i : R)) = Ideal.span {a} := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    set i₀ : Fin N := ⟨0, hN⟩ with hi₀
    have hmem : a * (u i₀ : R) ∈ Ideal.span (Set.range fun i : Fin N => a * (u i : R)) :=
      Ideal.subset_span ⟨i₀, rfl⟩
    have heq : (((u i₀)⁻¹ : Rˣ) : R) * (a * (u i₀ : R)) = a := by
      rw [← mul_assoc, mul_comm (((u i₀)⁻¹ : Rˣ) : R) a, mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, mul_one]
    have hgoal := Ideal.mul_mem_left
      (Ideal.span (Set.range fun i : Fin N => a * (u i : R))) (((u i₀)⁻¹ : Rˣ) : R) hmem
    rwa [heq] at hgoal

end Saturation

/-! ## The type-`A` root module -/

section RootModule

open GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {N : ℕ}

/-- **Cards `(2)`, `(9)`, `(10)` boxed.**  The corpus unit-weighted augmentation is the card's
constraint covector, its kernel is the excess module, and that kernel is free on the non-pivot
coordinates — the type-`A_{N-1}` root module.  Nothing here is rebuilt: the augmentation, its
section, the split `R^N = R·v ⊕ E` and the explicit basis all come from
`HTGeometry.CommonFactorKoszulHomology`. -/
theorem finrank_unitWeightedRelations [Nontrivial R] (u : Fin N → Rˣ) (i₀ : Fin N) :
    Module.finrank R (unitWeightedRelations u) = N - 1 := by
  classical
  rw [Module.finrank_eq_card_basis (unitWeightedRelationsBasis u i₀), card_unitWeightedAway]
  simp

/-- **Card `(8)`.**  The derived excess in degree `j` has rank `binom (N-1) j`. -/
theorem finrank_exteriorPower_unitWeightedRelations [IsDomain R]
    (u : Fin N → Rˣ) (i₀ : Fin N) (j : ℕ) :
    Module.finrank R (⋀[R]^j (unitWeightedRelations u)) = (N - 1).choose j := by
  classical
  haveI : Module.Free R (unitWeightedRelations u) :=
    Module.Free.of_basis (unitWeightedRelationsBasis u i₀)
  haveI : Module.Finite R (unitWeightedRelations u) :=
    Module.Finite.of_basis (unitWeightedRelationsBasis u i₀)
  rw [exteriorPower.finrank_eq, finrank_unitWeightedRelations u i₀]

end RootModule

/-! ## Derived excess: the Koszul homology of the common-factor sequence -/

section KoszulExcess

open GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- **Cards `(7)`, `(8)`.**  In the normalized frame the constraint sequence is row-reduced, and
the corpus computes its degree-`k` Koszul homology as a product of `binom (N-1) k` copies of the
Cartier quotient `R/(a)`.  The homology is therefore the degree-`k` piece of the exterior algebra
of the type-`A_{N-1}` root module, tensored with the residue ring — the card's `k ⊗ ⋀^• E`.

Nothing is rebuilt: the row-reduced Koszul complex, its cycles, its reduction and the surviving
basis all come from `HTGeometry.PhysicalCharacteristicIncidence`. -/
theorem card_koszul_excess (r k : ℕ) :
    Nat.card (physicalKoszulSurvivingBasis r k) = Nat.choose r k :=
  card_physicalKoszulSurvivingBasis r k

/-- **Cards `(7)`, `(8)`.**  The degree-`k` derived excess of the common-factor sequence. -/
noncomputable def koszulExcessEquiv (r k : ℕ) (a : R) :
    (rowReducedPhysicalKoszulCycleSubmodule (R := R) r k ⧸
        LinearMap.ker (rowReducedPhysicalKoszulReduction r k a)) ≃ₗ[R]
      (physicalKoszulSurvivingBasis r k → R ⧸ Ideal.span ({a} : Set R)) :=
  rowReducedPhysicalKoszulHomologyEquiv r k a

end KoszulExcess

/-! ## The observer Smith staircase -/

section Staircase

variable {R : Type*} [CommRing R] {N : ℕ}

/-- **Cards `(5)`, `(14)`.**  The sheet-evaluation observer in the monomial basis. -/
def sheetObserver (a : R) (u : Fin N → Rˣ) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => (a * (u i : R)) ^ (j : ℕ)

/-- **Card `(14)`.**  The observer factors as a Vandermonde of the leading units times the depth
staircase. -/
theorem sheetObserver_eq (a : R) (u : Fin N → Rˣ) :
    sheetObserver a u
      = (Matrix.vandermonde fun i => ((u i : R)))
        * Matrix.diagonal fun j : Fin N => a ^ (j : ℕ) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp [sheetObserver, Matrix.vandermonde, mul_pow, mul_comm]

/-- The staircase exponent is the number of positive type-`A` roots. -/
theorem sum_val_eq_choose (N : ℕ) : ∑ j : Fin N, (j : ℕ) = N.choose 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hc : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    rw [ih, hc, Nat.choose_one_right]
    omega

/-- **Cards `(15)`, `(16)`.**  The orientation order: the determinant is the Vandermonde of the
leading units times `a^{binom N 2}`. -/
theorem det_sheetObserver (a : R) (u : Fin N → Rˣ) :
    (sheetObserver a u).det
      = (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R))) * a ^ N.choose 2 := by
  rw [sheetObserver_eq, Matrix.det_mul, Matrix.det_vandermonde, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, sum_val_eq_choose]

end Staircase

/-! ## The observer cokernel is the persistence staircase -/

section Cokernel

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The range of a diagonal map is the product of the principal ideals of its entries. -/
theorem range_diagonal_mulVecLin' {n : Type*} [Fintype n] [DecidableEq n] (d : n → R) :
    LinearMap.range (Matrix.diagonal d).mulVecLin
      = Submodule.pi Set.univ fun j : n => Ideal.span {d j} := by
  classical
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Ideal.mem_span_singleton, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨x, rfl⟩ j
    exact ⟨x j, by rw [Matrix.mulVec_diagonal]⟩
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    funext j
    rw [Matrix.mulVec_diagonal, hc j]

/-- The range of the depth staircase is the product of the principal ideals. -/
theorem range_diagonal_mulVecLin (a : R) :
    LinearMap.range (Matrix.diagonal (fun j : Fin N => a ^ (j : ℕ))).mulVecLin
      = Submodule.pi Set.univ fun j : Fin N => Ideal.span {a ^ (j : ℕ)} :=
  range_diagonal_mulVecLin' _

/-- **Reusable.**  A matrix carried to a diagonal one by unimodular factors has the corresponding
product cokernel.  Both the observer staircase below and the tensor-square splitting of the
Gorenstein card are instances. -/
theorem nonempty_coker_equiv_pi_of_smith {n : Type*} [Fintype n] [DecidableEq n]
    {M D P Q : Matrix n n R} (hP : IsUnit P.det) (hQ : IsUnit Q.det) (d : n → R)
    (hD : D = Matrix.diagonal d) (h : P * M * Q = D) :
    Nonempty (((n → R) ⧸ LinearMap.range M.mulVecLin) ≃ₗ[R] ∀ i, (R ⧸ Ideal.span {d i})) := by
  classical
  haveI hPi : Invertible P := Matrix.invertibleOfIsUnitDet P hP
  haveI hQi : Invertible Q := Matrix.invertibleOfIsUnitDet Q hQ
  set eP : (n → R) ≃ₗ[R] (n → R) := Matrix.toLinearEquiv' P hPi with heP
  have hePl : (eP : (n → R) →ₗ[R] (n → R)) = P.mulVecLin := rfl
  have hMPQ : P * M = D * Q⁻¹ := by
    rw [← h, Matrix.mul_inv_cancel_right_of_invertible]
  have hQsurj : Function.Surjective (Q⁻¹ : Matrix n n R).mulVecLin := by
    intro x
    refine ⟨Q.mulVecLin x, ?_⟩
    simp
  have hmap : Submodule.map (eP : (n → R) →ₗ[R] (n → R)) (LinearMap.range M.mulVecLin)
      = LinearMap.range D.mulVecLin := by
    rw [hePl, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, hMPQ, Matrix.mulVecLin_mul,
      LinearMap.range_comp, LinearMap.range_eq_top.2 hQsurj, Submodule.map_top]
  have e1 : ((n → R) ⧸ LinearMap.range M.mulVecLin)
      ≃ₗ[R] ((n → R) ⧸ LinearMap.range D.mulVecLin) :=
    Submodule.Quotient.equiv _ _ eP hmap
  have e2 : ((n → R) ⧸ LinearMap.range D.mulVecLin)
      ≃ₗ[R] ∀ i, (R ⧸ Ideal.span {d i}) := by
    rw [hD, range_diagonal_mulVecLin']
    exact Submodule.quotientPi _
  exact ⟨e1.trans e2⟩

/-- **Cards `(11)`, `(12)` boxed.**  When the Vandermonde factor of the leading units is
invertible, the observer cokernel is the persistence staircase `⊕_j R/(a^j)`. -/
noncomputable def cokerSheetObserverEquiv (a : R) (u : Fin N → Rˣ)
    (hV : IsUnit ((Matrix.vandermonde fun i => (u i : R)).det)) :
    ((Fin N → R) ⧸ LinearMap.range (sheetObserver a u).mulVecLin)
      ≃ₗ[R] ∀ j : Fin N, (R ⧸ Ideal.span {a ^ (j : ℕ)}) := by
  classical
  set V : Matrix (Fin N) (Fin N) R := Matrix.vandermonde fun i => (u i : R) with hVdef
  set D : Matrix (Fin N) (Fin N) R := Matrix.diagonal fun j : Fin N => a ^ (j : ℕ) with hDdef
  haveI : Invertible V := (Matrix.isUnit_iff_isUnit_det V).2 hV |>.invertible
  set eV : (Fin N → R) ≃ₗ[R] (Fin N → R) := Matrix.toLinearEquiv' V inferInstance with heV
  have hrange : LinearMap.range (sheetObserver a u).mulVecLin
      = Submodule.map (eV : (Fin N → R) →ₗ[R] (Fin N → R)) (LinearMap.range D.mulVecLin) := by
    rw [sheetObserver_eq, ← hVdef, ← hDdef, Matrix.mulVecLin_mul, LinearMap.range_comp]
    rfl
  have hmap' : Submodule.map ((eV.symm : (Fin N → R) ≃ₗ[R] (Fin N → R)) :
      (Fin N → R) →ₗ[R] (Fin N → R)) (LinearMap.range (sheetObserver a u).mulVecLin)
      = LinearMap.range D.mulVecLin := by
    rw [hrange, ← Submodule.map_comp]
    simp
  have e1 : ((Fin N → R) ⧸ LinearMap.range (sheetObserver a u).mulVecLin)
      ≃ₗ[R] ((Fin N → R) ⧸ LinearMap.range D.mulVecLin) :=
    Submodule.Quotient.equiv _ _ eV.symm hmap'
  have e2 : ((Fin N → R) ⧸ LinearMap.range D.mulVecLin)
      ≃ₗ[R] ∀ j : Fin N, (R ⧸ Ideal.span {a ^ (j : ℕ)}) := by
    rw [hDdef, range_diagonal_mulVecLin]
    exact Submodule.quotientPi _
  exact e1.trans e2

end Cokernel

/-! ## Discriminant order and the successor law -/

section Discriminant

variable {R : Type*} [CommRing R] {N : ℕ}

/-- **Card `(16)`.**  Each pairwise difference of constraints carries exactly one uniformizer. -/
theorem constraint_sub (a : R) (u : Fin N → Rˣ) (i j : Fin N) :
    a * (u j : R) - a * (u i : R) = a * ((u j : R) - (u i : R)) := by ring

/-- **Card `(16)`.**  The discriminant of the sheet polynomial has uniformizer order twice the
orientation order. -/
theorem disc_constraints (a : R) (u : Fin N → Rˣ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (a * (u j : R) - a * (u i : R)) ^ 2)
      = a ^ (2 * ∑ i : Fin N, (Finset.Ioi i).card)
        * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)) ^ 2 := by
  have hterm : ∀ i j : Fin N, (a * (u j : R) - a * (u i : R)) ^ 2
      = a ^ 2 * ((u j : R) - (u i : R)) ^ 2 := fun i j => by rw [constraint_sub]; ring
  calc (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (a * (u j : R) - a * (u i : R)) ^ 2)
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (a ^ 2 * ((u j : R) - (u i : R)) ^ 2) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hterm i j
    _ = ∏ i : Fin N, ((a ^ 2) ^ (Finset.Ioi i).card
          * ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)) ^ 2) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = (∏ i : Fin N, (a ^ 2) ^ (Finset.Ioi i).card)
          * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)) ^ 2 :=
        Finset.prod_mul_distrib
    _ = a ^ (2 * ∑ i : Fin N, (Finset.Ioi i).card)
          * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)) ^ 2 := by
        congr 1
        rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]

/-- The number of ordered pairs `i < j` in `Fin N` is `binom N 2`. -/
theorem sum_card_Ioi_eq_choose (N : ℕ) : ∑ i : Fin N, (Finset.Ioi i).card = N.choose 2 := by
  have h2 : ∑ i : Fin N, (Finset.Ioi i).card = ∑ i : Fin N, (N - 1 - (i : ℕ)) :=
    Finset.sum_congr rfl fun i _ => Fin.card_Ioi i
  have h3 : ∑ i : Fin N, (N - 1 - (i : ℕ)) = ∑ j ∈ Finset.range N, (N - 1 - j) :=
    Fin.sum_univ_eq_sum_range (fun k => N - 1 - k) N
  have h4 : ∑ j ∈ Finset.range N, (N - 1 - j) = ∑ j ∈ Finset.range N, j :=
    Finset.sum_range_reflect (fun k => k) N
  have h5 : ∑ j ∈ Finset.range N, j = ∑ i : Fin N, (i : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun k => k) N).symm
  rw [h2, h3, h4, h5]
  exact sum_val_eq_choose N

/-- A unit multiple generates the same principal ideal. -/
theorem span_singleton_unit_mul {R : Type*} [CommRing R] (v : Rˣ) (x : R) :
    Ideal.span ({(v : R) * x} : Set R) = Ideal.span {x} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro y (rfl : y = (v : R) * x)
    exact Ideal.mem_span_singleton.2 ⟨(v : R), mul_comm _ _⟩
  · rintro y (rfl : y = x)
    refine Ideal.mem_span_singleton.2 ⟨((v⁻¹ : Rˣ) : R), ?_⟩
    rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- **Card `(15)`, first half.**  The zeroth Fitting ideal of the observer cokernel — the ideal
generated by the determinant of the square presentation — is `(a^m)` with `m = binom N 2`. -/
theorem span_det_sheetObserver (a : R) (u : Fin N → Rˣ)
    (hv : IsUnit (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)))) :
    Ideal.span {(sheetObserver a u).det} = Ideal.span {a ^ N.choose 2} := by
  obtain ⟨v, hvv⟩ := hv
  rw [det_sheetObserver, ← hvv]
  exact span_singleton_unit_mul v _

/-- **Card `(15)`, second half.**  The discriminant ideal of the sheet constraints is `(a^{2m})`. -/
theorem span_disc_constraints (a : R) (u : Fin N → Rˣ)
    (hv : IsUnit (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)))) :
    Ideal.span {∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (a * (u j : R) - a * (u i : R)) ^ 2}
      = Ideal.span {a ^ (2 * N.choose 2)} := by
  have hsq : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)) ^ 2)
      = (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R))) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_pow _ _ _
  obtain ⟨v, hvv⟩ := hv
  rw [disc_constraints, sum_card_Ioi_eq_choose, hsq, ← hvv, ← Units.val_pow_eq_pow_val,
    mul_comm (a ^ (2 * N.choose 2)) _]
  exact span_singleton_unit_mul (v ^ 2) _

/-- **Card `(15)`, boxed.**  The discriminant ideal is the *square* of the orientation ideal: the
cotangent Fitting ideal is the square of the observer-cokernel Fitting ideal. -/
theorem span_disc_eq_span_det_sq (a : R) (u : Fin N → Rˣ)
    (hv : IsUnit (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((u j : R) - (u i : R)))) :
    Ideal.span {∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (a * (u j : R) - a * (u i : R)) ^ 2}
      = Ideal.span {(sheetObserver a u).det} ^ 2 := by
  rw [span_disc_constraints a u hv, span_det_sheetObserver a u hv, Ideal.span_singleton_pow,
    ← pow_mul, mul_comm (N.choose 2) 2]

/-- **Card `(17)`, boxed.**  The successor law: one more sheet appends a bar of length `N`. -/
theorem successor_bars (N : ℕ) (hN : 0 < N) :
    Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- **Card `(13)`.**  The `a`-adic grade dimensions of the observer cokernel are `N−1, …, 1`. -/
theorem grade_dimension (N q : ℕ) :
    ((Finset.Icc 1 (N - 1)).filter fun j => q < j).card = (N - 1) - q := by
  classical
  have hset : ((Finset.Icc 1 (N - 1)).filter fun j => q < j)
      = Finset.Icc (max 1 (q + 1)) (N - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff]
    omega
  rw [hset, Nat.card_Icc]
  omega

end Discriminant

end HTGeometry.ConstraintRelativity
