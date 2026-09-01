import GaloisForLFunctions.HTGeometry.SymmetricSquareMatrix
import GaloisForLFunctions.HTGeometry.DifferenceGaloisIrreducibilityTensor

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- An invariant unordered pair for all separating comparison points descends to a projective
solution of the symmetric-square system over the base field. -/
theorem exists_base_projective_symmetricSquare_solution_of_invariantPair
    (E : Subalgebra C (R ⊗[K] R))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    (Y : Matrix (Fin 2) (Fin 2) R) (hYdet : IsUnit Y.det)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hpair : HasInvariantPairNormalForm (galoisMonoid E Z hZE S)) :
    ∃ (a : Fin 3 → K) (q : R), a ≠ 0 ∧ q ≠ 0 ∧
      ∃ c : Fin 3 → C, c ≠ 0 ∧
        ∀ i, (symmetricSquareMatrix Y).mulVec
          (fun j => algebraMap C R (c j)) i = algebraMap K R (a i) * q := by
  classical
  let T := R ⊗[K] R
  let F := symmetricSquareMatrix Y
  let ZE : Matrix (Fin 2) (Fin 2) E := fun i j => ⟨Z i j, hZE i j⟩
  let WE : Matrix (Fin 3) (Fin 3) E := symmetricSquareMatrix ZE
  let W : Matrix (Fin 3) (Fin 3) T := WE.map E.val
  have htwoE : ((2 : E) : T) = 2 := by
    change ((2 : E) : T) = (2 : T)
    rw [show (2 : E) = algebraMap C E (2 : C) from
      (map_ofNat (algebraMap C E) 2).symm]
    change algebraMap C T (2 : C) = (2 : T)
    exact map_ofNat (algebraMap C T) 2
  have hW : W = symmetricSquareMatrix Z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W, WE, ZE, symmetricSquareMatrix]
    all_goals rw [htwoE]
  have hleftSym : leftFundamental K F =
      symmetricSquareMatrix (leftFundamental K Y) := by
    change (symmetricSquareMatrix Y).map
        (Algebra.TensorProduct.includeLeft : R →ₐ[K] T).toRingHom =
      symmetricSquareMatrix
        (Y.map (Algebra.TensorProduct.includeLeft : R →ₐ[K] T).toRingHom)
    exact symmetricSquareMatrix_map
      (Algebra.TensorProduct.includeLeft : R →ₐ[K] T).toRingHom Y
  have hrightSym : rightFundamental K F =
      symmetricSquareMatrix (rightFundamental K Y) := by
    change (symmetricSquareMatrix Y).map
        (Algebra.TensorProduct.includeRight : R →ₐ[K] T).toRingHom =
      symmetricSquareMatrix
        (Y.map (Algebra.TensorProduct.includeRight : R →ₐ[K] T).toRingHom)
    exact symmetricSquareMatrix_map
      (Algebra.TensorProduct.includeRight : R →ₐ[K] T).toRingHom Y
  have hFW : leftFundamental K F * W = rightFundamental K F := by
    rw [hW, hleftSym, hrightSym]
    calc
      symmetricSquareMatrix (leftFundamental K Y) * symmetricSquareMatrix Z =
          symmetricSquareMatrix (leftFundamental K Y * Z) := by
        rw [symmetricSquareMatrix_mul]
      _ = symmetricSquareMatrix (rightFundamental K Y) := by rw [hZ]
  obtain ⟨c, hc, hcsemi⟩ :=
    exists_symmetricSquare_semiInvariant_of_invariantPairNormalForm hpair
  let cE : Fin 3 → E := fun j => algebraMap C E (c j)
  let zcE : Fin 3 → E := fun i =>
    ∑ j, WE i j * cE j
  have hχW : ∀ (χ : E →ₐ[C] C) (i j : Fin 3),
      χ (WE i j) =
        symmetricSquareMatrix (galoisMatrixAt E Z hZE χ) i j := by
    intro χ i j
    change ((symmetricSquareMatrix ZE).map χ.toRingHom) i j =
      symmetricSquareMatrix (ZE.map χ.toRingHom) i j
    exact congrFun (congrFun (symmetricSquareMatrix_map χ.toRingHom ZE) i) j
  have hχzc : ∀ (χ : E →ₐ[C] C) (i : Fin 3),
      χ (zcE i) =
        (symmetricSquareMatrix (galoisMatrixAt E Z hZE χ)).mulVec c i := by
    intro χ i
    simp only [zcE, map_sum, map_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hχW]
    congr 1
    exact χ.commutes (c j)
  have hck : ∃ k : Fin 3, c k ≠ 0 := by
    by_contra h
    have hz : ∀ k, c k = 0 := by simpa only [not_exists, not_not] using h
    apply hc
    funext k
    exact hz k
  obtain ⟨k, hck⟩ := hck
  let lamE : E := algebraMap C E ((c k)⁻¹) * zcE k
  have hzcE : ∀ i, zcE i = lamE * cE i := by
    intro i
    have hwedge : cE k * zcE i - cE i * zcE k = 0 := by
      apply hsep
      intro χ hχ
      obtain ⟨lam, hlam⟩ := hcsemi _
        (galoisMatrixAt_mem_galoisMonoid E Z hZE S hχ)
      have hk := congrFun hlam k
      have hi := congrFun hlam i
      simp only [Pi.smul_apply, smul_eq_mul] at hk hi
      simp only [map_sub, map_mul, hχzc]
      rw [χ.commutes, χ.commutes]
      rw [hk, hi]
      rw [Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
      ring
    have heq : cE k * zcE i = cE i * zcE k := sub_eq_zero.mp hwedge
    calc
      zcE i = algebraMap C E ((c k)⁻¹ * c k) * zcE i := by
        rw [inv_mul_cancel₀ hck, map_one, one_mul]
      _ = algebraMap C E ((c k)⁻¹) * (cE k * zcE i) := by
        simp only [map_mul, cE]
        ring
      _ = algebraMap C E ((c k)⁻¹) * (cE i * zcE k) := by rw [heq]
      _ = lamE * cE i := by simp only [lamE]; ring

  let cT : Fin 3 → T := fun j => (cE j : T)
  let zcT : Fin 3 → T := fun i => (zcE i : T)
  have hzcT : zcT = W.mulVec cT := by
    funext i
    simp [zcT, zcE, W, cT, Matrix.mulVec, dotProduct]
  have hzcScale : zcT = (lamE : T) • cT := by
    funext i
    simp only [zcT, cT, Pi.smul_apply, smul_eq_mul]
    exact congrArg Subtype.val (hzcE i)
  have hvec : (leftFundamental K F).mulVec zcT =
      (rightFundamental K F).mulVec cT := by
    calc
      (leftFundamental K F).mulVec zcT =
          (leftFundamental K F).mulVec (W.mulVec cT) := by rw [hzcT]
      _ = (leftFundamental K F * W).mulVec cT := Matrix.mulVec_mulVec _ _ _
      _ = (rightFundamental K F).mulVec cT := by rw [hFW]
  let cR : Fin 3 → R := fun j => algebraMap C R (c j)
  let v : Fin 3 → R := F.mulVec cR
  have hleftC : ∀ d : C,
      (algebraMap C R d) ⊗ₜ[K] (1 : R) = algebraMap C T d := by
    intro d
    rw [IsScalarTower.algebraMap_apply C R T]
    rfl
  have hrightC : ∀ d : C,
      (1 : R) ⊗ₜ[K] algebraMap C R d = algebraMap C T d := by
    intro d
    rw [IsScalarTower.algebraMap_apply C K R]
    calc
      (1 : R) ⊗ₜ[K] algebraMap K R (algebraMap C K d) =
          (1 : R) ⊗ₜ[K] ((algebraMap C K d) • (1 : R)) := by
            simp [Algebra.smul_def]
      _ = ((algebraMap C K d) • (1 : R)) ⊗ₜ[K] (1 : R) := by
            exact (TensorProduct.smul_tmul (algebraMap C K d) (1 : R) (1 : R)).symm
      _ = algebraMap K R (algebraMap C K d) ⊗ₜ[K] (1 : R) := by
            simp [Algebra.smul_def]
      _ = (algebraMap C R d) ⊗ₜ[K] (1 : R) := by
            rw [IsScalarTower.algebraMap_apply C K R]
      _ = algebraMap C T d := hleftC d
  have hcTleft : cT = fun j => cR j ⊗ₜ[K] (1 : R) := by
    funext j
    change algebraMap C T (c j) =
      (algebraMap C R (c j)) ⊗ₜ[K] (1 : R)
    exact (hleftC (c j)).symm
  have hcTright : cT = fun j => (1 : R) ⊗ₜ[K] cR j := by
    funext j
    change algebraMap C T (c j) =
      (1 : R) ⊗ₜ[K] algebraMap C R (c j)
    exact (hrightC (c j)).symm
  have hleftv : (leftFundamental K F).mulVec cT =
      fun i => v i ⊗ₜ[K] (1 : R) := by
    rw [hcTleft]
    funext i
    simp [leftFundamental_apply, v, cR, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Algebra.TensorProduct.tmul_mul_tmul]
    rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
  have hrightv : (rightFundamental K F).mulVec cT =
      fun i => (1 : R) ⊗ₜ[K] v i := by
    rw [hcTright]
    funext i
    simp [rightFundamental_apply, v, cR, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Algebra.TensorProduct.tmul_mul_tmul]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
  have hprop : ∀ i,
      (1 : R) ⊗ₜ[K] v i = (lamE : T) * (v i ⊗ₜ[K] (1 : R)) := by
    intro i
    have hi := congrFun hvec i
    rw [hzcScale] at hi
    rw [matrix_mulVec_smul] at hi
    have hl := congrFun hleftv i
    have hr := congrFun hrightv i
    simpa only [Pi.smul_apply, smul_eq_mul, hl, hr] using hi.symm
  have hcomm : ∀ i j, v i ⊗ₜ[K] v j = v j ⊗ₜ[K] v i := by
    intro i j
    calc
      v i ⊗ₜ[K] v j =
          (v i ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v j) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      _ = (v i ⊗ₜ[K] (1 : R)) *
          ((lamE : T) * (v j ⊗ₜ[K] (1 : R))) := by rw [hprop j]
      _ = (v j ⊗ₜ[K] (1 : R)) *
          ((lamE : T) * (v i ⊗ₜ[K] (1 : R))) := by ring
      _ = (v j ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v i) := by rw [hprop i]
      _ = v j ⊗ₜ[K] v i := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hcR : cR ≠ 0 := by
    intro hcR0
    apply hc
    funext j
    apply (algebraMap C R).injective
    simpa [cR] using congrFun hcR0 j
  have hv : v ≠ 0 := by
    intro hv0
    have hback := congrArg (fun x => (symmetricSquareMatrix (Y⁻¹)).mulVec x) hv0
    have hFinv : symmetricSquareMatrix (Y⁻¹) * F = 1 := by
      change symmetricSquareMatrix (Y⁻¹) * symmetricSquareMatrix Y = 1
      rw [← symmetricSquareMatrix_mul, Matrix.nonsing_inv_mul Y hYdet,
        symmetricSquareMatrix_one]
    rw [show v = F.mulVec cR from rfl, Matrix.mulVec_mulVec, hFinv,
      Matrix.one_mulVec, Matrix.mulVec_zero] at hback
    exact hcR hback
  have hvk : ∃ k : Fin 3, v k ≠ 0 := by
    by_contra h
    have hz : ∀ k, v k = 0 := by simpa only [not_exists, not_not] using h
    apply hv
    funext k
    exact hz k
  obtain ⟨r, hr⟩ := hvk
  have hdesc : ∀ i, ∃ ai : K, v i = algebraMap K R ai * v r := by
    intro i
    obtain ⟨ai, hai⟩ := exists_eq_algebraMap_mul_of_tmul_comm hr (hcomm r i)
    exact ⟨ai, hai⟩
  choose a ha using hdesc
  have ha0 : a ≠ 0 := by
    intro haZero
    have har := congrFun haZero r
    have har' : a r = 0 := by simpa only [Pi.zero_apply] using har
    have hvr := ha r
    rw [har', map_zero, zero_mul] at hvr
    exact hr (by simpa using hvr)
  exact ⟨a, v r, ha0, hr, c, hc, ha⟩

omit [Nontrivial R] [Algebra C K] [IsScalarTower C K R] in
/-- A base-projective symmetric-square solution is a base semi-invariant of the symmetric-square
system. -/
theorem symmetricSquare_base_semiInvariant_of_projective_solution
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconst : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (A : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R)
    (hsys : Y.map σR = A.map (algebraMap K R) * Y)
    (a : Fin 3 → K) (q : R) (ha : a ≠ 0) (hq : q ≠ 0)
    (c : Fin 3 → C)
    (hrep : ∀ i, (symmetricSquareMatrix Y).mulVec
      (fun j => algebraMap C R (c j)) i = algebraMap K R (a i) * q) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ i,
      σK (a i) = lam * (symmetricSquareMatrix A).mulVec a i := by
  classical
  let F := symmetricSquareMatrix Y
  let B := symmetricSquareMatrix A
  let cR : Fin 3 → R := fun j => algebraMap C R (c j)
  let v : Fin 3 → R := F.mulVec cR
  have hFsys : F.map σR = B.map (algebraMap K R) * F := by
    calc
      F.map σR = symmetricSquareMatrix (Y.map σR) :=
        symmetricSquareMatrix_map σR.toRingHom Y
      _ = symmetricSquareMatrix (A.map (algebraMap K R) * Y) := by rw [hsys]
      _ = symmetricSquareMatrix (A.map (algebraMap K R)) * F := by
        rw [symmetricSquareMatrix_mul]
      _ = B.map (algebraMap K R) * F := by
        rw [symmetricSquareMatrix_map]
  have hmapv : ∀ i, σR (v i) = (F.map σR).mulVec cR i := by
    intro i
    simp only [v, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hconst]
  have hvsys : ∀ i, σR (v i) =
      algebraMap K R ((B.mulVec a) i) * q := by
    intro i
    calc
      σR (v i) = (F.map σR).mulVec cR i := hmapv i
      _ = ((B.map (algebraMap K R) * F).mulVec cR) i := by rw [hFsys]
      _ = (B.map (algebraMap K R)).mulVec (F.mulVec cR) i := by
        rw [Matrix.mulVec_mulVec]
      _ = algebraMap K R ((B.mulVec a) i) * q := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        rw [map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul]
        change algebraMap K R (B i j) * v j =
          algebraMap K R (B i j) * algebraMap K R (a j) * q
        rw [show v j = algebraMap K R (a j) * q from hrep j]
        ring
  have hak : ∃ k : Fin 3, a k ≠ 0 := by
    by_contra h
    have hz : ∀ k, a k = 0 := by simpa only [not_exists, not_not] using h
    apply ha
    funext k
    exact hz k
  obtain ⟨k, hak⟩ := hak
  let μ : K := (σK (a k))⁻¹ * (B.mulVec a) k
  have hσak : σK (a k) ≠ 0 := fun h => hak (σK.injective (by rw [h, map_zero]))
  have hσq : σR q = algebraMap K R μ * q := by
    have hkrep := congrArg σR (hrep k)
    have hkeq : algebraMap K R (σK (a k)) * σR q =
        algebraMap K R ((B.mulVec a) k) * q := by
      rw [map_mul, hcompat] at hkrep
      exact hkrep.symm.trans (hvsys k)
    calc
      σR q = algebraMap K R ((σK (a k))⁻¹ * σK (a k)) * σR q := by
        rw [inv_mul_cancel₀ hσak, map_one, one_mul]
      _ = algebraMap K R ((σK (a k))⁻¹) *
          (algebraMap K R (σK (a k)) * σR q) := by rw [map_mul]; ring
      _ = algebraMap K R ((σK (a k))⁻¹) *
          (algebraMap K R ((B.mulVec a) k) * q) := by rw [hkeq]
      _ = algebraMap K R μ * q := by simp only [μ, map_mul]; ring
  have hμ : μ ≠ 0 := by
    intro hμ0
    rw [hμ0, map_zero, zero_mul] at hσq
    exact hq (σR.injective (by rw [hσq, map_zero]))
  have scalar_eq_of_mul_eq : ∀ {x y : K},
      algebraMap K R x * q = algebraMap K R y * q → x = y := by
    intro x y hxy
    by_contra hne
    have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hne
    have huK : IsUnit (x - y) := isUnit_iff_ne_zero.mpr hdiff
    have huR : IsUnit (algebraMap K R (x - y)) := huK.map (algebraMap K R)
    have hz : algebraMap K R (x - y) * q = 0 := by
      rw [map_sub, sub_mul, hxy, sub_self]
    exact hq (huR.mul_left_cancel (by simpa using hz))
  refine ⟨μ⁻¹, inv_ne_zero hμ, ?_⟩
  intro i
  have hirep := congrArg σR (hrep i)
  have hieq : algebraMap K R (σK (a i) * μ) * q =
      algebraMap K R ((B.mulVec a) i) * q := by
    calc
      algebraMap K R (σK (a i) * μ) * q =
          algebraMap K R (σK (a i)) * (algebraMap K R μ * q) := by
        rw [map_mul]
        ring
      _ = algebraMap K R (σK (a i)) * σR q := by rw [hσq]
      _ = σR (algebraMap K R (a i) * q) := by rw [map_mul, hcompat]
      _ = σR (v i) := (congrArg σR (hrep i)).symm
      _ = algebraMap K R ((B.mulVec a) i) * q := hvsys i
  have hcoef : σK (a i) * μ = (B.mulVec a) i := scalar_eq_of_mul_eq hieq
  field_simp
  linear_combination hcoef

/-- An invariant unordered pair for the comparison Galois monoid produces a semi-invariant vector
of the base symmetric-square system. -/
theorem exists_symmetricSquare_base_semiInvariant_of_invariantPair
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconst : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (A : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R)
    (hYdet : IsUnit Y.det) (hsys : Y.map σR = A.map (algebraMap K R) * Y)
    (E : Subalgebra C (R ⊗[K] R))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hpair : HasInvariantPairNormalForm (galoisMonoid E Z hZE S)) :
    ∃ (a : Fin 3 → K) (lam : K), a ≠ 0 ∧ lam ≠ 0 ∧ ∀ i,
      σK (a i) = lam * (symmetricSquareMatrix A).mulVec a i := by
  obtain ⟨a, q, ha, hq, c, hc, hrep⟩ :=
    exists_base_projective_symmetricSquare_solution_of_invariantPair
      E S hsep Y hYdet Z hZE hZ hpair
  obtain ⟨lam, hlam, hsemi⟩ :=
    symmetricSquare_base_semiInvariant_of_projective_solution
      hcompat hconst A Y hsys a q ha hq c hrep
  exact ⟨a, lam, ha, hlam, hsemi⟩

/-- Exact Riccati and symmetric-square obstructions rule out both proper adjoint normal forms of
the comparison Galois monoid. -/
theorem not_invariantLine_orPair_of_no_riccati_no_symmetricSquare
    (E : Subalgebra C (R ⊗[K] R))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconst : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (A : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R)
    (hYdet : IsUnit Y.det) (hsys : Y.map σR = A.map (algebraMap K R) * Y)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) =
      algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hnoSym : ¬ ∃ (a : Fin 3 → K) (lam : K), a ≠ 0 ∧ lam ≠ 0 ∧ ∀ i,
      σK (a i) = lam * (symmetricSquareMatrix A).mulVec a i) :
    ¬ HasInvariantLineNormalForm (galoisMonoid E Z hZE S) ∧
      ¬ HasInvariantPairNormalForm (galoisMonoid E Z hZE S) := by
  constructor
  · intro hline
    obtain ⟨c, hc, hsemi⟩ :=
      exists_semiInvariant_of_invariantLineNormalForm hline
    apply not_semiInvariant_coordinate_of_no_riccati_of_pointSeparation
      E S hsep hcompat hconst hric Y hYdet hY1 hYrec Z hZE hZ c hc
    intro χ hχ
    exact hsemi _ (galoisMatrixAt_mem_galoisMonoid E Z hZE S hχ)
  · intro hpair
    apply hnoSym
    exact exists_symmetricSquare_base_semiInvariant_of_invariantPair
      hcompat hconst A Y hYdet hsys E S hsep Z hZE hZ hpair

section

variable {F₀ : Type*} [Field F₀]

/-- The symmetric-square semi-invariant is exactly the imprimitive `(e,p)` obstruction whenever
its first coordinate is nonzero; if that coordinate vanishes, nonzero slope forces the whole
vector to vanish. -/
theorem not_symmetricSquare_semiInvariant_of_no_imprimitive
    (σ : F₀ ≃+* F₀) (b : F₀) (hb : b ≠ 0)
    (hno : ∀ e p : F₀, p ≠ 0 →
      σ e = e / p + 2 * b →
      p * σ p = 1 + b * e + b ^ 2 * p → False) :
    ¬ ∃ (a : Fin 3 → F₀) (lam : F₀), a ≠ 0 ∧ lam ≠ 0 ∧ ∀ i,
      σ (a i) = lam *
        (symmetricSquareMatrix (!![0, 1; 1, b] : Matrix (Fin 2) (Fin 2) F₀)).mulVec a i := by
  rintro ⟨a, lam, ha, hlam, hsemi⟩
  have hd := hsemi 0
  have hn := hsemi 1
  have hm := hsemi 2
  simp [symmetricSquareMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hd hn hm
  by_cases had : a 0 = 0
  · have ham : a 2 = 0 := by
      rw [had, map_zero] at hd
      exact (mul_eq_zero.mp hd.symm).resolve_left hlam
    have han : a 1 = 0 := by
      rw [ham, map_zero, had] at hm
      have hprod : lam * (b * a 1) = 0 := by linear_combination -hm
      have hbn : b * a 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hlam
      exact (mul_eq_zero.mp hbn).resolve_left hb
    apply ha
    funext i
    fin_cases i <;> assumption
  · have hσad : σ (a 0) ≠ 0 := fun h => had (σ.injective (by rw [h, map_zero]))
    have ham : a 2 ≠ 0 := by
      intro ham
      rw [ham, mul_zero] at hd
      exact hσad hd
    let e : F₀ := a 1 / a 0
    let p : F₀ := a 2 / a 0
    have hp : p ≠ 0 := div_ne_zero ham had
    apply hno e p hp
    · dsimp [e, p]
      rw [map_div₀, hn, hd]
      field_simp [had, ham, hlam]
    · dsimp [e, p]
      rw [map_div₀, hm, hd]
      field_simp [had, ham, hlam]
      ring

end

end

end GaloisForLFunctions.HTGeometry
