import GaloisForLFunctions.HTGeometry.DifferenceGaloisIrreducibility
import GaloisForLFunctions.HTGeometry.DifferenceGaloisEndgame

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- Point separation alone turns a common invariant coordinate line into a Riccati solution. -/
theorem not_semiInvariant_coordinate_of_no_riccati_of_pointSeparation
    (E : Subalgebra C (R ⊗[K] R))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hconst : ∀ c : C, σR (algebraMap C R c) = algebraMap C R c)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (Y : Matrix (Fin 2) (Fin 2) R) (hYdet : IsUnit Y.det)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (c : Fin 2 → C) (hc : c ≠ 0) :
    ¬ ∀ χ ∈ S, ∃ lam : C, (galoisMatrixAt E Z hZE χ).mulVec c = lam • c := by
  classical
  intro hstable
  let T := R ⊗[K] R
  let cE : Fin 2 → E := fun j => algebraMap C E (c j)
  let zcE : Fin 2 → E := fun i =>
    ∑ j, (⟨Z i j, hZE i j⟩ : E) * cE j
  let cT : Fin 2 → T := fun j => (cE j : T)
  let zc : Fin 2 → T := fun i => (zcE i : T)
  have hzc : zc = Z.mulVec cT := by
    funext i
    simp [zc, zcE, cT, cE, Matrix.mulVec, dotProduct]
  let eE : E := cE 0 * zcE 1 - cE 1 * zcE 0
  have hχzc : ∀ (χ : E →ₐ[C] C) (i : Fin 2),
      χ (zcE i) = (galoisMatrixAt E Z hZE χ).mulVec c i := by
    intro χ i
    simp [zcE, cE, Matrix.mulVec, dotProduct, galoisMatrixAt]
  have hezeroE : eE = 0 := by
    apply hsep
    intro χ hχ
    obtain ⟨lam, hlam⟩ := hstable χ hχ
    change χ (cE 0 * zcE 1 - cE 1 * zcE 0) = 0
    rw [map_sub, map_mul, map_mul]
    rw [show χ (cE 0) = c 0 by simp [cE], show χ (cE 1) = c 1 by simp [cE]]
    rw [hχzc, hχzc]
    have h0 := congrFun hlam 0
    have h1 := congrFun hlam 1
    simp only [Pi.smul_apply] at h0 h1
    rw [h0, h1]
    ring
  let eT : T := (eE : T)
  have hezero : eT = 0 := congrArg Subtype.val hezeroE
  let y : R := ∑ j, Y 0 j * algebraMap C R (c j)
  have hyne : y ≠ 0 := by
    intro h0
    have h1 : σR y = 0 := by rw [h0, map_zero]
    have hy1 : ∑ j, Y 1 j * algebraMap C R (c j) = σR y := by
      rw [show y = ∑ j, Y 0 j * algebraMap C R (c j) from rfl, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hY1 j, hconst]
    have hzero : Y.mulVec (fun j => algebraMap C R (c j)) = 0 := by
      funext i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, y] using h0
      · simpa [Matrix.mulVec, dotProduct, hy1] using h1
    have hc0 : (fun j => algebraMap C R (c j)) = (0 : Fin 2 → R) := by
      have hmul := congrArg
        (fun v : Fin 2 → R => (Y⁻¹ : Matrix (Fin 2) (Fin 2) R).mulVec v) hzero
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Y hYdet, Matrix.one_mulVec,
        Matrix.mulVec_zero] at hmul
      exact hmul
    apply hc
    funext j
    exact (algebraMap C R).injective (by simpa using congrFun hc0 j)
  have hyrec : σR (σR y) =
      algebraMap K R a₁ * σR y + algebraMap K R a₀ * y := by
    have hy1 : σR y = ∑ j, Y 1 j * algebraMap C R (c j) := by
      rw [show y = ∑ j, Y 0 j * algebraMap C R (c j) from rfl, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hY1 j, hconst]
    rw [hy1, map_sum]
    have hterm : ∀ j : Fin 2,
        σR (Y 1 j * algebraMap C R (c j)) =
          (algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j) *
            algebraMap C R (c j) := by
      intro j
      rw [map_mul, hconst, hYrec j]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
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
  have hcE : ∀ j, (cE j : T) = algebraMap C T (c j) := by
    intro j
    rfl
  let L := leftFundamental K Y
  let RR := rightFundamental K Y
  let lv : Fin 2 → T := L.mulVec cT
  let rv : Fin 2 → T := RR.mulVec cT
  have hvec : L.mulVec zc = rv := by
    calc
      L.mulVec zc = L.mulVec (Z.mulVec cT) := by rw [hzc]
      _ = (L * Z).mulVec cT := Matrix.mulVec_mulVec cT L Z
      _ = RR.mulVec cT := by rw [hZ]
      _ = rv := rfl
  have hcross : lv 0 * rv 1 = lv 1 * rv 0 := by
    have heform : eT = cT 0 * zc 1 - cT 1 * zc 0 := by
      rfl
    apply sub_eq_zero.mp
    rw [← congrFun hvec 1, ← congrFun hvec 0]
    calc
      lv 0 * L.mulVec zc 1 - lv 1 * L.mulVec zc 0 = L.det * eT := by
        rw [heform]
        simp only [lv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, L, leftFundamental,
          Matrix.map_apply, Matrix.det_fin_two]
        ring
      _ = 0 := by rw [hezero, mul_zero]
  have hy1 : σR y = ∑ j, Y 1 j * algebraMap C R (c j) := by
    rw [show y = ∑ j, Y 0 j * algebraMap C R (c j) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hY1 j, hconst]
  have hl0 : lv 0 = y ⊗ₜ[K] (1 : R) := by
    simp only [lv, L, leftFundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, cT]
    rw [hcE, hcE]
    rw [← hleftC, ← hleftC]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one]
    rw [show y = ∑ j, Y 0 j * algebraMap C R (c j) from rfl,
      Fin.sum_univ_two, TensorProduct.add_tmul]
  have hl1 : lv 1 = σR y ⊗ₜ[K] (1 : R) := by
    simp only [lv, L, leftFundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, cT]
    rw [hcE, hcE]
    rw [← hleftC, ← hleftC]
    rw [hy1]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one]
    rw [Fin.sum_univ_two, TensorProduct.add_tmul]
  have hr0 : rv 0 = (1 : R) ⊗ₜ[K] y := by
    simp only [rv, RR, rightFundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, cT]
    rw [hcE, hcE]
    rw [← hrightC, ← hrightC]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one]
    rw [show y = ∑ j, Y 0 j * algebraMap C R (c j) from rfl,
      Fin.sum_univ_two, TensorProduct.tmul_add]
  have hr1 : rv 1 = (1 : R) ⊗ₜ[K] σR y := by
    simp only [rv, RR, rightFundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, cT]
    rw [hcE, hcE]
    rw [← hrightC, ← hrightC]
    rw [hy1]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one]
    rw [Fin.sum_univ_two, TensorProduct.tmul_add]
  have hsym : y ⊗ₜ[K] σR y = σR y ⊗ₜ[K] y := by
    calc
      y ⊗ₜ[K] σR y = (y ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] σR y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      _ = lv 0 * rv 1 := by rw [hl0, hr1]
      _ = lv 1 * rv 0 := hcross
      _ = (σR y ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] y) := by rw [hl1, hr0]
      _ = σR y ⊗ₜ[K] y := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨r, hr⟩ := exists_riccati_of_tmul_comm_without_simple hcompat hyne hyrec hsym
  exact hric r hr

/-- Point separation and absence of Riccati solutions force irreducibility of the full Galois
monoid, without a torsor basis or difference-simplicity premise. -/
theorem galoisMonoid_irreducible_of_no_riccati_of_pointSeparation
    (E : Subalgebra C (R ⊗[K] R))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hconst : ∀ c : C, σR (algebraMap C R c) = algebraMap C R c)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (Y : Matrix (Fin 2) (Fin 2) R) (hYdet : IsUnit Y.det)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    ∀ q : Fin 2 → C, q ≠ 0 → ∀ u : Fin 2 → C,
      u ∈ Submodule.span C {x : Fin 2 → C |
        ∃ g ∈ galoisMonoid E Z hZE S, g.mulVec q = x} := by
  intro q hq u
  apply span_orbit_eq_top_of_no_semiInvariant (G := galoisMonoid E Z hZE S)
      (Submonoid.one_mem _) ?_ q hq u
  intro c hc hstable
  apply not_semiInvariant_coordinate_of_no_riccati_of_pointSeparation E S hsep hcompat
    hconst hric Y hYdet hY1 hYrec Z hZE hZ c hc
  intro χ hχ
  exact hstable _ (galoisMatrixAt_mem_galoisMonoid E Z hZE S hχ)

end

end GaloisForLFunctions.HTGeometry
