import GaloisForLFunctions.HTGeometry.DifferenceSystemPicardVessiot

/-!
# Constants are linearly disjoint from the base, and the difference Galois matrix

Two facts carry the difference Galois correspondence.

The first is that constants of an extension which are linearly independent over the constants of
the base stay linearly independent over the base itself: any base relation among constants can be
replaced by a relation with constant coefficients.  This is the minimal-support argument again, now
for a ring extension rather than inside one field.

The second is that a difference automorphism of an extension carrying an invertible fundamental
solution matrix `Y` multiplies it on the right by a matrix of *constants*, invertibly, and is
determined on the entries of `Y` by that matrix.  This is the map to `GL_n` of the constants on
which the whole Galois theory rests.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-! ### Linear disjointness of the constants -/

/-- **Base relations among constants can be made constant.**  If constants of a difference ring
extension satisfy a nontrivial linear relation over the base, they satisfy one whose coefficients
are constants of the base. -/
theorem exists_constant_coeffs_of_relation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (e : ι → R) (he : ∀ i, σR (e i) = e i)
    (a : ι → K) (ha0 : a ≠ 0)
    (ha : ∑ i, algebraMap K R (a i) * e i = 0) :
    ∃ b : ι → K, (∀ i, σK (b i) = b i) ∧ b ≠ 0 ∧
      ∑ i, algebraMap K R (b i) * e i = 0 := by
  classical
  set m := (Function.support a).toFinset.card with hm
  clear_value m
  induction m using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      exact ha0 (funext fun i => by simpa using not_not.mp (fun h => hcon ⟨i, h⟩))
    set c : K := (a i₀)⁻¹ with hc
    set a' : ι → K := fun i => c * a i with ha'
    have ha'i₀ : a' i₀ = 1 := by
      simp [ha', hc, inv_mul_cancel₀ hi₀]
    have hrel' : ∑ i, algebraMap K R (a' i) * e i = 0 := by
      have : ∑ i, algebraMap K R (a' i) * e i
          = algebraMap K R c * ∑ i, algebraMap K R (a i) * e i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [ha']; rw [map_mul]; ring
      rw [this, ha, mul_zero]
    set d : ι → K := fun i => a' i - σK (a' i) with hd
    have hreld : ∑ i, algebraMap K R (d i) * e i = 0 := by
      have hshift : ∑ i, algebraMap K R (σK (a' i)) * e i = 0 := by
        have := congrArg σR hrel'
        rw [map_sum, map_zero] at this
        refine this ▸ (Finset.sum_congr rfl fun i _ => ?_).symm
        rw [map_mul, hcompat, he i]
      have : ∑ i, algebraMap K R (d i) * e i
          = (∑ i, algebraMap K R (a' i) * e i) -
            ∑ i, algebraMap K R (σK (a' i)) * e i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hd]; rw [map_sub]; ring
      rw [this, hrel', hshift, sub_zero]
    by_cases hdzero : d = 0
    · refine ⟨a', fun i => ?_, ?_, hrel'⟩
      · have hz : a' i - σK (a' i) = 0 := congrFun hdzero i
        exact (sub_eq_zero.mp hz).symm
      · intro hzero
        rw [hzero] at ha'i₀
        exact one_ne_zero ha'i₀.symm
    · have hsub : (Function.support d).toFinset ⊆
          (Function.support a).toFinset.erase i₀ := by
        intro i hi
        simp only [Set.mem_toFinset, Function.mem_support] at hi
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · rintro rfl
          apply hi
          rw [hd]
          simp only []
          rw [ha'i₀, map_one, sub_self]
        · simp only [Set.mem_toFinset, Function.mem_support]
          intro hai
          apply hi
          have ha'i : a' i = 0 := by show c * a i = 0; rw [hai, mul_zero]
          rw [hd]
          simp only []
          rw [ha'i, map_zero, sub_zero]
      have hcard : (Function.support d).toFinset.card < m := by
        rw [hm]
        calc (Function.support d).toFinset.card
            ≤ ((Function.support a).toFinset.erase i₀).card := Finset.card_le_card hsub
          _ < (Function.support a).toFinset.card :=
              Finset.card_erase_lt_of_mem (by
                simp only [Set.mem_toFinset, Function.mem_support]; exact hi₀)
      exact ih _ hcard d hdzero hreld rfl

/-! ### The difference automorphism group and its matrix -/

/-- The group of `K`-algebra automorphisms of a difference ring extension which commute with the
difference operator. -/
def differenceAut (σR : R ≃+* R) : Subgroup (R ≃ₐ[K] R) where
  carrier := {φ | ∀ x : R, φ (σR x) = σR (φ x)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro φ ψ hφ hψ x
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hψ, hφ]
  inv_mem' := by
    intro φ hφ x
    show (φ⁻¹ : R ≃ₐ[K] R) (σR x) = σR ((φ⁻¹ : R ≃ₐ[K] R) x)
    have hsymm : ∀ y : R, (φ⁻¹ : R ≃ₐ[K] R) y = φ.symm y := fun _ => rfl
    rw [hsymm, hsymm]
    apply φ.injective
    rw [φ.apply_symm_apply, hφ, φ.apply_symm_apply]

@[simp] theorem mem_differenceAut {σR : R ≃+* R} {φ : R ≃ₐ[K] R} :
    φ ∈ differenceAut σR ↔ ∀ x : R, φ (σR x) = σR (φ x) := Iff.rfl

variable {n : ℕ}

/-- The matrix by which a `K`-algebra automorphism moves a fundamental solution matrix. -/
def galoisMatrix (Y : Matrix (Fin n) (Fin n) R) [Invertible Y] (φ : R ≃ₐ[K] R) :
    Matrix (Fin n) (Fin n) R := ⅟Y * Y.map φ

theorem mul_galoisMatrix (Y : Matrix (Fin n) (Fin n) R) [Invertible Y] (φ : R ≃ₐ[K] R) :
    Y * galoisMatrix Y φ = Y.map φ := by
  rw [galoisMatrix, ← mul_assoc, mul_invOf_self, one_mul]

/-- The Galois matrix is invertible. -/
theorem isUnit_det_galoisMatrix (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (φ : R ≃ₐ[K] R) : IsUnit (galoisMatrix Y φ).det := by
  haveI : Invertible (Y.map (φ : R → R)) := by
    have h := Invertible.map
      (φ.toRingEquiv.mapMatrix : Matrix (Fin n) (Fin n) R ≃+* Matrix (Fin n) (Fin n) R) Y
    rwa [RingEquiv.mapMatrix_apply] at h
  haveI hiv : Invertible (⅟Y : Matrix (Fin n) (Fin n) R) := invertibleInvOf
  have hdet : (galoisMatrix Y φ).det = (⅟Y : Matrix (Fin n) (Fin n) R).det *
      (Y.map (φ : R → R)).det := by
    rw [galoisMatrix, Matrix.det_mul]
  rw [hdet]
  exact (Matrix.isUnit_det_of_invertible _).mul (Matrix.isUnit_det_of_invertible _)

/-- **The Galois matrix has constant entries.**  A difference automorphism moves an invertible
fundamental solution matrix by right multiplication by a matrix fixed by the difference operator.
This is the map to `GL_n` of the constants on which difference Galois theory rests. -/
theorem galoisMatrix_map_eq_self (σR : R ≃+* R)
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (φ : R ≃ₐ[K] R) (hφ : ∀ x : R, φ (σR x) = σR (φ x)) :
    (galoisMatrix Y φ).map (σR : R → R) = galoisMatrix Y φ := by
  classical
  set BR : Matrix (Fin n) (Fin n) R := B.map (algebraMap K R) with hBR
  set M : Matrix (Fin n) (Fin n) R := galoisMatrix Y φ with hM
  haveI hYσ : Invertible (Y.map (σR : R → R)) := by
    have h := Invertible.map
      (σR.mapMatrix : Matrix (Fin n) (Fin n) R ≃+* Matrix (Fin n) (Fin n) R) Y
    rwa [RingEquiv.mapMatrix_apply] at h
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) R,
      (X.map (φ : R → R)).map (σR : R → R) = (X.map (σR : R → R)).map (φ : R → R) := by
    intro X
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact (hφ (X i j)).symm
  have hBfix : BR.map (φ : R → R) = BR := by
    refine Matrix.ext fun i j => ?_
    simp [hBR, Matrix.map_apply, AlgEquiv.commutes]
  have h2 : Y * M = Y.map (φ : R → R) := mul_galoisMatrix Y φ
  have hL : (Y.map (σR : R → R)) * (M.map (σR : R → R)) = BR * (Y.map (φ : R → R)) := by
    have h1 : (Y * M).map (σR : R → R)
        = (Y.map (σR : R → R)) * (M.map (σR : R → R)) := Matrix.map_mul
    rw [← h1, h2, hcomm Y, hY, Matrix.map_mul, hBfix]
  have hR : (Y.map (σR : R → R)) * M = BR * (Y.map (φ : R → R)) := by
    rw [hY, mul_assoc, h2]
  have hcancel := congrArg (fun Z => ⅟(Y.map (σR : R → R)) * Z) (hL.trans hR.symm)
  simpa only [← mul_assoc, invOf_mul_self, one_mul] using hcancel

/-- A difference automorphism is determined on the fundamental matrix by its Galois matrix. -/
theorem map_eq_of_galoisMatrix_eq (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    {φ ψ : R ≃ₐ[K] R} (h : galoisMatrix Y φ = galoisMatrix Y ψ) (i j : Fin n) :
    φ (Y i j) = ψ (Y i j) := by
  have h1 : Y.map (φ : R → R) = Y.map (ψ : R → R) := by
    rw [← mul_galoisMatrix Y φ, ← mul_galoisMatrix Y ψ, h]
  exact congrFun (congrFun h1 i) j


theorem galoisMatrix_one (Y : Matrix (Fin n) (Fin n) R) [Invertible Y] :
    galoisMatrix Y (1 : R ≃ₐ[K] R) = 1 := by
  have hmap : Y.map ((1 : R ≃ₐ[K] R) : R → R) = Y := Matrix.ext fun _ _ => rfl
  rw [galoisMatrix, hmap, invOf_mul_self]

/-- **The Galois matrix is multiplicative.**  Composition of difference automorphisms multiplies
their Galois matrices, as soon as the first fixes the constants — which is exactly what the
no-new-constants theorem supplies. -/
theorem galoisMatrix_mul (σR : R ≃+* R) (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (φ ψ : R ≃ₐ[K] R) (hψσ : ∀ x : R, ψ (σR x) = σR (ψ x))
    (hfix : ∀ x : R, σR x = x → φ x = x) :
    galoisMatrix Y (φ * ψ) = galoisMatrix Y φ * galoisMatrix Y ψ := by
  classical
  have hconst := galoisMatrix_map_eq_self σR B Y hY ψ hψσ
  have hfixM : (galoisMatrix Y ψ).map (φ : R → R) = galoisMatrix Y ψ := by
    refine Matrix.ext fun i j => ?_
    refine hfix _ ?_
    exact congrFun (congrFun hconst i) j
  have hcomp : Y.map ((φ * ψ : R ≃ₐ[K] R) : R → R) = (Y.map (ψ : R → R)).map (φ : R → R) :=
    Matrix.ext fun i j => AlgEquiv.mul_apply φ ψ (Y i j)
  have hkey : Y * galoisMatrix Y (φ * ψ) = Y * (galoisMatrix Y φ * galoisMatrix Y ψ) := by
    rw [mul_galoisMatrix, hcomp, ← mul_galoisMatrix Y ψ, Matrix.map_mul, hfixM,
      ← mul_assoc, mul_galoisMatrix Y φ]
  have := congrArg (fun Z => ⅟Y * Z) hkey
  simpa only [← mul_assoc, invOf_mul_self, one_mul] using this


end

end GaloisForLFunctions.HTGeometry
