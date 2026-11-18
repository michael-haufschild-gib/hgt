import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.ZMod.Basic

/-!
# Small-prime obstructions for canonical binary lifts

Bordering a zero-one matrix by a row and column of signs multiplies its
determinant by a power of two. Hadamard's inequality bounds all integral
minors simultaneously. In rank three every odd minor is a unit. In rank
four the only possible bad odd reduction is modulo three. In rank five,
a bordered clique realizes the new obstruction modulo five.
-/
namespace GaloisForLFunctions.RepresentationLifting
open Matrix Finset
open scoped Classical
noncomputable section

variable {ι κ : Type*}
/-- The entrywise zero-one lift of every binary matrix. -/
def binaryLift (A : Matrix ι κ (ZMod 2)) : Matrix ι κ ℤ := of fun i j => ((A i j).val:ℤ)

private theorem binaryLift_cases (A : Matrix ι κ (ZMod 2)) (i : ι) (j : κ) :
    binaryLift A i j=0 ∨ binaryLift A i j=1 := by
  have h := (A i j).val_lt
  change ((A i j).val:ℤ)=0 ∨ ((A i j).val:ℤ)=1
  omega

theorem binaryLift_reduction (A : Matrix ι κ (ZMod 2)) : (Int.castRingHom (ZMod 2)).mapMatrix (binaryLift A)=A := by
  ext i j
  change (((A i j).val : ℤ):ZMod 2) = _
  simp

private def signBorder {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℤ :=
  fromBlocks (of fun i j => 1-2*B i j) (of fun _ _ => 1) (of fun _ _ => 1) 1

private theorem signBorder_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    (signBorder B).det = (-2:ℤ)^n*B.det := by
  rw [signBorder,det_fromBlocks_one₂₂]
  have h : (of fun i j => 1-2*B i j) -
      (of fun (_ : Fin n) (_ : Fin 1) => (1:ℤ))*(of fun (_ : Fin 1) (_ : Fin n) => (1:ℤ)) =
      (-2:ℤ) • B := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [h,Matrix.det_smul,Fintype.card_fin]

/-- An integral determinant bound for binary matrices, valid in all orders.
Squaring removes the square root from the Hadamard bound. -/
theorem binaryLift_det_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    4^n*(binaryLift A).det.natAbs^2 ≤ (n+1)^(n+1) := by
  let B := binaryLift A
  let S := signBorder B
  have hs (i j) : S i j=1 ∨ S i j= -1 := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change 1-2*binaryLift A i j=1 ∨ 1-2*binaryLift A i j= -1
        rcases binaryLift_cases A i j with h | h <;> simp [h]
      | inr j => exact Or.inl rfl
    | inr i =>
      cases j with
      | inl j => exact Or.inl rfl
      | inr j => exact Or.inl (by simp [S,signBorder,Subsingleton.elim i j])
  let e : (Fin n ⊕ Fin 1) ≃ Fin (n+1) := finSumFinEquiv
  let H := (Int.castRingHom ℂ).mapMatrix S
  have hh := ContinuousKernelFredholm.complex_hadamard_entry_bound (reindex e e H) (M:=1)
    (fun i j => by
      change ‖((S (e.symm i) (e.symm j):ℤ):ℂ)‖ ≤ 1
      rcases hs (e.symm i) (e.symm j) with h|h <;> simp [h])
  rw [det_reindex_self,show H.det=(S.det:ℂ) from ((Int.castRingHom ℂ).map_det S).symm,
    Complex.norm_intCast,mul_one] at hh
  have h := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs,← pow_mul,Nat.mul_comm (n+1) 2,pow_mul,Real.sq_sqrt (Nat.cast_nonneg _)] at h
  have he : S.det.natAbs = 2^n*B.det.natAbs := by
    simp [S,signBorder_det,Int.natAbs_mul,Int.natAbs_pow]
  have hz : ((S.det.natAbs:ℕ):ℝ)^2 = (S.det:ℝ)^2 := by
    rw [Int.cast_natAbs,sq_abs]
  rw [← hz] at h
  have hnat : S.det.natAbs^2 ≤ (n+1)^(n+1) := by exact_mod_cast h
  rw [he,mul_pow,← pow_mul,Nat.mul_comm n 2,pow_mul] at hnat
  exact hnat

private theorem odd_of_binary {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (h : A.det ≠ 0) :
    ¬ 2 ∣ (binaryLift A).det.natAbs := by
  intro hd
  apply h
  rw [← binaryLift_reduction A,← RingHom.map_det]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact Int.natAbs_dvd_natAbs.mp hd

/-- Every binary basis in rank three lifts canonically to an integral basis. -/
theorem rankThree_binaryBasis_unimodular (A : {M : Matrix (Fin 3) (Fin 3) (ZMod 2) // M.det ≠ 0}) :
    IsUnit (binaryLift A.val).det := by
  apply Int.isUnit_iff_natAbs_eq.mpr
  let d := (binaryLift A.val).det.natAbs
  have hb := binaryLift_det_bound A.val
  have ho := odd_of_binary A.val A.property
  change ¬ 2 ∣ d at ho
  change 4^3*d^2 ≤ 4^4 at hb
  have hh : d ≤ 2 := by
    by_contra! hn
    have := pow_le_pow_left' (show 3 ≤ d by omega) 2
    norm_num at hb this
    omega
  change d = 1
  omega

/-- Odd rank-four minors of the canonical lift are exactly constrained to
absolute determinant one or three. -/
theorem rankFour_binaryBasis_det (A : {M : Matrix (Fin 4) (Fin 4) (ZMod 2) // M.det ≠ 0}) :
    (binaryLift A.val).det.natAbs=1 ∨ (binaryLift A.val).det.natAbs=3 := by
  let d := (binaryLift A.val).det.natAbs
  have hb := binaryLift_det_bound A.val
  have ho := odd_of_binary A.val A.property
  change ¬ 2 ∣ d at ho
  change 4^4*d^2 ≤ 5^5 at hb
  have hh : d ≤ 3 := by
    by_contra! hn
    have := pow_le_pow_left' (show 4 ≤ d by omega) 2
    norm_num at hb this
    omega
  change d=1 ∨ d=3
  omega

/-- A single canonical lift of a rank-four labelled binary configuration
preserves every binary basis simultaneously in all characteristics at least five. -/
theorem rankFour_transfer {V : Type*} (A : Matrix (Fin 4) V (ZMod 2))
    (p : {p : Nat.Primes // 3 < p.val}) (c : Fin 4 → V) :
    (A.submatrix id c).det ≠ 0 →
      (((Int.castRingHom (ZMod p.val.val)).mapMatrix (binaryLift A)).submatrix id c).det ≠ 0 := by
  intro h
  let B := binaryLift (A.submatrix id c)
  have hr := rankFour_binaryBasis_det ⟨A.submatrix id c,h⟩
  have he : (((Int.castRingHom (ZMod p.val.val)).mapMatrix (binaryLift A)).submatrix id c).det =
      (B.det:ZMod p.val.val) := ((Int.castRingHom _).map_det B).symm
  rw [he,ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hd
  have hh := Int.natAbs_dvd_natAbs.mpr hd
  change p.val.val ∣ B.det.natAbs at hh
  have hlt : 3 < p.val.val := p.property
  rcases hr with h₁ | h₃
  · exact (by omega : ¬ p.val.val ≤ 1) (Nat.le_of_dvd zero_lt_one (h₁ ▸ hh))
  · exact (by omega : ¬ p.val.val ≤ 3) (Nat.le_of_dvd (by norm_num) (h₃ ▸ hh))

private def outsideDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := of fun i j => if i=j then 0 else 1

/-- The complete graph adjacency gives a sharp witness in rank four.
Its binary columns form a basis, but their zero-one lifts lose rank modulo three. -/
theorem rankFour_exception_realized :
    ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 2), A.det ≠ 0 ∧ (binaryLift A).det= -3 ∧
      ((Int.castRingHom (ZMod 3)).mapMatrix (binaryLift A)).det=0 := by
  let H := outsideDiagonal 4
  have hdet : H.det = -3 := by
    let u : Fin 4 → ℤ := fun _ => -1
    let v : Fin 4 → ℤ := fun _ => 1
    have he : -H = 1+replicateCol (Fin 1) u * replicateRow (Fin 1) v := by
      ext i j
      by_cases h : i=j <;> simp [H,outsideDiagonal,u,v,h,one_apply,Matrix.mul_apply]
    have hh := congrArg Matrix.det he
    rw [det_neg,det_one_add_replicateCol_mul_replicateRow] at hh
    simpa [v,u,dotProduct] using hh
  let A := (Int.castRingHom (ZMod 2)).mapMatrix H
  have hA : binaryLift A=H := by
    ext i j
    by_cases h : i=j <;> simp [binaryLift,A,H,outsideDiagonal,h]
  refine ⟨A,?_,by rw [hA,hdet],?_⟩
  · rw [show A.det=(H.det:ZMod 2) from ((Int.castRingHom _).map_det H).symm,hdet]
    exact (not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)).mpr (by norm_num)
  · rw [hA,← RingHom.map_det,hdet]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by norm_num)


/-- The binary adjacency matrix of a clique, with a final looped vertex
joined to an arbitrary chosen subset. -/
def borderedClique {n : ℕ} (S : Finset (Fin n)) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℤ :=
  fromBlocks (outsideDiagonal n) (of fun i _ => if i ∈ S then 1 else 0)
    (of fun _ i => if i ∈ S then 1 else 0) 1

/-- An arbitrary chosen neighborhood gives a quadratic determinant law.
Sylvester's identity reduces the entire calculation to a two-by-two matrix. -/
theorem borderedClique_det {n : ℕ} (S : Finset (Fin n)) :
    (borderedClique S).det = (-1:ℤ)^n*((1-(n:ℤ))*(1+(S.card:ℤ))+(S.card:ℤ)^2) := by
  let b (i : Fin n) : ℤ := if i ∈ S then 1 else 0
  let U : Matrix (Fin n) (Fin 2) ℤ := of fun i => ![-1,b i]
  let V : Matrix (Fin 2) (Fin n) ℤ := of ![fun _ => 1,b]
  have hsum : ∑ i, b i = S.card := by simp [b,sum_boole]
  have hsq (i : Fin n) : b i*b i = b i := by by_cases h : i∈S <;> simp [b,h]
  have hcore : outsideDiagonal n - (of fun i (_:Fin 1) => b i)*(of fun (_:Fin 1) i => b i) =
      -(1 + U*V) := by
    ext i j
    by_cases h : i=j <;>
      simp [outsideDiagonal,U,V,one_apply,Matrix.mul_apply,Fin.sum_univ_two,h]
  have h₂ : V*U = !![-(n:ℤ), (S.card:ℤ); -(S.card:ℤ), (S.card:ℤ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U,V,Matrix.mul_apply,hsum,hsq]
  rw [borderedClique,det_fromBlocks_one₂₂,show (of fun i (_ : Fin 1) => if i ∈ S then (1:ℤ) else 0) =
      (of fun i (_ : Fin 1) => b i) from rfl,hcore,det_neg,Fintype.card_fin,det_one_add_mul_comm,h₂,det_fin_two]
  simp [one_apply,pow_two]
  ring

/-- Rank five is the first rank in which the zero-one lift of a binary basis
can lose rank modulo five. In this rank no prime greater than five can divide
a binary-basis determinant. -/
theorem rankFive_binaryBasis_det (A : {M : Matrix (Fin 5) (Fin 5) (ZMod 2) // M.det ≠ 0}) :
    (binaryLift A.val).det.natAbs=1 ∨ (binaryLift A.val).det.natAbs=3 ∨
      (binaryLift A.val).det.natAbs=5 := by
  let d := (binaryLift A.val).det.natAbs
  have hb := binaryLift_det_bound A.val
  have ho := odd_of_binary A.val A.property
  change ¬ 2 ∣ d at ho
  change 4^5*d^2 ≤ 6^6 at hb
  have hh : d ≤ 6 := by
    by_contra! hn
    have h := pow_le_pow_left' (show 7 ≤ d by omega) 2
    norm_num at hb h
    omega
  change d=1 ∨ d=3 ∨ d=5
  omega

/-- The looped extension of the four-clique with two neighbors realizes
absolute determinant five while retaining every binary pivot. -/
theorem rankFive_five_realized :
    ∃ A : Matrix (Fin 5) (Fin 5) (ZMod 2), A.det ≠ 0 ∧ (binaryLift A).det= -5 ∧
      ((Int.castRingHom (ZMod 5)).mapMatrix (binaryLift A)).det=0 := by
  let S : Finset (Fin 4) := {0,1}
  let e : (Fin 4 ⊕ Fin 1) ≃ Fin 5 := finSumFinEquiv
  let H := reindex e e (borderedClique S)
  have hd : H.det = -5 := by
    rw [show H.det=(borderedClique S).det from det_reindex_self _ _,borderedClique_det]
    norm_num [S]
  have entries (i j : Fin 5) : H i j = 0 ∨ H i j = 1 := by
    change (borderedClique S) (e.symm i) (e.symm j) = 0 ∨ (borderedClique S) (e.symm i) (e.symm j) = 1
    rcases e.symm i with i|i <;> rcases e.symm j with j|j <;>
      simp only [borderedClique,fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁,
        fromBlocks_apply₂₂,outsideDiagonal,of_apply,one_apply] <;> split_ifs <;> simp
  let A := (Int.castRingHom (ZMod 2)).mapMatrix H
  have hl : binaryLift A = H := by
    ext i j
    change ((H i j : ZMod 2).val : ℤ) = H i j
    rcases entries i j with h|h <;> simp [h]
  refine ⟨A,?_,by rw [hl,hd],?_⟩
  · rw [show A.det=(H.det:ZMod 2) from ((Int.castRingHom _).map_det H).symm,hd]
    exact (not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)).mpr (by norm_num)
  · rw [hl,← RingHom.map_det,hd]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by norm_num)
end
end GaloisForLFunctions.RepresentationLifting
