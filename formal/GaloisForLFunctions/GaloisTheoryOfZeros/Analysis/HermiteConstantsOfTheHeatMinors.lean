import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheLowerDiscriminantsOfAHeatCollision
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheHermiteMeshIsPinched
import Mathlib.LinearAlgebra.Lagrange

/-!
# Explicit leading coefficients of the heat minors

Uniform mass on the roots of the Hermite polynomial has the reversed
Hermite recurrence. Multiplying its jth monic polynomial by the last
Hermite polynomial on those roots gives a falling factorial times the
Hermite polynomial j places below it. Lagrange's leading-coefficient
formula makes the mixed moment matrix triangular and gives every minor
as an explicit product.
-/

open Polynomial Finset Matrix GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section

private def reversedHermite (n : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | j+2 => X*reversedHermite n (j+1)-C ((n-j:ℕ):ℝ)*reversedHermite n j

private theorem reversed_top (n j : ℕ) :
    (reversedHermite n j).natDegree ≤ j ∧ (reversedHermite n j).coeff j = 1 := by
  induction j using Nat.twoStepInduction with
  | zero => simp [reversedHermite]
  | one => simp [reversedHermite]
  | more j hj hj' =>
    rw [reversedHermite]
    constructor
    · apply (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · apply (natDegree_mul_le).trans
        rw [natDegree_X]
        omega
      · exact (natDegree_C_mul_le _ _).trans (by omega)
    · simp only [coeff_sub,coeff_X_mul,coeff_C_mul,hj'.2,coeff_eq_zero_of_natDegree_lt
        (show (reversedHermite n j).natDegree < j+2 by omega),mul_zero,sub_zero]

private theorem hermite_step (n : ℕ) :
    hermiteReal (n+2) = X*hermiteReal (n+1)-C ((n+1:ℕ):ℝ)*hermiteReal n := by
  rw [hermiteReal_succ (n+1),gaussShift,derivative_hermiteReal_succ,C_1,one_mul,Nat.cast_succ]

private theorem at_node_step {x : ℝ} (k : ℕ) (hk : 0 < k) :
    x*(hermiteReal k).eval x = (hermiteReal (k+1)).eval x + (k:ℝ)*(hermiteReal (k-1)).eval x := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [hermite_step]
  simp only [eval_sub,eval_mul,eval_X,eval_C,Nat.add_sub_cancel]
  ring

private theorem reverse_value {n : ℕ} {x : ℝ} (hx : (hermiteReal (n+1)).eval x = 0) (j : ℕ) (hj : j ≤ n) :
    (reversedHermite n j).eval x*(hermiteReal n).eval x =
      (n.descFactorial j:ℝ)*(hermiteReal (n-j)).eval x := by
  induction j using Nat.twoStepInduction with
  | zero => simp [reversedHermite]
  | one =>
    have H := at_node_step (x:=x) n (by omega)
    simpa [hx,reversedHermite] using H
  | more j h₀ h₁ =>
    have h₀' := h₀ (by omega)
    have h₁' := h₁ (by omega)
    let k := n-(j+1)
    have hk : 0 < k := by dsimp only [k]; omega
    have H := at_node_step (x:=x) k hk
    have he : k+1 = n-j := by dsimp only [k]; omega
    have he' : k-1 = n-(j+2) := by dsimp only [k]; omega
    rw [he,he'] at H
    change x*(hermiteReal (n-(j+1))).eval x = _ at H
    have hfac : (n.descFactorial (j+1):ℝ) = ((n-j:ℕ):ℝ)*n.descFactorial j := by
      rw [Nat.descFactorial_succ,Nat.cast_mul]
    rw [reversedHermite,eval_sub,eval_mul,eval_X,eval_mul,eval_C,sub_mul,mul_assoc,mul_assoc,
      h₁',h₀',Nat.descFactorial_succ n (j+1),Nat.cast_mul]
    change _ = ((k:ℝ)*n.descFactorial (j+1))*(hermiteReal (n-(j+2))).eval x
    calc _ = (n.descFactorial (j+1):ℝ)*
               (x*(hermiteReal (n-(j+1))).eval x-(hermiteReal (n-j)).eval x) := by rw [hfac]; ring
         _ = _ := by rw [H]; ring

private theorem node_quadrature (n : ℕ) (p : ℝ[X]) (hd : p.natDegree ≤ n) :
    (∑ i : Fin (n+1), p.eval (hermiteRoot (n+1) i)/(hermiteReal n).eval (hermiteRoot (n+1) i)) =
      ((n:ℝ)+1)*p.coeff n := by
  let x := hermiteRoot (n+1)
  have hx := (hermiteRoot_strictMono (n+1)).injective
  have hnod : Lagrange.nodal univ x = hermiteReal (n+1) := (realHermite_eq_prod (n+1)).symm
  have hden (i : Fin (n+1)) : (∏ j ∈ univ.erase i, (x i-x j)) = ((n:ℝ)+1)*(hermiteReal n).eval (x i) := by
    have h := Lagrange.eval_nodal_derivative_eval_node_eq (s:=univ) (v:=x) (mem_univ i)
    rwa [hnod,derivative_hermiteReal_succ,eval_mul,eval_C,Lagrange.eval_nodal,eq_comm] at h
  have hg := Lagrange.coeff_eq_sum (s:=univ) (v:=x) hx.injOn (P:=p) (by
    rw [card_univ,Fintype.card_fin]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hd))
  simp only [card_univ,Fintype.card_fin,Nat.add_sub_cancel] at hg
  rw [hg,mul_sum]
  apply sum_congr rfl
  intro i _
  rw [hden]
  change _ = ((n:ℝ)+1)*(_/(((n:ℝ)+1)*_))
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  by_cases he : (hermiteReal n).eval (x i) = 0
  · simp [he,x]
  · field_simp [he,hn]

private theorem mixed_entry (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (∑ a : Fin (n+1), hermiteRoot (n+1) a^i*(reversedHermite n j).eval (hermiteRoot (n+1) a)) =
      if i=j then ((n:ℝ)+1)*n.descFactorial j else 0 := by
  let x := hermiteRoot (n+1)
  let p : ℝ[X] := X^i*hermiteReal (n-j)
  have hd : p.natDegree ≤ n := natDegree_mul_le.trans (by rw [natDegree_X_pow,natDegree_hermiteReal]; omega)
  have htop : p.coeff n = if i=j then 1 else 0 := by
    dsimp only [p]
    rw [coeff_X_pow_mul', if_pos (by omega)]
    by_cases he : i=j
    · rw [if_pos he,he,←natDegree_hermiteReal (n-j),coeff_natDegree]
      exact ((hermite_monic _).map _)
    · rw [if_neg he]
      exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_hermiteReal]; omega)
  have H := node_quadrature n p hd
  rw [htop] at H
  have he (a : Fin (n+1)) : x a^i*(reversedHermite n j).eval (x a) =
      n.descFactorial j*(p.eval (x a)/(hermiteReal n).eval (x a)) := by
    have hr := (mem_roots (realHermite_ne_zero (n+1))).mp
      (Multiset.mem_toFinset.mp (hermiteRoot_mem (n+1) a))
    have hnon := derivative_eval_ne_zero_of_roots_nodup (realHermite_ne_zero (n+1))
      (realHermite_roots_nodup_card (n+1)).1 hr
    change (derivative (hermiteReal (n+1))).eval (x a) ≠ 0 at hnon
    rw [derivative_hermiteReal_succ,eval_mul,eval_C] at hnon
    have hn := right_ne_zero_of_mul hnon
    have h := reverse_value (x:=x a) (n:=n) hr j hj
    dsimp only [p]
    rw [eval_mul,eval_pow,eval_X,←mul_div_assoc,eq_div_iff hn,mul_assoc,h]
    ring
  change (∑ a, x a^i*(reversedHermite n j).eval (x a)) = _
  simp_rw [he,←mul_sum]
  rw [H]
  split_ifs <;> ring

/-- Every principal minor for uniform unit mass at the standard Hermite roots. -/
theorem hermiteRoot_clusterMomentMinor (n q : ℕ) (hq : q ≤ n+1) :
    clusterMomentMinor (hermiteRoot (n+1)) q =
      ∏ j : Fin q, ((n:ℝ)+1)*(n.descFactorial j.val : ℝ) := by
  let x := hermiteRoot (n+1)
  let A := Matrix.of fun i j : Fin q => ∑ a, x a^(i.val+j.val)
  let T := Matrix.of fun i j : Fin q => (reversedHermite n j.val).coeff i.val
  let M := Matrix.of fun i j : Fin q => ∑ a : Fin (n+1), x a^i.val*(reversedHermite n j.val).eval (x a)
  have hT : T.BlockTriangular id := by
    intro i j hj
    exact coeff_eq_zero_of_natDegree_lt ((reversed_top n j.val).1.trans_lt hj)
  have hdet : T.det = 1 := by
    rw [det_of_upperTriangular hT]
    exact prod_eq_one fun j _ => (reversed_top n j.val).2
  have hM : A*T = M := by
    ext i j
    change (∑ k : Fin q, (∑ a, x a^(i.val+k.val))*(reversedHermite n j.val).coeff k.val) = _
    simp only [sum_mul,pow_add]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    change _ = x a^i.val*(reversedHermite n j.val).eval (x a)
    rw [eval_eq_sum_range' (n:=q) ((reversed_top n j.val).1.trans_lt j.isLt),←Fin.sum_univ_eq_sum_range,mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  have hL : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h : i.val < j.val := hij
    exact (mixed_entry n i.val j.val h.le (by have := j.isLt; omega)).trans (if_neg h.ne)
  change A.det = _
  rw [←mul_one A.det,←hdet,←det_mul,hM,det_of_lowerTriangular _ hL]
  apply prod_congr rfl
  intro i _
  simpa using mixed_entry n i.val i.val le_rfl (by have := i.isLt; omega)

/-- Closed product for the leading coefficient in physical heat time, at every
collision multiplicity and every minor size up to that multiplicity. -/
theorem hermiteMinorCoefficient_product (n q : ℕ) (hq : q ≤ n+1) :
    hermiteMinorCoefficient (n+1) q =
      2^(q.choose 2)*∏ j : Fin q, ((n:ℝ)+1)*(n.descFactorial j.val : ℝ) := by
  let u := fun i : Fin (n+1) => ((orderedHeatProfileRoot (n+1) i : profileRoots (n+1)) : ℝ)
  let x := hermiteRoot (n+1)
  have heq : univ.image u = univ.image (fun i => Real.sqrt 2*x i) := by
    ext r
    constructor
    · rintro hr
      obtain ⟨i,_,rfl⟩ := mem_image.mp hr
      obtain ⟨y,hy,he⟩ := mem_image.mp (orderedHeatProfileRoot (n+1) i).property
      obtain ⟨j,hj⟩ := exists_hermiteRoot_eq hy
      exact mem_image.mpr ⟨j,mem_univ _,by simpa [x,hj] using he⟩
    · intro hr
      obtain ⟨j,_,rfl⟩ := mem_image.mp hr
      have hm : Real.sqrt 2*x j ∈ profileRoots (n+1) := mem_image.mpr ⟨_,hermiteRoot_mem _ j,rfl⟩
      obtain ⟨i,hi⟩ := (orderedHeatProfileRoot (n+1)).surjective ⟨_,hm⟩
      exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩
  have hu : Function.Injective u := fun _ _ h => (orderedHeatProfileRoot _).injective (Subtype.ext h)
  have hv : Function.Injective (fun i => Real.sqrt 2*x i) := fun i j h =>
    (hermiteRoot_strictMono _).injective (mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h)
  have hm (k : ℕ) : (∑ i, u i^k) = ∑ i, (Real.sqrt 2*x i)^k := by
    calc _ = ∑ r ∈ univ.image u, r^k := (sum_image hu.injOn).symm
         _ = _ := by rw [heq,sum_image hv.injOn]
  change clusterMomentMinor u q = _
  have hminor : clusterMomentMinor u q = clusterMomentMinor (fun i => Real.sqrt 2*x i) q := by
    simp only [clusterMomentMinor,hm]
  have ha := clusterMomentMinor_affine x q 0 (Real.sqrt 2)
  simp only [zero_add,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at ha
  rw [hminor,ha,hermiteRoot_clusterMomentMinor n q hq]

/-- The physical derivative of the two-row heat determinant reads the multiplicity
as the strictly increasing integer 2m²(m−1). -/
theorem hermiteMinorCoefficient_two (n : ℕ) :
    hermiteMinorCoefficient (n+2) 2 = 2*((n:ℝ)+2)^2*((n:ℝ)+1) := by
  rw [hermiteMinorCoefficient_product (n+1) 2 (by omega)]
  simp [Fin.prod_univ_succ,Nat.cast_succ]
  <;> ring


end

end GaloisForLFunctions.GaloisTheoryOfZeros
