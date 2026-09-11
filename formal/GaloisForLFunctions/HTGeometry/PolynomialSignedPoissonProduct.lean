import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/-!
# Exact signed Poisson product squares for polynomial atom pairs

On each bounded-degree polynomial space, forward difference is nilpotent.
Its finite exponential defines a real-parameter moment functional, including
negative parameters. The product rule has three commuting tensor terms,
which gives exact one- and two-variable signed-square decompositions.

For the theta atom-pair application, the negative parameters are the two
physical atom scales. Identification of the seeded functional with the
literal theta jets and domination of its negative squares are separate
source estimates; this module asserts neither source positivity nor RH.
-/

open Polynomial
namespace HTGeometry.SignedPoisson
noncomputable section

open scoped TensorProduct
abbrev PolyBelow (n : ℕ) : Type := ↥(Polynomial.degreeLT ℝ n)
noncomputable local instance (n : ℕ) : AddCommGroup (PolyBelow n) := inferInstance
noncomputable local instance (n m : ℕ) : AddCommGroup (PolyBelow n ⊗[ℝ] PolyBelow m) := inferInstance

def difference (n : ℕ) : Module.End ℝ (PolyBelow n) :=
  (Polynomial.taylorLinearEquiv (1 : ℝ) n).toLinearMap - LinearMap.id

@[simp] theorem difference_coe (n : ℕ) (P : PolyBelow n) :
    (difference n P : ℝ[X]) = Polynomial.taylor 1 (P : ℝ[X]) - (P : ℝ[X]) := rfl

theorem difference_degree_lt {P : ℝ[X]} (hP : P ≠ 0) :
    (Polynomial.taylor 1 P-P).degree < P.degree := by
  have ht : Polynomial.taylor 1 P ≠ 0 := (Polynomial.taylor_eq_zero 1 P).not.mpr hP
  have h := Polynomial.degree_sub_lt (Polynomial.degree_taylor P 1) ht
    (Polynomial.leadingCoeff_taylor 1 P)
  simpa only [Polynomial.degree_taylor] using h

theorem difference_iterate_zero (n k : ℕ) (P : PolyBelow n)
    (hdeg : (P : ℝ[X]).natDegree < k) : ((difference n)^k) P = 0 := by
  induction k generalizing P with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    by_cases hz : difference n P = 0
    · simp [hz]
    · have hp : (P : ℝ[X]) ≠ 0 := by
        intro h
        have hh : P = 0 := Subtype.ext h
        simp [hh] at hz
      have hdp : (difference n P : ℝ[X]) ≠ 0 := by
        intro h
        exact hz (Subtype.ext h)
      have hdrop : (difference n P : ℝ[X]).natDegree < (P : ℝ[X]).natDegree :=
        Polynomial.natDegree_lt_natDegree hdp (by simpa using difference_degree_lt hp)
      exact ih (difference n P) (by omega)

theorem difference_pow_eq_zero (n : ℕ) : (difference n)^n = 0 := by
  apply LinearMap.ext
  intro P
  by_cases hp : (P : ℝ[X]) = 0
  · have hh : P = 0 := Subtype.ext hp
    simp [hh]
  · apply difference_iterate_zero
    exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
      (Polynomial.mem_degreeLT.mp P.property)


theorem difference_isNilpotent (n : ℕ) : IsNilpotent (difference n) :=
  ⟨n, difference_pow_eq_zero n⟩

open scoped TensorProduct

private theorem mul_mem_below {n m : ℕ} (P : PolyBelow n) (Q : PolyBelow m) :
    (P : ℝ[X])*(Q : ℝ[X]) ∈ Polynomial.degreeLT ℝ (n+m+1) := by
  have hp : (P : ℝ[X]).natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLT.mp P.property).le
  have hq : (Q : ℝ[X]).natDegree ≤ m :=
    Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLT.mp Q.property).le
  apply Polynomial.mem_degreeLT.mpr
  calc
    ((P : ℝ[X])*(Q : ℝ[X])).degree ≤
        (((P : ℝ[X])*(Q : ℝ[X])).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
    _ ≤ ((n+m : ℕ) : WithBot ℕ) := by
      exact_mod_cast (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq))
    _ < ((n+m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self (n+m)

def mulBelow (n m : ℕ) : PolyBelow n →ₗ[ℝ] PolyBelow m →ₗ[ℝ] PolyBelow (n+m+1) where
  toFun P :=
    { toFun := fun Q => ⟨(P : ℝ[X])*(Q : ℝ[X]), mul_mem_below P Q⟩
      map_add' := by intro Q R; apply Subtype.ext; simp [mul_add]
      map_smul' := by intro r Q; apply Subtype.ext; simp }
  map_add' := by intro P Q; ext R; simp [add_mul]
  map_smul' := by intro r P; ext Q; simp

def tensorMul (n m : ℕ) : PolyBelow n ⊗[ℝ] PolyBelow m →ₗ[ℝ] PolyBelow (n+m+1) :=
  TensorProduct.lift (mulBelow n m)

@[simp] theorem tensorMul_tmul (n m : ℕ) (P : PolyBelow n) (Q : PolyBelow m) :
    tensorMul n m (P ⊗ₜ[ℝ] Q) = mulBelow n m P Q := rfl

def leftDifference (n m : ℕ) : Module.End ℝ (PolyBelow n ⊗[ℝ] PolyBelow m) :=
  (difference n).rTensor (PolyBelow m)

def rightDifference (n m : ℕ) : Module.End ℝ (PolyBelow n ⊗[ℝ] PolyBelow m) :=
  (difference m).lTensor (PolyBelow n)

theorem tensorDifference_commute (n m : ℕ) :
    Commute (leftDifference n m) (rightDifference n m) := by
  ext P Q
  simp [leftDifference,rightDifference]

theorem tensorDifference_intertwine (n m : ℕ) :
    (difference (n+m+1)).comp (tensorMul n m) =
      (tensorMul n m).comp (leftDifference n m+rightDifference n m+
        leftDifference n m*rightDifference n m) := by
  apply TensorProduct.ext'
  intro P Q
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.mul_apply,
    leftDifference,rightDifference,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul,
    map_add,tensorMul_tmul,difference_coe]
  change Polynomial.taylor 1 ((P : ℝ[X])*(Q : ℝ[X]))-(P : ℝ[X])*(Q : ℝ[X]) =
    (Polynomial.taylor 1 (P : ℝ[X])-(P : ℝ[X]))*(Q : ℝ[X])+
    (P : ℝ[X])*(Polynomial.taylor 1 (Q : ℝ[X])-(Q : ℝ[X]))+
    (Polynomial.taylor 1 (P : ℝ[X])-(P : ℝ[X]))*
      (Polynomial.taylor 1 (Q : ℝ[X])-(Q : ℝ[X]))
  rw [Polynomial.taylor_mul]
  ring


private theorem commute_same_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A B : Module.End ℝ V} (h : Commute A B) (r : ℝ) : Commute (r • A) (r • B) := by
  show (r • A)*(r • B) = (r • B)*(r • A)
  simpa only [smul_mul_smul_comm] using congrArg (fun T => (r*r) • T) h.eq

theorem differenceProduct_exponential (n m : ℕ) (r : ℝ) :
    (IsNilpotent.exp (r • difference (n+m+1))).comp (tensorMul n m) =
      (tensorMul n m).comp
        (IsNilpotent.exp (r • leftDifference n m)*
         IsNilpotent.exp (r • rightDifference n m)*
         IsNilpotent.exp (r • (leftDifference n m*rightDifference n m))) := by
  let L := leftDifference n m
  let R := rightDifference n m
  have hc : Commute L R := tensorDifference_commute n m
  have hL : IsNilpotent L :=
    (difference_isNilpotent n).map (Module.End.rTensorAlgHom ℝ (PolyBelow n) (PolyBelow m))
  have hR : IsNilpotent R :=
    (difference_isNilpotent m).map (Module.End.lTensorAlgHom ℝ (PolyBelow m) (PolyBelow n))
  have hC : IsNilpotent (L*R) := by
    obtain ⟨k,hk⟩ := hL
    refine ⟨k, ?_⟩
    rw [hc.mul_pow,hk,zero_mul]
  have hs := hc.isNilpotent_add hL hR
  have hsc : Commute (L+R) (L*R) :=
    ((Commute.refl L).mul_right hc).add_left (hc.symm.mul_right (Commute.refl R))
  have ht := hsc.isNilpotent_add hs hC
  have hi : (r • difference (n+m+1)).comp (tensorMul n m) =
      (tensorMul n m).comp (r • (L+R+L*R)) := by
    simp only [LinearMap.smul_comp,LinearMap.comp_smul]
    exact congrArg (fun T => r • T) (tensorDifference_intertwine n m)
  have he := Module.End.commute_exp_left_of_commute (ht.smul r)
    ((difference_isNilpotent (n+m+1)).smul r) hi
  have hf : IsNilpotent.exp (r • (L+R+L*R)) =
      IsNilpotent.exp (r • L)*IsNilpotent.exp (r • R)*IsNilpotent.exp (r • (L*R)) := by
    rw [smul_add, IsNilpotent.exp_add_of_commute (commute_same_smul hsc r)
      (hs.smul r) (hC.smul r),smul_add,
      IsNilpotent.exp_add_of_commute (commute_same_smul hc r) (hL.smul r) (hR.smul r)]
  rw [hf] at he
  exact he

private theorem leftDifference_pow (n m k : ℕ) :
    (leftDifference n m)^k = ((difference n)^k).rTensor (PolyBelow m) := by
  exact ((Module.End.rTensorAlgHom ℝ (PolyBelow n) (PolyBelow m)).map_pow _ k).symm

private theorem rightDifference_pow (n m k : ℕ) :
    (rightDifference n m)^k = ((difference m)^k).lTensor (PolyBelow n) := by
  exact ((Module.End.lTensorAlgHom ℝ (PolyBelow m) (PolyBelow n)).map_pow _ k).symm

private theorem crossDifference_pow_tmul (n m k : ℕ) (P : PolyBelow n) (Q : PolyBelow m) :
    ((leftDifference n m*rightDifference n m)^k) (P ⊗ₜ[ℝ] Q) =
      (((difference n)^k) P) ⊗ₜ[ℝ] (((difference m)^k) Q) := by
  rw [(tensorDifference_commute n m).mul_pow,Module.End.mul_apply,
    leftDifference_pow,rightDifference_pow]
  simp only [LinearMap.rTensor_tmul,LinearMap.lTensor_tmul]

private theorem crossDifference_pow_zero (n m : ℕ) :
    (leftDifference n m*rightDifference n m)^n = 0 := by
  apply TensorProduct.ext'
  intro P Q
  simp [crossDifference_pow_tmul,difference_pow_eq_zero]

private theorem exp_leftDifference (n m : ℕ) (r : ℝ) :
    IsNilpotent.exp (r • leftDifference n m) =
      (IsNilpotent.exp (r • difference n)).rTensor (PolyBelow m) := by
  have h := ((difference_isNilpotent n).smul r).map_exp
    (Module.End.rTensorAlgHom ℝ (PolyBelow n) (PolyBelow m))
  simpa [leftDifference,rightDifference,Module.End.rTensorAlgHom,Module.End.lTensorAlgHom] using h.symm

private theorem exp_rightDifference (n m : ℕ) (r : ℝ) :
    IsNilpotent.exp (r • rightDifference n m) =
      (IsNilpotent.exp (r • difference m)).lTensor (PolyBelow n) := by
  have h := ((difference_isNilpotent m).smul r).map_exp
    (Module.End.lTensorAlgHom ℝ (PolyBelow m) (PolyBelow n))
  simpa [leftDifference,rightDifference,Module.End.rTensorAlgHom,Module.End.lTensorAlgHom] using h.symm

/-- Exact product formula for the finite polynomial difference exponential. -/
theorem differenceProduct_sum (n m : ℕ) (r : ℝ) (P : PolyBelow n) (Q : PolyBelow m) :
    IsNilpotent.exp (r • difference (n+m+1)) (mulBelow n m P Q) =
      ∑ k ∈ Finset.range n, (k.factorial : ℚ)⁻¹ • r^k •
        mulBelow n m
          (IsNilpotent.exp (r • difference n) (((difference n)^k) P))
          (IsNilpotent.exp (r • difference m) (((difference m)^k) Q)) := by
  have h := LinearMap.congr_fun (differenceProduct_exponential n m r) (P ⊗ₜ[ℝ] Q)
  have hz : (r • (leftDifference n m*rightDifference n m))^n = 0 := by
    rw [smul_pow,crossDifference_pow_zero,smul_zero]
  simpa only [LinearMap.comp_apply,tensorMul_tmul,IsNilpotent.exp_eq_sum hz,
    LinearMap.sum_apply,LinearMap.smul_apply,smul_pow,Module.End.mul_apply,
    map_sum,map_smul,map_rat_smul,crossDifference_pow_tmul,exp_leftDifference,
    exp_rightDifference,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul] using h

/-- Origin evaluation on the degree-bounded polynomial space. -/
def origin (n : ℕ) : PolyBelow n →ₗ[ℝ] ℝ where
  toFun P := (P : ℝ[X]).eval 0
  map_add' := by intro P Q; simp
  map_smul' := by intro r P; simp

@[simp] theorem origin_mulBelow (n m : ℕ) (P : PolyBelow n) (Q : PolyBelow m) :
    origin (n+m+1) (mulBelow n m P Q) = origin n P * origin m Q := by
  change ((P : ℝ[X])*(Q : ℝ[X])).eval 0 = _
  exact Polynomial.eval_mul

/-- Evaluation of the exact finite difference exponential at the polynomial origin. -/
def moment (n : ℕ) (r : ℝ) (P : PolyBelow n) : ℝ :=
  origin n (IsNilpotent.exp (r • difference n) P)

/-- Signed Poisson product identity, valid for every real parameter, including negative ones. -/
theorem moment_product (n m : ℕ) (r : ℝ) (P : PolyBelow n) (Q : PolyBelow m) :
    moment (n+m+1) r (mulBelow n m P Q) =
      ∑ k ∈ Finset.range n, (k.factorial : ℚ)⁻¹ • (r^k *
        moment n r (((difference n)^k) P)*moment m r (((difference m)^k) Q)) := by
  have h := congrArg (origin (n+m+1)) (differenceProduct_sum n m r P Q)
  simpa only [moment,map_sum,map_rat_smul,map_smul,origin_mulBelow,
    smul_eq_mul,mul_assoc] using h

/-- The same formula is a finite signed square sum when both factors agree. -/
theorem moment_square (n : ℕ) (r : ℝ) (P : PolyBelow n) :
    moment (n+n+1) r (mulBelow n n P P) =
      ∑ k ∈ Finset.range n, (k.factorial : ℚ)⁻¹ •
        (r^k * moment n r (((difference n)^k) P)^2) := by
  simpa only [pow_two,mul_assoc] using moment_product n n r P P

/-- The real coefficient carries the sign of the parameter power. -/
def weight (r : ℝ) (k : ℕ) : ℝ := (k.factorial : ℚ)⁻¹ • r^k

/-- Product identity with a single real signed coefficient. -/
theorem moment_product_weight (n m : ℕ) (r : ℝ) (P : PolyBelow n) (Q : PolyBelow m) :
    moment (n+m+1) r (mulBelow n m P Q) =
      ∑ k ∈ Finset.range n, weight r k *
        moment n r (((difference n)^k) P)*moment m r (((difference m)^k) Q) := by
  simpa only [weight,smul_mul_assoc] using moment_product n m r P Q

/-- Two-variable polynomial-square moment, allowing an arbitrary finite separated expansion. -/
def pairSquare {N : ℕ} (n m : ℕ) (p r : ℝ)
    (P : Fin N → PolyBelow n) (Q : Fin N → PolyBelow m) : ℝ :=
  ∑ i, ∑ j, moment (n+n+1) p (mulBelow n n (P i) (P j))*
    moment (m+m+1) r (mulBelow m m (Q i) (Q j))

private theorem fourfold_shuffle {ι κ α β : Type*} (I : Finset ι) (J : Finset κ)
    (K : Finset α) (L : Finset β) (f : ι → κ → α → β → ℝ) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, f i j k l) =
      ∑ k ∈ K, ∑ l ∈ L, ∑ i ∈ I, ∑ j ∈ J, f i j k l := by
  calc
    _ = ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, ∑ l ∈ L, f i j k l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ L, f i j k l := Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ l ∈ L, ∑ j ∈ J, f i j k l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm

/-- Exact two-parameter signed-square decomposition; no measure-positivity assumption. -/
theorem pairSquare_eq_difference_squares {N : ℕ} (n m : ℕ) (p r : ℝ)
    (P : Fin N → PolyBelow n) (Q : Fin N → PolyBelow m) :
    pairSquare n m p r P Q =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range m, weight p k*weight r l*
        (∑ i, moment n p (((difference n)^k) (P i))*
          moment m r (((difference m)^l) (Q i)))^2 := by
  unfold pairSquare
  simp_rw [moment_product_weight,Finset.sum_mul,Finset.mul_sum]
  rw [fourfold_shuffle]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end HTGeometry.SignedPoisson
