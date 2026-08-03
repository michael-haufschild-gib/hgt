import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The total derivation on jet polynomials

A differential relation is a polynomial in the jets of a function.  Differentiating such an
expression along the curve is a purely algebraic operation on the polynomial: the derivation which
raises every jet variable by one.  This file introduces that derivation and proves the chain rule
identifying it with the actual derivative of the evaluated expression.

This is the engine for every jet substitution which is not polynomial in the function itself — in
particular for the reciprocal, whose jets are polynomial in the jets of the function divided by a
power of its value.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Topology

noncomputable section

/-- The jet vector of a function at a point: all iterated derivatives. -/
def jetVec (f : ℂ → ℂ) (z : ℂ) : ℕ → ℂ := fun n => iteratedDeriv n f z

@[simp]
theorem jetVec_apply (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : jetVec f z n = iteratedDeriv n f z := rfl

/-- The total derivation on jet polynomials: it raises every jet variable by one. -/
def jetTotalDerivation : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun n => MvPolynomial.X (n + 1)

@[simp]
theorem jetTotalDerivation_X (n : ℕ) :
    jetTotalDerivation (MvPolynomial.X n) = MvPolynomial.X (n + 1) :=
  MvPolynomial.mkDerivation_X ℂ _ n

@[simp]
theorem jetTotalDerivation_C (a : ℂ) : jetTotalDerivation (MvPolynomial.C a) = 0 := by
  rw [show (MvPolynomial.C a : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) a from rfl]
  exact jetTotalDerivation.map_algebraMap a

/-- On an open set of smoothness every iterated derivative is again differentiable. -/
theorem differentiableAt_iteratedDeriv_of_contDiffAt {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) {z : ℂ} (hz : z ∈ U) (n : ℕ) :
    DifferentiableAt ℂ (iteratedDeriv n f) z := by
  have hcd : ContDiffOn ℂ ((n + 1 : ℕ) : WithTop ℕ∞) f U := fun w hw =>
    ((hf w hw).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hlt : ((n : ℕ) : WithTop ℕ∞) < ((n + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self n
  have hdw : DifferentiableOn ℂ (iteratedDerivWithin n f U) U :=
    hcd.differentiableOn_iteratedDerivWithin hlt hU.uniqueDiffOn
  have hdaw : DifferentiableAt ℂ (iteratedDerivWithin n f U) z :=
    (hdw z hz).differentiableAt (hU.mem_nhds hz)
  refine hdaw.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (iteratedDerivWithin_of_isOpen (n := n) (f := f) hU hw).symm

/-- Evaluating a jet polynomial along a smooth function is differentiable. -/
theorem differentiableAt_eval_jetVec {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) {z : ℂ} (hz : z ∈ U)
    (P : MvPolynomial ℕ ℂ) :
    DifferentiableAt ℂ (fun w => MvPolynomial.eval (jetVec f w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact differentiableAt_const a
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval_X, jetVec_apply]
      exact hp.mul (differentiableAt_iteratedDeriv_of_contDiffAt hU hf hz n)

/-- **The jet chain rule.**  Differentiating the evaluation of a jet polynomial along a smooth
function is evaluating the total derivation of that polynomial. -/
theorem deriv_eval_jetVec {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) {z : ℂ} (hz : z ∈ U)
    (P : MvPolynomial ℕ ℂ) :
    deriv (fun w => MvPolynomial.eval (jetVec f w) P) z
      = MvPolynomial.eval (jetVec f z) (jetTotalDerivation P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C, jetTotalDerivation_C, map_zero]
      exact deriv_const z a
  | add p q hp hq =>
      have hdp := differentiableAt_eval_jetVec hU hf hz p
      have hdq := differentiableAt_eval_jetVec hU hf hz q
      simp only [map_add]
      rw [deriv_fun_add hdp hdq, hp, hq]
  | mul_X p n hp =>
      have hdp := differentiableAt_eval_jetVec hU hf hz p
      have hdjet := differentiableAt_iteratedDeriv_of_contDiffAt hU hf hz n
      have hsucc : deriv (fun w => iteratedDeriv n f w) z = iteratedDeriv (n + 1) f z := by
        rw [iteratedDeriv_succ]
      simp only [map_mul, MvPolynomial.eval_X, jetVec_apply, Derivation.leibniz,
        jetTotalDerivation_X, smul_eq_mul]
      rw [deriv_fun_mul hdp hdjet, hp, hsucc]
      simp only [map_add, map_mul, MvPolynomial.eval_X, jetVec_apply]
      ring

/-- Universal numerators of the reciprocal jets. -/
def invJetNum : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (k + 1) => jetTotalDerivation (invJetNum k) * MvPolynomial.X 0
      - MvPolynomial.C ((k : ℂ) + 1) * (MvPolynomial.X 1 * invJetNum k)

@[simp] theorem invJetNum_zero : invJetNum 0 = 1 := rfl

theorem invJetNum_succ (k : ℕ) :
    invJetNum (k + 1) = jetTotalDerivation (invJetNum k) * MvPolynomial.X 0
      - MvPolynomial.C ((k : ℂ) + 1) * (MvPolynomial.X 1 * invJetNum k) := rfl

/-- **The reciprocal jet formula.**  Every jet of `1 / f` is a universal polynomial in the jets of
`f`, divided by the corresponding power of `f`. -/
theorem iteratedDeriv_inv_eq_invJetNum_div {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) (hne : ∀ w ∈ U, f w ≠ 0) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k (fun w => (f w)⁻¹) z
      = MvPolynomial.eval (jetVec f z) (invJetNum k) / (f z) ^ (k + 1) := by
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, invJetNum_zero]
      simp
  | succ k ih =>
      intro z hz
      have hfz : f z ≠ 0 := hne z hz
      have hdf : DifferentiableAt ℂ f z := (hf z hz).differentiableAt (by simp)
      have hdnum : DifferentiableAt ℂ
          (fun w => MvPolynomial.eval (jetVec f w) (invJetNum k)) z :=
        differentiableAt_eval_jetVec hU hf hz (invJetNum k)
      have hdpow : DifferentiableAt ℂ (fun w => (f w) ^ (k + 1)) z := hdf.pow (k + 1)
      have hEq : (fun w => iteratedDeriv k (fun u => (f u)⁻¹) w)
          =ᶠ[nhds z] fun w => MvPolynomial.eval (jetVec f w) (invJetNum k) / (f w) ^ (k + 1) := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hEq.deriv_eq]
      rw [deriv_fun_div hdnum hdpow (pow_ne_zero _ hfz)]
      rw [deriv_eval_jetVec hU hf hz, deriv_fun_pow hdf]
      have hzero : MvPolynomial.eval (jetVec f z) (MvPolynomial.X 0) = f z := by
        simp [jetVec]
      have hone : MvPolynomial.eval (jetVec f z) (MvPolynomial.X 1) = deriv f z := by
        simp [jetVec, iteratedDeriv_one]
      rw [invJetNum_succ]
      simp only [map_sub, map_mul, MvPolynomial.eval_C, hzero, hone]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- **Vanishing on the nonzero locus of finitely many coordinates forces vanishing.**  This is the
nonvanishing step of every rational jet substitution: the substituted relation is only defined where
the zeroth jets do not vanish, and that is enough. -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates {σ : Type*} [DecidableEq σ]
    (S : Finset σ) (P : MvPolynomial σ ℂ)
    (h : ∀ y : σ → ℂ, (∀ i ∈ S, y i ≠ 0) → MvPolynomial.eval y P = 0) : P = 0 := by
  have hprod : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial σ ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    exact MvPolynomial.X_ne_zero i
  have hQ : P * ∏ i ∈ S, (MvPolynomial.X i : MvPolynomial σ ℂ) = 0 := by
    refine MvPolynomial.funext fun y => ?_
    rw [map_mul, map_zero]
    by_cases hy : ∀ i ∈ S, y i ≠ 0
    · rw [h y hy, zero_mul]
    · push Not at hy
      obtain ⟨i, hiS, hi0⟩ := hy
      have hzero : MvPolynomial.eval y (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial σ ℂ)) = 0 := by
        rw [map_prod]
        refine Finset.prod_eq_zero hiS ?_
        rw [MvPolynomial.eval_X, hi0]
      rw [hzero, mul_zero]
  rcases mul_eq_zero.mp hQ with hP | hcon
  · exact hP
  · exact absurd hcon hprod

/-- The total derivation raises the jet support by at most one. -/
theorem jetTotalDerivation_mem_supported {k : ℕ} {P : MvPolynomial ℕ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ (Set.Iic k)) :
    jetTotalDerivation P ∈ MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hP ⊢
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [jetTotalDerivation_X]
      refine Algebra.subset_adjoin ⟨j + 1, ?_, rfl⟩
      simp only [Set.mem_Iic] at hj ⊢
      omega
  | algebraMap r =>
      have hCr : (algebraMap ℂ (MvPolynomial ℕ ℂ)) r = MvPolynomial.C r := rfl
      rw [hCr, jetTotalDerivation_C]
      exact Subalgebra.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      have hxmem : x ∈ Algebra.adjoin ℂ (MvPolynomial.X '' Set.Iic (k + 1)) := by
        refine Algebra.adjoin_mono ?_ hx
        exact Set.image_mono (fun j hj => by simp only [Set.mem_Iic] at hj ⊢; omega)
      have hymem : y ∈ Algebra.adjoin ℂ (MvPolynomial.X '' Set.Iic (k + 1)) := by
        refine Algebra.adjoin_mono ?_ hy
        exact Set.image_mono (fun j hj => by simp only [Set.mem_Iic] at hj ⊢; omega)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hxmem ihy)
        (Subalgebra.mul_mem _ hymem ihx)

/-- **The reciprocal numerators only involve the jets they may.**  `invJetNum k` is a polynomial in
the jet variables of order at most `k`. -/
theorem invJetNum_mem_supported (k : ℕ) :
    invJetNum k ∈ MvPolynomial.supported ℂ (Set.Iic k) := by
  induction k with
  | zero =>
      rw [invJetNum_zero]
      exact Subalgebra.one_mem _
  | succ k ih =>
      rw [invJetNum_succ]
      have hmono : MvPolynomial.supported ℂ (Set.Iic k) ≤
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        refine MvPolynomial.supported_mono ?_
        intro j hj
        simp only [Set.mem_Iic] at hj ⊢
        omega
      have hD : jetTotalDerivation (invJetNum k) ∈ MvPolynomial.supported ℂ (Set.Iic (k + 1)) :=
        jetTotalDerivation_mem_supported ih
      have hX0 : (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        rw [MvPolynomial.X_mem_supported]
        simp only [Set.mem_Iic]
        omega
      have hX1 : (MvPolynomial.X 1 : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        rw [MvPolynomial.X_mem_supported]
        simp only [Set.mem_Iic]
        omega
      have hNk : invJetNum k ∈ MvPolynomial.supported ℂ (Set.Iic (k + 1)) := hmono ih
      have hC : (MvPolynomial.C ((k : ℂ) + 1) : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        exact Subalgebra.algebraMap_mem _ _
      exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hD hX0)
        (Subalgebra.mul_mem _ hC (Subalgebra.mul_mem _ hX1 hNk))

end

end GaloisForLFunctions.HTGeometry
