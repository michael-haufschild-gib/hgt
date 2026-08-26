import GaloisForLFunctions.HTGeometry.AdditivePolynomialHopfIdeal

/-!
# Degree filtration for slices of the additive polynomial coalgebra

Contracting the right leg of the additive coproduct against an arbitrary linear functional never
increases total degree in the surviving left variables.  The proof is coefficient-free and works
for an arbitrary variable type.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry
namespace AdditivePolynomialCoalgebraFiltration

noncomputable section
variable {k σ : Type*} [Field k]

def tensorRightSlice (ψ : MvPolynomial σ k →ₗ[k] k) :
    MvPolynomial σ k ⊗[k] MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (TensorProduct.rid k (MvPolynomial σ k)).toLinearMap.comp
    (TensorProduct.map (LinearMap.id) ψ)

@[simp] theorem tensorRightSlice_tmul (ψ : MvPolynomial σ k →ₗ[k] k)
    (P Q : MvPolynomial σ k) :
    tensorRightSlice ψ (P ⊗ₜ[k] Q) = ψ Q • P := by
  simp [tensorRightSlice]

def rightSlice (ψ : MvPolynomial σ k →ₗ[k] k) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (tensorRightSlice ψ).comp
    ((MvPolynomial.tensorEquivSum k σ σ k).symm.toLinearMap.comp
      (GaloisForLFunctions.HTGeometry.AdditivePolynomialHopf.addComul
        (σ := σ) (k := k)).toLinearMap)

theorem tensorEquivSum_symm_C (c : k) :
    (MvPolynomial.tensorEquivSum k σ σ k).symm (MvPolynomial.C c) =
      MvPolynomial.C c ⊗ₜ[k] 1 := by
  apply (MvPolynomial.tensorEquivSum k σ σ k).injective
  simp

theorem tensorEquivSum_symm_X_inl (i : σ) :
    (MvPolynomial.tensorEquivSum k σ σ k).symm (MvPolynomial.X (Sum.inl i)) =
      (Algebra.TensorProduct.includeLeft :
        MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⊗[k] MvPolynomial σ k)
          (MvPolynomial.X i) := by
  apply (MvPolynomial.tensorEquivSum k σ σ k).injective
  simp

theorem tensorEquivSum_symm_X_inr (i : σ) :
    (MvPolynomial.tensorEquivSum k σ σ k).symm (MvPolynomial.X (Sum.inr i)) =
      (Algebra.TensorProduct.includeRight :
        MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⊗[k] MvPolynomial σ k)
          (MvPolynomial.X i) := by
  apply (MvPolynomial.tensorEquivSum k σ σ k).injective
  simp

@[simp] theorem rightSlice_C (ψ : MvPolynomial σ k →ₗ[k] k) (c : k) :
    rightSlice ψ (MvPolynomial.C c) = ψ 1 • MvPolynomial.C c := by
  rw [rightSlice, LinearMap.coe_comp, LinearMap.coe_comp, Function.comp_apply]
  simp [tensorEquivSum_symm_C, tensorRightSlice]

def mulXFunctional (ψ : MvPolynomial σ k →ₗ[k] k) (i : σ) :
    MvPolynomial σ k →ₗ[k] k :=
  ψ.comp ((LinearMap.mul k (MvPolynomial σ k)).flip (MvPolynomial.X i))

theorem tensorRightSlice_mul_includeLeft (ψ : MvPolynomial σ k →ₗ[k] k)
    (t : MvPolynomial σ k ⊗[k] MvPolynomial σ k) (P : MvPolynomial σ k) :
    tensorRightSlice ψ (t * (Algebra.TensorProduct.includeLeft :
      MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⊗[k] MvPolynomial σ k) P) =
      tensorRightSlice ψ t * P := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa [add_mul, map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [Algebra.TensorProduct.includeLeft_apply]
      simp [tensorRightSlice, Algebra.smul_def, mul_comm, mul_assoc]

theorem tensorRightSlice_mul_includeRight (ψ : MvPolynomial σ k →ₗ[k] k)
    (t : MvPolynomial σ k ⊗[k] MvPolynomial σ k) (P : MvPolynomial σ k) :
    tensorRightSlice ψ (t * (Algebra.TensorProduct.includeRight :
      MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⊗[k] MvPolynomial σ k) P) =
      tensorRightSlice (ψ.comp ((LinearMap.mul k (MvPolynomial σ k)).flip P)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa [add_mul, map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [Algebra.TensorProduct.includeRight_apply]
      simp [tensorRightSlice, Algebra.smul_def, mul_comm]

theorem rightSlice_mul_X (ψ : MvPolynomial σ k →ₗ[k] k)
    (P : MvPolynomial σ k) (i : σ) :
    rightSlice ψ (P * MvPolynomial.X i) =
      rightSlice ψ P * MvPolynomial.X i + rightSlice (mulXFunctional ψ i) P := by
  change tensorRightSlice ψ
      ((MvPolynomial.tensorEquivSum k σ σ k).symm
        (GaloisForLFunctions.HTGeometry.AdditivePolynomialHopf.addComul
          (P * MvPolynomial.X i))) = _
  rw [map_mul (GaloisForLFunctions.HTGeometry.AdditivePolynomialHopf.addComul
    (σ := σ) (k := k))]
  rw [map_mul (MvPolynomial.tensorEquivSum k σ σ k).symm]
  simp only [GaloisForLFunctions.HTGeometry.AdditivePolynomialHopf.addComul_X]
  rw [map_add, tensorEquivSum_symm_X_inl, tensorEquivSum_symm_X_inr, mul_add, map_add]
  rw [tensorRightSlice_mul_includeLeft, tensorRightSlice_mul_includeRight]
  rfl

theorem totalDegree_sum_le {α : Type*} (s : Finset α)
    (P : α → MvPolynomial σ k) (d : ℕ)
    (h : ∀ a ∈ s, (P a).totalDegree ≤ d) :
    (∑ a ∈ s, P a).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (h a (Finset.mem_insert_self a s))
          (ih (fun b hb => h b (Finset.mem_insert_of_mem hb))))

theorem rightSlice_monomial_totalDegree_le
    (ψ : MvPolynomial σ k →ₗ[k] k) (s : σ →₀ ℕ) (c : k) :
    (rightSlice ψ (MvPolynomial.monomial s c)).totalDegree ≤
      s.sum fun _ n => n := by
  classical
  induction hd : s.sum (fun _ n => n) using Nat.strong_induction_on generalizing s ψ c with
  | h d ih =>
      by_cases hs0 : s = 0
      · subst s
        simp at hd
        subst d
        change (rightSlice ψ (MvPolynomial.C c)).totalDegree ≤ 0
        rw [rightSlice_C]
        have hle := MvPolynomial.totalDegree_smul_le (ψ 1)
          (MvPolynomial.C c : MvPolynomial σ k)
        simpa using hle
      · have hsupp : s.support.Nonempty := by
          simpa [Finsupp.support_nonempty_iff] using hs0
        obtain ⟨i, hi⟩ := hsupp
        have hsi : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
        let t : σ →₀ ℕ := s - Finsupp.single i 1
        have hle : Finsupp.single i 1 ≤ s :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hsi)
        have htadd : t + Finsupp.single i 1 = s := tsub_add_cancel_of_le hle
        have hsum : t.sum (fun _ n => n) + 1 = d := by
          calc
            t.sum (fun _ n => n) + 1 =
                t.sum (fun _ n => n) +
                  (Finsupp.single i 1).sum (fun _ n => n) := by simp
            _ = (t + Finsupp.single i 1).sum (fun _ n => n) := by
              symm
              apply Finsupp.sum_add_index <;> simp
            _ = d := by rw [htadd, hd]
        have htlt : t.sum (fun _ n => n) < d := by omega
        have hmono : MvPolynomial.monomial s c =
            MvPolynomial.monomial t c * MvPolynomial.X i := by
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, htadd, mul_one]
        rw [hmono, rightSlice_mul_X]
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_X]
          have hrec := ih (t.sum fun _ n => n) htlt ψ t c rfl
          omega
        · have hrec := ih (t.sum fun _ n => n) htlt (mulXFunctional ψ i) t c rfl
          omega

theorem rightSlice_totalDegree_le (ψ : MvPolynomial σ k →ₗ[k] k)
    (P : MvPolynomial σ k) : (rightSlice ψ P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_sum_le P.support
  intro s hs
  exact (rightSlice_monomial_totalDegree_le ψ s (MvPolynomial.coeff s P)).trans
    (MvPolynomial.le_totalDegree hs)

theorem tensorRightSlice_sub_functional
    (ψ χ : MvPolynomial σ k →ₗ[k] k)
    (t : MvPolynomial σ k ⊗[k] MvPolynomial σ k) :
    tensorRightSlice (ψ - χ) t = tensorRightSlice ψ t - tensorRightSlice χ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
  | tmul x y => simp [tensorRightSlice, sub_smul]

theorem rightSlice_sub_functional
    (ψ χ : MvPolynomial σ k →ₗ[k] k) (P : MvPolynomial σ k) :
    rightSlice (ψ - χ) P = rightSlice ψ P - rightSlice χ P := by
  exact tensorRightSlice_sub_functional ψ χ _

/-- If the slicing functional kills constants, contraction lowers total degree strictly whenever
the result is nonzero. -/
theorem rightSlice_monomial_totalDegree_lt_of_one_eq_zero
    (ψ : MvPolynomial σ k →ₗ[k] k) (hψ : ψ 1 = 0)
    (s : σ →₀ ℕ) (c : k)
    (hzero : rightSlice ψ (MvPolynomial.monomial s c) ≠ 0) :
    (rightSlice ψ (MvPolynomial.monomial s c)).totalDegree <
      s.sum fun _ n => n := by
  classical
  induction hd : s.sum (fun _ n => n) using Nat.strong_induction_on generalizing s ψ c with
  | h d ih =>
      by_cases hs0 : s = 0
      · subst s
        change rightSlice ψ (MvPolynomial.C c) ≠ 0 at hzero
        rw [rightSlice_C, hψ, zero_smul] at hzero
        exact (hzero rfl).elim
      · have hsupp : s.support.Nonempty := by
          simpa [Finsupp.support_nonempty_iff] using hs0
        obtain ⟨i, hi⟩ := hsupp
        have hsi : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
        let t : σ →₀ ℕ := s - Finsupp.single i 1
        have hle : Finsupp.single i 1 ≤ s :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hsi)
        have htadd : t + Finsupp.single i 1 = s := tsub_add_cancel_of_le hle
        have hsum : t.sum (fun _ n => n) + 1 = d := by
          calc
            t.sum (fun _ n => n) + 1 =
                t.sum (fun _ n => n) +
                  (Finsupp.single i 1).sum (fun _ n => n) := by simp
            _ = (t + Finsupp.single i 1).sum (fun _ n => n) := by
              symm
              apply Finsupp.sum_add_index <;> simp
            _ = d := by rw [htadd, hd]
        have htlt : t.sum (fun _ n => n) < d := by omega
        have hdpos : 0 < d := by omega
        have hmono : MvPolynomial.monomial s c =
            MvPolynomial.monomial t c * MvPolynomial.X i := by
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, htadd, mul_one]
        rw [hmono, rightSlice_mul_X] at hzero ⊢
        have hfirst : (rightSlice ψ (MvPolynomial.monomial t c) *
            MvPolynomial.X i).totalDegree < d := by
          by_cases hpart : rightSlice ψ (MvPolynomial.monomial t c) = 0
          · simp [hpart, hdpos]
          · refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
            rw [MvPolynomial.totalDegree_X]
            have hrec := ih (t.sum fun _ n => n) htlt ψ hψ t c hpart rfl
            omega
        have hsecond : (rightSlice (mulXFunctional ψ i)
            (MvPolynomial.monomial t c)).totalDegree < d := by
          exact lt_of_le_of_lt
            (rightSlice_monomial_totalDegree_le (mulXFunctional ψ i) t c) (by omega)
        exact lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _) (max_lt hfirst hsecond)

/-- Functional slices killing constants strictly lower total degree. -/
theorem rightSlice_totalDegree_lt_of_one_eq_zero
    (ψ : MvPolynomial σ k →ₗ[k] k) (hψ : ψ 1 = 0)
    (P : MvPolynomial σ k) (hzero : rightSlice ψ P ≠ 0) :
    (rightSlice ψ P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hzero
  have hDpos : 0 < P.totalDegree := by
    by_contra hD
    have hDz : P.totalDegree = 0 := Nat.eq_zero_of_not_pos hD
    have hPC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hDz
    have : rightSlice ψ P = 0 := by rw [hPC, rightSlice_C, hψ, zero_smul]
    exact hzero this
  have hle : (rightSlice ψ P).totalDegree ≤ P.totalDegree - 1 := by
    conv_lhs => rw [P.as_sum, map_sum]
    apply totalDegree_sum_le P.support
    intro s hs
    by_cases hz : rightSlice ψ
        (MvPolynomial.monomial s (MvPolynomial.coeff s P)) = 0
    · simp [hz]
    · have hlt := rightSlice_monomial_totalDegree_lt_of_one_eq_zero ψ hψ s _ hz
      have hsle := MvPolynomial.le_totalDegree hs
      omega
  omega

/-- Two slices with the same value on constants have the same top-degree component: their
difference is either zero or has strictly smaller total degree. -/
theorem rightSlice_sub_totalDegree_lt_of_apply_one_eq
    (ψ χ : MvPolynomial σ k →ₗ[k] k) (h : ψ 1 = χ 1)
    (P : MvPolynomial σ k)
    (hzero : rightSlice ψ P - rightSlice χ P ≠ 0) :
    (rightSlice ψ P - rightSlice χ P).totalDegree < P.totalDegree := by
  rw [← rightSlice_sub_functional]
  apply rightSlice_totalDegree_lt_of_one_eq_zero (ψ - χ)
  · simpa using sub_eq_zero.mpr h
  · simpa [rightSlice_sub_functional] using hzero

/-- If the slicing functional kills constants and every linear monomial, contraction drops at
least two degrees whenever nonzero. -/
theorem rightSlice_monomial_totalDegree_add_two_le
    (ψ : MvPolynomial σ k →ₗ[k] k) (hψone : ψ 1 = 0)
    (hψX : ∀ i : σ, ψ (MvPolynomial.X i) = 0)
    (s : σ →₀ ℕ) (c : k)
    (hzero : rightSlice ψ (MvPolynomial.monomial s c) ≠ 0) :
    (rightSlice ψ (MvPolynomial.monomial s c)).totalDegree + 2 ≤
      s.sum fun _ n => n := by
  classical
  induction hd : s.sum (fun _ n => n) using Nat.strong_induction_on generalizing s ψ c with
  | h d ih =>
      by_cases hs0 : s = 0
      · subst s
        change rightSlice ψ (MvPolynomial.C c) ≠ 0 at hzero
        rw [rightSlice_C, hψone, zero_smul] at hzero
        exact (hzero rfl).elim
      · have hsupp : s.support.Nonempty := by
          simpa [Finsupp.support_nonempty_iff] using hs0
        obtain ⟨i, hi⟩ := hsupp
        have hsi : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
        let t : σ →₀ ℕ := s - Finsupp.single i 1
        have hle : Finsupp.single i 1 ≤ s :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hsi)
        have htadd : t + Finsupp.single i 1 = s := tsub_add_cancel_of_le hle
        have hsum : t.sum (fun _ n => n) + 1 = d := by
          calc
            t.sum (fun _ n => n) + 1 =
                t.sum (fun _ n => n) +
                  (Finsupp.single i 1).sum (fun _ n => n) := by simp
            _ = (t + Finsupp.single i 1).sum (fun _ n => n) := by
              symm
              apply Finsupp.sum_add_index <;> simp
            _ = d := by rw [htadd, hd]
        have htlt : t.sum (fun _ n => n) < d := by omega
        have hmono : MvPolynomial.monomial s c =
            MvPolynomial.monomial t c * MvPolynomial.X i := by
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, htadd, mul_one]
        rw [hmono, rightSlice_mul_X] at hzero ⊢
        have hd2 : 2 ≤ d := by
          by_contra hd2
          have ht0 : t = 0 := by
            apply Finsupp.ext
            intro a
            have hsum0 : t.sum (fun _ n => n) = 0 := by omega
            have hleSum : t a ≤ t.sum (fun _ n => n) := by
              classical
              simpa using Finsupp.single_le_sum (N := ℕ) t
                (g := fun _ n => n) (fun _ _ => Nat.zero_le _) a
            exact Nat.eq_zero_of_le_zero (hleSum.trans_eq hsum0)
          have hleft : rightSlice ψ (MvPolynomial.monomial 0 c) = 0 := by
            change rightSlice ψ (MvPolynomial.C c) = 0
            rw [rightSlice_C, hψone, zero_smul]
          have hmulOne : mulXFunctional ψ i 1 = 0 := by
            simpa [mulXFunctional, mul_comm] using hψX i
          have hright : rightSlice (mulXFunctional ψ i)
              (MvPolynomial.monomial 0 c) = 0 := by
            change rightSlice (mulXFunctional ψ i) (MvPolynomial.C c) = 0
            rw [rightSlice_C, hmulOne, zero_smul]
          exact hzero (by rw [ht0, hleft, hright]; simp)
        have hfirst : (rightSlice ψ (MvPolynomial.monomial t c) *
            MvPolynomial.X i).totalDegree + 2 ≤ d := by
          by_cases hpart : rightSlice ψ (MvPolynomial.monomial t c) = 0
          · simp [hpart, hd2]
          · have hrec := ih (t.sum fun _ n => n) htlt ψ hψone hψX t c hpart rfl
            have hmul := MvPolynomial.totalDegree_mul
              (rightSlice ψ (MvPolynomial.monomial t c)) (MvPolynomial.X i)
            rw [MvPolynomial.totalDegree_X] at hmul
            omega
        have hmulOne : mulXFunctional ψ i 1 = 0 := by
          simpa [mulXFunctional, mul_comm] using hψX i
        have hsecond : (rightSlice (mulXFunctional ψ i)
            (MvPolynomial.monomial t c)).totalDegree + 2 ≤ d := by
          by_cases hpart : rightSlice (mulXFunctional ψ i)
              (MvPolynomial.monomial t c) = 0
          · simp [hpart, hd2]
          · have hdrop := rightSlice_monomial_totalDegree_lt_of_one_eq_zero
              (mulXFunctional ψ i) hmulOne t c hpart
            omega
        have hadd := MvPolynomial.totalDegree_add
          (rightSlice ψ (MvPolynomial.monomial t c) * MvPolynomial.X i)
          (rightSlice (mulXFunctional ψ i) (MvPolynomial.monomial t c))
        omega

/-- Global two-degree drop for functionals annihilating constants and all linear monomials. -/
theorem rightSlice_totalDegree_add_two_le
    (ψ : MvPolynomial σ k →ₗ[k] k) (hψone : ψ 1 = 0)
    (hψX : ∀ i : σ, ψ (MvPolynomial.X i) = 0)
    (P : MvPolynomial σ k) (hzero : rightSlice ψ P ≠ 0) :
    (rightSlice ψ P).totalDegree + 2 ≤ P.totalDegree := by
  classical
  have hD2 : 2 ≤ P.totalDegree := by
    by_contra hD2
    have hterms : ∀ s ∈ P.support,
        rightSlice ψ (MvPolynomial.monomial s (MvPolynomial.coeff s P)) = 0 := by
      intro s hs
      by_contra hs0
      have htwo := rightSlice_monomial_totalDegree_add_two_le ψ hψone hψX s _ hs0
      have hsle := MvPolynomial.le_totalDegree hs
      omega
    apply hzero
    conv_lhs => rw [P.as_sum, map_sum]
    exact Finset.sum_eq_zero hterms
  have hle : (rightSlice ψ P).totalDegree ≤ P.totalDegree - 2 := by
    conv_lhs => rw [P.as_sum, map_sum]
    apply totalDegree_sum_le P.support
    intro s hs
    by_cases hz : rightSlice ψ
        (MvPolynomial.monomial s (MvPolynomial.coeff s P)) = 0
    · simp [hz]
    · have htwo := rightSlice_monomial_totalDegree_add_two_le ψ hψone hψX s _ hz
      have hsle := MvPolynomial.le_totalDegree hs
      omega
  omega

/-- Slices agreeing on constants and generators differ only two or more degrees below the top. -/
theorem rightSlice_sub_totalDegree_add_two_le_of_apply_one_X_eq
    (ψ χ : MvPolynomial σ k →ₗ[k] k)
    (hone : ψ 1 = χ 1) (hX : ∀ i : σ, ψ (MvPolynomial.X i) = χ (MvPolynomial.X i))
    (P : MvPolynomial σ k)
    (hzero : rightSlice ψ P - rightSlice χ P ≠ 0) :
    (rightSlice ψ P - rightSlice χ P).totalDegree + 2 ≤ P.totalDegree := by
  rw [← rightSlice_sub_functional]
  apply rightSlice_totalDegree_add_two_le (ψ - χ)
  · simpa using sub_eq_zero.mpr hone
  · intro i
    simpa using sub_eq_zero.mpr (hX i)
  · simpa [rightSlice_sub_functional] using hzero

/-- Linear coefficient functional, equivalently first derivative at the additive identity. -/
noncomputable def linearCoefficient (j : σ) : MvPolynomial σ k →ₗ[k] k where
  toFun P := MvPolynomial.coeff (Finsupp.single j 1) P
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] theorem linearCoefficient_one (j : σ) : linearCoefficient (k := k) j 1 = 0 := by
  classical
  have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h
    have hj := congrArg (fun f : σ →₀ ℕ => f j) h
    simp at hj
  change MvPolynomial.coeff (Finsupp.single j 1)
    (MvPolynomial.C 1 : MvPolynomial σ k) = 0
  rw [MvPolynomial.coeff_C]
  simp [hne]

@[simp] theorem linearCoefficient_X [DecidableEq σ] (j i : σ) :
    linearCoefficient (k := k) j (MvPolynomial.X i) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst i
    simp [linearCoefficient]
  · simp [linearCoefficient, h]

@[simp] theorem tensorEquivSum_tmul (P Q : MvPolynomial σ k) :
    (MvPolynomial.tensorEquivSum k σ σ k) (P ⊗ₜ[k] Q) =
      AdditivePolynomialHopf.left P * AdditivePolynomialHopf.right Q := by
  let inclL : MvPolynomial σ k →ₐ[k]
      MvPolynomial σ k ⊗[k] MvPolynomial σ k := Algebra.TensorProduct.includeLeft
  let inclR : MvPolynomial σ k →ₐ[k]
      MvPolynomial σ k ⊗[k] MvPolynomial σ k := Algebra.TensorProduct.includeRight
  have hleft : (MvPolynomial.tensorEquivSum k σ σ k).toAlgHom.comp inclL =
      AdditivePolynomialHopf.left := by
    ext i
    simp [inclL, AdditivePolynomialHopf.left]
  have hright : (MvPolynomial.tensorEquivSum k σ σ k).toAlgHom.comp inclR =
      AdditivePolynomialHopf.right := by
    ext i
    simp [inclR, AdditivePolynomialHopf.right]
  calc
    (MvPolynomial.tensorEquivSum k σ σ k) (P ⊗ₜ[k] Q) =
        (MvPolynomial.tensorEquivSum k σ σ k)
          (inclL P * inclR Q) := by
            congr 1
            change P ⊗ₜ[k] Q = (P ⊗ₜ[k] 1) * (1 ⊗ₜ[k] Q)
            simp
    _ = (MvPolynomial.tensorEquivSum k σ σ k)
          (inclL P) *
        (MvPolynomial.tensorEquivSum k σ σ k)
          (inclR Q) := by rw [map_mul]
    _ = AdditivePolynomialHopf.left P * AdditivePolynomialHopf.right Q := by
      have hl := DFunLike.congr_fun hleft P
      have hr := DFunLike.congr_fun hright Q
      change (MvPolynomial.tensorEquivSum k σ σ k)
          (inclL P) = AdditivePolynomialHopf.left P at hl
      change (MvPolynomial.tensorEquivSum k σ σ k)
          (inclR Q) = AdditivePolynomialHopf.right Q at hr
      rw [hl, hr]

/-- Under the tensor/product-polynomial equivalence, first-order evaluation of the right
variables is contraction against the linear coefficient functional. -/
theorem rightPartialAtZero_tensorEquiv (j : σ)
    (t : MvPolynomial σ k ⊗[k] MvPolynomial σ k) :
    AdditivePolynomialHopf.rightPartialAtZero j
        ((MvPolynomial.tensorEquivSum k σ σ k) t) =
      tensorRightSlice (linearCoefficient (k := k) j) t := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul P Q =>
      rw [tensorEquivSum_tmul, AdditivePolynomialHopf.rightPartialAtZero_mul,
        AdditivePolynomialHopf.rightPartialAtZero_left,
        AdditivePolynomialHopf.rightZero_left,
        AdditivePolynomialHopf.rightPartialAtZero_right,
        AdditivePolynomialHopf.rightZero_right]
      simp [tensorRightSlice, linearCoefficient, Algebra.smul_def, mul_comm]

/-- Contraction of additive comultiplication against the linear coefficient functional is the
ordinary partial derivative. -/
@[simp] theorem rightSlice_linearCoefficient (j : σ) (P : MvPolynomial σ k) :
    rightSlice (linearCoefficient (k := k) j) P = MvPolynomial.pderiv j P := by
  have h := rightPartialAtZero_tensorEquiv (k := k) j
    ((MvPolynomial.tensorEquivSum k σ σ k).symm
      (AdditivePolynomialHopf.addComul P))
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm.trans (AdditivePolynomialHopf.rightPartialAtZero_addComul j P)

end
end AdditivePolynomialCoalgebraFiltration
end GaloisForLFunctions.HTGeometry
