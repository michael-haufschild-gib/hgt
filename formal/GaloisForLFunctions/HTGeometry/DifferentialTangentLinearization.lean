import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.DualNumber

/-!
# The linearisation of a differential polynomial, and why tangent spaces are linear

Evaluating a differential polynomial at a dual-number point `p + εX`, with `ε` a constant square-zero
element, splits into the value at `p` and an `ε`-part which is the **linearisation**

`dF_p(X) = ∑_v (∂_v F)(p) · δ^{v.2} X_{v.1}`,

a *linear* differential polynomial in `X` with coefficients in the base.  This is the reason
tangent spaces of differential algebraic sets are cut out by linear differential operators, and so
the reason their scalar stabilisers are finite dimensional over the constants: a nonlinear
differential constraint on a set does not survive to its tangent space, a linear one does.

* `dualDifferential` — the derivation of the dual numbers extending a given one;
* `differentialJet_dual` — jets act componentwise on dual numbers;
* `fst_differentialPolynomialEvalOver_dual` — the `ε`-free part is the value at `p`;
* `snd_differentialPolynomialEvalOver_dual` — **the linearisation formula**;
* `exists_linear_form_snd_evalOver_dual` — the `ε`-part is a linear differential form in `X`;
* `exists_scalar_linear_form` — for one indeterminate, `dF_p(X) = ∑_{i ≤ n} (∂_i F)(p) · δ^i X`;
* `exists_nonzero_linear_relation_of_tangent` — **a set of tangent directions lies in the solution
  set of one nonzero scalar linear differential operator**.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

/-! ### The dual numbers as a differential ring -/

/-- A dual number from its two components. -/
def dualMk (a b : C) : DualNumber C := TrivSqZeroExt.inl a + TrivSqZeroExt.inr b

omit [Differential C] in
@[simp] theorem dualMk_fst (a b : C) : (dualMk a b).fst = a := by
  simp [dualMk]

omit [Differential C] in
@[simp] theorem dualMk_snd (a b : C) : (dualMk a b).snd = b := by
  simp [dualMk]

omit [Differential C] in
theorem dualMk_eq (x : DualNumber C) : dualMk x.fst x.snd = x := by
  apply TrivSqZeroExt.ext <;> simp

/-- The derivation of the dual numbers extending a derivation of the base. -/
def dualDifferentialDeriv : Derivation ℤ (DualNumber C) (DualNumber C) where
  toLinearMap :=
    { toFun := fun x => dualMk (Differential.deriv x.fst) (Differential.deriv x.snd)
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext <;>
          simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
      map_smul' := by
        intro n x
        apply TrivSqZeroExt.ext <;>
          simp [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, dualMk, mul_comm] }
  map_one_eq_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  leibniz' := by
    intro x y
    apply TrivSqZeroExt.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, dualMk_fst, dualMk_snd, smul_eq_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_mul, op_smul_eq_mul, map_add, Derivation.leibniz]
    all_goals ring

instance dualDifferential : Differential (DualNumber C) := ⟨dualDifferentialDeriv⟩

@[simp] theorem deriv_dual_fst (x : DualNumber C) :
    (Differential.deriv x).fst = Differential.deriv x.fst := by
  show (dualMk (Differential.deriv x.fst) (Differential.deriv x.snd)).fst = _
  simp

@[simp] theorem deriv_dual_snd (x : DualNumber C) :
    (Differential.deriv x).snd = Differential.deriv x.snd := by
  show (dualMk (Differential.deriv x.fst) (Differential.deriv x.snd)).snd = _
  simp

instance dualDifferentialAlgebra : DifferentialAlgebra C (DualNumber C) := by
  refine ⟨fun a => ?_⟩
  apply TrivSqZeroExt.ext <;>
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem differentialJet_dual (n : ℕ) (x : DualNumber C) :
    differentialJet n x = dualMk (differentialJet n x.fst) (differentialJet n x.snd) := by
  induction n with
  | zero => simp [dualMk_eq]
  | succ n ih =>
      rw [differentialJet_succ, ih]
      apply TrivSqZeroExt.ext <;> simp [differentialJet_succ]

/-! ### The linearisation -/

variable {ι : Type*}

/-- The dual-number point `p + εX`. -/
def dualPoint (p X : ι → C) : ι → DualNumber C := fun i => dualMk (p i) (X i)

omit [Differential C] in
@[simp] theorem dualPoint_fst (p X : ι → C) (i : ι) : (dualPoint p X i).fst = p i := by
  simp [dualPoint]

omit [Differential C] in
@[simp] theorem dualPoint_snd (p X : ι → C) (i : ι) : (dualPoint p X i).snd = X i := by
  simp [dualPoint]

theorem evalOver_dual_X (p X : ι → C) (v : ι × ℕ) :
    differentialPolynomialEvalOver (K := C) (dualPoint p X) (MvPolynomial.X v)
      = dualMk (differentialJet v.2 (p v.1)) (differentialJet v.2 (X v.1)) := by
  rw [differentialPolynomialEvalOver_X, differentialJet_dual]
  simp

/-- **The `ε`-free part of a dual-number evaluation is the value at the base point.** -/
theorem fst_differentialPolynomialEvalOver_dual (p X : ι → C) (F : DifferentialPolynomial ι C) :
    (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).fst
      = differentialPolynomialEvalOver (K := C) p F := by
  have hext : (TrivSqZeroExt.fstHom C C C).comp
      (differentialPolynomialEvalOver (K := C) (dualPoint p X))
      = differentialPolynomialEvalOver (K := C) p := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, evalOver_dual_X, differentialPolynomialEvalOver_X]
    show (dualMk (differentialJet v.2 (p v.1)) (differentialJet v.2 (X v.1))).fst = _
    simp
  exact congrArg (fun φ : DifferentialPolynomial ι C →ₐ[C] C => φ F) hext

/-! ### The linearisation formula -/

/-- The linearisation sum does not see indices outside the variables of the polynomial. -/
theorem sum_pderiv_eval_congr (p X : ι → C) (F : DifferentialPolynomial ι C)
    {s t : Finset (ι × ℕ)} (hst : s ⊆ t) (hF : F.vars ⊆ s) :
    ∑ v ∈ s, differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v F)
        * differentialJet v.2 (X v.1)
      = ∑ v ∈ t, differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v F)
        * differentialJet v.2 (X v.1) := by
  refine Finset.sum_subset hst fun v _ hvs => ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hcon => hvs (hF hcon)), map_zero, zero_mul]

/-- **The linearisation formula.**  The `ε`-part of the value at `p + εX` is the linear differential
form `∑_v (∂_v F)(p) · δ^{v.2} X_{v.1}`. -/
theorem snd_differentialPolynomialEvalOver_dual (p X : ι → C) :
    ∀ (F : DifferentialPolynomial ι C) (s : Finset (ι × ℕ)), F.vars ⊆ s →
      (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).snd
        = ∑ v ∈ s, differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v F)
            * differentialJet v.2 (X v.1) := by
  classical
  intro F
  induction F using MvPolynomial.induction_on with
  | C a =>
      intro s _
      rw [differentialPolynomialEvalOver_C]
      have hz : (algebraMap C (DualNumber C) a).snd = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [hz]
      refine (Finset.sum_eq_zero fun v _ => ?_).symm
      rw [MvPolynomial.pderiv_C, map_zero, zero_mul]
  | add q r hq hr =>
      intro s hs
      set t : Finset (ι × ℕ) := s ∪ q.vars ∪ r.vars with ht
      have hst : s ⊆ t := by
        intro v hv
        simp [ht, hv]
      have hqt : q.vars ⊆ t := by
        intro v hv
        simp [ht, hv]
      have hrt : r.vars ⊆ t := by
        intro v hv
        simp [ht, hv]
      rw [sum_pderiv_eval_congr p X (q + r) hst hs, map_add, TrivSqZeroExt.snd_add,
        hq t hqt, hr t hrt, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_add, map_add, add_mul]
  | mul_X q n hq =>
      intro s hs
      set t : Finset (ι × ℕ) := s ∪ q.vars ∪ {n} with ht
      have hst : s ⊆ t := by
        intro v hv
        simp [ht, hv]
      have hqt : q.vars ⊆ t := by
        intro v hv
        simp [ht, hv]
      have hnt : n ∈ t := by simp [ht]
      rw [sum_pderiv_eval_congr p X (q * MvPolynomial.X n) hst hs, map_mul,
        TrivSqZeroExt.snd_mul, op_smul_eq_mul, smul_eq_mul,
        fst_differentialPolynomialEvalOver_dual, evalOver_dual_X, dualMk_fst, dualMk_snd,
        hq t hqt]
      have hterm : ∀ v ∈ t,
          differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v (q * MvPolynomial.X n))
              * differentialJet v.2 (X v.1)
            = (if v = n then differentialPolynomialEvalOver (K := C) p q
                  * differentialJet n.2 (X n.1) else 0)
              + differentialJet n.2 (p n.1)
                * (differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v q)
                    * differentialJet v.2 (X v.1)) := by
        intro v _
        rw [(MvPolynomial.pderiv v).leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul,
          map_add, map_mul, map_mul, differentialPolynomialEvalOver_X]
        by_cases hv : v = n
        · subst hv
          rw [if_pos rfl]
          simp only [Pi.single_eq_same, map_one, mul_one]
          ring
        · rw [if_neg hv]
          rw [Pi.single_eq_of_ne (Ne.symm hv), map_zero, mul_zero, zero_add]
          ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hone : ∑ v ∈ t, (if v = n then differentialPolynomialEvalOver (K := C) p q
            * differentialJet n.2 (X n.1) else 0)
          = differentialPolynomialEvalOver (K := C) p q * differentialJet n.2 (X n.1) := by
        rw [Finset.sum_eq_single_of_mem n hnt]
        · rw [if_pos rfl]
        · intro v _ hv
          rw [if_neg hv]
      rw [hone]
      ring

/-- **The `ε`-part is a linear differential form in the perturbation.** -/
theorem exists_linear_form_snd_evalOver_dual (p : ι → C) (F : DifferentialPolynomial ι C) :
    ∃ (s : Finset (ι × ℕ)) (c : ι × ℕ → C), ∀ X : ι → C,
      (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).snd
        = ∑ v ∈ s, c v * differentialJet v.2 (X v.1) :=
  ⟨F.vars, fun v => differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v F),
    fun X => snd_differentialPolynomialEvalOver_dual p X F F.vars (le_refl _)⟩

/-! ### The scalar case, in operator form -/

/-- **The scalar linearisation is a linear differential operator.**  For one differential
indeterminate the `ε`-part of the value at `p + εX` is `∑_{i ≤ n} L i · δ^i X`, with
`L i = (∂_{i}F)(p)`. -/
theorem exists_scalar_linear_form (p : Unit → C) (F : DifferentialPolynomial Unit C) :
    ∃ (n : ℕ), (∀ i, n < i → MvPolynomial.pderiv (((), i) : Unit × ℕ) F = 0) ∧ ∀ X : Unit → C,
      (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).snd
        = ∑ i ∈ Finset.range (n + 1),
            differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv ((), i) F)
              * differentialJet i (X ()) := by
  classical
  set n : ℕ := (F.vars.image Prod.snd).sup id with hn
  have hle : ∀ v ∈ F.vars, v.2 ≤ n := by
    intro v hv
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd hv)
  set t : Finset (Unit × ℕ) :=
    (Finset.range (n + 1)).image (fun i => (((), i) : Unit × ℕ)) with hts
  have hinj : Set.InjOn (fun i => (((), i) : Unit × ℕ)) (Finset.range (n + 1)) := by
    intro i _ j _ hij
    exact congrArg Prod.snd hij
  have hsub : F.vars ⊆ t := by
    intro v hv
    refine Finset.mem_image.mpr ⟨v.2, Finset.mem_range.mpr (Nat.lt_succ_of_le (hle v hv)), ?_⟩
    rcases v with ⟨u, k⟩
    cases u
    rfl
  refine ⟨n, fun i hi => ?_, fun X => ?_⟩
  · refine MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hmem => ?_
    exact absurd (hle _ hmem) (by omega)
  · rw [snd_differentialPolynomialEvalOver_dual p X F t hsub, hts,
      Finset.sum_image (fun i hi j hj hij => hinj hi hj hij)]

/-- **A nonzero linearisation gives a nonzero linear differential operator.** -/
theorem exists_scalar_linear_form_ne_zero (p : Unit → C) (F : DifferentialPolynomial Unit C)
    {X₀ : Unit → C}
    (hX₀ : (differentialPolynomialEvalOver (K := C) (dualPoint p X₀) F).snd ≠ 0) :
    ∃ (n : ℕ) (i₀ : ℕ), i₀ ∈ Finset.range (n + 1) ∧
      differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv ((), i₀) F) ≠ 0 ∧
      ∀ X : Unit → C,
        (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).snd
          = ∑ i ∈ Finset.range (n + 1),
              differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv ((), i) F)
                * differentialJet i (X ()) := by
  obtain ⟨n, -, hform⟩ := exists_scalar_linear_form p F
  by_cases hall : ∀ i ∈ Finset.range (n + 1),
      differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv ((), i) F) = 0
  · exact absurd (by
      rw [hform X₀]
      exact Finset.sum_eq_zero fun i hi => by rw [hall i hi, zero_mul]) hX₀
  · push Not at hall
    obtain ⟨i₀, hi₀mem, hi₀⟩ := hall
    exact ⟨n, i₀, hi₀mem, hi₀, hform⟩

/-- **The tangent relation, in the shape a linear jet operator takes.**  If a differential
polynomial vanishes at every dual point `p + εX` with `X` in a set `T`, and its linearisation at `p`
is not identically zero, then `T` lies in the solution set of one nonzero scalar linear differential
operator. -/
theorem exists_nonzero_linear_relation_of_tangent
    (p : Unit → C) (F : DifferentialPolynomial Unit C)
    {i₁ : ℕ} (hi₁ : differentialPolynomialEvalOver (K := C) p
      (MvPolynomial.pderiv (((), i₁) : Unit × ℕ) F) ≠ 0)
    (T : Set (Unit → C))
    (hT : ∀ X ∈ T, differentialPolynomialEvalOver (K := C) (dualPoint p X) F = 0) :
    ∃ (n : ℕ) (L : ℕ → C) (i₀ : ℕ), i₀ ∈ Finset.range (n + 1) ∧ L i₀ ≠ 0 ∧
      ∀ X ∈ T, ∑ i ∈ Finset.range (n + 1), L i * differentialJet i (X ()) = 0 := by
  obtain ⟨n, hvanish, hform⟩ := exists_scalar_linear_form p F
  have hle : i₁ ≤ n := by
    by_contra hcon
    exact hi₁ (by rw [hvanish i₁ (by omega), map_zero])
  refine ⟨n, fun i => differentialPolynomialEvalOver (K := C) p
      (MvPolynomial.pderiv (((), i) : Unit × ℕ) F), i₁,
    Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hi₁, fun X hX => ?_⟩
  rw [← hform X, hT X hX]
  simp [TrivSqZeroExt.snd_zero]

end

end GaloisForLFunctions.HTGeometry
