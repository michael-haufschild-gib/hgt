import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-!
# The shift-difference operator on polynomials is surjective

For a nonzero step `a` the operator

```text
(Δ_a p)(X) = p(X + a) - p(X)
```

is a surjective linear endomorphism of `ℂ[X]`.  The witness is the falling-factorial basis of the
step,

```text
F_k(X) = ∏_{i < k} (X - i a),      Δ_a F_{k+1} = (k+1) a · F_k,
```

which is monic of degree `k`, so `Δ_a` hits every `F_k` and therefore, by downward induction on the
degree, every polynomial.

This is the discrete integration used to normalize a difference equation: a rational correction with
a prescribed polynomial difference always exists.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The falling-factorial basis of a step -/

/-- The falling-factorial polynomial of the step `a`. -/
def fallPoly (a : ℂ) (k : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range k, (X - C ((i : ℂ) * a))

@[simp] theorem fallPoly_zero (a : ℂ) : fallPoly a 0 = 1 := by
  rw [fallPoly, Finset.range_zero, Finset.prod_empty]

theorem fallPoly_succ (a : ℂ) (k : ℕ) :
    fallPoly a (k + 1) = fallPoly a k * (X - C ((k : ℂ) * a)) := by
  rw [fallPoly, fallPoly, Finset.prod_range_succ]

theorem monic_fallPoly (a : ℂ) (k : ℕ) : (fallPoly a k).Monic := by
  rw [fallPoly]
  exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem natDegree_fallPoly (a : ℂ) (k : ℕ) : (fallPoly a k).natDegree = k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [fallPoly_succ, (monic_fallPoly a n).natDegree_mul (monic_X_sub_C _), ih,
        natDegree_X_sub_C]

theorem coeff_fallPoly_self (a : ℂ) (k : ℕ) : (fallPoly a k).coeff k = 1 := by
  have := (monic_fallPoly a k).coeff_natDegree
  rwa [natDegree_fallPoly] at this

theorem coeff_fallPoly_eq_zero (a : ℂ) {k m : ℕ} (h : k < m) : (fallPoly a k).coeff m = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_fallPoly]; exact h)

/-! ### The shift difference of the basis -/

theorem fallPoly_comp_shift (a : ℂ) (k : ℕ) :
    (fallPoly a (k + 1)).comp (X + C a) = (X + C a) * fallPoly a k := by
  rw [fallPoly, Polynomial.prod_comp]
  have hterm : ∀ i : ℕ, (X - C ((i : ℂ) * a)).comp (X + C a)
      = X - C (((i : ℂ) - 1) * a) := by
    intro i
    simp only [sub_comp, X_comp, mul_comp, C_comp, map_mul, map_sub, map_one]
    ring
  rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_range_succ']
  have hzero : X - C ((((0 : ℕ) : ℂ) - 1) * a) = X + C a := by
    rw [show (((0 : ℕ) : ℂ) - 1) * a = -a by push_cast; ring, map_neg]
    ring
  have hshift : ∀ i ∈ Finset.range k,
      X - C ((((i + 1 : ℕ) : ℂ) - 1) * a) = X - C ((i : ℂ) * a) := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl hshift, hzero, fallPoly]
  ring

/-- **The shift difference of the falling-factorial basis.** -/
theorem shiftDiff_fallPoly (a : ℂ) (k : ℕ) :
    (fallPoly a (k + 1)).comp (X + C a) - fallPoly a (k + 1)
      = C (((k : ℂ) + 1) * a) * fallPoly a k := by
  rw [fallPoly_comp_shift, fallPoly_succ]
  have : (X + C a) * fallPoly a k - fallPoly a k * (X - C ((k : ℂ) * a))
      = fallPoly a k * (C a + C ((k : ℂ) * a)) := by ring
  rw [this, ← map_add]
  have hc : a + (k : ℂ) * a = ((k : ℂ) + 1) * a := by ring
  rw [hc]
  ring

/-! ### The operator and its surjectivity -/

/-- The shift-difference operator `p ↦ p(X + a) - p`. -/
def shiftDiffPoly (a : ℂ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun p := p.comp (X + C a) - p
  map_add' p q := by
    simp only [add_comp]
    ring
  map_smul' c p := by
    simp only [RingHom.id_apply, smul_eq_C_mul, mul_comp, C_comp]
    ring

@[simp] theorem shiftDiffPoly_apply (a : ℂ) (p : Polynomial ℂ) :
    shiftDiffPoly a p = p.comp (X + C a) - p := rfl

theorem fallPoly_mem_range {a : ℂ} (ha : a ≠ 0) (k : ℕ) :
    fallPoly a k ∈ LinearMap.range (shiftDiffPoly a) := by
  have hne : ((k : ℂ) + 1) * a ≠ 0 := by
    refine mul_ne_zero ?_ ha
    intro hcon
    have hre : ((k : ℕ) : ℝ) + 1 = 0 := by
      exact_mod_cast congrArg Complex.re hcon
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine ⟨(((k : ℂ) + 1) * a)⁻¹ • fallPoly a (k + 1), ?_⟩
  rw [map_smul, shiftDiffPoly_apply, shiftDiff_fallPoly, smul_eq_C_mul, ← mul_assoc,
    ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

theorem mem_range_of_degree_lt {a : ℂ} (ha : a ≠ 0) :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.degree < (n : WithBot ℕ) →
      p ∈ LinearMap.range (shiftDiffPoly a) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hp0 : p = 0 := by
        rw [← degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hp)
      rw [hp0]
      exact Submodule.zero_mem _
  | succ n ih =>
      intro p hp
      set c : ℂ := p.coeff n with hc
      set q : Polynomial ℂ := p - C c * fallPoly a n with hq
      have hqdeg : q.degree < (n : WithBot ℕ) := by
        refine (degree_lt_iff_coeff_zero q n).mpr fun m hm => ?_
        have hmn : n ≤ m := by exact_mod_cast hm
        rw [hq, coeff_sub, coeff_C_mul]
        rcases eq_or_lt_of_le hmn with rfl | hlt
        · rw [coeff_fallPoly_self, mul_one, ← hc, sub_self]
        · have hpm : p.coeff m = 0 := by
            refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp ?_)
            exact_mod_cast Nat.succ_le_of_lt hlt
          rw [hpm, coeff_fallPoly_eq_zero a hlt, mul_zero, sub_zero]
      have hqmem := ih q hqdeg
      have hfmem : C c * fallPoly a n ∈ LinearMap.range (shiftDiffPoly a) := by
        rw [← smul_eq_C_mul]
        exact Submodule.smul_mem _ c (fallPoly_mem_range ha n)
      have hsum := Submodule.add_mem _ hqmem hfmem
      rw [hq] at hsum
      simpa using hsum

/-- **The shift-difference operator is surjective.**  Every polynomial is the shift difference of a
polynomial, for every nonzero step. -/
theorem surjective_shiftDiffPoly {a : ℂ} (ha : a ≠ 0) :
    Function.Surjective (shiftDiffPoly a) := by
  intro p
  obtain ⟨q, hq⟩ := mem_range_of_degree_lt ha (p.natDegree + 1) p
    (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self _))
  exact ⟨q, hq⟩

/-- **Discrete integration of a polynomial.**  For a nonzero step there is a polynomial with any
prescribed shift difference. -/
theorem exists_shiftDiff_eq {a : ℂ} (ha : a ≠ 0) (p : Polynomial ℂ) :
    ∃ q : Polynomial ℂ, q.comp (X + C a) - q = p := by
  obtain ⟨q, hq⟩ := surjective_shiftDiffPoly ha p
  exact ⟨q, hq⟩

end

end GaloisForLFunctions.HTGeometry
