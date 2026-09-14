import GaloisForLFunctions.RHTower.ArithmeticFunctionScalarEvaluation
import GaloisForLFunctions.HTGeometry.FiniteAbscissaDirichletUpperEnd
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Quotient.Operations


/-!
# Degree-zero Mellin-twisted relations on arithmetic sources

Reuse the literal coefficient shift `T_s f(n)=n^(-s) f(n)` on the Dirichlet
convolution algebra. For `Re(s) != 0`, every family with coefficient one zero
is a single relation `T_s(u)*v-v*u`. The relation ideal is the augmentation
ideal, and its quotient is canonically `ℂ`.

The explicit primitive is `f(n)/(n^(-s)-1)`; at index one its value is zero.
For `Re(s)>0` its norm is bounded coefficientwise by
`norm(f(n))/(1-2^(-Re(s)))`. It therefore preserves every point of absolute
Dirichlet convergence and the finite-abscissa source algebra. Scalar linear
readouts invariant under the shift read only coefficient one, also on that
analytic source algebra.

This audits the ordinary-ring degree-zero relation in Example 4.25(1) of
Sun, arXiv:2609.04660v1. It does not use higher equivariant constructions or
identify a zeta zero with a quotient class. Higher homology, different
bimodules, and domains not preserved by this primitive are not classified.
The result excludes this specific proposed receiver; it is not a new RH route.
-/

noncomputable section
namespace RHTower.ArithmeticTwistedBoundary

abbrev A := ArithmeticFunction ℂ

abbrev twist := GaloisForLFunctions.HTGeometry.dirichletShift

@[simp] theorem twist_apply (s : ℂ) (f : A) (n : ℕ) :
    twist s f n = (n : ℂ) ^ (-s) * f n := rfl

@[simp] theorem twist_one_coefficient (s : ℂ) (f : A) : twist s f 1 = f 1 := by
  rw [twist_apply, Nat.cast_one, Complex.one_cpow, one_mul]

def twistHom (s : ℂ) : A →ₐ[ℂ] A where
  toFun := twist s
  map_zero' := by ext n; simp
  map_add' := GaloisForLFunctions.HTGeometry.dirichletShift_add s
  map_one' := by
    ext n
    by_cases hn : n = 1
    · subst n; simp [GaloisForLFunctions.HTGeometry.cpowWeight]
    · simp [ArithmeticFunction.one_apply_ne hn]
  map_mul' := GaloisForLFunctions.HTGeometry.dirichletShift_mul s
  commutes' c := by
    ext n
    by_cases hn : n = 1
    · subst n; simp [GaloisForLFunctions.HTGeometry.cpowWeight]
    · simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.one_apply_ne hn]

theorem twist_neg_twist (s : ℂ) (f : A) : twist (-s) (twist s f) = f := by
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n; simp only [ArithmeticFunction.map_zero]
  · simp only [twist_apply, neg_neg, ← mul_assoc]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_neg_cancel,
      Complex.cpow_zero, one_mul]

def twistEquiv (s : ℂ) : A ≃ₐ[ℂ] A where
  toFun := twist s
  invFun := twist (-s)
  left_inv := twist_neg_twist s
  right_inv f := by simpa only [neg_neg] using twist_neg_twist (-s) f
  map_mul' := (twistHom s).map_mul
  map_add' := (twistHom s).map_add
  commutes' := (twistHom s).commutes

theorem nat_cpow_ne_one {s : ℂ} (hs : s.re ≠ 0) {n : ℕ} (hn : 1 < n) :
    (n : ℂ) ^ (-s) ≠ 1 := by
  intro h
  have heq := congrArg norm h
  rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn), norm_one] at heq
  have hbase : (n : ℝ) = 1 :=
    (Real.rpow_left_inj (Nat.cast_nonneg n) zero_le_one
      (show (-s).re ≠ 0 from neg_ne_zero.mpr hs)).mp
        (heq.trans (Real.one_rpow _).symm)
  apply (Nat.ne_of_gt hn)
  exact_mod_cast hbase

def primitive (s : ℂ) (f : A) : A :=
  ⟨fun n => f n / ((n : ℂ) ^ (-s) - 1), by simp⟩

@[simp] theorem primitive_apply (s : ℂ) (f : A) (n : ℕ) :
    primitive s f n = f n / ((n : ℂ) ^ (-s) - 1) := rfl

theorem twist_primitive_sub {s : ℂ} (hs : s.re ≠ 0) (f : A) :
    twist s (primitive s f) - primitive s f =
      f - algebraMap ℂ A (f 1) := by
  apply ArithmeticFunction.ext
  intro n
  by_cases hn0 : n = 0
  · subst n; simp only [ArithmeticFunction.map_zero]
  by_cases hn1 : n = 1
  · subst n
    change twist s (primitive s f) 1 - primitive s f 1 =
      f 1 - (algebraMap ℂ A (f 1)) 1
    rw [twist_one_coefficient, sub_self, ArithmeticFunction.algebraMap_apply_one]
    exact (sub_self _).symm
  change (n : ℂ) ^ (-s) * (f n / ((n : ℂ) ^ (-s) - 1)) -
    f n / ((n : ℂ) ^ (-s) - 1) = f n - (algebraMap ℂ A (f 1)) n
  rw [← sub_one_mul, mul_div_cancel₀ _ (sub_ne_zero.mpr (nat_cpow_ne_one hs (by omega)))]
  simp only [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
    ArithmeticFunction.one_apply_ne hn1, smul_zero, sub_zero]

def boundaryIdeal (s : ℂ) : Ideal A :=
  Ideal.span {v | ∃ f g : A, v = twist s f * g - g * f}

theorem boundaryIdeal_eq_ker {s : ℂ} (hs : s.re ≠ 0) :
    boundaryIdeal s = RingHom.ker arithmeticFunctionAugmentation.toRingHom := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro v ⟨f,g,rfl⟩
    change (twist s f * g) 1 - (g * f) 1 = 0
    simp only [ArithmeticFunction.mul_apply_one, twist_one_coefficient]
    exact sub_eq_zero.mpr (mul_comm _ _)
  · intro f hf
    have hf1 : f 1 = 0 := hf
    have heq := twist_primitive_sub hs f
    rw [hf1, map_zero, sub_zero] at heq
    apply Ideal.subset_span
    exact ⟨primitive s f, 1, by simpa only [mul_one, one_mul] using heq.symm⟩

def boundaryQuotientEquiv {s : ℂ} (hs : s.re ≠ 0) : (A ⧸ boundaryIdeal s) ≃ₐ[ℂ] ℂ := by
  rw [boundaryIdeal_eq_ker hs]
  apply Ideal.quotientKerAlgEquivOfSurjective
  intro c
  exact ⟨algebraMap ℂ A c, arithmeticFunctionAugmentation.commutes c⟩

theorem invariant_linear_eval {s : ℂ} (hs : s.re ≠ 0) (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ f, τ (twist s f) = τ f) (f : A) : τ f = f 1 * τ 1 := by
  have h := congrArg τ (twist_primitive_sub hs f)
  rw [map_sub, hτ, sub_self, map_sub] at h
  rw [sub_eq_zero.mp h.symm, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]

/-- The coefficient inverse is bounded throughout the strict right half-plane. -/
theorem norm_primitive_le {s : ℂ} (hs : 0 < s.re) (f : A) (n : ℕ) :
    ‖primitive s f n‖ ≤ ‖f n‖ / (1 - (2 : ℝ) ^ (-s.re)) := by
  have hd : 0 < 1 - (2 : ℝ) ^ (-s.re) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hs))
  by_cases hn0 : n = 0
  · subst n; simp only [ArithmeticFunction.map_zero, norm_zero, zero_div, le_refl]
  by_cases hn1 : n = 1
  · subst n
    simp only [primitive_apply, Nat.cast_one, Complex.one_cpow, sub_self, div_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) hd.le
  have hn : 1 < n := by omega
  have hw : ‖(n : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn), Complex.neg_re]
    exact Real.rpow_le_rpow_of_nonpos zero_lt_two (by exact_mod_cast hn)
      (neg_nonpos.mpr hs.le)
  have hden : 1 - (2 : ℝ) ^ (-s.re) ≤ ‖(n : ℂ) ^ (-s) - 1‖ := by
    calc
      _ ≤ 1 - ‖(n : ℂ) ^ (-s)‖ := sub_le_sub_left hw 1
      _ ≤ _ := by simpa only [norm_one, norm_sub_rev] using
        (norm_sub_norm_le (1 : ℂ) ((n : ℂ) ^ (-s)))
  rw [primitive_apply, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hd hden

/-- No loss of a point of absolute Dirichlet convergence is needed for the inverse. -/
theorem primitive_lSeriesSummable {s z : ℂ} (hs : 0 < s.re) (f : A)
    (hf : LSeriesSummable (fun n => f n) z) :
    LSeriesSummable (fun n => primitive s f n) z := by
  apply (hf.norm.div_const (1 - (2 : ℝ) ^ (-s.re))).of_norm_bounded
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn]
    exact (div_le_div_of_nonneg_right (norm_primitive_le hs f n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans_eq (by rw [div_div, div_div, mul_comm])

open GaloisForLFunctions.HTGeometry in
/-- The explicit primitive belongs to the actual finite-abscissa coefficient algebra. -/
theorem primitive_mem_finiteAbscissa {s : ℂ} (hs : 0 < s.re)
    (f : finiteAbscissaArithmeticSubalgebra) :
    primitive s f.1 ∈ finiteAbscissaArithmeticSubalgebra := by
  obtain ⟨H, hH⟩ := f.2
  exact ⟨H, fun y hy => primitive_lSeriesSummable hs f.1 (hH y hy)⟩

open GaloisForLFunctions.HTGeometry in
/-- Exact difference solution inside the finite-abscissa source algebra. -/
theorem exists_finiteAbscissa_primitive {s : ℂ} (hs : 0 < s.re)
    (f : finiteAbscissaArithmeticSubalgebra) :
    ∃ g : finiteAbscissaArithmeticSubalgebra,
      finiteAbscissaDirichletShift s g - g =
        f - algebraMap ℂ finiteAbscissaArithmeticSubalgebra (f.1 1) := by
  refine ⟨⟨primitive s f.1, primitive_mem_finiteAbscissa hs f⟩, ?_⟩
  apply Subtype.ext
  exact twist_primitive_sub (ne_of_gt hs) f.1

open GaloisForLFunctions.HTGeometry in
/-- Shift-invariant scalar linear functionals on the analytic source read only coefficient one. -/
theorem finiteAbscissa_invariant_linear_eval {s : ℂ} (hs : 0 < s.re)
    (τ : finiteAbscissaArithmeticSubalgebra →ₗ[ℂ] ℂ)
    (hτ : ∀ f, τ (finiteAbscissaDirichletShift s f) = τ f)
    (f : finiteAbscissaArithmeticSubalgebra) : τ f = f.1 1 * τ 1 := by
  obtain ⟨g, hg⟩ := exists_finiteAbscissa_primitive hs f
  have h := congrArg τ hg
  have hleft := _root_.map_sub τ (finiteAbscissaDirichletShift s g) g
  have hright := _root_.map_sub τ f
    (algebraMap ℂ finiteAbscissaArithmeticSubalgebra (f.1 1))
  rw [hleft, hτ, sub_self, hright] at h
  rw [sub_eq_zero.mp h.symm, Algebra.algebraMap_eq_smul_one, _root_.map_smul, smul_eq_mul]

/-- Every augmentation-zero family is a single twisted relation, before taking a span. -/
theorem exists_twisted_relation_iff {s : ℂ} (hs : s.re ≠ 0) (f : A) :
    (∃ u v : A, f = twist s u * v - v * u) ↔ f 1 = 0 := by
  constructor
  · rintro ⟨u, v, rfl⟩
    change (twist s u * v) 1 - (v * u) 1 = 0
    rw [ArithmeticFunction.mul_apply_one, ArithmeticFunction.mul_apply_one,
      twist_one_coefficient]
    exact sub_eq_zero.mpr (mul_comm _ _)
  · intro hf
    refine ⟨primitive s f, 1, ?_⟩
    simpa only [mul_one, one_mul, hf, map_zero, sub_zero]
      using (twist_primitive_sub hs f).symm

/-- Vanishing in the quotient detects precisely coefficient one, not a formed zeta zero. -/
theorem quotient_mk_eq_zero_iff {s : ℂ} (hs : s.re ≠ 0) (f : A) :
    Ideal.Quotient.mk (boundaryIdeal s) f = 0 ↔ f 1 = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, boundaryIdeal_eq_ker hs]
  rfl

end RHTower.ArithmeticTwistedBoundary
