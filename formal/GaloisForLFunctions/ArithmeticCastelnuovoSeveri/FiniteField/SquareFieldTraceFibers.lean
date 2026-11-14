import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusDescent

/-!
# Fixed fields and trace fibers over a square finite field

For `Q=p^(s+1)`, the fixed field of the `Q`-power Frobenius has `Q` elements.
The equation `u^Q+u=a` has `Q` solutions when `a` is fixed and none otherwise.
A trace-one element is obtained from any `x` not fixed by Frobenius as
`x/(x-x^Q)`, including in characteristic two.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- The actual subfield fixed by the middle Frobenius. -/
def squareFrobeniusFixedField (s : ℕ) : Subfield (SquareConstantField p s) :=
  (iterateFrobenius (SquareConstantField p s) p (s + 1)).eqLocusField (RingHom.id _)

/-- Membership in the fixed subfield is the expected power equation. -/
theorem mem_squareFrobeniusFixedField (s : ℕ) (x : SquareConstantField p s) :
    x ∈ squareFrobeniusFixedField p s ↔ x ^ p ^ (s + 1) = x := Iff.rfl

/-- The fixed field has `Q` elements, by descent along a concrete finite-field embedding. -/
theorem squareFrobeniusFixedField_card (s : ℕ) :
    Nat.card (squareFrobeniusFixedField p s) = p ^ (s + 1) := by
  let K := FiniteField.Extension (ZMod p) p (s + 1)
  letI := Fintype.ofFinite K
  have hK : Module.finrank (ZMod p) K = s + 1 :=
    by simpa only [Module.finrank_self, one_mul] using
      FiniteField.finrank_zmod_extension (ZMod p) p (s + 1)
  have hS : Module.finrank (ZMod p) (SquareConstantField p s) = 2 * (s + 1) :=
    by simpa only [Module.finrank_self, one_mul] using
      FiniteField.finrank_zmod_extension (ZMod p) p (2 * (s + 1))
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := K) (L := SquareConstantField p s)
    (by rw [hK, hS]; exact dvd_mul_left _ _)
  have he := GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.finiteFieldFrobeniusFixedEquiv
    (ZMod p) K (SquareConstantField p s) e
  have hc := Nat.card_congr he
  simp only [GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.finiteField_frobenius_pow_apply,
    hK, ZMod.card] at hc
  change Nat.card {x : SquareConstantField p s // x ^ p ^ (s + 1) = x} = _
  rw [← hc]
  exact (FiniteField.natCard_extension (ZMod p) p (s + 1)).trans (by rw [Nat.card_zmod])

/-- The square finite field has degree two over its middle fixed field. -/
theorem squareFrobeniusFixedField_finrank (s : ℕ) :
    Module.finrank (squareFrobeniusFixedField p s) (SquareConstantField p s) = 2 := by
  have hc := Module.natCard_eq_pow_finrank
    (K := squareFrobeniusFixedField p s) (V := SquareConstantField p s)
  rw [squareConstantField_card, squareFrobeniusFixedField_card] at hc
  have hpow : p ^ (2 * (s + 1)) = (p ^ (s + 1)) ^ 2 := by
    rw [Nat.mul_comm 2 (s + 1), pow_mul]
  exact Nat.pow_right_injective
    (Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt) (hc.symm.trans hpow)

/-- The quadratic trace as an additive homomorphism on the ambient field. -/
def squareFieldTrace (s : ℕ) : SquareConstantField p s →+ SquareConstantField p s :=
  (iterateFrobenius (SquareConstantField p s) p (s + 1)).toAddMonoidHom + AddMonoidHom.id _

/-- The trace is the sum of the two Frobenius conjugates. -/
theorem squareFieldTrace_apply (s : ℕ) (x : SquareConstantField p s) :
    squareFieldTrace p s x = x ^ p ^ (s + 1) + x := rfl

/-- Every trace value lies in the fixed subfield. -/
theorem squareFieldTrace_fixed (s : ℕ) (x : SquareConstantField p s) :
    squareFieldTrace p s x ∈ squareFrobeniusFixedField p s := by
  change (x ^ p ^ (s + 1) + x) ^ p ^ (s + 1) = x ^ p ^ (s + 1) + x
  rw [add_pow_char_pow, squareConstantField_frobenius_sq, add_comm]

/-- A Frobenius difference gives a trace-one element in every characteristic. -/
theorem squareFieldTrace_exists_one (s : ℕ) :
    ∃ u : SquareConstantField p s, squareFieldTrace p s u = 1 := by
  obtain ⟨x, hx⟩ := squareConstantField_exists_not_fixed p s
  have ht : x - x ^ p ^ (s + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨x / (x - x ^ p ^ (s + 1)), ?_⟩
  rw [squareFieldTrace_apply, div_pow, squareConstantField_difference_traceZero,
    div_neg, add_comm, ← sub_eq_add_neg, ← sub_div, div_self ht]

/-- A fixed trace-one element. -/
def squareTraceOne (s : ℕ) : SquareConstantField p s :=
  (squareFieldTrace_exists_one p s).choose

/-- The chosen element has trace one. -/
theorem squareTraceOne_trace (s : ℕ) :
    squareFieldTrace p s (squareTraceOne p s) = 1 :=
  (squareFieldTrace_exists_one p s).choose_spec

/-- Every element of the fixed field is a trace. -/
theorem squareFieldTrace_exists_iff (s : ℕ) (a : SquareConstantField p s) :
    (∃ u : SquareConstantField p s, squareFieldTrace p s u = a) ↔
      a ∈ squareFrobeniusFixedField p s := by
  constructor
  · rintro ⟨u, rfl⟩
    exact squareFieldTrace_fixed p s u
  · intro ha
    refine ⟨a * squareTraceOne p s, ?_⟩
    change a ^ p ^ (s + 1) = a at ha
    rw [squareFieldTrace_apply, mul_pow, ha, ← mul_add,
      ← squareFieldTrace_apply, squareTraceOne_trace, mul_one]

/-- Dividing by a nonzero trace-zero constant identifies the trace kernel with the fixed field. -/
def squareTraceKernelEquivFixed (s : ℕ) :
    (squareFieldTrace p s).ker ≃ squareFrobeniusFixedField p s where
  toFun x := ⟨x.val / (kummerTraceConstant p s : SquareConstantField p s),
    kummerTraceConstant_ratio_fixed p s x.val
      (eq_neg_of_add_eq_zero_left x.property)⟩
  invFun a := ⟨(kummerTraceConstant p s : SquareConstantField p s) * a.val, by
    change ((kummerTraceConstant p s : SquareConstantField p s) * a.val) ^ p ^ (s + 1) +
      (kummerTraceConstant p s : SquareConstantField p s) * a.val = 0
    rw [mul_pow, kummerTraceConstant_frobenius,
      (show a.val ^ p ^ (s + 1) = a.val from a.property)]
    ring⟩
  left_inv x := by
    apply Subtype.ext
    change (kummerTraceConstant p s : SquareConstantField p s) *
      (x.val / (kummerTraceConstant p s : SquareConstantField p s)) = x.val
    field_simp
  right_inv a := by
    apply Subtype.ext
    change ((kummerTraceConstant p s : SquareConstantField p s) * a.val) /
      (kummerTraceConstant p s : SquareConstantField p s) = a.val
    field_simp

/-- The trace kernel has `Q` elements. -/
theorem squareFieldTrace_kernel_card (s : ℕ) :
    Nat.card (squareFieldTrace p s).ker = p ^ (s + 1) :=
  (Nat.card_congr (squareTraceKernelEquivFixed p s)).trans (squareFrobeniusFixedField_card p s)

/-- Every soluble trace equation has exactly `Q` solutions. -/
theorem squareFieldTrace_fiber_card_of_fixed (s : ℕ) (a : SquareConstantField p s)
    (ha : a ∈ squareFrobeniusFixedField p s) :
    Nat.card {u : SquareConstantField p s | u ^ p ^ (s + 1) + u = a} = p ^ (s + 1) := by
  obtain ⟨u, rfl⟩ := (squareFieldTrace_exists_iff p s a).mpr ha
  have hc := Nat.card_congr ((squareFieldTrace p s).fiberEquivKer u)
  simpa only [Set.preimage, Set.mem_singleton_iff, squareFieldTrace_apply] using
    hc.trans (squareFieldTrace_kernel_card p s)

/-- The exact count for every trace fiber, without an assumed solvability premise. -/
theorem squareFieldTrace_fiber_card (s : ℕ) (a : SquareConstantField p s) :
    Nat.card {u : SquareConstantField p s | u ^ p ^ (s + 1) + u = a} =
      if a ^ p ^ (s + 1) = a then p ^ (s + 1) else 0 := by
  by_cases ha : a ^ p ^ (s + 1) = a
  · rw [if_pos ha]
    exact squareFieldTrace_fiber_card_of_fixed p s a ha
  · rw [if_neg ha]
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun u =>
      ha ((squareFieldTrace_exists_iff p s a).mp ⟨u.val, u.property⟩)⟩)

/-- The affine trace hyperplane used to construct rational Kummer fibers has `Q` elements. -/
theorem squareFieldTrace_one_card (s : ℕ) :
    Nat.card {u : SquareConstantField p s | u ^ p ^ (s + 1) + u = 1} = p ^ (s + 1) :=
  squareFieldTrace_fiber_card_of_fixed p s 1 (squareFrobeniusFixedField p s).one_mem

/-- The trace-zero line has the same size in odd and even characteristic. -/
theorem squareFieldTrace_zero_card (s : ℕ) :
    Nat.card {u : SquareConstantField p s | u ^ p ^ (s + 1) = -u} = p ^ (s + 1) := by
  simpa only [← eq_neg_iff_add_eq_zero] using
    squareFieldTrace_fiber_card_of_fixed p s 0 (squareFrobeniusFixedField p s).zero_mem

/-- Both Frobenius eigensets occurring in the Kummer point construction have `Q` elements. -/
theorem squareField_signedFrobenius_card (s R : ℕ) :
    Nat.card {u : SquareConstantField p s | u ^ p ^ (s + 1) = (-1) ^ R * u} =
      p ^ (s + 1) := by
  rcases neg_one_pow_eq_or (SquareConstantField p s) R with h | h
  · simp only [h, one_mul]
    exact squareFrobeniusFixedField_card p s
  · simp only [h, neg_one_mul]
    exact squareFieldTrace_zero_card p s

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
