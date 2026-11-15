import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality
import Mathlib.FieldTheory.Finite.Trace

/-!
# Four-divisible codes in characteristic two

Heng–Xie's Euclidean criterion (arXiv:2611.13963, Theorem 19) follows by
passing to binary trace words. Divisibility of every symbol count makes this
binary trace code doubly even. Binary polarization and a trace-dual basis
then recover the original field-valued pairing.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Every symbol multiplicity inherits any common divisor of the code weights. -/
theorem symbolCount_dvd (Δ : ℕ) (C : Submodule K (ι → K))
    (h1 : (fun _ => (1 : K)) ∈ C) (hC : Divisible Δ C)
    (c : ι → K) (hc : c ∈ C) (a : K) : Δ ∣ symbolCount c a := by
  have hn : Δ ∣ Fintype.card ι := by simpa only [weight_one] using hC _ h1
  have hd : Δ ∣ weight (fun i => c i - a) := hC _ (C.sub_mem hc (by
    simpa only [Pi.smul_def, smul_eq_mul, mul_one] using C.smul_mem a h1))
  rw [← symbolCount_add_weight_sub c a] at hn
  exact (Nat.dvd_add_iff_left hd).mpr hn

/-- Hamming weight as a sum of support indicators. -/
theorem weight_eq_sum (c : ι → K) :
    weight c = ∑ i, if c i = 0 then 0 else 1 := by
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = 0 <;> simp only [h, ne_eq, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false]

/-- A symbol map preserves divisibility when all symbol multiplicities are divisible. -/
theorem weight_comp_dvd [Fintype K] {L : Type*} [Field L]
    (Δ : ℕ) (C : Submodule K (ι → K)) (h1 : (fun _ => (1 : K)) ∈ C)
    (hC : Divisible Δ C) (c : ι → K) (hc : c ∈ C) (f : K → L) :
    Δ ∣ weight (fun i => f (c i)) := by
  rw [weight_eq_sum, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := c)
    (fun _ _ => Finset.mem_univ _) (fun i => if f (c i) = 0 then 0 else 1)]
  apply Finset.dvd_sum
  intro a _
  have h : (∑ i ∈ Finset.univ.filter (fun i => c i = a),
      if f (c i) = 0 then 0 else 1) =
      if f a = 0 then 0 else symbolCount c a := by
    calc
      _ = ∑ _i ∈ Finset.univ.filter (fun i => c i = a),
          if f a = 0 then 0 else 1 :=
        Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
      _ = _ := by split_ifs <;> simp only [Finset.sum_const_zero, Finset.sum_const,
        smul_eq_mul, mul_one, symbolCount]
  rw [h]
  split_ifs
  · exact dvd_zero Δ
  · exact symbolCount_dvd Δ C h1 hC c hc a

/-- The two possible binary symbols, obtained from their canonical representatives. -/
theorem binary_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx := ZMod.val_lt x
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · left
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_one]

/-- The binary weight identity measures the overlap of two supports. -/
theorem binary_weight_add (c d : ι → ZMod 2) :
    weight c + weight d = weight (c + d) + 2 * weight (c * d) := by
  simp only [weight_eq_sum, Pi.add_apply, Pi.mul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases binary_eq_zero_or_one (c i) with h | h <;>
    rcases binary_eq_zero_or_one (d i) with h' | h' <;>
    simp [h, h', CharTwo.add_self_eq_zero]

/-- A binary word's coordinate sum is its weight modulo two. -/
theorem binary_sum_eq_weight (c : ι → ZMod 2) : ∑ i, c i = (weight c : ZMod 2) := by
  rw [weight_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases binary_eq_zero_or_one (c i) with h | h <;> simp [h]

/-- Three weights divisible by four force the binary mixed pairing to vanish. -/
theorem binary_pair_eq_zero (c d : ι → ZMod 2)
    (hc : 4 ∣ weight c) (hd : 4 ∣ weight d) (hcd : 4 ∣ weight (c + d)) :
    ∑ i, c i * d i = 0 := by
  have h : 4 ∣ 2 * weight (c * d) := by
    have hsum := dvd_add hc hd
    rw [binary_weight_add] at hsum
    exact (Nat.dvd_add_iff_right hcd).mpr hsum
  have heven : 2 ∣ weight (c * d) := Nat.dvd_of_mul_dvd_mul_left (by omega) h
  rw [show (∑ i, c i * d i) = ∑ i, (c * d) i from rfl, binary_sum_eq_weight]
  exact (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr heven

/-- Binary four-divisible linear codes need no assumption about the constant word. -/
theorem binary_divisible_selfOrthogonal (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hC : Divisible 4 C) : SelfOrthogonal (RingHom.id _) C := by
  intro c hc d hd
  exact binary_pair_eq_zero c d (hC c hc) (hC d hd) (hC _ (C.add_mem hc hd))

section FiniteField
variable [Fintype K] [CharP K 2]

local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Binary trace tests detect the full field-valued dot product. -/
theorem pair_eq_zero_of_trace_tests (c d : ι → K)
    (h : ∀ a b : K, ∑ i, Algebra.trace (ZMod 2) K (a * c i) *
      Algebra.trace (ZMod 2) K (b * d i) = 0) : ∑ i, c i * d i = 0 := by
  have hweighted (a : K) : ∑ i, Algebra.trace (ZMod 2) K (a * c i) • d i = 0 := by
    apply (traceForm_nondegenerate (ZMod 2) K).1
    intro b
    change Algebra.trace (ZMod 2) K
      ((∑ i, Algebra.trace (ZMod 2) K (a * c i) • d i) * b) = 0
    simp only [Finset.sum_mul, smul_mul_assoc,
      map_sum, map_smul, smul_eq_mul]
    simpa only [mul_comm (d _) b] using h a b
  let B := Module.finBasis (ZMod 2) K
  have hexpand (x : K) :
      ∑ j, Algebra.trace (ZMod 2) K (B j * x) • B.traceDual j = x := by
    simpa only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      mul_comm x] using B.traceDual.sum_repr x
  calc
    ∑ i, c i * d i = ∑ i, (∑ j,
        Algebra.trace (ZMod 2) K (B j * c i) • B.traceDual j) * d i := by
      simp only [hexpand]
    _ = ∑ j, B.traceDual j *
        (∑ i, Algebra.trace (ZMod 2) K (B j * c i) • d i) := by
      simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp only [hweighted, mul_zero, Finset.sum_const_zero]

/-- Four-divisible codes containing one are Euclidean self-orthogonal over every finite
field of characteristic two. Binary traces turn divisibility into bilinear identities. -/
theorem fourDivisible_selfOrthogonal (C : Submodule K (ι → K))
    (h1 : (fun _ => (1 : K)) ∈ C) (hC : Divisible 4 C) :
    SelfOrthogonal (RingHom.id K) C := by
  intro c hc d hd
  change ∑ i, c i * d i = 0
  apply pair_eq_zero_of_trace_tests
  intro a b
  let tr := Algebra.trace (ZMod 2) K
  have hword (v : ι → K) (hv : v ∈ C) : 4 ∣ weight (fun i => tr (v i)) :=
    weight_comp_dvd 4 C h1 hC v hv tr
  apply binary_pair_eq_zero
  · exact hword (a • c) (C.smul_mem a hc)
  · exact hword (b • d) (C.smul_mem b hd)
  · change 4 ∣ weight (fun i => tr (a * c i) + tr (b * d i))
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] using
      hword (a • c + b • d) (C.add_mem (C.smul_mem a hc) (C.smul_mem b hd))

end FiniteField

#print axioms binary_divisible_selfOrthogonal
#print axioms fourDivisible_selfOrthogonal

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
