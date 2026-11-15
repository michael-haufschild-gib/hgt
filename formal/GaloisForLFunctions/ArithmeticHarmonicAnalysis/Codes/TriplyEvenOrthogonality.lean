import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FourDivisibleEuclidean
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryAffineCodes

/-!
# Cubic orthogonality from triply even codes

Binary polarization divides support-overlap divisibility by two. Applying
it twice shows that an eight-divisible linear code has vanishing cubic
coordinate moments. Affine binary codes on cubes of dimension at least
four give an unconditional family.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
variable {ι : Type*} [Fintype ι]

/-- Polarization removes one factor of two from support-intersection divisibility. -/
theorem binary_product_weight_dvd (Δ : ℕ) (c d : ι → ZMod 2)
    (hc : 2 * Δ ∣ weight c) (hd : 2 * Δ ∣ weight d)
    (hcd : 2 * Δ ∣ weight (c + d)) : Δ ∣ weight (c * d) := by
  have h : 2 * Δ ∣ 2 * weight (c * d) := by
    have hsum := dvd_add hc hd
    rw [binary_weight_add] at hsum
    exact (Nat.dvd_add_iff_right hcd).mpr hsum
  exact Nat.dvd_of_mul_dvd_mul_left (by omega) h

/-- Every cubic coordinate moment vanishes on triples of codewords. -/
def Triorthogonal {K : Type*} [Field K] (C : Submodule K (ι → K)) : Prop :=
  ∀ c ∈ C, ∀ d ∈ C, ∀ e ∈ C, ∑ i, c i * d i * e i = 0

/-- Eight-divisible binary linear codes have vanishing cubic coordinate moments. -/
theorem binary_eightDivisible_triorthogonal (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hC : Divisible 8 C) : Triorthogonal C := by
  have hpair (c : ι → ZMod 2) (hc : c ∈ C) (d : ι → ZMod 2) (hd : d ∈ C) :
      4 ∣ weight (c * d) :=
    binary_product_weight_dvd 4 c d (hC c hc) (hC d hd) (hC _ (C.add_mem hc hd))
  intro c hc d hd e he
  have hsum : 4 ∣ weight (c * d + c * e) := by
    rw [← mul_add]
    exact hpair c hc (d + e) (C.add_mem hd he)
  have h := binary_pair_eq_zero (c * d) (c * e) (hpair c hc d hd) (hpair c hc e he) hsum
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rcases binary_eq_zero_or_one (c i) with hc | hc <;>
    simp only [Pi.mul_apply, hc, zero_mul, one_mul]

/-- Twice the desired divisor in the group order makes every affine weight divisible. -/
theorem binaryAffineCode_divisible_of_twice_dvd {G : Type*} [AddCommGroup G] [Fintype G]
    (Δ : ℕ) (hG : 2 * Δ ∣ Fintype.card G) : Divisible Δ (binaryAffineCode G) := by
  intro c hc
  rcases binaryAffine_weight_cases c hc with h | h | h
  · rw [h]; exact dvd_zero Δ
  · rw [h]
    exact dvd_trans (dvd_mul_left Δ 2) hG
  · have hdiv : 2 * Δ ∣ 2 * weight c := by rw [h]; exact hG
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdiv

/-- Every affine cube of dimension at least four gives an eight-divisible code. -/
theorem binaryCubeAffineCode_eightDivisible (n : ℕ) :
    Divisible 8 (binaryCubeAffineCode (n + 1)) := by
  apply binaryAffineCode_divisible_of_twice_dvd
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  refine ⟨2 ^ n, ?_⟩
  rw [show n + 1 + 3 = n + 4 by omega, pow_add]
  ring

/-- Cubic orthogonality holds for the entire affine cube family in dimension at least four. -/
theorem binaryCubeAffineCode_triorthogonal (n : ℕ) :
    Triorthogonal (binaryCubeAffineCode (n + 1)) :=
  binary_eightDivisible_triorthogonal _ (binaryCubeAffineCode_eightDivisible n)

/-- The product of all binary coordinates is supported at the all-one vertex. -/
theorem binaryCube_topMoment_eq_one (ν : Type*) [Fintype ν] [DecidableEq ν] :
    (∑ x : ν → ZMod 2, ∏ j, x j) = 1 := by
  have hterm (x : ν → ZMod 2) :
      (∏ j, x j) = if x = (fun _ => 1) then 1 else 0 := by
    by_cases hx : x = fun _ => 1
    · simp only [hx, Finset.prod_const_one, if_true]
    · rw [if_neg hx]
      have hz : ∃ j, x j = 0 := by
        by_contra! h
        apply hx
        funext j
        exact (binary_eq_zero_or_one (x j)).resolve_left (h j)
      obtain ⟨j, hj⟩ := hz
      exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Three coordinate words on the three-dimensional cube have nonzero cubic moment. -/
theorem binaryCubeAffineCode_zero_not_triorthogonal :
    ¬Triorthogonal (binaryCubeAffineCode 0) := by
  intro h
  have hmem (j : Fin 3) : (fun x : Fin 3 → ZMod 2 => x j) ∈ binaryCubeAffineCode 0 := by
    let f : (Fin 3 → ZMod 2) →+ ZMod 2 :=
      { toFun := fun x => x j
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact ⟨0, f, fun _ => (zero_add _).symm⟩
  have hz := h _ (hmem 0) _ (hmem 1) _ (hmem 2)
  have hone : (∑ x : Fin 3 → ZMod 2, x 0 * x 1 * x 2) = 1 := by
    simpa only [Fin.prod_univ_three] using binaryCube_topMoment_eq_one (Fin 3)
  exact zero_ne_one (hz.symm.trans hone)

/-- The dimension-four threshold for cubic orthogonality is sharp. -/
theorem binaryCubeAffineCode_triorthogonal_iff (n : ℕ) :
    Triorthogonal (binaryCubeAffineCode n) ↔ n ≠ 0 := by
  cases n with
  | zero => simp only [binaryCubeAffineCode_zero_not_triorthogonal, ne_eq, not_true_eq_false]
  | succ n => exact iff_of_true (binaryCubeAffineCode_triorthogonal n) (Nat.succ_ne_zero n)

section FiniteField
variable {K : Type*} [Field K] [Fintype K] [CharP K 2]
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Applying the absolute trace independently to every coordinate is binary linear. -/
def coordinateTrace : (ι → K) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun c i := Algebra.trace (ZMod 2) K (c i)
  map_add' c d := by
    funext i
    exact map_add (Algebra.trace (ZMod 2) K) (c i) (d i)
  map_smul' a c := by
    funext i
    change Algebra.trace (ZMod 2) K (a • c i) = a • Algebra.trace (ZMod 2) K (c i)
    exact map_smul (Algebra.trace (ZMod 2) K) a (c i)

/-- The binary trace code of a linear code over a finite field of characteristic two. -/
def binaryTraceCode (C : Submodule K (ι → K)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  (C.restrictScalars (ZMod 2)).map coordinateTrace

/-- Constant words make weight divisibility survive passage to the binary trace code. -/
theorem binaryTraceCode_divisible (Δ : ℕ) (C : Submodule K (ι → K))
    (h1 : (fun _ => (1 : K)) ∈ C) (hC : Divisible Δ C) :
    Divisible Δ (binaryTraceCode C) := by
  rintro v ⟨c, hc, rfl⟩
  exact weight_comp_dvd Δ C h1 hC c hc (Algebra.trace (ZMod 2) K)

/-- Binary trace tests detect the full cubic coordinate moment. -/
theorem triple_eq_zero_of_trace_tests (c d e : ι → K)
    (h : ∀ a b z : K, ∑ i, Algebra.trace (ZMod 2) K (a * c i) *
      Algebra.trace (ZMod 2) K (b * d i) * Algebra.trace (ZMod 2) K (z * e i) = 0) :
    ∑ i, c i * d i * e i = 0 := by
  have hweighted (a : K) :
      ∑ i, Algebra.trace (ZMod 2) K (a * c i) • (d i * e i) = 0 := by
    have hpair : ∑ i, d i * (Algebra.trace (ZMod 2) K (a * c i) • e i) = 0 := by
      apply pair_eq_zero_of_trace_tests
      intro b z
      simpa only [mul_smul_comm, map_smul, smul_eq_mul, mul_assoc, mul_left_comm]
        using h a b z
    simpa only [mul_smul_comm] using hpair
  let B := Module.finBasis (ZMod 2) K
  have hexpand (x : K) :
      ∑ j, Algebra.trace (ZMod 2) K (B j * x) • B.traceDual j = x := by
    simpa only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      mul_comm x] using B.traceDual.sum_repr x
  calc
    ∑ i, c i * d i * e i = ∑ i, (∑ j,
        Algebra.trace (ZMod 2) K (B j * c i) • B.traceDual j) * d i * e i := by
      simp only [hexpand]
    _ = ∑ j, B.traceDual j *
        (∑ i, Algebra.trace (ZMod 2) K (B j * c i) • (d i * e i)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp only [hweighted, mul_zero, Finset.sum_const_zero]

/-- Eight-divisible codes containing one have zero cubic moments over the full finite field. -/
theorem eightDivisible_triorthogonal (C : Submodule K (ι → K))
    (h1 : (fun _ => (1 : K)) ∈ C) (hC : Divisible 8 C) : Triorthogonal C := by
  have htrace := binary_eightDivisible_triorthogonal (binaryTraceCode C)
    (binaryTraceCode_divisible 8 C h1 hC)
  have hmem (c : ι → K) (hc : c ∈ C) (a : K) :
      (fun i => Algebra.trace (ZMod 2) K (a * c i)) ∈ binaryTraceCode C :=
    Submodule.mem_map.mpr ⟨a • c, C.smul_mem a hc, rfl⟩
  intro c hc d hd e he
  apply triple_eq_zero_of_trace_tests
  intro a b z
  exact htrace _ (hmem c hc a) _ (hmem d hd b) _ (hmem e he z)

end FiniteField

#print axioms binary_eightDivisible_triorthogonal
#print axioms binaryCubeAffineCode_triorthogonal
#print axioms binaryCubeAffineCode_triorthogonal_iff
#print axioms eightDivisible_triorthogonal

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
