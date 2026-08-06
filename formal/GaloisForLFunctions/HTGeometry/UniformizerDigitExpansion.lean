import GaloisForLFunctions.HTGeometry.TameDifferentFreeExtension

/-!
# Digit expansion in a uniformizer

If every element of the upper ring agrees with an element of the base modulo the maximal ideal --
that is, if the residue extension is trivial -- then every element has a finite expansion in powers
of a uniformizer with coefficients from the base, up to a remainder divisible by the chosen power.

Carried out to the ramification index, this is the statement that the powers of the uniformizer
below that index generate the upper ring modulo the maximal ideal of the base, which is the
generation statement a monogenic presentation needs.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- An element of positive valuation is divisible by a uniformizer. -/
theorem dvd_of_addVal_ne_zero {x y : B} (hx : addVal B x = 1) (hy : addVal B y ≠ 0) : x ∣ y := by
  rw [← addVal_le_iff_dvd, hx]
  exact Order.one_le_iff_ne_zero.mpr hy

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- **Digit expansion in a uniformizer.**  With a trivial residue extension every element is a
polynomial in the uniformizer with coefficients from the base, up to a remainder divisible by the
chosen power. -/
theorem exists_digit_expansion (ψ : A →+* B) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - ψ a) ≠ 0) (n : ℕ) (b : B) :
    ∃ (c : ℕ → A) (b' : B),
      b = (∑ i ∈ Finset.range n, ψ (c i) * x ^ i) + x ^ n * b' := by
  classical
  induction n generalizing b with
  | zero => exact ⟨fun _ => 0, b, by simp⟩
  | succ n ih =>
    obtain ⟨a0, ha0⟩ := hres b
    obtain ⟨q, hq⟩ := dvd_of_addVal_ne_zero hx ha0
    obtain ⟨d, b', hd⟩ := ih q
    set c : ℕ → A := fun i => if i = 0 then a0 else d (i - 1) with hc
    have hc0 : c 0 = a0 := by simp [hc]
    have hcs : ∀ i : ℕ, c (i + 1) = d i := by
      intro i
      simp [hc]
    refine ⟨c, b', ?_⟩
    rw [Finset.sum_range_succ']
    have hsum : ∑ i ∈ Finset.range n, ψ (c (i + 1)) * x ^ (i + 1) =
        x * ∑ i ∈ Finset.range n, ψ (d i) * x ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcs i, pow_succ]
      ring
    rw [hsum, hc0, pow_zero, mul_one]
    have hb : b = ψ a0 + x * q := by
      linear_combination (norm := ring_nf) hq
    rw [hb, hd]
    ring

end GaloisForLFunctions.HTGeometry
