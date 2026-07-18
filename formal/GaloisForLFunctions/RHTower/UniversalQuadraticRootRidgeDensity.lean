import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# Universal quadratic-root ridge density

For the reducible root packet `r * (r + h) = 0` modulo a nonzero modulus, the roots `0` and
`-h` are present for every gap.  Finite additive-character orthogonality shows that the full
untwisted frequency sum selects `0`, while the `h`-twisted frequency sum selects `-h`.

The involution `r ↦ -h-r` exchanges those two branches and identifies the twisted response with
the complex conjugate of the untwisted response.  Removing zero frequency then gives an exact
density law: the root density is one minus the ambient-normalized real mass of all nonzero
responses.

These are unconditional finite identities.  They do not estimate a physical subfamily of
frequencies and do not supply the open response correlation required by FCRJ.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- The quadratic root response with its frequency indexed intrinsically by `ZMod n`. -/
noncomputable def quadraticCongruenceZModRootResponse
    (n : ℕ) [NeZero n] (h : ℤ) (a : ZMod n) : ℂ :=
  ∑ r : quadraticCongruenceRoots n h,
    ZMod.stdAddChar (a * r.1)

/-- Intrinsic `ZMod` frequency agrees with the integer-frequency root sum already used by the
reduced-frequency alias API. -/
@[simp] theorem quadraticCongruenceZModRootResponse_intCast
    (n : ℕ) [NeZero n] (h a : ℤ) :
    quadraticCongruenceZModRootResponse n h (a : ZMod n) =
      quadraticCongruenceRootSum n h a := rfl

/-- Finite orthogonality for the standard additive character on `ZMod n`. -/
private theorem sum_stdAddChar_mul_zmod
    (n : ℕ) [NeZero n] (x : ZMod n) :
    ∑ a : ZMod n, ZMod.stdAddChar (a * x) = if x = 0 then (n : ℂ) else 0 := by
  split_ifs with hx
  · simp [hx, ZMod.card]
  · simpa [mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n hx)

/-- The universal zero root of the reducible quadratic packet. -/
def quadraticCongruenceZeroRoot
    (n : ℕ) [NeZero n] (h : ℤ) : quadraticCongruenceRoots n h :=
  ⟨0, by simp⟩

/-- The universal negative-gap root of the reducible quadratic packet. -/
def quadraticCongruenceNegativeGapRoot
    (n : ℕ) [NeZero n] (h : ℤ) : quadraticCongruenceRoots n h :=
  ⟨-(h : ZMod n), by simp⟩

/-- The exact branch involution `r ↦ -h-r` on the reducible quadratic root packet. -/
noncomputable def quadraticCongruenceRootInvolution
    (n : ℕ) [NeZero n] (h : ℤ) :
    quadraticCongruenceRoots n h ≃ quadraticCongruenceRoots n h where
  toFun r := ⟨-(h : ZMod n) - r.1, by
    calc
      (-(h : ZMod n) - r.1) * (-(h : ZMod n) - r.1 + (h : ZMod n)) =
          r.1 * (r.1 + (h : ZMod n)) := by ring
      _ = 0 := r.2⟩
  invFun r := ⟨-(h : ZMod n) - r.1, by
    calc
      (-(h : ZMod n) - r.1) * (-(h : ZMod n) - r.1 + (h : ZMod n)) =
          r.1 * (r.1 + (h : ZMod n)) := by ring
      _ = 0 := r.2⟩
  left_inv r := Subtype.ext (by ring)
  right_inv r := Subtype.ext (by ring)

@[simp] theorem quadraticCongruenceRootInvolution_zeroRoot
    (n : ℕ) [NeZero n] (h : ℤ) :
    quadraticCongruenceRootInvolution n h (quadraticCongruenceZeroRoot n h) =
      quadraticCongruenceNegativeGapRoot n h := by
  apply Subtype.ext
  simp [quadraticCongruenceRootInvolution, quadraticCongruenceZeroRoot,
    quadraticCongruenceNegativeGapRoot]

@[simp] theorem quadraticCongruenceRootInvolution_negativeGapRoot
    (n : ℕ) [NeZero n] (h : ℤ) :
    quadraticCongruenceRootInvolution n h (quadraticCongruenceNegativeGapRoot n h) =
      quadraticCongruenceZeroRoot n h := by
  apply Subtype.ext
  simp [quadraticCongruenceRootInvolution, quadraticCongruenceZeroRoot,
    quadraticCongruenceNegativeGapRoot]

/-- **Universal zero-root selector.** Summing the root response over every frequency leaves exactly
the root `0`, hence one copy of the ambient modulus. -/
theorem sum_quadraticCongruenceZModRootResponse
    (n : ℕ) [NeZero n] (h : ℤ) :
    ∑ a : ZMod n, quadraticCongruenceZModRootResponse n h a = (n : ℂ) := by
  unfold quadraticCongruenceZModRootResponse
  rw [Fintype.sum_comm]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (quadraticCongruenceZeroRoot n h)]
  simp only [sum_stdAddChar_mul_zmod]
  simp [quadraticCongruenceZeroRoot, Subtype.ext_iff]

/-- **Branch-conjugacy law.** The `h`-twisted root response is pointwise the complex conjugate of
the untwisted response.  It is the Fourier form of the involution `r ↦ -h-r`. -/
theorem quadraticCongruenceZModRootResponse_twist_eq_conj
    (n : ℕ) [NeZero n] (h : ℤ) (a : ZMod n) :
    ZMod.stdAddChar (a * (h : ZMod n)) *
        quadraticCongruenceZModRootResponse n h a =
      (starRingEnd ℂ) (quadraticCongruenceZModRootResponse n h a) := by
  unfold quadraticCongruenceZModRootResponse
  rw [map_sum, Finset.mul_sum]
  let e := quadraticCongruenceRootInvolution n h
  calc
    (∑ r : quadraticCongruenceRoots n h,
        ZMod.stdAddChar (a * (h : ZMod n)) * ZMod.stdAddChar (a * r.1)) =
        ∑ r : quadraticCongruenceRoots n h,
          ZMod.stdAddChar (-(a * (e r).1)) := by
            apply Fintype.sum_congr
            intro r
            rw [← map_add]
            congr 1
            simp only [e, quadraticCongruenceRootInvolution]
            ring
    _ = ∑ r : quadraticCongruenceRoots n h,
          ZMod.stdAddChar (-(a * r.1)) := by
            simpa only using e.sum_comp
              (fun r : quadraticCongruenceRoots n h =>
                ZMod.stdAddChar (-(a * r.1)))
    _ = ∑ r : quadraticCongruenceRoots n h,
          (starRingEnd ℂ) (ZMod.stdAddChar (a * r.1)) := by
            apply Fintype.sum_congr
            intro r
            exact AddChar.map_neg_eq_conj _ _

/-- **Half-center phase lock.** If `c` is a half-gap, then twisting the response by the
half-gap character makes it fixed by complex conjugation.  Thus the apparent complex phase of the
reducible root response is deterministic rather than arbitrary. -/
theorem star_stdAddChar_halfGap_mul_quadraticCongruenceZModRootResponse
    (n : ℕ) [NeZero n] (h : ℤ) (a c : ZMod n)
    (hc : c + c = (h : ZMod n)) :
    (starRingEnd ℂ)
        (ZMod.stdAddChar (a * c) * quadraticCongruenceZModRootResponse n h a) =
      ZMod.stdAddChar (a * c) * quadraticCongruenceZModRootResponse n h a := by
  rw [map_mul, ← AddChar.map_neg_eq_conj,
    ← quadraticCongruenceZModRootResponse_twist_eq_conj]
  rw [← mul_assoc, ← map_add]
  congr 2
  rw [← hc]
  ring

/-- The half-gap phase-locked response is real. -/
theorem im_stdAddChar_halfGap_mul_quadraticCongruenceZModRootResponse_eq_zero
    (n : ℕ) [NeZero n] (h : ℤ) (a c : ZMod n)
    (hc : c + c = (h : ZMod n)) :
    (ZMod.stdAddChar (a * c) *
      quadraticCongruenceZModRootResponse n h a).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact star_stdAddChar_halfGap_mul_quadraticCongruenceZModRootResponse n h a c hc

/-- **Universal negative-gap-root selector.** Twisting by the gap and summing over every frequency
leaves exactly the root `-h`, hence again one copy of the ambient modulus. -/
theorem sum_quadraticCongruenceZModRootResponse_twist
    (n : ℕ) [NeZero n] (h : ℤ) :
    ∑ a : ZMod n,
        ZMod.stdAddChar (a * (h : ZMod n)) *
          quadraticCongruenceZModRootResponse n h a = (n : ℂ) := by
  simp_rw [quadraticCongruenceZModRootResponse_twist_eq_conj]
  rw [← map_sum, sum_quadraticCongruenceZModRootResponse]
  simp

/-- At zero frequency the response is exactly the number of quadratic roots. -/
@[simp] theorem quadraticCongruenceZModRootResponse_zero
    (n : ℕ) [NeZero n] (h : ℤ) :
    quadraticCongruenceZModRootResponse n h 0 =
      (quadraticCongruenceRootCount n h : ℂ) := by
  simp [quadraticCongruenceZModRootResponse, quadraticCongruenceRootCount]

/-- The complete nonzero-frequency response has the forced real value `n - nu_h(n)`. -/
theorem sum_ne_zero_quadraticCongruenceZModRootResponse
    (n : ℕ) [NeZero n] (h : ℤ) :
    ∑ a : {a : ZMod n // a ≠ 0},
        quadraticCongruenceZModRootResponse n h a.1 =
      (n : ℂ) - quadraticCongruenceRootCount n h := by
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun a : ZMod n => quadraticCongruenceZModRootResponse n h a) 0
  rw [sum_quadraticCongruenceZModRootResponse n h,
    quadraticCongruenceZModRootResponse_zero] at hsplit
  linear_combination hsplit

/-- **Exact ridge-density identity.** The normalized root density is one minus the
ambient-normalized real mass of all nonzero root responses.  In particular those responses do not
form a mean-zero family unless the root packet fills the entire residue space. -/
theorem quadraticCongruenceRootDensity_eq_one_sub_average_re_ne_zero
    (n : ℕ) [NeZero n] (h : ℤ) :
    (quadraticCongruenceRootCount n h : ℝ) / (n : ℝ) =
      1 - (∑ a : {a : ZMod n // a ≠ 0},
        (quadraticCongruenceZModRootResponse n h a.1).re) / (n : ℝ) := by
  have hsum := congrArg Complex.re
    (sum_ne_zero_quadraticCongruenceZModRootResponse n h)
  simp only [map_sum, Complex.sub_re, Complex.natCast_re] at hsum
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp [hnR]
  linear_combination hsum

end RHTower
