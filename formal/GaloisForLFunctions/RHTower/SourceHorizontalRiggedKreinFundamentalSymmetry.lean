import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinGlobalIndex

/-!
# Fundamental symmetry of the source-horizontal rigged prime form

The exact global index-one classification of the all-prime source form produces its own
polarization.  The sum of the first two canonical prime deltas is a negative time axis on every
left fibre and a positive time axis on every reflected right fibre.  Reflection in its orthogonal
hyperplane, multiplied by the source orientation, is therefore a global fundamental symmetry.

The resulting polarized form is nonnegative on the full nuclear Köthe source, not merely on finite
prime packets.  Its nullspace is exactly the coefficient radical already classified by the global
index theorem, and critical-line reflection fixes the polarized form.  No Xi zero, spectral
reality, Hilbert-space realization, or added positivity premise is used.
-/

open Complex

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization

/-- Canonical two-prime time axis of the all-prime rigged form. -/
def preDivisorRiggedPrimeTimeAxis : DeningerHeightKothe :=
  preDivisorRiggedPrimeDelta (nthPrimePoint 0) +
    preDivisorRiggedPrimeDelta (nthPrimePoint 1)

/-- The canonical time axis is strictly negative on every left critical-strip fibre. -/
theorem preDivisorRiggedPrimeTimeAxis_negative_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2) :
    preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis < 0 := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  let p : Nat.Primes := nthPrimePoint 0
  let q : Nat.Primes := nthPrimePoint 1
  have hpq : p ≠ q := by
    apply preDivisorRiggedNthPrimePoint_injective.ne
    norm_num
  have hqp : q ≠ p := Ne.symm hpq
  have hwp : 0 < preDivisorRiggedPrimeWeight s p :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) p
  have hwq : 0 < preDivisorRiggedPrimeWeight s q :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) q
  change preDivisorRiggedPrimeWittPairing s
      (preDivisorRiggedPrimeDelta p + preDivisorRiggedPrimeDelta q)
      (preDivisorRiggedPrimeDelta p + preDivisorRiggedPrimeDelta q) < 0
  rw [preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorOrientation_eq_one_of_left s hleft]
  simp [hpq, hqp]
  have hsqrtp : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s p) :=
    Real.sqrt_pos.2 hwp
  have hsqrtq : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s q) :=
    Real.sqrt_pos.2 hwq
  rw [mul_comm (Real.sqrt (preDivisorRiggedPrimeWeight s q))]
  nlinarith [mul_pos hsqrtp hsqrtq]

/-- The same canonical time axis is strictly positive on every reflected right fibre. -/
theorem preDivisorRiggedPrimeTimeAxis_positive_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1) :
    0 < preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis := by
  let t := PreDivisorReflectionDefectStabilization.preDivisorLineConj s
  have ht0 : 0 < t.re := by
    change 0 < 1 - s.re
    linarith
  have htleft : t.re < 1 / 2 := by
    change 1 - s.re < 1 / 2
    linarith
  have ht := preDivisorRiggedPrimeTimeAxis_negative_left t ht0 htleft
  rw [preDivisorRiggedPrimeWittPairing_lineConj] at ht
  linarith

/-- Rank-one reflection in the orthogonal complement of the canonical time axis. -/
def preDivisorRiggedPrimeTimeReflection
    (s : ℂ) (a : DeningerHeightKothe) : DeningerHeightKothe :=
  a -
    (2 * (preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis /
      preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis)) •
      preDivisorRiggedPrimeTimeAxis

/-- Source-oriented rank-one fundamental symmetry. -/
def preDivisorRiggedPrimeFundamentalSymmetry
    (s : ℂ) (a : DeningerHeightKothe) : DeningerHeightKothe :=
  preDivisorOrientation s • preDivisorRiggedPrimeTimeReflection s a

/-- Positive pairing produced from the rigged form by its source-selected fundamental symmetry. -/
def preDivisorRiggedPrimePolarizedPairing
    (s : ℂ) (a b : DeningerHeightKothe) : ℝ :=
  preDivisorRiggedPrimeWittPairing s a
    (preDivisorRiggedPrimeFundamentalSymmetry s b)

/-! ## Rank-one reflection laws -/

theorem preDivisorRiggedPrimeTimeReflection_pairing_left
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeReflection s a) b =
      preDivisorRiggedPrimeWittPairing s a b -
        2 * (preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis /
          preDivisorRiggedPrimeWittPairing s
            preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis) *
          preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis b := by
  rw [preDivisorRiggedPrimeTimeReflection, sub_eq_add_neg,
    preDivisorRiggedPrimeWittPairing_add_left hs]
  rw [show -((2 * (preDivisorRiggedPrimeWittPairing s a
      preDivisorRiggedPrimeTimeAxis /
        preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis
          preDivisorRiggedPrimeTimeAxis)) • preDivisorRiggedPrimeTimeAxis) =
      (-(2 * (preDivisorRiggedPrimeWittPairing s a
        preDivisorRiggedPrimeTimeAxis /
          preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis
            preDivisorRiggedPrimeTimeAxis))) •
        preDivisorRiggedPrimeTimeAxis by module,
    preDivisorRiggedPrimeWittPairing_smul_left]
  ring

theorem preDivisorRiggedPrimeTimeReflection_pairing_right
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a
        (preDivisorRiggedPrimeTimeReflection s b) =
      preDivisorRiggedPrimeWittPairing s a b -
        2 * (preDivisorRiggedPrimeWittPairing s b preDivisorRiggedPrimeTimeAxis /
          preDivisorRiggedPrimeWittPairing s
            preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis) *
          preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeWittPairing_comm s a,
    preDivisorRiggedPrimeTimeReflection_pairing_left hs,
    preDivisorRiggedPrimeWittPairing_comm s b a,
    preDivisorRiggedPrimeWittPairing_comm s preDivisorRiggedPrimeTimeAxis a]

theorem preDivisorRiggedPrimeTimeReflection_pairing_timeAxis
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeReflection s a)
        preDivisorRiggedPrimeTimeAxis =
      -preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeTimeReflection_pairing_left hs]
  field_simp
  ring

theorem preDivisorRiggedPrimeTimeReflection_add
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeTimeReflection s (a + b) =
      preDivisorRiggedPrimeTimeReflection s a +
        preDivisorRiggedPrimeTimeReflection s b := by
  rw [preDivisorRiggedPrimeTimeReflection,
    preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeTimeReflection,
    preDivisorRiggedPrimeTimeReflection]
  module

theorem preDivisorRiggedPrimeTimeReflection_smul
    (s : ℂ) (c : ℝ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeTimeReflection s (c • a) =
      c • preDivisorRiggedPrimeTimeReflection s a := by
  rw [preDivisorRiggedPrimeTimeReflection,
    preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimeTimeReflection]
  module

theorem preDivisorRiggedPrimeTimeReflection_sq
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeTimeReflection s
        (preDivisorRiggedPrimeTimeReflection s a) = a := by
  rw [preDivisorRiggedPrimeTimeReflection,
    preDivisorRiggedPrimeTimeReflection_pairing_timeAxis hs haxis,
    preDivisorRiggedPrimeTimeReflection]
  module

/-- The rank-one reflection is self-adjoint for the original rigged form. -/
theorem preDivisorRiggedPrimeTimeReflection_isSelfAdjoint
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeReflection s a) b =
      preDivisorRiggedPrimeWittPairing s a
        (preDivisorRiggedPrimeTimeReflection s b) := by
  rw [preDivisorRiggedPrimeTimeReflection_pairing_left hs,
    preDivisorRiggedPrimeTimeReflection_pairing_right hs,
    preDivisorRiggedPrimeWittPairing_comm s b preDivisorRiggedPrimeTimeAxis,
    preDivisorRiggedPrimeWittPairing_comm s preDivisorRiggedPrimeTimeAxis b]
  ring

/-- The rank-one reflection preserves the indefinite form. -/
theorem preDivisorRiggedPrimeTimeReflection_isometry
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeReflection s a)
        (preDivisorRiggedPrimeTimeReflection s b) =
      preDivisorRiggedPrimeWittPairing s a b := by
  rw [preDivisorRiggedPrimeTimeReflection_isSelfAdjoint hs,
    preDivisorRiggedPrimeTimeReflection_sq hs haxis]

private theorem preDivisorRiggedPrimeWittPairing_smul_right
    (s : ℂ) (c : ℝ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a (c • b) =
      c * preDivisorRiggedPrimeWittPairing s a b := by
  rw [preDivisorRiggedPrimeWittPairing_comm s a,
    preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimeWittPairing_comm s b a]

private theorem preDivisorRiggedPrimeWittPairing_neg_left
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s (-a) b =
      -preDivisorRiggedPrimeWittPairing s a b := by
  rw [show -a = (-1 : ℝ) • a by module,
    preDivisorRiggedPrimeWittPairing_smul_left]
  ring

private theorem preDivisorRiggedPrimeWittPairing_neg_right
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a (-b) =
      -preDivisorRiggedPrimeWittPairing s a b := by
  rw [show -b = (-1 : ℝ) • b by module,
    preDivisorRiggedPrimeWittPairing_smul_right]
  ring

private theorem preDivisorRiggedPrimeWittPairing_linearCombination_self
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (c d : ℝ) (x y : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s (c • x + d • y) (c • x + d • y) =
      c ^ 2 * preDivisorRiggedPrimeWittPairing s x x +
        2 * c * d * preDivisorRiggedPrimeWittPairing s x y +
        d ^ 2 * preDivisorRiggedPrimeWittPairing s y y := by
  rw [preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_add_right hs]
  simp only [preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimeWittPairing_smul_right]
  rw [preDivisorRiggedPrimeWittPairing_comm s y x]
  ring

/-! ## Fundamental-symmetry laws -/

theorem preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left
    (s : ℂ) (hleft : s.re < 1 / 2) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s a =
      preDivisorRiggedPrimeTimeReflection s a := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorOrientation_eq_one_of_left s hleft, one_smul]

theorem preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right
    (s : ℂ) (hright : 1 / 2 < s.re) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s a =
      -preDivisorRiggedPrimeTimeReflection s a := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorOrientation_eq_neg_one_of_right s hright]
  module

@[simp] theorem preDivisorRiggedPrimeTimeReflection_lineConj
    (s : ℂ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeTimeReflection (preDivisorLineConj s) a =
      preDivisorRiggedPrimeTimeReflection s a := by
  simp [preDivisorRiggedPrimeTimeReflection]

/-- Reflection exchanges the two signs of the source fundamental symmetry. -/
@[simp] theorem preDivisorRiggedPrimeFundamentalSymmetry_lineConj
    (s : ℂ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry (preDivisorLineConj s) a =
      -preDivisorRiggedPrimeFundamentalSymmetry s a := by
  simp [preDivisorRiggedPrimeFundamentalSymmetry]
  module

theorem preDivisorRiggedPrimeFundamentalSymmetry_add
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s (a + b) =
      preDivisorRiggedPrimeFundamentalSymmetry s a +
        preDivisorRiggedPrimeFundamentalSymmetry s b := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorRiggedPrimeTimeReflection_add hs,
    smul_add,
    preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorRiggedPrimeFundamentalSymmetry]

theorem preDivisorRiggedPrimeFundamentalSymmetry_smul
    (s : ℂ) (c : ℝ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s (c • a) =
      c • preDivisorRiggedPrimeFundamentalSymmetry s a := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorRiggedPrimeTimeReflection_smul, smul_comm,
    preDivisorRiggedPrimeFundamentalSymmetry]

/-- The source-selected fundamental symmetry is an involution on every left fibre. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_sq_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s
        (preDivisorRiggedPrimeFundamentalSymmetry s a) = a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  have haxis := (preDivisorRiggedPrimeTimeAxis_negative_left s hs0 hleft).ne
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
    preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
    preDivisorRiggedPrimeTimeReflection_sq hs haxis]

/-- The source-selected fundamental symmetry is an involution on every right fibre. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_sq_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s
        (preDivisorRiggedPrimeFundamentalSymmetry s a) = a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  have haxis := (preDivisorRiggedPrimeTimeAxis_positive_right s hright hs1).ne'
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright,
    preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright]
  rw [show -preDivisorRiggedPrimeTimeReflection s a =
      (-1 : ℝ) • preDivisorRiggedPrimeTimeReflection s a by module,
    preDivisorRiggedPrimeTimeReflection_smul,
    preDivisorRiggedPrimeTimeReflection_sq hs haxis]
  module

/-- The source-selected fundamental symmetry is self-adjoint for the rigged form. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_isSelfAdjoint
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeFundamentalSymmetry s a) b =
      preDivisorRiggedPrimeWittPairing s a
        (preDivisorRiggedPrimeFundamentalSymmetry s b) := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorRiggedPrimeFundamentalSymmetry,
    preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimeWittPairing_smul_right,
    preDivisorRiggedPrimeTimeReflection_isSelfAdjoint hs]

/-! ## Global positivity from exact index one -/

/-- Orthogonal projection away from the canonical time axis. -/
def preDivisorRiggedPrimeTimeOrthogonalProjection
    (s : ℂ) (a : DeningerHeightKothe) : DeningerHeightKothe :=
  a -
    (preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis /
      preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis) •
      preDivisorRiggedPrimeTimeAxis

theorem preDivisorRiggedPrimeTimeOrthogonalProjection_pairing_timeAxis
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeOrthogonalProjection s a)
        preDivisorRiggedPrimeTimeAxis = 0 := by
  rw [preDivisorRiggedPrimeTimeOrthogonalProjection, sub_eq_add_neg,
    preDivisorRiggedPrimeWittPairing_add_left hs]
  rw [show -((preDivisorRiggedPrimeWittPairing s a
      preDivisorRiggedPrimeTimeAxis /
        preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis
          preDivisorRiggedPrimeTimeAxis) • preDivisorRiggedPrimeTimeAxis) =
      (-(preDivisorRiggedPrimeWittPairing s a
        preDivisorRiggedPrimeTimeAxis /
          preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis
            preDivisorRiggedPrimeTimeAxis)) •
        preDivisorRiggedPrimeTimeAxis by module,
    preDivisorRiggedPrimeWittPairing_smul_left]
  field_simp
  ring

private theorem preDivisorRiggedPrimeWittPairing_nonneg_of_timeAxis_orthogonal_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (u : DeningerHeightKothe)
    (huorth : preDivisorRiggedPrimeWittPairing s u
      preDivisorRiggedPrimeTimeAxis = 0) :
    0 ≤ preDivisorRiggedPrimeWittPairing s u u := by
  by_contra hu
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  have haxis := preDivisorRiggedPrimeTimeAxis_negative_left s hs0 hleft
  have huu : preDivisorRiggedPrimeWittPairing s u u < 0 := lt_of_not_ge hu
  obtain ⟨c, d, hcd, hnonneg⟩ :=
    preDivisorRiggedPrimeWittPairing_atMostOneNegativeSquare_left s hs0 hleft
      preDivisorRiggedPrimeTimeAxis u haxis huu
  rw [preDivisorRiggedPrimeWittPairing_linearCombination_self hs] at hnonneg
  have hcross : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis u = 0 := by
    rw [preDivisorRiggedPrimeWittPairing_comm]
    exact huorth
  rw [hcross] at hnonneg
  simp only [mul_zero, add_zero] at hnonneg
  rcases hcd with hc | hd
  · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hfirst : c ^ 2 * preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis < 0 :=
      mul_neg_of_pos_of_neg hc2 haxis
    have hsecond : d ^ 2 * preDivisorRiggedPrimeWittPairing s u u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd2 huu.le
    linarith
  · have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    have hfirst : c ^ 2 * preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc2 haxis.le
    have hsecond : d ^ 2 * preDivisorRiggedPrimeWittPairing s u u < 0 :=
      mul_neg_of_pos_of_neg hd2 huu
    linarith

private theorem preDivisorRiggedPrimeWittPairing_nonpos_of_timeAxis_orthogonal_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (u : DeningerHeightKothe)
    (huorth : preDivisorRiggedPrimeWittPairing s u
      preDivisorRiggedPrimeTimeAxis = 0) :
    preDivisorRiggedPrimeWittPairing s u u ≤ 0 := by
  by_contra hu
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  have haxis := preDivisorRiggedPrimeTimeAxis_positive_right s hright hs1
  have huu : 0 < preDivisorRiggedPrimeWittPairing s u u := lt_of_not_ge hu
  obtain ⟨c, d, hcd, hnonpos⟩ :=
    preDivisorRiggedPrimeWittPairing_atMostOnePositiveSquare_right s hright hs1
      preDivisorRiggedPrimeTimeAxis u haxis huu
  rw [preDivisorRiggedPrimeWittPairing_linearCombination_self hs] at hnonpos
  have hcross : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis u = 0 := by
    rw [preDivisorRiggedPrimeWittPairing_comm]
    exact huorth
  rw [hcross] at hnonpos
  simp only [mul_zero, add_zero] at hnonpos
  rcases hcd with hc | hd
  · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hfirst : 0 < c ^ 2 * preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis :=
      mul_pos hc2 haxis
    have hsecond : 0 ≤ d ^ 2 * preDivisorRiggedPrimeWittPairing s u u :=
      mul_nonneg hd2 huu.le
    linarith
  · have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    have hfirst : 0 ≤ c ^ 2 * preDivisorRiggedPrimeWittPairing s
        preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis :=
      mul_nonneg hc2 haxis.le
    have hsecond : 0 < d ^ 2 * preDivisorRiggedPrimeWittPairing s u u :=
      mul_pos hd2 huu
    linarith

theorem preDivisorRiggedPrimeTimeOrthogonalProjection_self
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeTimeOrthogonalProjection s a)
        (preDivisorRiggedPrimeTimeOrthogonalProjection s a) =
      preDivisorRiggedPrimeWittPairing s a a -
        preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis ^ 2 /
          preDivisorRiggedPrimeWittPairing s
            preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeTimeOrthogonalProjection, sub_eq_add_neg]
  rw [preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_add_right hs]
  simp only [preDivisorRiggedPrimeWittPairing_neg_left,
    preDivisorRiggedPrimeWittPairing_neg_right,
    preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimeWittPairing_smul_right]
  rw [preDivisorRiggedPrimeWittPairing_comm s preDivisorRiggedPrimeTimeAxis a]
  field_simp
  ring

/-- **Global left polarization.**  The source-selected `J`-pairing is nonnegative on the full
nuclear Köthe carrier. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_nonneg_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) :
    0 ≤ preDivisorRiggedPrimePolarizedPairing s a a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  have haxisNeg := preDivisorRiggedPrimeTimeAxis_negative_left s hs0 hleft
  have haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0 :=
    haxisNeg.ne
  let u := preDivisorRiggedPrimeTimeOrthogonalProjection s a
  have huorth : preDivisorRiggedPrimeWittPairing s u
      preDivisorRiggedPrimeTimeAxis = 0 :=
    preDivisorRiggedPrimeTimeOrthogonalProjection_pairing_timeAxis hs haxis a
  have hu : 0 ≤ preDivisorRiggedPrimeWittPairing s u u :=
    preDivisorRiggedPrimeWittPairing_nonneg_of_timeAxis_orthogonal_left
      s hs0 hleft u huorth
  have hprojection := preDivisorRiggedPrimeTimeOrthogonalProjection_self hs haxis a
  have hcorrection :
      0 ≤ -(preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis ^ 2 /
        preDivisorRiggedPrimeWittPairing s
          preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis) := by
    exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos
      (sq_nonneg _) haxisNeg.le)
  have hpolar :
      preDivisorRiggedPrimePolarizedPairing s a a =
        preDivisorRiggedPrimeWittPairing s u u -
          preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis ^ 2 /
            preDivisorRiggedPrimeWittPairing s
              preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis := by
    rw [preDivisorRiggedPrimePolarizedPairing,
      preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
      preDivisorRiggedPrimeTimeReflection_pairing_right hs,
      hprojection]
    field_simp
    ring
  rw [hpolar]
  exact add_nonneg hu hcorrection

/-- **Global right polarization.**  The reflected source-selected `J`-pairing is nonnegative on
the full nuclear Köthe carrier. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_nonneg_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a : DeningerHeightKothe) :
    0 ≤ preDivisorRiggedPrimePolarizedPairing s a a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  have haxisPos := preDivisorRiggedPrimeTimeAxis_positive_right s hright hs1
  have haxis : preDivisorRiggedPrimeWittPairing s
      preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis ≠ 0 :=
    haxisPos.ne'
  let u := preDivisorRiggedPrimeTimeOrthogonalProjection s a
  have huorth : preDivisorRiggedPrimeWittPairing s u
      preDivisorRiggedPrimeTimeAxis = 0 :=
    preDivisorRiggedPrimeTimeOrthogonalProjection_pairing_timeAxis hs haxis a
  have hu : preDivisorRiggedPrimeWittPairing s u u ≤ 0 :=
    preDivisorRiggedPrimeWittPairing_nonpos_of_timeAxis_orthogonal_right
      s hright hs1 u huorth
  have hprojection := preDivisorRiggedPrimeTimeOrthogonalProjection_self hs haxis a
  have hcorrection :
      0 ≤ preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis ^ 2 /
        preDivisorRiggedPrimeWittPairing s
          preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis :=
    div_nonneg (sq_nonneg _) haxisPos.le
  have hpolar :
      preDivisorRiggedPrimePolarizedPairing s a a =
        -preDivisorRiggedPrimeWittPairing s u u +
          preDivisorRiggedPrimeWittPairing s a preDivisorRiggedPrimeTimeAxis ^ 2 /
            preDivisorRiggedPrimeWittPairing s
              preDivisorRiggedPrimeTimeAxis preDivisorRiggedPrimeTimeAxis := by
    rw [preDivisorRiggedPrimePolarizedPairing,
      preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright]
    rw [show -preDivisorRiggedPrimeTimeReflection s a =
        (-1 : ℝ) • preDivisorRiggedPrimeTimeReflection s a by module,
      preDivisorRiggedPrimeWittPairing_smul_right,
      preDivisorRiggedPrimeTimeReflection_pairing_right hs,
      hprojection]
    field_simp
    ring
  rw [hpolar]
  exact add_nonneg (neg_nonneg.mpr hu) hcorrection

/-! ## Polarized form and exact radical -/

/-- The polarized pairing is symmetric. -/
theorem preDivisorRiggedPrimePolarizedPairing_comm
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a b =
      preDivisorRiggedPrimePolarizedPairing s b a := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    ← preDivisorRiggedPrimeFundamentalSymmetry_isSelfAdjoint hs,
    preDivisorRiggedPrimeWittPairing_comm]
  rfl

theorem preDivisorRiggedPrimePolarizedPairing_add_left
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b c : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s (a + b) c =
      preDivisorRiggedPrimePolarizedPairing s a c +
        preDivisorRiggedPrimePolarizedPairing s b c := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimePolarizedPairing]

theorem preDivisorRiggedPrimePolarizedPairing_add_right
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b c : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a (b + c) =
      preDivisorRiggedPrimePolarizedPairing s a b +
        preDivisorRiggedPrimePolarizedPairing s a c := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimeFundamentalSymmetry_add hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimePolarizedPairing]

theorem preDivisorRiggedPrimePolarizedPairing_smul_left
    (s : ℂ) (c : ℝ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s (c • a) b =
      c * preDivisorRiggedPrimePolarizedPairing s a b := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimeWittPairing_smul_left,
    preDivisorRiggedPrimePolarizedPairing]

theorem preDivisorRiggedPrimePolarizedPairing_smul_right
    (s : ℂ) (c : ℝ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a (c • b) =
      c * preDivisorRiggedPrimePolarizedPairing s a b := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimeFundamentalSymmetry_smul,
    preDivisorRiggedPrimeWittPairing_smul_right,
    preDivisorRiggedPrimePolarizedPairing]

private theorem preDivisorRiggedPrimePolarizedPairing_linearCombination_self
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (c d : ℝ) (x y : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s (c • x + d • y) (c • x + d • y) =
      c ^ 2 * preDivisorRiggedPrimePolarizedPairing s x x +
        2 * c * d * preDivisorRiggedPrimePolarizedPairing s x y +
        d ^ 2 * preDivisorRiggedPrimePolarizedPairing s y y := by
  rw [preDivisorRiggedPrimePolarizedPairing_add_left hs,
    preDivisorRiggedPrimePolarizedPairing_add_right hs,
    preDivisorRiggedPrimePolarizedPairing_add_right hs]
  simp only [preDivisorRiggedPrimePolarizedPairing_smul_left,
    preDivisorRiggedPrimePolarizedPairing_smul_right]
  rw [preDivisorRiggedPrimePolarizedPairing_comm hs y x]
  ring

/-- Critical-line reflection preserves the positive polarization even though it negates both the
original form and its fundamental symmetry. -/
@[simp] theorem preDivisorRiggedPrimePolarizedPairing_lineConj
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing (preDivisorLineConj s) a b =
      preDivisorRiggedPrimePolarizedPairing s a b := by
  rw [preDivisorRiggedPrimePolarizedPairing,
    preDivisorRiggedPrimeFundamentalSymmetry_lineConj,
    preDivisorRiggedPrimeWittPairing_lineConj,
    preDivisorRiggedPrimeWittPairing_neg_right,
    preDivisorRiggedPrimePolarizedPairing]
  ring

private theorem preDivisorRiggedPrimePolarizedPairing_cross_eq_zero_of_self_eq_zero
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (hnonneg : ∀ z : DeningerHeightKothe,
      0 ≤ preDivisorRiggedPrimePolarizedPairing s z z)
    (x : DeningerHeightKothe)
    (hx : preDivisorRiggedPrimePolarizedPairing s x x = 0)
    (y : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s x y = 0 := by
  let c := preDivisorRiggedPrimePolarizedPairing s x y
  let d := preDivisorRiggedPrimePolarizedPairing s y y
  have hd : 0 ≤ d := hnonneg y
  by_cases hd0 : d = 0
  · have hplus := hnonneg ((1 : ℝ) • x + (1 : ℝ) • y)
    have hminus := hnonneg ((1 : ℝ) • x + (-1 : ℝ) • y)
    rw [preDivisorRiggedPrimePolarizedPairing_linearCombination_self hs,
      hx] at hplus hminus
    change preDivisorRiggedPrimePolarizedPairing s y y = 0 at hd0
    rw [hd0] at hplus hminus
    nlinarith
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have htrial := hnonneg
      ((1 : ℝ) • x + (-(c / d)) • y)
    have htrialEq :
        preDivisorRiggedPrimePolarizedPairing s
            ((1 : ℝ) • x + (-(c / d)) • y)
            ((1 : ℝ) • x + (-(c / d)) • y) =
          -(c ^ 2 / d) := by
      rw [preDivisorRiggedPrimePolarizedPairing_linearCombination_self hs, hx]
      dsimp [c, d]
      field_simp
      ring
    rw [htrialEq] at htrial
    by_contra hc
    have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    have hquot : 0 < c ^ 2 / d := div_pos hc2 hdpos
    linarith

/-- Nullspace of the positive polarization is exactly the original rigged radical on the left. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_radical_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
      PreDivisorRiggedPrimeRadical s a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  constructor
  · intro ha b
    have hcross :=
      preDivisorRiggedPrimePolarizedPairing_cross_eq_zero_of_self_eq_zero
        hs (preDivisorRiggedPrimePolarizedPairing_self_nonneg_left s hs0 hleft)
        a ha (preDivisorRiggedPrimeFundamentalSymmetry s b)
    rw [preDivisorRiggedPrimePolarizedPairing,
      preDivisorRiggedPrimeFundamentalSymmetry_sq_left s hs0 hleft] at hcross
    exact hcross
  · intro ha
    exact ha (preDivisorRiggedPrimeFundamentalSymmetry s a)

/-- Nullspace of the positive polarization is exactly the original rigged radical on the right. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_radical_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
      PreDivisorRiggedPrimeRadical s a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  constructor
  · intro ha b
    have hcross :=
      preDivisorRiggedPrimePolarizedPairing_cross_eq_zero_of_self_eq_zero
        hs (preDivisorRiggedPrimePolarizedPairing_self_nonneg_right s hright hs1)
        a ha (preDivisorRiggedPrimeFundamentalSymmetry s b)
    rw [preDivisorRiggedPrimePolarizedPairing,
      preDivisorRiggedPrimeFundamentalSymmetry_sq_right s hright hs1] at hcross
    exact hcross
  · intro ha
    exact ha (preDivisorRiggedPrimeFundamentalSymmetry s a)

/-! ## Closed source-polarization package -/

/-- The source-selected symmetry as an actual real-linear operator on the nuclear Köthe source. -/
def preDivisorRiggedPrimeFundamentalSymmetryLinear
    (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    DeningerHeightKothe →ₗ[ℝ] DeningerHeightKothe where
  toFun := preDivisorRiggedPrimeFundamentalSymmetry s
  map_add' := preDivisorRiggedPrimeFundamentalSymmetry_add hs
  map_smul' := preDivisorRiggedPrimeFundamentalSymmetry_smul s

@[simp] theorem preDivisorRiggedPrimeFundamentalSymmetryLinear_apply
    (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetryLinear s hs a =
      preDivisorRiggedPrimeFundamentalSymmetry s a := rfl

/-- The fundamental symmetry preserves the rigged form on left fibres. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_isometry_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeFundamentalSymmetry s a)
        (preDivisorRiggedPrimeFundamentalSymmetry s b) =
      preDivisorRiggedPrimeWittPairing s a b := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  have haxis := (preDivisorRiggedPrimeTimeAxis_negative_left s hs0 hleft).ne
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
    preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
    preDivisorRiggedPrimeTimeReflection_isometry hs haxis]

/-- The fundamental symmetry preserves the rigged form on right fibres. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_isometry_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeFundamentalSymmetry s a)
        (preDivisorRiggedPrimeFundamentalSymmetry s b) =
      preDivisorRiggedPrimeWittPairing s a b := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  have haxis := (preDivisorRiggedPrimeTimeAxis_positive_right s hright hs1).ne'
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright,
    preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright,
    preDivisorRiggedPrimeWittPairing_neg_left,
    preDivisorRiggedPrimeWittPairing_neg_right,
    preDivisorRiggedPrimeTimeReflection_isometry hs haxis]
  ring

/-- The positive polarization loses exactly the invisible real prime coefficients on the left. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_prime_re_eq_zero_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
      ∀ p : Nat.Primes,
        (((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re) = 0 := by
  rw [preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_radical_left
      s hs0 hleft a,
    preDivisorRiggedPrimeRadical_iff_left s hs0 hleft a]

/-- The positive polarization loses exactly the invisible real prime coefficients on the right. -/
theorem preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_prime_re_eq_zero_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a : DeningerHeightKothe) :
    preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
      ∀ p : Nat.Primes,
        (((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re) = 0 := by
  rw [preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_radical_right
      s hright hs1 a,
    preDivisorRiggedPrimeRadical_iff_right s hright hs1 a]

/--
**SC source-polarization capstone.**  The two canonical prime axes produce an unconditional
real-linear fundamental symmetry on every open-strip fibre.  It is involutive and rigged-form
self-adjoint, and its reflection-even polarized form is nonnegative with exactly the previously
classified coefficient radical on both sides of the critical wall.
-/
theorem preDivisorRiggedPrimeFundamentalSymmetry_capstone :
    (∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      (∀ a : DeningerHeightKothe,
        preDivisorRiggedPrimeFundamentalSymmetry s
            (preDivisorRiggedPrimeFundamentalSymmetry s a) = a) ∧
      (∀ a b : DeningerHeightKothe,
        preDivisorRiggedPrimeWittPairing s
            (preDivisorRiggedPrimeFundamentalSymmetry s a) b =
          preDivisorRiggedPrimeWittPairing s a
            (preDivisorRiggedPrimeFundamentalSymmetry s b)) ∧
      (∀ a : DeningerHeightKothe,
        0 ≤ preDivisorRiggedPrimePolarizedPairing s a a ∧
          (preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
            ∀ p : Nat.Primes,
              (((a : DeningerPrimeLattice → ℂ)
                (preDivisorRiggedPrimeAxis p)).re) = 0))) ∧
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∀ a : DeningerHeightKothe,
        preDivisorRiggedPrimeFundamentalSymmetry s
            (preDivisorRiggedPrimeFundamentalSymmetry s a) = a) ∧
      (∀ a b : DeningerHeightKothe,
        preDivisorRiggedPrimeWittPairing s
            (preDivisorRiggedPrimeFundamentalSymmetry s a) b =
          preDivisorRiggedPrimeWittPairing s a
            (preDivisorRiggedPrimeFundamentalSymmetry s b)) ∧
      (∀ a : DeningerHeightKothe,
        0 ≤ preDivisorRiggedPrimePolarizedPairing s a a ∧
          (preDivisorRiggedPrimePolarizedPairing s a a = 0 ↔
            ∀ p : Nat.Primes,
              (((a : DeningerPrimeLattice → ℂ)
                (preDivisorRiggedPrimeAxis p)).re) = 0))) ∧
    (∀ s : ℂ, ∀ a b : DeningerHeightKothe,
      preDivisorRiggedPrimePolarizedPairing (preDivisorLineConj s) a b =
        preDivisorRiggedPrimePolarizedPairing s a b) := by
  constructor
  · intro s hs0 hleft
    have hs : 0 < s.re ∧ s.re < 1 :=
      ⟨hs0, lt_trans hleft (by norm_num)⟩
    exact ⟨preDivisorRiggedPrimeFundamentalSymmetry_sq_left s hs0 hleft,
      preDivisorRiggedPrimeFundamentalSymmetry_isSelfAdjoint hs,
      fun a => ⟨preDivisorRiggedPrimePolarizedPairing_self_nonneg_left
          s hs0 hleft a,
        preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_prime_re_eq_zero_left
          s hs0 hleft a⟩⟩
  constructor
  · intro s hright hs1
    have hs : 0 < s.re ∧ s.re < 1 :=
      ⟨lt_trans (by norm_num) hright, hs1⟩
    exact ⟨preDivisorRiggedPrimeFundamentalSymmetry_sq_right s hright hs1,
      preDivisorRiggedPrimeFundamentalSymmetry_isSelfAdjoint hs,
      fun a => ⟨preDivisorRiggedPrimePolarizedPairing_self_nonneg_right
          s hright hs1 a,
        preDivisorRiggedPrimePolarizedPairing_self_eq_zero_iff_prime_re_eq_zero_right
          s hright hs1 a⟩⟩
  · exact preDivisorRiggedPrimePolarizedPairing_lineConj

end

end RHTower
