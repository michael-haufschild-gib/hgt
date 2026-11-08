import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!+# The exact dissipating class for conjugate pairs

The interaction of two upper zeros includes both their direct interaction and
their interactions with the reflected zeros. Its sign is controlled by the
logarithmic derivative weight `y F'(y)`, rather than by `F'` alone. Positivity
for every pair is equivalent to this weight being nonnegative and increasing.
-/

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- The interaction of two upper roots, including their reflected partners. -/
def conjugatePairWork (A B a b d : ℝ) : ℝ :=
  (A - B) * (a - b) / (d ^ 2 + (a - b) ^ 2) +
    (A + B) * (a + b) / (d ^ 2 + (a + b) ^ 2)

/-- Clearing the two squared distances exposes the logarithmic derivative weights. -/
theorem conjugatePairWork_numerator {A B a b d : ℝ}
    (hm : d ^ 2 + (a - b) ^ 2 ≠ 0) (hp : d ^ 2 + (a + b) ^ 2 ≠ 0) :
    conjugatePairWork A B a b d * (d ^ 2 + (a - b) ^ 2) *
      (d ^ 2 + (a + b) ^ 2) =
      2 * ((a * A + b * B) * d ^ 2 + (a ^ 2 - b ^ 2) * (a * A - b * B)) := by
  unfold conjugatePairWork
  field_simp [hm, hp]
  ring

private theorem reflectedDistance_pos {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < d ^ 2 + (a + b) ^ 2 := by
  exact add_pos_of_nonneg_of_pos (sq_nonneg d) (sq_pos_of_pos (add_pos ha hb))

/-- Nonnegative increasing logarithmic weights dissipate every conjugate pair. -/
theorem conjugatePairWork_nonneg {f : ℝ → ℝ}
    (hn : ∀ y, 0 < y → 0 ≤ y * f y)
    (hm : MonotoneOn (fun y => y * f y) (Set.Ioi 0))
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d ^ 2 + (a - b) ^ 2) :
    0 ≤ conjugatePairWork (f a) (f b) a b d := by
  have hp := reflectedDistance_pos (d := d) ha hb
  have hprod : 0 ≤ (a ^ 2 - b ^ 2) * (a * f a - b * f b) := by
    rcases le_total a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (sq_le_sq₀ ha.le hb.le |>.mpr hab))
        (sub_nonpos.mpr (hm ha hb hab))
    · exact mul_nonneg (sub_nonneg.mpr (sq_le_sq₀ hb.le ha.le |>.mpr hba))
        (sub_nonneg.mpr (hm hb ha hba))
  have hnum := conjugatePairWork_numerator (A := f a) (B := f b) hd.ne' hp.ne'
  have hsign : 0 ≤ conjugatePairWork (f a) (f b) a b d *
      (d ^ 2 + (a - b) ^ 2) * (d ^ 2 + (a + b) ^ 2) := by
    rw [hnum]
    exact mul_nonneg (by positivity) (add_nonneg
      (mul_nonneg (add_nonneg (hn a ha) (hn b hb)) (sq_nonneg d)) hprod)
  exact (mul_nonneg_iff_of_pos_right hd).mp
    ((mul_nonneg_iff_of_pos_right hp).mp hsign)

/-- Equal-height pairs force nonnegativity; vertically aligned pairs force monotonicity. -/
theorem conjugatePairWork_nonneg_iff (f : ℝ → ℝ) :
    (∀ a b d : ℝ, 0 < a → 0 < b → 0 < d ^ 2 + (a - b) ^ 2 →
      0 ≤ conjugatePairWork (f a) (f b) a b d) ↔
    (∀ y, 0 < y → 0 ≤ y * f y) ∧
      MonotoneOn (fun y => y * f y) (Set.Ioi 0) := by
  constructor
  · intro h
    constructor
    · intro a ha
      have hd : 0 < (1 : ℝ) ^ 2 + (a - a) ^ 2 := by positivity
      have hp := reflectedDistance_pos (d := 1) ha ha
      have hn := conjugatePairWork_numerator (A := f a) (B := f a) hd.ne' hp.ne'
      have hs := mul_nonneg (mul_nonneg (h a a 1 ha ha hd) hd.le) hp.le
      rw [hn] at hs
      nlinarith only [hs]
    · intro a ha b hb hab
      rcases eq_or_lt_of_le hab with he | hlt
      · rw [he]
      have hd : 0 < (0 : ℝ) ^ 2 + (a - b) ^ 2 := by
        simpa only [zero_pow two_ne_zero, zero_add] using
          sq_pos_of_ne_zero (sub_ne_zero.mpr hlt.ne)
      have hp := reflectedDistance_pos (d := 0) ha hb
      have hn := conjugatePairWork_numerator (A := f a) (B := f b) hd.ne' hp.ne'
      have hs := mul_nonneg (mul_nonneg (h a b 0 ha hb hd) hd.le) hp.le
      rw [hn] at hs
      have hsq : a ^ 2 < b ^ 2 := (sq_lt_sq₀ ha.le hb.le).mpr hlt
      by_contra hnot
      have hg : 0 < a * f a - b * f b := sub_pos.mpr (lt_of_not_ge hnot)
      have hx := mul_neg_of_neg_of_pos (sub_neg.mpr hsq) hg
      nlinarith only [hs, hx]
  · rintro ⟨hn, hm⟩ a b d ha hb hd
    exact conjugatePairWork_nonneg hn hm ha hb hd

#print axioms conjugatePairWork_nonneg_iff

/-- Derivative weight of the elapsed-depth moment `(y²+c)^q`. -/
def elapsedDepthWeight (q c y : ℝ) : ℝ :=
  2 * q * y * (y ^ 2 + c) ^ (q - 1)

private theorem logarithmic_elapsedDepthWeight {q c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) :
    y * elapsedDepthWeight q c y =
      2 * q * (y ^ 2 / (y ^ 2 + c) * (y ^ 2 + c) ^ q) := by
  have hbase : 0 < y ^ 2 + c := add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) hc
  rw [elapsedDepthWeight, Real.rpow_sub hbase, Real.rpow_one]
  ring

/-- Every positive power is admissible, including powers below one. -/
theorem elapsedDepthWeight_admissible {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (∀ y, 0 < y → 0 ≤ y * elapsedDepthWeight q c y) ∧
      MonotoneOn (fun y => y * elapsedDepthWeight q c y) (Set.Ioi 0) := by
  constructor
  · intro y hy
    unfold elapsedDepthWeight
    exact mul_nonneg hy.le (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hq) hy.le)
      (Real.rpow_nonneg (add_nonneg (sq_nonneg y) hc) _))
  · intro a ha b hb hab
    change a * elapsedDepthWeight q c a ≤ b * elapsedDepthWeight q c b
    rw [logarithmic_elapsedDepthWeight hc ha, logarithmic_elapsedDepthWeight hc hb]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) hq)
    have habsq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha.le hb.le).mpr hab
    have hapos : 0 < a ^ 2 + c := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hc
    have hbpos : 0 < b ^ 2 + c := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) hc
    have hratio : a ^ 2 / (a ^ 2 + c) ≤ b ^ 2 / (b ^ 2 + c) := by
      rw [div_le_div_iff₀ hapos hbpos]
      nlinarith only [mul_nonneg hc (sub_nonneg.mpr habsq)]
    exact mul_le_mul hratio (Real.rpow_le_rpow hapos.le (add_le_add habsq le_rfl) hq)
      (Real.rpow_nonneg hapos.le _) (div_nonneg (sq_nonneg b) hbpos.le)

/-- The interaction of distinct conjugate pairs dissipates every elapsed-depth power. -/
theorem elapsedDepth_conjugatePairWork_nonneg {q c a b d : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d ^ 2 + (a - b) ^ 2) :
    0 ≤ conjugatePairWork (elapsedDepthWeight q c a) (elapsedDepthWeight q c b) a b d :=
  conjugatePairWork_nonneg (elapsedDepthWeight_admissible hq hc).1
    (elapsedDepthWeight_admissible hq hc).2 ha hb hd

#print axioms elapsedDepth_conjugatePairWork_nonneg

/-- The imaginary reciprocal field of another upper zero and its conjugate. -/
def upperPairField (a b d : ℝ) : ℝ :=
  (a - b) / (d ^ 2 + (a - b) ^ 2) + (a + b) / (d ^ 2 + (a + b) ^ 2)

theorem upperPairField_symmetrize (A B a b d : ℝ) :
    A * upperPairField a b d + B * upperPairField b a (-d) =
      conjugatePairWork A B a b d := by
  unfold upperPairField conjugatePairWork
  rw [neg_sq, show (b - a) ^ 2 = (a - b) ^ 2 by ring, add_comm b a]
  ring

/-- Summing complete conjugate pairs preserves the logarithmic-weight sign. -/
theorem sum_upperPairField_nonneg {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x y : ι → ℝ) (f : ℝ → ℝ)
    (hy : ∀ i ∈ S, 0 < y i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      0 < (x i - x j) ^ 2 + (y i - y j) ^ 2)
    (hn : ∀ a, 0 < a → 0 ≤ a * f a)
    (hm : MonotoneOn (fun a => a * f a) (Set.Ioi 0)) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      if i = j then 0 else f (y i) * upperPairField (y i) (y j) (x i - x j) := by
  let W : ι → ι → ℝ := fun i j =>
    if i = j then 0 else f (y i) * upperPairField (y i) (y j) (x i - x j)
  have hterm : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ W i j + W j i := by
    intro i hi j hj
    by_cases he : i = j
    · subst j
      simp only [W, if_true, add_zero, le_refl]
    · have hd : x j - x i = -(x i - x j) := by ring
      simpa only [W, if_neg he, if_neg (Ne.symm he), hd,
        upperPairField_symmetrize] using
        conjugatePairWork_nonneg hn hm (hy i hi) (hy j hj) (hsep i hi j hj he)
  have hsum := Finset.sum_nonneg fun i hi => Finset.sum_nonneg (hterm i hi)
  have hswap : (∑ i ∈ S, ∑ j ∈ S, W j i) = ∑ i ∈ S, ∑ j ∈ S, W i j :=
    Finset.sum_comm
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  change 0 ≤ ∑ i ∈ S, ∑ j ∈ S, W i j
  linarith only [hsum]

/-- Every upper root pays its own conjugate's velocity; all other pairs dissipate. -/
theorem elapsedDepth_packet_drift_nonpos {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x y : ι → ℝ) {q c : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hy : ∀ i ∈ S, 0 < y i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      0 < (x i - x j) ^ 2 + (y i - y j) ^ 2) :
    (∑ i ∈ S, (2 * q * (y i ^ 2 + c) ^ (q - 1) +
      elapsedDepthWeight q c (y i) *
        (-(y i)⁻¹ - 2 * ∑ j ∈ S,
          if i = j then 0 else upperPairField (y i) (y j) (x i - x j)))) ≤ 0 := by
  have hw := elapsedDepthWeight_admissible hq hc
  have hsum := sum_upperPairField_nonneg S x y (elapsedDepthWeight q c) hy hsep hw.1 hw.2
  have heq (i : ι) (hi : i ∈ S) :
      2 * q * (y i ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c (y i) *
        (-(y i)⁻¹ - 2 * ∑ j ∈ S,
          if i = j then 0 else upperPairField (y i) (y j) (x i - x j)) =
      -2 * ∑ j ∈ S, if i = j then 0 else
        elapsedDepthWeight q c (y i) * upperPairField (y i) (y j) (x i - x j) := by
    have hmul : (∑ j ∈ S, if i = j then 0 else
        elapsedDepthWeight q c (y i) * upperPairField (y i) (y j) (x i - x j)) =
        elapsedDepthWeight q c (y i) * ∑ j ∈ S,
          if i = j then 0 else upperPairField (y i) (y j) (x i - x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp only [mul_zero]
    rw [hmul, elapsedDepthWeight]
    have hcancel : y i * (y i)⁻¹ = 1 := mul_inv_cancel₀ (hy i hi).ne'
    calc
      _ = 2 * q * (y i ^ 2 + c) ^ (q - 1) * (1 - y i * (y i)⁻¹) -
          2 * (2 * q * y i * (y i ^ 2 + c) ^ (q - 1)) *
            (∑ j ∈ S, if i = j then 0 else upperPairField (y i) (y j) (x i - x j)) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hsum

#print axioms elapsedDepth_packet_drift_nonpos

/-- The time derivative of an elapsed-depth moment separates the heat credit
from the work done by the zero's vertical velocity. -/
theorem elapsedDepth_hasDerivWithinAt {y : ℝ → ℝ} {v t a q : ℝ} {s : Set ℝ}
    (hy : HasDerivWithinAt y v s t) (hypos : 0 < y t) (hat : a ≤ t) :
    HasDerivWithinAt (fun u => (y u ^ 2 + 2 * (u - a)) ^ q)
      (2 * q * (y t ^ 2 + 2 * (t - a)) ^ (q - 1) +
        elapsedDepthWeight q (2 * (t - a)) (y t) * v) s t := by
  have hbase : 0 < y t ^ 2 + 2 * (t - a) :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hypos)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hat))
  have htime := (HasDerivAt.const_mul 2 ((hasDerivAt_id t).sub_const a)).hasDerivWithinAt
    (s := s)
  have hd := ((hy.pow 2).add htime).rpow_const (Or.inl hbase.ne') (p := q)
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at hd
  convert hd using 1
  unfold elapsedDepthWeight
  ring

/-- Real exterior roots, or any additional downward field, preserve dissipation. -/
theorem elapsedDepth_packet_drift_nonpos_of_velocity_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x y v : ι → ℝ) {q c : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hy : ∀ i ∈ S, 0 < y i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      0 < (x i - x j) ^ 2 + (y i - y j) ^ 2)
    (hv : ∀ i ∈ S, v i ≤ -(y i)⁻¹ - 2 * ∑ j ∈ S,
      if i = j then 0 else upperPairField (y i) (y j) (x i - x j)) :
    (∑ i ∈ S, (2 * q * (y i ^ 2 + c) ^ (q - 1) +
      elapsedDepthWeight q c (y i) * v i)) ≤ 0 := by
  apply le_trans _ (elapsedDepth_packet_drift_nonpos S x y hq hc hy hsep)
  apply Finset.sum_le_sum
  intro i hi
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left (hv i hi)
  unfold elapsedDepthWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hq) (hy i hi).le)
    (Real.rpow_nonneg (add_nonneg (sq_nonneg _) hc) _)

#print axioms elapsedDepth_hasDerivWithinAt
#print axioms elapsedDepth_packet_drift_nonpos_of_velocity_le

end

end GaloisForLFunctions.ArithmeticElectrostatics
