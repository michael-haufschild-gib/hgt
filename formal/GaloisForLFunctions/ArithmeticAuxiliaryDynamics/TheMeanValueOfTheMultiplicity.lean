import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil

/-!
# The mean value of the multiplicity

The multiplicity of a balanced stencil has mean `w/2`, and it reaches that mean at a scale set by the
first moment `E = Σ |c(k)| k` of its coefficients:

`|Σ_{r<n} g(r) − n w/2| ≤ E/8`.

So over a block `[Y, 2Y)` with `Y ≍ E/w` the multiplicity has size `w`. A block at scale `Y` costs
slope `≍ w/Y`, which gives the mean-value law `144 T E ≥ w²` for `w ≥ 4m`. A large peak therefore has
a price: the slope pays for it unless the first moment is even larger.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The first moment `E = Σ |c(k)| k` of the coefficients. -/
def firstMoment (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, |(c k : ℝ)| * k

/-- The partial sum of a residue sequence, in closed form. -/
theorem sum_range_mod {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∑ r ∈ range n, ((r % k : ℕ) : ℝ) =
      (n : ℝ) * ((k : ℝ) - 1) / 2 - ((n % k : ℕ) : ℝ) * ((k : ℝ) - ((n % k : ℕ) : ℝ)) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hdiv := Nat.div_add_mod n k
    have hlt := Nat.mod_lt n hk
    by_cases h : n % k + 1 < k
    · have hmod : (n + 1) % k = n % k + 1 := by
        have hrew : n + 1 = (n % k + 1) + k * (n / k) := by omega
        rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
      rw [hmod]
      push_cast
      ring
    · have hk' : k = n % k + 1 := by omega
      have hmod : (n + 1) % k = 0 := by
        have hrew : n + 1 = k * (n / k + 1) := by
          rw [mul_add, mul_one]
          omega
        rw [hrew, Nat.mul_mod_right]
      have hkR : (k : ℝ) = ((n % k : ℕ) : ℝ) + 1 := by exact_mod_cast hk'
      rw [hmod, hkR]
      push_cast
      ring

/-- **The partial sum of the multiplicity.** -/
theorem sum_range_stepWeight {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (n : ℕ) :
    ∑ r ∈ range n, (stepWeight c r : ℝ) = (n : ℝ) * ((peak c : ℝ) / 2) +
      ∑ k ∈ c.support, ((c k : ℝ) / k) * (((n % k : ℕ) : ℝ) * ((k : ℝ) - ((n % k : ℕ) : ℝ)) / 2) := by
  have hswap : ∑ r ∈ range n, (stepWeight c r : ℝ) =
      ∑ k ∈ c.support, (-(c k : ℝ) / k) * ∑ r ∈ range n, ((r % k : ℕ) : ℝ) := by
    simp_rw [stepWeight_eq_sum_mod hc0 hbal, mul_sum]
    exact sum_comm
  rw [hswap]
  have hterm : ∀ k ∈ c.support, (-(c k : ℝ) / k) * ∑ r ∈ range n, ((r % k : ℕ) : ℝ) =
      (n : ℝ) / 2 * (-(c k : ℝ) + (c k : ℝ) / k) +
        ((c k : ℝ) / k) * (((n % k : ℕ) : ℝ) * ((k : ℝ) - ((n % k : ℕ) : ℝ)) / 2) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    rw [sum_range_mod hk0]
    field_simp
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_add_distrib]
  have hb : ∑ k ∈ c.support, (c k : ℝ) / k = 0 := hbal
  rw [hb, add_zero, sum_neg_distrib]
  congr 1
  rw [peak]
  push_cast
  ring

/-- **The mean-value inequality.** `|Σ_{r<n} g(r) − n w/2| ≤ E/8`. -/
theorem abs_sum_range_stepWeight_sub_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (n : ℕ) :
    |∑ r ∈ range n, (stepWeight c r : ℝ) - (n : ℝ) * ((peak c : ℝ) / 2)| ≤ firstMoment c / 8 := by
  rw [sum_range_stepWeight hc0 hbal, add_sub_cancel_left, firstMoment, sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set s : ℝ := ((n % k : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hsk : s ≤ k := by
    rw [hs]
    exact_mod_cast (Nat.mod_lt n hk0).le
  have hprod0 : 0 ≤ s * ((k : ℝ) - s) := mul_nonneg hs0 (by linarith)
  have hprod1 : s * ((k : ℝ) - s) ≤ (k : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * s - k)]
  rw [abs_mul, abs_div, abs_of_pos hkR, abs_of_nonneg (by positivity : 0 ≤ s * ((k : ℝ) - s) / 2)]
  have habs := abs_nonneg (c k : ℝ)
  calc |(c k : ℝ)| / k * (s * ((k : ℝ) - s) / 2)
      ≤ |(c k : ℝ)| / k * ((k : ℝ) ^ 2 / 4 / 2) := by gcongr
    _ = |(c k : ℝ)| * k / 8 := by
        field_simp
        ring

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

theorem coeffMass_le_firstMoment (hP : IsProducer c m B) : coeffMass c ≤ firstMoment c := by
  refine sum_le_sum fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hP.zero
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have := abs_nonneg (c k : ℝ)
  nlinarith

theorem firstMoment_le_mul (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    firstMoment c ≤ (K : ℝ) * coeffMass c := by
  rw [firstMoment, coeffMass, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hK k hk
  have := abs_nonneg (c k : ℝ)
  nlinarith

/-- The excess bounds the mean of `g − m` over a block `[Y + 1, 2Y + 1)`. -/
private lemma block_le_excess (hP : IsProducer c m B) {Y : ℕ} (hY : 1 ≤ Y) :
    (∑ x ∈ range Y, ((stepWeight c (Y + x + 1) : ℝ) - m)) / (6 * (Y : ℝ) ^ 2) ≤ excess c m B := by
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hdenom : 0 < 6 * (Y : ℝ) ^ 2 := by positivity
  have hsum : ∑ j ∈ range (Y + Y), excessTerm m B c j ≤ excess c m B :=
    sum_le_hasSum _ (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess
  rw [Finset.sum_range_add] at hsum
  have hfirst : 0 ≤ ∑ j ∈ range Y, excessTerm m B c j :=
    sum_nonneg fun j _ => hP.excessTerm_nonneg j
  refine le_trans ?_ (by linarith : ∑ x ∈ range Y, excessTerm m B c (Y + x) ≤ excess c m B)
  rw [sum_div]
  refine sum_le_sum fun x hx => ?_
  have hxY : (x : ℝ) + 1 ≤ Y := by exact_mod_cast mem_range.mp hx
  have hG := hP.tailWeight_nonneg (Y + x)
  have hE := hP.excessTerm_nonneg (Y + x)
  have hid := tailWeight_eq c m B (Y + x)
  have hlow : (stepWeight c (Y + x + 1) : ℝ) - m ≤ tailWeight c m B (Y + x) := by
    rw [tailWeight]
    split_ifs
    · exact le_rfl
    · have := hP.m_pos
      linarith
  have hprod : (((Y + x : ℕ) : ℝ) + 1) * (((Y + x : ℕ) : ℝ) + 2) ≤ 6 * (Y : ℝ) ^ 2 := by
    push_cast
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith
  have hup : tailWeight c m B (Y + x) ≤ excessTerm m B c (Y + x) * (6 * (Y : ℝ) ^ 2) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hprod hE
  rw [div_le_iff₀ hdenom]
  linarith

/-- **The mean-value law.** If `w ≥ 4m`, then `w² ≤ 144 T E`. -/
theorem peak_sq_le (hP : IsProducer c m B) (hw4 : 4 * (m : ℝ) ≤ peak c) :
    (peak c : ℝ) ^ 2 ≤ 144 * excess c m B * firstMoment c := by
  have hm := hP.m_pos
  have hw : (0 : ℝ) < peak c := by linarith
  have hwE : (peak c : ℝ) ≤ firstMoment c :=
    (peak_le_coeffMass c).trans hP.coeffMass_le_firstMoment
  have hE : 0 < firstMoment c := by linarith
  set w : ℝ := (peak c : ℝ) with hwdef
  set E := firstMoment c with hEdef
  set y : ℝ := 2 * E / w with hy
  have hy2 : 2 ≤ y := by
    rw [hy, le_div_iff₀ hw]; linarith
  set Y : ℕ := ⌈y⌉₊ with hYdef
  have hYy : y ≤ Y := Nat.le_ceil y
  have hYle : (Y : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact_mod_cast this
  have hYpos : (0 : ℝ) < Y := by linarith
  -- The block sum.
  have hsplit := Finset.sum_range_add (fun r => (stepWeight c r : ℝ)) (Y + 1) Y
  have hA := abs_le.mp (abs_sum_range_stepWeight_sub_le hP.zero hP.balanced (Y + 1 + Y))
  have hB := abs_le.mp (abs_sum_range_stepWeight_sub_le hP.zero hP.balanced (Y + 1))
  have hblock : (Y : ℝ) * (w / 2) - E / 4 ≤ ∑ x ∈ range Y, (stepWeight c (Y + 1 + x) : ℝ) := by
    push_cast at hA hB
    have h1 := hA.1
    have h2 := hB.2
    rw [← hwdef, ← hEdef] at h1 h2
    have hexp : ((Y : ℝ) + 1 + (Y : ℝ)) * (w / 2) = ((Y : ℝ) + 1) * (w / 2) + (Y : ℝ) * (w / 2) := by
      ring
    linarith
  have hexcess := hP.block_le_excess hY1
  have hrew : ∑ x ∈ range Y, ((stepWeight c (Y + x + 1) : ℝ) - m) =
      ∑ x ∈ range Y, (stepWeight c (Y + 1 + x) : ℝ) - (Y : ℝ) * m := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [show Y + x + 1 = Y + 1 + x by ring]
  rw [hrew] at hexcess
  have hdenom : 0 < 6 * (Y : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hdenom] at hexcess
  -- The block has mass at least `Y w / 8`.
  have hYw : E / 2 ≤ (Y : ℝ) * (w / 4) := by
    have h1 : y * w = 2 * E := by rw [hy]; field_simp
    nlinarith
  have hmass : (Y : ℝ) * (w / 8) ≤ excess c m B * (6 * (Y : ℝ) ^ 2) := by
    have h4 : (Y : ℝ) * (m : ℝ) ≤ (Y : ℝ) * (w / 4) := by
      apply mul_le_mul_of_nonneg_left _ hYpos.le
      linarith
    linarith
  have hT : w / 48 ≤ excess c m B * (Y : ℝ) := by
    have h := hP.excess_pos
    have hdiv : (Y : ℝ) * (w / 48) ≤ (Y : ℝ) * (excess c m B * (Y : ℝ)) := by
      nlinarith
    exact le_of_mul_le_mul_left hdiv hYpos
  have hY3 : (Y : ℝ) * w ≤ 3 * E := by
    have h1 : y * w = 2 * E := by rw [hy]; field_simp
    have h2 : (y + 1) * w ≤ 3 * E := by nlinarith
    exact (mul_le_mul_of_nonneg_right hYle hw.le).trans h2
  have hTpos := hP.excess_pos
  have hfinal : w ^ 2 = 48 * w * (w / 48) := by ring
  rw [hfinal]
  calc 48 * w * (w / 48) ≤ 48 * w * (excess c m B * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 48 * excess c m B * ((Y : ℝ) * w) := by ring
    _ ≤ 48 * excess c m B * (3 * E) := mul_le_mul_of_nonneg_left hY3 (by positivity)
    _ = 144 * excess c m B * E := by ring

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
