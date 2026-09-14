import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Fixed arithmetic orderings of the alternating Dirichlet source

After `N` rounds of `a` odd terms followed by `b` even terms, `roundPrefix` contains
exactly the first `a*N` odd terms and the first `b*N` even terms with their original
signs and Dirichlet weights. For positive `a,b`, both lists exhaust their respective
parity classes. The theorems concern these complete-round prefixes.

The retained endpoint is
`2^(-s) * (a^(1-s) - b^(1-s)) / (1-s) * N^(1-s)`.
Subtracting it gives limit `(1-2^(1-s))*zeta(s)` on `0 < Re(s)`, `s != 1`.
Throughout `0 < Re(s) < 1`, the prefixes converge exactly when `a=b`; otherwise
their magnitudes tend to infinity. On `Re(s)>1`, every positive quota converges
to the usual eta value.

This is a classical summation-order boundary derived from the actual zeta
partial-sum asymptotic. It supplies no zero-location law, and does not classify
arbitrary permutations, variable quotas or other summation procedures.
-/

open Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.EtaArithmeticRounds

/-- Ordinary positive-integer Dirichlet prefix. -/
def powerPrefix (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)

/-- Complete rounds of `a` odd terms followed by `b` even terms. -/
def roundPrefix (a b : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range (a * N), ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) -
    ∑ n ∈ Finset.range (b * N), ((2 * (n + 1) : ℕ) : ℂ) ^ (-s)

def endpointCoefficient (a b : ℕ) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (-s) * ((a : ℂ) ^ (1 - s) - (b : ℂ) ^ (1 - s)) / (1 - s)

def finitePart (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

theorem powerPrefix_eq_Icc (s : ℂ) (N : ℕ) :
    powerPrefix s N = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [powerPrefix]
  | succ N ih =>
    rw [powerPrefix, Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [powerPrefix, Complex.ofReal_natCast]

theorem nat_mul_cpow (a b : ℕ) (z : ℂ) :
    ((a * b : ℕ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ z := by
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem evenPrefix_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((2 * (n + 1) : ℕ) : ℂ) ^ (-s)) =
      (2 : ℂ) ^ (-s) * powerPrefix s N := by
  simp only [nat_mul_cpow, Nat.cast_ofNat, powerPrefix, Finset.mul_sum]

theorem oddPrefix_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) =
      powerPrefix s (2 * N) - (2 : ℂ) ^ (-s) * powerPrefix s N := by
  suffices h : powerPrefix s (2 * N) =
      (∑ n ∈ Finset.range N, ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) +
        ∑ n ∈ Finset.range N, ((2 * (n + 1) : ℕ) : ℂ) ^ (-s) by
    rw [h, evenPrefix_eq]; exact (add_sub_cancel_right _ _).symm
  induction N with
  | zero => simp [powerPrefix]
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
    simp only [powerPrefix, Finset.sum_range_succ] at ih ⊢
    rw [ih, show 2 * N + 1 + 1 = 2 * (N + 1) by omega]
    abel

theorem roundPrefix_eq (a b : ℕ) (s : ℂ) (N : ℕ) :
    roundPrefix a b s N = powerPrefix s (2 * (a * N)) -
      (2 : ℂ) ^ (-s) * powerPrefix s (a * N) -
      (2 : ℂ) ^ (-s) * powerPrefix s (b * N) := by
  rw [roundPrefix, oddPrefix_eq, evenPrefix_eq]

theorem two_cpow_one_sub (s : ℂ) :
    (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]

theorem tendsto_scale {a : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * N) atTop atTop := by
  exact tendsto_id.const_mul_atTop' ha

theorem tendsto_powerPrefix_centered {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {a : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => powerPrefix s (a * N) -
      ((a * N : ℕ) : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) := by
  have h := (RHTower.tendsto_sum_cpow_sub_pow hs hs1).comp (tendsto_scale ha)
  change Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 (a * N), ((n : ℝ) : ℂ) ^ (-s)) -
    (((a * N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) at h
  simpa only [powerPrefix_eq_Icc, Complex.ofReal_natCast] using h

/-- The endpoint is retained before taking any limit. -/
theorem roundPrefix_centered_eq (a b : ℕ) (s : ℂ) (N : ℕ) :
    roundPrefix a b s N - endpointCoefficient a b s * (N : ℂ) ^ (1 - s) =
      (powerPrefix s ((2 * a) * N) - (((2 * a) * N : ℕ) : ℂ) ^ (1 - s) / (1 - s)) -
      (2 : ℂ) ^ (-s) * (powerPrefix s (a * N) - ((a * N : ℕ) : ℂ) ^ (1 - s) / (1 - s)) -
      (2 : ℂ) ^ (-s) * (powerPrefix s (b * N) - ((b * N : ℕ) : ℂ) ^ (1 - s) / (1 - s)) := by
  rw [roundPrefix_eq]
  simp only [endpointCoefficient, nat_mul_cpow, Nat.cast_ofNat, two_cpow_one_sub, Nat.mul_assoc]
  ring

theorem tendsto_roundPrefix_centered {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => roundPrefix a b s N -
      endpointCoefficient a b s * (N : ℂ) ^ (1 - s)) atTop (𝓝 (finitePart s)) := by
  have h := ((tendsto_powerPrefix_centered hs hs1 (Nat.mul_pos zero_lt_two ha)).sub
    ((tendsto_powerPrefix_centered hs hs1 ha).const_mul ((2 : ℂ) ^ (-s)))).sub
    ((tendsto_powerPrefix_centered hs hs1 hb).const_mul ((2 : ℂ) ^ (-s)))
  have heq : riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s -
      (2 : ℂ) ^ (-s) * riemannZeta s = finitePart s := by
    rw [finitePart, two_cpow_one_sub]; ring
  simpa only [← roundPrefix_centered_eq, heq] using h


/-- The retained endpoint vanishes exactly for equal odd and even quotas in the strip. -/
theorem endpointCoefficient_eq_zero_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : s.re < 1) : endpointCoefficient a b s = 0 ↔ a = b := by
  have hw : (1 - s).re ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  have hden : (1 : ℂ) - s ≠ 0 := fun h => hw (by rw [h]; rfl)
  have htwo : (2 : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  simp only [endpointCoefficient, div_eq_zero_iff, hden, or_false, mul_eq_zero,
    htwo, false_or, sub_eq_zero]
  constructor
  · intro heq
    have hn := congrArg norm heq
    rw [Complex.norm_natCast_cpow_of_pos ha, Complex.norm_natCast_cpow_of_pos hb] at hn
    exact Nat.cast_inj.mp
      ((Real.rpow_left_inj (Nat.cast_nonneg a) (Nat.cast_nonneg b) hw).mp hn)
  · rintro rfl
    rfl

private theorem tendsto_negative_nat_cpow {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ z) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ ((tendsto_rpow_neg_atTop (neg_pos.mpr hz)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- The leading coefficient is visible without any zero hypothesis. -/
theorem tendsto_roundPrefix_normalized {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    Tendsto (fun N : ℕ => roundPrefix a b s N * (N : ℂ) ^ (s - 1)) atTop
      (𝓝 (endpointCoefficient a b s)) := by
  have hs1 : s ≠ 1 := fun h => hs'.ne (congrArg Complex.re h)
  have hp := tendsto_negative_nat_cpow (z := s - 1) (sub_neg.mpr hs')
  have h := ((tendsto_roundPrefix_centered ha hb hs hs1).mul hp).add_const
    (endpointCoefficient a b s)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hprod : (N : ℂ) ^ (1 - s) * (N : ℂ) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ hN0,
      show 1 - s + (s - 1) = 0 by rw [sub_add_sub_cancel, sub_self], Complex.cpow_zero]
  rw [sub_mul, mul_assoc, hprod, mul_one, sub_add_cancel]

/-- Among fixed positive round quotas, finite convergence occurs exactly for balanced quotas. -/
theorem roundPrefix_converges_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (∃ L : ℂ, Tendsto (roundPrefix a b s) atTop (𝓝 L)) ↔ a = b := by
  constructor
  · rintro ⟨L, hL⟩
    have hz := hL.mul (tendsto_negative_nat_cpow (z := s - 1) (sub_neg.mpr hs'))
    rw [mul_zero] at hz
    exact (endpointCoefficient_eq_zero_iff ha hb hs').mp
      (tendsto_nhds_unique (tendsto_roundPrefix_normalized ha hb hs hs') hz)
  · rintro rfl
    have hs1 : s ≠ 1 := fun h => hs'.ne (congrArg Complex.re h)
    refine ⟨finitePart s, ?_⟩
    simpa only [endpointCoefficient, sub_self, mul_zero, zero_div, zero_mul, sub_zero]
      using tendsto_roundPrefix_centered ha ha hs hs1

/-- Every imbalanced fixed ordering has magnitude tending to infinity throughout the strip. -/
theorem tendsto_norm_roundPrefix_atTop {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    Tendsto (fun N : ℕ => ‖roundPrefix a b s N‖) atTop atTop := by
  have hc : 0 < ‖endpointCoefficient a b s‖ :=
    norm_pos_iff.mpr (fun h => hab ((endpointCoefficient_eq_zero_iff ha hb hs').mp h))
  have hg : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - s.re)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hs')).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_roundPrefix_normalized ha hb hs hs').norm.pos_mul_atTop hc hg
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), mul_assoc,
    ← Real.rpow_add (Nat.cast_pos.mpr (by omega : 0 < N))]
  simp only [Complex.sub_re, Complex.one_re, sub_add_sub_cancel, sub_self, Real.rpow_zero, mul_one]

/-- In the absolute half-plane every fixed positive round quota has the usual eta limit. -/
theorem tendsto_roundPrefix_of_one_lt_re {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (roundPrefix a b s) atTop (𝓝 (finitePart s)) := by
  have hs1 : s ≠ 1 := fun h => hs.ne (congrArg Complex.re h).symm
  have hp := (tendsto_negative_nat_cpow (z := 1 - s) (sub_neg.mpr hs)).const_mul
    (endpointCoefficient a b s)
  have h := (tendsto_roundPrefix_centered ha hb (lt_trans zero_lt_one hs) hs1).add hp
  simpa only [mul_zero, add_zero, sub_add_cancel] using h

end RHTower.EtaArithmeticRounds
