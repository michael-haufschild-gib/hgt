import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Data.ZMod.Basic

/-!
# Pro-Kummer holonomy: reconstruction and the linear capacity threshold

The depth-`n` Kummer holonomy of an integer divisor charge is the root of unity `exp(2πiq/n)`.
Its finite orbit is periodic while the marked logarithmic lift is unbounded, so no finite depth
closes the source history.  The whole tower reconstructs the charge, and a weighted chordal action
over the tower is finite for a nonzero charge exactly when the weights are square-summable against
the depth — a sharp threshold crossed first by linear depth capacity.
-/

open Real Complex Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The holonomy tower -/

/-- The depth-`n` Kummer holonomy of an integer divisor charge. -/
def kummerHolonomy (n : ℕ) (q : ℤ) : ℂ :=
  Complex.exp (((2 * π * q / n : ℝ) : ℂ) * Complex.I)

theorem kummerHolonomy_ne_zero (n : ℕ) (q : ℤ) : kummerHolonomy n q ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem kummerHolonomy_zero (n : ℕ) : kummerHolonomy n 0 = 1 := by
  simp [kummerHolonomy]

/-- **Charge conservation** (PKH.13). -/
theorem kummerHolonomy_add (n : ℕ) (q q' : ℤ) :
    kummerHolonomy n (q + q') = kummerHolonomy n q * kummerHolonomy n q' := by
  rw [kummerHolonomy, kummerHolonomy, kummerHolonomy, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem kummerHolonomy_eq_one_iff {n : ℕ} (hn : n ≠ 0) (q : ℤ) :
    kummerHolonomy n q = 1 ↔ (n : ℤ) ∣ q := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [kummerHolonomy, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hI : ((2 * π * q / n : ℝ) : ℂ) = (k : ℂ) * (2 * (π : ℂ)) := by
      have hk' : ((2 * π * q / n : ℝ) : ℂ) * Complex.I
          = ((k : ℂ) * (2 * (π : ℂ))) * Complex.I := by
        rw [hk]; ring
      exact mul_right_cancel₀ Complex.I_ne_zero hk'
    have hreal : (2 * π * q / n : ℝ) = (k : ℝ) * (2 * π) := by
      have : (((2 * π * q / n : ℝ)) : ℂ) = (((k : ℝ) * (2 * π) : ℝ) : ℂ) := by
        rw [hI]; push_cast; ring
      exact_mod_cast this
    refine ⟨k, ?_⟩
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have : (q : ℝ) = (n : ℝ) * (k : ℝ) := by
      field_simp at hreal
      nlinarith [hreal, Real.pi_pos]
    exact_mod_cast this
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    have : (2 * π * ((n : ℤ) * k : ℤ) / n : ℝ) = (k : ℝ) * (2 * π) := by
      push_cast
      field_simp
    rw [this]
    push_cast
    ring

/-- **Theorem 2.1, one depth.**  Two charges have the same depth-`n` holonomy exactly when the
depth divides their difference. -/
theorem kummerHolonomy_eq_iff {n : ℕ} (hn : n ≠ 0) (q q' : ℤ) :
    kummerHolonomy n q = kummerHolonomy n q' ↔ (n : ℤ) ∣ (q - q') := by
  rw [← kummerHolonomy_eq_one_iff hn]
  constructor
  · intro h
    have hmul : kummerHolonomy n (q - q') * kummerHolonomy n q' = kummerHolonomy n q := by
      rw [← kummerHolonomy_add]
      congr 1
      ring
    rw [h] at hmul
    exact mul_right_cancel₀ (kummerHolonomy_ne_zero n q') (by rw [hmul, one_mul])
  · intro h
    have hmul : kummerHolonomy n (q - q') * kummerHolonomy n q' = kummerHolonomy n q := by
      rw [← kummerHolonomy_add]
      congr 1
      ring
    rw [h, one_mul] at hmul
    exact hmul.symm

/-- **Theorem 2.1, a finite depth set** (PKH.4).  A finite packet of holonomies determines the
charge modulo the least common multiple of the depths. -/
theorem forall_mem_kummerHolonomy_eq_iff {F : Finset ℕ} (hF : ∀ n ∈ F, n ≠ 0) (q q' : ℤ) :
    (∀ n ∈ F, kummerHolonomy n q = kummerHolonomy n q') ↔ ((F.lcm id : ℕ) : ℤ) ∣ (q - q') := by
  constructor
  · intro h
    rw [Int.natCast_dvd]
    refine Finset.lcm_dvd fun n hn => ?_
    have := (kummerHolonomy_eq_iff (hF n hn) q q').1 (h n hn)
    rwa [Int.natCast_dvd] at this
  · intro h n hn
    refine (kummerHolonomy_eq_iff (hF n hn) q q').2 ?_
    exact dvd_trans (Int.natCast_dvd_natCast.2 (Finset.dvd_lcm hn)) h

/-- **Theorem 2.1, the full tower.**  All depths together determine the charge exactly. -/
theorem eq_of_forall_kummerHolonomy_eq {q q' : ℤ}
    (h : ∀ n : ℕ, 2 ≤ n → kummerHolonomy n q = kummerHolonomy n q') : q = q' := by
  by_contra hne
  set d : ℤ := q - q' with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set n : ℕ := max 2 (d.natAbs + 1) with hn
  have hn2 : 2 ≤ n := le_max_left _ _
  have hdvd : (n : ℤ) ∣ d := (kummerHolonomy_eq_iff (by omega) q q').1 (h n hn2)
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hd0
  simp only [Int.natAbs_natCast] at hle
  have : d.natAbs + 1 ≤ n := le_max_right _ _
  omega

/-! ## Finite recurrence with open lift -/

/-- The exact period of the depth-`n` observer orbit. -/
def kummerPeriod (n : ℕ) (q : ℤ) : ℕ := n / Nat.gcd n q.natAbs

theorem kummerHolonomy_pow (n : ℕ) (q : ℤ) (k : ℕ) :
    kummerHolonomy n q ^ k = kummerHolonomy n (q * k) := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ih, ← kummerHolonomy_add]
      congr 1
      push_cast
      ring

/-- **Corollary 2.2, exact recurrence.**  The observer orbit closes exactly at the multiples of
`n / gcd(n, |q|)`. -/
theorem kummerHolonomy_pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (q : ℤ) (k : ℕ) :
    kummerHolonomy n q ^ k = 1 ↔ kummerPeriod n q ∣ k := by
  haveI : NeZero n := ⟨hn⟩
  rw [kummerHolonomy_pow, kummerHolonomy_eq_one_iff hn]
  have hnat : ((n : ℤ) ∣ q * k) ↔ n ∣ q.natAbs * k := by
    rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
  rw [hnat]
  have hord : addOrderOf ((q.natAbs : ℕ) : ZMod n) = kummerPeriod n q :=
    ZMod.addOrderOf_coe _ hn
  rw [← hord, addOrderOf_dvd_iff_nsmul_eq_zero]
  constructor
  · intro h
    have hz : ((q.natAbs * k : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_mul, mul_comm] at hz
    rw [nsmul_eq_mul]
    exact hz
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    rw [Nat.cast_mul, mul_comm]
    rw [nsmul_eq_mul] at h
    exact h

/-- **Corollary 2.2, open lift** (PKH.3).  The marked logarithmic lift of a nonzero charge is
unbounded, so no finite observer closes the source history. -/
theorem tendsto_abs_markedLift_atTop {n : ℕ} (hn : n ≠ 0) {q : ℤ} (hq : q ≠ 0) :
    Tendsto (fun k : ℕ => |2 * π * q * k / n|) atTop atTop := by
  have hc : 0 < |2 * π * (q : ℝ) / n| := by
    have hπ := Real.pi_pos
    have hq' : (q : ℝ) ≠ 0 := Int.cast_ne_zero.2 hq
    have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hn
    positivity
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  refine this.congr fun k => ?_
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), ← abs_mul]
  congr 1
  rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
  ring

/-! ## The weighted chordal action -/

/-- The squared chord of the depth-`n` holonomy. -/
def chordSq (n : ℕ) (q : ℤ) : ℝ := ‖1 - kummerHolonomy n q‖ ^ 2

theorem chordSq_nonneg (n : ℕ) (q : ℤ) : 0 ≤ chordSq n q := sq_nonneg _

@[simp] theorem chordSq_zero (n : ℕ) : chordSq n 0 = 0 := by
  simp [chordSq]

/-- The chord of a unit-circle point is four times a squared half-angle sine. -/
theorem norm_one_sub_exp_sq (x : ℝ) :
    ‖1 - Complex.exp ((x : ℂ) * Complex.I)‖ ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I) = Complex.cos x + Complex.sin x * Complex.I :=
    Complex.exp_mul_I _
  have hnorm : ‖1 - Complex.exp ((x : ℂ) * Complex.I)‖ ^ 2
      = (1 - Complex.exp ((x : ℂ) * Complex.I)).re * (1 - Complex.exp ((x : ℂ) * Complex.I)).re
        + (1 - Complex.exp ((x : ℂ) * Complex.I)).im
          * (1 - Complex.exp ((x : ℂ) * Complex.I)).im := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
  rw [hnorm, h1]
  have hre : (1 - (Complex.cos (x : ℂ) + Complex.sin (x : ℂ) * Complex.I)).re
      = 1 - Real.cos x := by simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : (1 - (Complex.cos (x : ℂ) + Complex.sin (x : ℂ) * Complex.I)).im
      = - Real.sin x := by simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  rw [hre, him]
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have hdouble := Real.cos_two_mul (x / 2)
    have hpy := Real.sin_sq_add_cos_sq (x / 2)
    have hx : 2 * (x / 2) = x := by ring
    rw [hx] at hdouble
    nlinarith [hdouble, hpy]
  nlinarith [Real.sin_sq_add_cos_sq x, hc]

theorem chordSq_eq_sin_sq (n : ℕ) (q : ℤ) :
    chordSq n q = 4 * Real.sin (π * q / n) ^ 2 := by
  rw [chordSq, kummerHolonomy, norm_one_sub_exp_sq]
  have harg : (2 * π * (q : ℝ) / n) / 2 = π * (q : ℝ) / n := by ring
  rw [harg]

/-- **Theorem 3.1** (PKH.6).  Above the doubling depth the squared chord is trapped between two
explicit inverse-square profiles of the charge. -/
theorem chordSq_bounds {n : ℕ} {q : ℤ} (hq : q ≠ 0) (hn : 2 * q.natAbs ≤ n) :
    16 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ chordSq n q ∧
      chordSq n q ≤ 4 * π ^ 2 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hq1 : 1 ≤ q.natAbs := Int.natAbs_pos.2 hq
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hn2
  have hπ := Real.pi_pos
  set y : ℝ := π * (q.natAbs : ℝ) / n with hy
  have hy0 : 0 ≤ y := by positivity
  have habs : ((q.natAbs : ℝ)) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hyle : y ≤ π / 2 := by
    have hcast : (2 : ℝ) * (q.natAbs : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hy, div_le_iff₀ hnpos]
    nlinarith [hπ, hcast]
  have hsin : Real.sin (π * (q : ℝ) / n) ^ 2 = Real.sin y ^ 2 := by
    rcases le_or_gt 0 (q : ℝ) with hpos | hneg
    · have : (q.natAbs : ℝ) = (q : ℝ) := by rw [habs, abs_of_nonneg hpos]
      rw [hy, this]
    · have : (q.natAbs : ℝ) = -(q : ℝ) := by rw [habs, abs_of_neg hneg]
      rw [hy, this]
      have hneg' : π * -(q : ℝ) / n = -(π * (q : ℝ) / n) := by ring
      rw [hneg', Real.sin_neg, neg_pow_two]
  have hysq : y ^ 2 = π ^ 2 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [hy, div_pow, mul_pow, habs, sq_abs]
  have hlow : 2 / π * y ≤ Real.sin y := Real.mul_le_sin hy0 hyle
  have hupp : Real.sin y ≤ y := Real.sin_le hy0
  have hlow0 : 0 ≤ 2 / π * y := by positivity
  have hsq_low : (2 / π * y) ^ 2 ≤ Real.sin y ^ 2 := by nlinarith [hlow, hlow0]
  have hsq_upp : Real.sin y ^ 2 ≤ y ^ 2 := by
    nlinarith [hupp, Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [Real.pi_pos])]
  rw [chordSq_eq_sin_sq, hsin]
  refine ⟨?_, ?_⟩
  · have hexp : (2 / π * y) ^ 2 = 4 * ((q : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      rw [mul_pow, div_pow, hysq]
      field_simp
      ring
    rw [show (16 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ) ^ 2
        = 4 * (4 * ((q : ℝ) ^ 2 / (n : ℝ) ^ 2)) by ring]
    rw [← hexp]
    linarith [hsq_low]
  · rw [show (4 : ℝ) * π ^ 2 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2
        = 4 * (π ^ 2 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) by ring, ← hysq]
    linarith [hsq_upp]

/-! ## The sharp capacity threshold -/

/-- The depth-`n` term of the weighted pro-Kummer action (PKH.5). -/
def proKummerTerm (w : ℕ → ℝ) (q : ℤ) (n : ℕ) : ℝ := w n * chordSq n q

/-- The comparison profile of the weights. -/
def capacityProfile (w : ℕ → ℝ) (n : ℕ) : ℝ := w n / (n : ℝ) ^ 2

/-- **Theorem 3.1** (PKH.7).  For a nonzero charge the weighted action converges exactly when the
weights are summable against the inverse square of the depth. -/
theorem summable_proKummerTerm_iff {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {q : ℤ} (hq : q ≠ 0) :
    Summable (fun n : ℕ => proKummerTerm w q (n + 2))
      ↔ Summable (fun n : ℕ => capacityProfile w (n + 2)) := by
  set M : ℕ := 2 * q.natAbs with hM
  have hqR : (0 : ℝ) < (q : ℝ) ^ 2 := by
    have : (q : ℝ) ≠ 0 := Int.cast_ne_zero.2 hq
    positivity
  have hbound : ∀ k : ℕ,
      16 * (q : ℝ) ^ 2 * capacityProfile w (k + M + 2) ≤ proKummerTerm w q (k + M + 2) ∧
        proKummerTerm w q (k + M + 2) ≤ 4 * π ^ 2 * (q : ℝ) ^ 2
          * capacityProfile w (k + M + 2) := by
    intro k
    obtain ⟨hlo, hhi⟩ := chordSq_bounds (n := k + M + 2) hq (by omega)
    have hwk := hw (k + M + 2)
    constructor
    · rw [proKummerTerm, capacityProfile]
      have := mul_le_mul_of_nonneg_left hlo hwk
      calc 16 * (q : ℝ) ^ 2 * (w (k + M + 2) / ((k + M + 2 : ℕ) : ℝ) ^ 2)
          = w (k + M + 2) * (16 * (q : ℝ) ^ 2 / ((k + M + 2 : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ w (k + M + 2) * chordSq (k + M + 2) q := this
    · rw [proKummerTerm, capacityProfile]
      have := mul_le_mul_of_nonneg_left hhi hwk
      calc w (k + M + 2) * chordSq (k + M + 2) q
          ≤ w (k + M + 2) * (4 * π ^ 2 * (q : ℝ) ^ 2 / ((k + M + 2 : ℕ) : ℝ) ^ 2) := this
        _ = 4 * π ^ 2 * (q : ℝ) ^ 2 * (w (k + M + 2) / ((k + M + 2 : ℕ) : ℝ) ^ 2) := by ring
  have hshift1 : Summable (fun n : ℕ => proKummerTerm w q (n + 2))
      ↔ Summable (fun k : ℕ => proKummerTerm w q (k + M + 2)) := by
    rw [← summable_nat_add_iff (f := fun n : ℕ => proKummerTerm w q (n + 2)) M]
  have hshift2 : Summable (fun n : ℕ => capacityProfile w (n + 2))
      ↔ Summable (fun k : ℕ => capacityProfile w (k + M + 2)) := by
    rw [← summable_nat_add_iff (f := fun n : ℕ => capacityProfile w (n + 2)) M]
  rw [hshift1, hshift2]
  constructor
  · intro h
    have hcmp : Summable fun k : ℕ => (16 * (q : ℝ) ^ 2)⁻¹ * proKummerTerm w q (k + M + 2) :=
      h.mul_left _
    refine hcmp.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact div_nonneg (hw _) (sq_nonneg _)
    · have h16 : (0 : ℝ) < 16 * (q : ℝ) ^ 2 := by positivity
      have hstep := mul_le_mul_of_nonneg_left (hbound k).1 (le_of_lt (inv_pos.2 h16))
      calc capacityProfile w (k + M + 2)
          = (16 * (q : ℝ) ^ 2)⁻¹ * (16 * (q : ℝ) ^ 2 * capacityProfile w (k + M + 2)) := by
            field_simp
        _ ≤ (16 * (q : ℝ) ^ 2)⁻¹ * proKummerTerm w q (k + M + 2) := hstep
  · intro h
    have hcmp : Summable fun k : ℕ => (4 * π ^ 2 * (q : ℝ) ^ 2) * capacityProfile w (k + M + 2) :=
      h.mul_left _
    refine hcmp.of_nonneg_of_le (fun k => ?_) (fun k => (hbound k).2)
    exact mul_nonneg (hw _) (chordSq_nonneg _ _)

/-- **Theorem 4.1** (PKH.10).  When the capacity profile diverges the finite-action locus in the
charge lattice is exactly the origin. -/
theorem summable_proKummerTerm_iff_eq_zero {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hdiv : ¬ Summable (fun n : ℕ => capacityProfile w (n + 2))) (q : ℤ) :
    Summable (fun n : ℕ => proKummerTerm w q (n + 2)) ↔ q = 0 := by
  constructor
  · intro h
    by_contra hq
    exact hdiv ((summable_proKummerTerm_iff hw hq).1 h)
  · rintro rfl
    simp [proKummerTerm]

/-- **Theorem 4.1, uniform truncation.**  Uniformly bounded truncated actions already force the
charge to vanish. -/
theorem eq_zero_of_sum_range_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hdiv : ¬ Summable (fun n : ℕ => capacityProfile w (n + 2))) {q : ℤ} {C : ℝ}
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.range N, proKummerTerm w q (n + 2) ≤ C) : q = 0 := by
  refine (summable_proKummerTerm_iff_eq_zero hw hdiv q).1 ?_
  refine summable_of_sum_range_le (c := C) (fun n => ?_) hC
  exact mul_nonneg (hw _) (chordSq_nonneg _ _)

/-! ## The polynomial threshold -/

/-- **Corollary 3.2** (PKH.8).  Polynomial depth capacity `w n = n ^ a` gives finite action for a
nonzero charge exactly below the linear scale. -/
theorem summable_proKummerTerm_rpow {a : ℝ} {q : ℤ} (hq : q ≠ 0) :
    Summable (fun n : ℕ => proKummerTerm (fun m => (m : ℝ) ^ a) q (n + 2)) ↔ a < 1 := by
  have hw : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ^ a := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) a
  rw [summable_proKummerTerm_iff hw hq]
  have hprof : ∀ n : ℕ,
      capacityProfile (fun m => (m : ℝ) ^ a) (n + 2) = ((n + 2 : ℕ) : ℝ) ^ (a - 2) := by
    intro n
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [capacityProfile, Real.rpow_sub hpos]
    congr 1
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [summable_congr hprof]
  rw [summable_nat_add_iff (f := fun n : ℕ => ((n : ℕ) : ℝ) ^ (a - 2)) 2]
  rw [Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-! ## Contour form -/

/-- **(PKH.12).**  The contour holonomy of an integer charge is its Kummer holonomy. -/
theorem exp_contour_div_eq_kummerHolonomy {n : ℕ} (hn : n ≠ 0) (q : ℤ) :
    Complex.exp ((2 * (π : ℂ) * Complex.I * (q : ℂ)) / (n : ℂ)) = kummerHolonomy n q := by
  rw [kummerHolonomy]
  congr 1
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  push_cast
  field_simp

/-- **Corollary 5.1.**  Under a divergent capacity profile, finite pro-Kummer action on a contour
is equivalent to vanishing of its charge integral. -/
theorem summable_proKummerTerm_iff_contour_eq_zero {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hdiv : ¬ Summable (fun n : ℕ => capacityProfile w (n + 2))) (q : ℤ) :
    Summable (fun n : ℕ => proKummerTerm w q (n + 2))
      ↔ 2 * (π : ℂ) * Complex.I * (q : ℂ) = 0 := by
  rw [summable_proKummerTerm_iff_eq_zero hw hdiv q]
  constructor
  · rintro rfl
    simp
  · intro h
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hne : (2 : ℂ) * (π : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero
    have hq0 : (q : ℂ) = 0 := by
      rcases mul_eq_zero.1 h with h3 | h3
      · exact absurd h3 hne
      · exact h3
    exact_mod_cast hq0

end

end GaloisForLFunctions.HTGeometry
