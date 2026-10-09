import GaloisForLFunctions.RHTower.WeilLogShiftSingleProbeDomain

/-!
# Exact open and closed domains of log-kernel potentials

Every real-shift convergence domain is symmetric and an interval. Polynomially
damped reciprocal kernels realize every finite open or closed symmetric interval,
including the empty domain and the singleton origin.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- The paired autocorrelation at an integer logarithmic coordinate. -/
def pairedLogKernel (y : ℝ) (n : ℕ) : ℝ :=
  riemannAutocorr (y + log n) + riemannAutocorr (y - log n)

theorem pairedLogKernel_pos (y : ℝ) (n : ℕ) : 0 < pairedLogKernel y n :=
  add_pos (riemannAutocorr_pos _) (riemannAutocorr_pos _)

theorem pairedLogKernel_neg (y : ℝ) (n : ℕ) :
    pairedLogKernel (-y) n = pairedLogKernel y n := by
  unfold pairedLogKernel
  rw [show -y + log n = -(y - log n) by ring,
    show -y - log n = -(y + log n) by ring,
    riemannAutocorr_neg, riemannAutocorr_neg, add_comm]

theorem pairedLogKernel_eq_of_abs_eq {y c : ℝ} (h : |y| = |c|) (n : ℕ) :
    pairedLogKernel y n = pairedLogKernel c n := by
  rcases abs_eq_abs.mp h with h | h
  · rw [h]
  · rw [h, pairedLogKernel_neg]

/-- Convergence transfers weakly inward, including either endpoint with equal
absolute value. In particular every convergence domain is symmetric. -/
theorem summable_kernelPotential_of_abs_le {v : ℕ → ℝ} {y c : ℝ}
    (hyc : |y| ≤ |c|) (hs : Summable fun n => v n * pairedLogKernel c n) :
    Summable fun n => v n * pairedLogKernel y n := by
  rcases lt_or_eq_of_le hyc with h | h
  · exact summable_kernelPotential_of_abs_lt h hs
  · exact hs.congr fun n => by rw [pairedLogKernel_eq_of_abs_eq h]

/-- Every point between two convergent shifts also converges, for arbitrary
signed coefficients. -/
theorem summable_kernelPotential_between {v : ℕ → ℝ} {a y b : ℝ}
    (hay : a ≤ y) (hyb : y ≤ b)
    (ha : Summable fun n => v n * pairedLogKernel a n)
    (hb : Summable fun n => v n * pairedLogKernel b n) :
    Summable fun n => v n * pairedLogKernel y n := by
  by_cases hab : |a| ≤ |b|
  · apply summable_kernelPotential_of_abs_le (c := b) _ hb
    rw [abs_le]
    constructor <;> linarith only [hay, hyb, hab, neg_le_abs a, le_abs_self b]
  · apply summable_kernelPotential_of_abs_le (c := a) _ ha
    rw [abs_le]
    constructor <;> linarith only [hay, hyb, hab, neg_le_abs a, le_abs_self b]

/-- Reciprocal normalization fixes a radius; polynomial damping chooses the
behavior at its boundary. -/
def polynomialReciprocalLogKernelWeight (p : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1) ^ p) * (pairedLogKernel c n)⁻¹

theorem polynomialReciprocalLogKernelWeight_nonneg (p : ℕ) (c : ℝ) (n : ℕ) :
    0 ≤ polynomialReciprocalLogKernelWeight p c n := by
  unfold polynomialReciprocalLogKernelWeight
  exact mul_nonneg (div_nonneg zero_le_one (pow_nonneg (by positivity) _))
    (inv_nonneg.mpr (pairedLogKernel_pos c n).le)

private theorem criticalRate_strict_of_abs_lt {y c : ℝ} (h : |y| < |c|) :
    logKernelCriticalRate c < logKernelCriticalRate y :=
  mul_lt_mul_of_pos_left (exp_lt_exp.mpr (neg_lt_neg h)) (by positivity)

private theorem summable_reciprocal_pair_ratio {y c : ℝ} (hyc : |y| < |c|) :
    Summable fun n => (pairedLogKernel c n)⁻¹ * pairedLogKernel y n := by
  have hr := criticalRate_strict_of_abs_lt hyc
  let b := (2 * logKernelCriticalRate c + logKernelCriticalRate y) / 3
  let a := (logKernelCriticalRate c + 2 * logKernelCriticalRate y) / 3
  have hcb : logKernelCriticalRate c < b := by dsimp only [b]; linarith only [hr]
  have hba : b < a := by dsimp only [b, a]; linarith only [hr]
  have hay : a < logKernelCriticalRate y := by dsimp only [a]; linarith only [hr]
  have ha0 : 0 < a := (logKernelCriticalRate_pos c).trans (hcb.trans hba)
  obtain ⟨C, hC, hu⟩ := exists_paired_logKernel_upper_of_lt_rate ha0 hay
  obtain ⟨D, hD, hl⟩ := exists_paired_logKernel_lower_of_rate_lt hcb
  have hgeo : Summable fun n : ℕ => exp ((n : ℝ) * (b - a)) :=
    summable_exp_nat_mul_iff.mpr (by linarith only [hba])
  refine (hgeo.mul_left (C / D)).of_norm_bounded_eventually_nat ?_
  filter_upwards [hl, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  change D * exp (-(b * n)) ≤ pairedLogKernel c n at hn
  have hupper : pairedLogKernel y n ≤ C * exp (-(a * n)) := hu n hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (inv_nonneg.mpr (pairedLogKernel_pos c n).le) (pairedLogKernel_pos y n).le)]
  have heq : ((C / D) * exp ((n : ℝ) * (b - a))) * (D * exp (-(b * n))) =
      C * exp (-(a * n)) := by
    have hcancel : (C / D) * D = C := by field_simp
    calc _ = ((C / D) * D) *
        (exp ((n : ℝ) * (b - a)) * exp (-(b * n))) := by ring
      _ = _ := by
        rw [hcancel, ← exp_add,
          show (n : ℝ) * (b - a) + -(b * n) = -(a * n) by ring]
  calc (pairedLogKernel c n)⁻¹ * pairedLogKernel y n =
      pairedLogKernel y n / pairedLogKernel c n := by rw [div_eq_mul_inv]; ring
    _ ≤ (C / D) * exp ((n : ℝ) * (b - a)) :=
      (div_le_iff₀ (pairedLogKernel_pos c n)).mpr (hupper.trans (by
        rw [← heq]
        exact mul_le_mul_of_nonneg_left hn (by positivity)))

private theorem polynomial_weight_center (p : ℕ) (c : ℝ) (n : ℕ) :
    polynomialReciprocalLogKernelWeight p c n * pairedLogKernel c n =
      1 / ((n : ℝ) + 1) ^ p := by
  rw [polynomialReciprocalLogKernelWeight, mul_assoc,
    inv_mul_cancel₀ (pairedLogKernel_pos c n).ne', mul_one]

private theorem summable_polynomial_weight_inside (p : ℕ) {y c : ℝ} (hyc : |y| < |c|) :
    Summable fun n => polynomialReciprocalLogKernelWeight p c n * pairedLogKernel y n := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (polynomialReciprocalLogKernelWeight_nonneg p c n)
      (pairedLogKernel_pos y n).le) _ (summable_reciprocal_pair_ratio hyc)
  intro n
  have hscale : 1 / ((n : ℝ) + 1) ^ p ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]))
  have hw : polynomialReciprocalLogKernelWeight p c n ≤ (pairedLogKernel c n)⁻¹ := by
    simpa only [polynomialReciprocalLogKernelWeight, one_mul] using mul_le_mul_of_nonneg_right hscale
      (inv_nonneg.mpr (pairedLogKernel_pos c n).le)
  exact mul_le_mul_of_nonneg_right hw (pairedLogKernel_pos y n).le

private theorem summable_polynomial_weight_boundary_iff (p : ℕ) {y c : ℝ}
    (hyc : |y| = |c|) :
    (Summable fun n => polynomialReciprocalLogKernelWeight p c n * pairedLogKernel y n) ↔
      1 < p := by
  have heq : (fun n => polynomialReciprocalLogKernelWeight p c n * pairedLogKernel y n) =
      (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) := by
    funext n
    rw [pairedLogKernel_eq_of_abs_eq hyc, polynomial_weight_center]
  rw [heq]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) 1).trans
      (summable_one_div_nat_pow (p := p))

private theorem polynomial_exponential_tail (p : ℕ) {g : ℝ} (hg : 0 < g) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ p * exp (-(g * n))) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => g * ((n : ℝ) + 1)) atTop atTop := by
    refine tendsto_atTop.mpr fun B => ?_
    have hscaled := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hg
    filter_upwards [hscaled.eventually_ge_atTop B] with n hn
    nlinarith only [hn, hg]
  have hlim := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp hx).const_mul (exp g / g ^ p)
  have hfactor (n : ℕ) : (exp g / g ^ p) *
      ((g * ((n : ℝ) + 1)) ^ p * exp (-(g * ((n : ℝ) + 1)))) =
      ((n : ℝ) + 1) ^ p * exp (-(g * n)) := by
    have he : exp (-(g * ((n : ℝ) + 1))) = exp (-(g * n)) * exp (-g) := by
      rw [← exp_add]
      congr 1
      ring
    have hecancel : exp g * exp (-g) = 1 := by
      rw [← exp_add, add_neg_cancel, exp_zero]
    rw [mul_pow, he]
    calc _ = (g ^ p / g ^ p) * (exp g * exp (-g)) *
        (((n : ℝ) + 1) ^ p * exp (-(g * n))) := by ring
      _ = _ := by rw [div_self (pow_ne_zero p hg.ne'), hecancel, one_mul, one_mul]
  simpa only [Function.comp_def, hfactor, mul_zero] using hlim

private theorem not_summable_polynomial_weight_outside (p : ℕ) {y c : ℝ}
    (hcy : |c| < |y|) :
    ¬ Summable fun n => polynomialReciprocalLogKernelWeight p c n * pairedLogKernel y n := by
  intro hs
  have hr := criticalRate_strict_of_abs_lt hcy
  let b := (2 * logKernelCriticalRate y + logKernelCriticalRate c) / 3
  let a := (logKernelCriticalRate y + 2 * logKernelCriticalRate c) / 3
  have hyb : logKernelCriticalRate y < b := by dsimp only [b]; linarith only [hr]
  have hba : b < a := by dsimp only [b, a]; linarith only [hr]
  have hac : a < logKernelCriticalRate c := by dsimp only [a]; linarith only [hr]
  have ha0 : 0 < a := (logKernelCriticalRate_pos y).trans (hyb.trans hba)
  obtain ⟨M, hM0, hM⟩ := exponential_bound_of_summable_kernelPotential hyb hs
  obtain ⟨C, hC, hu⟩ := exists_paired_logKernel_upper_of_lt_rate ha0 hac
  have hlim := (polynomial_exponential_tail p (show 0 < a - b by linarith only [hba])).const_mul
    (M * C)
  rw [mul_zero] at hlim
  have hsmall := (tendsto_order.mp hlim).2 1 (by norm_num)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hw := (le_abs_self (polynomialReciprocalLogKernelWeight p c n)).trans (hM n)
  have hprod : polynomialReciprocalLogKernelWeight p c n * pairedLogKernel c n ≤
      (M * C) * exp (-((a - b) * n)) := by
    calc _ ≤ (M * exp (b * n)) * (C * exp (-(a * n))) :=
        mul_le_mul hw (hu n hn) (pairedLogKernel_pos c n).le (by positivity)
      _ = (M * C) * (exp (b * n) * exp (-(a * n))) := by ring
      _ = _ := by
        rw [← exp_add, show b * (n : ℝ) + -(a * n) = -((a - b) * n) by ring]
  rw [polynomial_weight_center] at hprod
  have hden : ((n : ℝ) + 1) ^ p ≠ 0 := pow_ne_zero p (by positivity)
  have hone : 1 ≤ (M * C) * (((n : ℝ) + 1) ^ p * exp (-((a - b) * n))) := by
    calc 1 = ((n : ℝ) + 1) ^ p * (1 / ((n : ℝ) + 1) ^ p) := by field_simp
      _ ≤ ((n : ℝ) + 1) ^ p * ((M * C) * exp (-((a - b) * n))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  linarith only [hone, hsmall]

/-- Exact convergence domain of a polynomially damped reciprocal kernel.
The chosen boundary is included exactly when the polynomial exponent exceeds one. -/
theorem summable_polynomialReciprocalLogKernelWeight_iff (p : ℕ) (c y : ℝ) :
    (Summable fun n => polynomialReciprocalLogKernelWeight p c n * pairedLogKernel y n) ↔
      |y| < |c| ∨ (|y| = |c| ∧ 1 < p) := by
  rcases lt_trichotomy |y| |c| with h | h | h
  · constructor
    · exact fun _ => Or.inl h
    · exact fun _ => summable_polynomial_weight_inside p h
  · constructor
    · intro hs
      exact Or.inr ⟨h, (summable_polynomial_weight_boundary_iff p h).mp hs⟩
    · rintro (hlt | ⟨_, hp⟩)
      · linarith only [hlt, h]
      · exact (summable_polynomial_weight_boundary_iff p h).mpr hp
  · constructor
    · intro hs
      exact False.elim (not_summable_polynomial_weight_outside p h hs)
    · rintro (hlt | ⟨heq, _⟩) <;> linarith

/-- Every finite open symmetric interval is exactly the convergence domain
of a nonnegative weight sequence. Radius zero realizes the empty domain. -/
theorem exists_nonneg_weight_with_open_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ v : ℕ → ℝ, (∀ n, 0 ≤ v n) ∧ ∀ y : ℝ,
      (Summable fun n => v n * pairedLogKernel y n) ↔ |y| < R := by
  refine ⟨polynomialReciprocalLogKernelWeight 0 R,
    polynomialReciprocalLogKernelWeight_nonneg 0 R, fun y => ?_⟩
  simpa [abs_of_nonneg hR] using summable_polynomialReciprocalLogKernelWeight_iff 0 R y

/-- Every finite closed symmetric interval is exactly the convergence domain
of a nonnegative weight sequence. Radius zero realizes only the origin. -/
theorem exists_nonneg_weight_with_closed_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ v : ℕ → ℝ, (∀ n, 0 ≤ v n) ∧ ∀ y : ℝ,
      (Summable fun n => v n * pairedLogKernel y n) ↔ |y| ≤ R := by
  refine ⟨polynomialReciprocalLogKernelWeight 2 R,
    polynomialReciprocalLogKernelWeight_nonneg 2 R, fun y => ?_⟩
  have hiff := summable_polynomialReciprocalLogKernelWeight_iff 2 R y
  rw [abs_of_nonneg hR] at hiff
  constructor
  · intro hs
    rcases hiff.mp hs with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  · intro hy
    apply hiff.mpr
    rcases lt_or_eq_of_le hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by norm_num⟩

end RHTower
