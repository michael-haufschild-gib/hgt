import GaloisForLFunctions.RHTower.DegreeZeroOffline

/-!
# A degree-zero integral FE polynomial with nonreal off-line zeros

The reciprocal single-column polynomial

`D(s) = 1 + 40 * 16^(-2s) + 256 * 16^(-4s)`

has integer multiplicative Dirichlet coefficients, satisfies an exact functional equation, is
strictly positive on the real axis, and has a simple nonreal zero on `Re s = 5/8`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The reciprocal quartic single-column Dirichlet polynomial. -/
def dzoQuartic (s : ℂ) : ℂ :=
  1 + 40 * (16 : ℂ) ^ (-2 * s) + 256 * (16 : ℂ) ^ (-4 * s)

/-- The single exponential coordinate in which the quartic is quadratic. -/
def dzoQuarticCoordinate (s : ℂ) : ℂ := (16 : ℂ) ^ (-2 * s)

theorem dzoQuartic_eq_coordinate (s : ℂ) :
    dzoQuartic s = 1 + 40 * dzoQuarticCoordinate s +
      256 * dzoQuarticCoordinate s ^ 2 := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  rw [dzoQuartic, dzoQuarticCoordinate, sq,
    ← Complex.cpow_add _ _ h16]
  congr 2
  ring_nf

/-- The exact degree-zero functional equation of the reciprocal quartic. -/
theorem dzoQuartic_fe (s : ℂ) :
    dzoQuartic s = (16 : ℂ) ^ (2 - 4 * s) * dzoQuartic (1 - s) := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  set w := (16 : ℂ) ^ (-s) with hw
  have hw0 : w ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h16)
  have h16s : (16 : ℂ) ^ s = w⁻¹ := by
    rw [hw, Complex.cpow_neg, inv_inv]
  have hz : (16 : ℂ) ^ (-(1 - s)) = (16 * w)⁻¹ := by
    rw [show -(1 - s) = (-1 : ℂ) + s by ring, Complex.cpow_add _ _ h16,
      show (-1 : ℂ) = -(1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one,
      h16s, mul_inv]
  have hw2 : (16 : ℂ) ^ (-2 * s) = w ^ 2 := by
    rw [show -2 * s = (-s) * (2 : ℕ) by norm_num; ring,
      Complex.cpow_mul_nat, hw]
  have hw4 : (16 : ℂ) ^ (-4 * s) = w ^ 4 := by
    rw [show -4 * s = (-s) * (4 : ℕ) by norm_num; ring,
      Complex.cpow_mul_nat, hw]
  have hz2 : (16 : ℂ) ^ (-2 * (1 - s)) = (16 * w)⁻¹ ^ 2 := by
    rw [show -2 * (1 - s) = (-(1 - s)) * (2 : ℕ) by norm_num; ring,
      Complex.cpow_mul_nat, hz]
  have hz4 : (16 : ℂ) ^ (-4 * (1 - s)) = (16 * w)⁻¹ ^ 4 := by
    rw [show -4 * (1 - s) = (-(1 - s)) * (4 : ℕ) by norm_num; ring,
      Complex.cpow_mul_nat, hz]
  have hq : (16 : ℂ) ^ (2 - 4 * s) = 256 * w ^ 4 := by
    rw [show 2 - 4 * s = (2 : ℂ) + (-s) * (4 : ℕ) by norm_num; ring,
      Complex.cpow_add _ _ h16,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast, Complex.cpow_mul_nat, hw]
    norm_num
  rw [dzoQuartic, dzoQuartic, hw2, hw4, hz2, hz4, hq]
  field_simp
  ring

/-! ## Integer multiplicative coefficient stream -/

/-- Integer coefficients supported on the single prime column at exponents `0, 8, 16`. -/
def dzoQuarticCoeff : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 1 then 1 else if n = 256 then 40 else if n = 65536 then 256 else 0,
    by simp⟩

private theorem dzoQuarticCoeff_apply (n : ℕ) :
    dzoQuarticCoeff n =
      if n = 1 then 1 else if n = 256 then 40 else if n = 65536 then 256 else 0 := rfl

/-- The quartic coefficient stream is multiplicative because its support is one prime column. -/
theorem dzoQuarticCoeff_multiplicative :
    ArithmeticFunction.IsMultiplicative dzoQuarticCoeff := by
  constructor
  · rw [dzoQuarticCoeff_apply]
    norm_num
  · intro m n hcop
    have hval : ∀ k : ℕ, dzoQuarticCoeff k ≠ 0 →
        k = 1 ∨ k = 256 ∨ k = 65536 := by
      intro k hk
      rw [dzoQuarticCoeff_apply] at hk
      by_contra hc
      rw [not_or, not_or] at hc
      obtain ⟨h1, h256, h65536⟩ := hc
      rw [if_neg h1, if_neg h256, if_neg h65536] at hk
      exact hk rfl
    rcases eq_or_ne (m * n) 1 with h1 | h1
    · obtain ⟨hm, hn⟩ := mul_eq_one.mp h1
      subst hm
      subst hn
      simp [dzoQuarticCoeff_apply]
    rcases eq_or_ne (m * n) 256 with h256 | h256
    · rcases coprime_mul_two_pow m n hcop 8
        (h256.trans (by norm_num)) with rfl | rfl
      · obtain rfl : n = 256 := by omega
        simp [dzoQuarticCoeff_apply]
      · obtain rfl : m = 256 := by omega
        simp [dzoQuarticCoeff_apply]
    rcases eq_or_ne (m * n) 65536 with h65536 | h65536
    · rcases coprime_mul_two_pow m n hcop 16
        (h65536.trans (by norm_num)) with rfl | rfl
      · obtain rfl : n = 65536 := by omega
        simp [dzoQuarticCoeff_apply]
      · obtain rfl : m = 65536 := by omega
        simp [dzoQuarticCoeff_apply]
    · rw [show dzoQuarticCoeff (m * n) = 0 by
        rw [dzoQuarticCoeff_apply, if_neg h1, if_neg h256, if_neg h65536]]
      by_cases hm : dzoQuarticCoeff m = 0
      · rw [hm]
        ring
      by_cases hn : dzoQuarticCoeff n = 0
      · rw [hn]
        ring
      exfalso
      rcases hval m hm with hm1 | hm256 | hm65536 <;>
        rcases hval n hn with hn1 | hn256 | hn65536 <;>
        subst_vars <;> first | omega | exact absurd hcop (by decide)

theorem dzoQuarticCoeff_integral (n : ℕ) :
    ∃ k : ℤ, dzoQuarticCoeff n = (k : ℂ) := by
  rw [dzoQuarticCoeff_apply]
  rcases eq_or_ne n 1 with h1 | h1
  · exact ⟨1, by rw [if_pos h1]; norm_num⟩
  rcases eq_or_ne n 256 with h256 | h256
  · exact ⟨40, by rw [if_neg h1, if_pos h256]; norm_num⟩
  rcases eq_or_ne n 65536 with h65536 | h65536
  · exact ⟨256, by rw [if_neg h1, if_neg h256, if_pos h65536]; norm_num⟩
  · exact ⟨0, by rw [if_neg h1, if_neg h256, if_neg h65536]; norm_num⟩

private theorem cpow256_eq_sq16 (s : ℂ) :
    (256 : ℂ) ^ s = ((16 : ℂ) ^ s) ^ 2 := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have h256 : (256 : ℂ) ≠ 0 := by norm_num
  have hlog16 : Complex.log 16 = ((Real.log 16 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 16)).symm
  have hlog256 : Complex.log 256 = ((Real.log 256 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 256)).symm
  have hr : ((Real.log 256 : ℝ) : ℂ) = 2 * ((Real.log 16 : ℝ) : ℂ) := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [sq, ← Complex.cpow_add _ _ h16, Complex.cpow_def_of_ne_zero h16,
    Complex.cpow_def_of_ne_zero h256, hlog16, hlog256, hr]
  congr 1
  ring

private theorem cpow65536_eq_fourth16 (s : ℂ) :
    (65536 : ℂ) ^ s = ((16 : ℂ) ^ s) ^ 4 := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have h65536 : (65536 : ℂ) ≠ 0 := by norm_num
  have hlog16 : Complex.log 16 = ((Real.log 16 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 16)).symm
  have hlog65536 : Complex.log 65536 = ((Real.log 65536 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 65536)).symm
  have hr : ((Real.log 65536 : ℝ) : ℂ) = 4 * ((Real.log 16 : ℝ) : ℂ) := by
    rw [show (65536 : ℝ) = 16 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [show ((16 : ℂ) ^ s) ^ 4 =
      (16 : ℂ) ^ (s * (4 : ℕ)) by rw [Complex.cpow_mul_nat],
    Complex.cpow_def_of_ne_zero h16, Complex.cpow_def_of_ne_zero h65536,
    hlog16, hlog65536, hr]
  congr 1
  ring

/-- The quartic coefficient stream has finite support, so its L-series converges everywhere. -/
theorem dzoQuarticCoeff_summable (s : ℂ) :
    LSeriesSummable (fun n => dzoQuarticCoeff n) s := by
  apply summable_of_ne_finset_zero (s := ({1, 256, 65536} : Finset ℕ))
  intro n hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hpos.ne' _ s]
    have h1 : n ≠ 1 := by rintro rfl; exact hn (by decide)
    have h256 : n ≠ 256 := by rintro rfl; exact hn (by decide)
    have h65536 : n ≠ 65536 := by rintro rfl; exact hn (by decide)
    rw [dzoQuarticCoeff_apply, if_neg h1, if_neg h256, if_neg h65536]
    simp

/-- The L-series of the coefficient stream is the reciprocal quartic at every point. -/
theorem LSeries_dzoQuarticCoeff (s : ℂ) :
    LSeries (fun n => dzoQuarticCoeff n) s = dzoQuartic s := by
  have hsupp : ∀ n ∉ ({1, 256, 65536} : Finset ℕ),
      LSeries.term (fun n => dzoQuarticCoeff n) s n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hpos.ne' _ s]
      have h1 : n ≠ 1 := by rintro rfl; exact hn (by decide)
      have h256 : n ≠ 256 := by rintro rfl; exact hn (by decide)
      have h65536 : n ≠ 65536 := by rintro rfl; exact hn (by decide)
      rw [dzoQuarticCoeff_apply, if_neg h1, if_neg h256, if_neg h65536]
      simp
  have hHS := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hsupp
  have hW0 : (16 : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hpow2 : (16 : ℂ) ^ (s * (2 : ℕ)) = ((16 : ℂ) ^ s) ^ 2 := by
    rw [Complex.cpow_mul_nat]
  have hpow4 : (16 : ℂ) ^ (s * (4 : ℕ)) = ((16 : ℂ) ^ s) ^ 4 := by
    rw [Complex.cpow_mul_nat]
  have hneg2 : (16 : ℂ) ^ (-((2 : ℂ) * s)) = (((16 : ℂ) ^ s) ^ 2)⁻¹ := by
    rw [show -((2 : ℂ) * s) = -(s * (2 : ℕ)) by norm_num; ring,
      Complex.cpow_neg, hpow2]
  have hneg4 : (16 : ℂ) ^ (-((4 : ℂ) * s)) = (((16 : ℂ) ^ s) ^ 4)⁻¹ := by
    rw [show -((4 : ℂ) * s) = -(s * (4 : ℕ)) by norm_num; ring,
      Complex.cpow_neg, hpow4]
  rw [show LSeries (fun n => dzoQuarticCoeff n) s =
      ∑' n, LSeries.term (fun n => dzoQuarticCoeff n) s n from rfl,
    hHS.tsum_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, LSeries.term_of_ne_zero (by norm_num) _ s,
    LSeries.term_of_ne_zero (by norm_num) _ s,
    LSeries.term_of_ne_zero (by norm_num) _ s, dzoQuarticCoeff_apply,
    dzoQuarticCoeff_apply, dzoQuarticCoeff_apply]
  norm_num [dzoQuartic, Complex.one_cpow]
  rw [cpow256_eq_sq16, cpow65536_eq_fourth16, hneg2, hneg4]
  field_simp
  ring

/-- The nonzero ordinate used by the explicit quartic zero. -/
def dzoQuarticTau : ℝ := Real.pi / (8 * Real.log 2)

/-- The explicit right-half-strip nonreal zero. -/
def ρdzoQuartic : ℂ :=
  (5 / 8 : ℂ) - (dzoQuarticTau : ℂ) * I

theorem ρdzoQuartic_re : ρdzoQuartic.re = 5 / 8 := by
  simp [ρdzoQuartic]

theorem ρdzoQuartic_im : ρdzoQuartic.im = -dzoQuarticTau := by
  simp [ρdzoQuartic]

theorem ρdzoQuartic_mem_right_strip :
    1 / 2 < ρdzoQuartic.re ∧ ρdzoQuartic.re < 1 := by
  rw [ρdzoQuartic_re]
  norm_num

theorem ρdzoQuartic_not_real : ρdzoQuartic.im ≠ 0 := by
  rw [ρdzoQuartic_im]
  exact neg_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num)
    (ne_of_gt (Real.log_pos (by norm_num)))))

/-- At the explicit point, the single exponential coordinate is the rational root `-1/32`. -/
theorem dzoQuartic_cpow_at_ρ :
    (16 : ℂ) ^ (-2 * ρdzoQuartic) = -(1 / 32 : ℂ) := by
  have hL : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hLC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hL
  have hlog162 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog16 : Complex.log 16 = ((Real.log 16 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have hexpArg : Complex.log 16 * (-2 * ρdzoQuartic) =
      ((-5 * Real.log 2 : ℝ) : ℂ) + (Real.pi : ℂ) * I := by
    rw [hlog16]
    simp only [ρdzoQuartic, dzoQuarticTau]
    rw [hlog162]
    push_cast
    field_simp [hLC]
    ring
  have hlog322 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  have hrexp : Real.exp (-5 * Real.log 2) = 1 / 32 := by
    rw [show -5 * Real.log 2 = -Real.log 32 by rw [hlog322]; ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
    norm_num
  rw [Complex.cpow_def_of_ne_zero (by norm_num), hexpArg, Complex.exp_add,
    Complex.exp_pi_mul_I, ← Complex.ofReal_exp, hrexp]
  norm_num

/-- The explicit point is a zero of the reciprocal quartic. -/
theorem dzoQuartic_ρ_eq_zero : dzoQuartic ρdzoQuartic = 0 := by
  rw [dzoQuartic]
  have h2 := dzoQuartic_cpow_at_ρ
  have h4 : (16 : ℂ) ^ (-4 * ρdzoQuartic) = (1 / 1024 : ℂ) := by
    rw [show -4 * ρdzoQuartic = (-2 * ρdzoQuartic) + (-2 * ρdzoQuartic) by ring,
      Complex.cpow_add _ _ (by norm_num), h2]
    norm_num
  rw [h2, h4]
  norm_num

theorem dzoQuarticCoordinate_hasDerivAt (s : ℂ) :
    HasDerivAt dzoQuarticCoordinate
      (-2 * Complex.log 16 * dzoQuarticCoordinate s) s := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have hfun : dzoQuarticCoordinate = fun z : ℂ =>
      Complex.exp (Complex.log 16 * (-2 * z)) := by
    funext z
    rw [dzoQuarticCoordinate, Complex.cpow_def_of_ne_zero h16]
  rw [hfun]
  have hinner : HasDerivAt (fun z : ℂ => Complex.log 16 * (-2 * z))
      (Complex.log 16 * -2) s := by
    convert ((hasDerivAt_id s).const_mul (-2 : ℂ)).const_mul (Complex.log 16) using 1
    all_goals ring
  convert hinner.cexp using 1
  all_goals ring

theorem dzoQuartic_hasDerivAt (s : ℂ) :
    HasDerivAt dzoQuartic
      ((40 + 512 * dzoQuarticCoordinate s) *
        (-2 * Complex.log 16 * dzoQuarticCoordinate s)) s := by
  have ht := dzoQuarticCoordinate_hasDerivAt s
  have h := ((hasDerivAt_const (x := s) (c := (1 : ℂ))).add (ht.const_mul 40)).add
    ((ht.pow 2).const_mul 256)
  rw [show dzoQuartic = fun z => 1 + 40 * dzoQuarticCoordinate z +
      256 * dzoQuarticCoordinate z ^ 2 by
    funext z
    exact dzoQuartic_eq_coordinate z]
  convert h using 1
  all_goals ring

theorem dzoQuartic_deriv_ρ :
    deriv dzoQuartic ρdzoQuartic = (3 / 2 : ℂ) * Complex.log 16 := by
  rw [(dzoQuartic_hasDerivAt ρdzoQuartic).deriv]
  rw [dzoQuarticCoordinate, dzoQuartic_cpow_at_ρ]
  ring

/-- The explicit nonreal strip zero is simple. -/
theorem dzoQuartic_order_one : analyticOrderAt dzoQuartic ρdzoQuartic = 1 := by
  have han : AnalyticAt ℂ dzoQuartic ρdzoQuartic := by
    exact Differentiable.analyticAt
      (fun s => (dzoQuartic_hasDerivAt s).differentiableAt) ρdzoQuartic
  apply han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero dzoQuartic_ρ_eq_zero
  rw [dzoQuartic_deriv_ρ]
  apply mul_ne_zero
  · norm_num
  · have hlog : Complex.log (16 : ℂ) = ((Real.log 16 : ℝ) : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 16)).symm
    rw [hlog]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

/-- The reciprocal quartic is strictly positive at every real argument. -/
theorem dzoQuartic_ofReal_re_pos (σ : ℝ) :
    0 < (dzoQuartic (σ : ℂ)).re := by
  have hcoord : dzoQuarticCoordinate (σ : ℂ) =
      (((16 : ℝ) ^ (-2 * σ) : ℝ) : ℂ) := by
    symm
    simpa [dzoQuarticCoordinate] using
      (Complex.ofReal_cpow (show (0 : ℝ) ≤ 16 by norm_num) (-2 * σ))
  rw [dzoQuartic_eq_coordinate, hcoord]
  let x : ℝ := (16 : ℝ) ^ (-2 * σ)
  have hcast : (1 + 40 * (x : ℂ) + 256 * (x : ℂ) ^ 2) =
      ((1 + 40 * x + 256 * x ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [show (16 : ℝ) ^ (-2 * σ) = x by rfl, hcast]
  simp only [ofReal_re]
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [sq_nonneg x]

theorem dzoQuartic_ofReal_ne_zero (σ : ℝ) : dzoQuartic (σ : ℂ) ≠ 0 := by
  intro h
  have hre : (dzoQuartic (σ : ℂ)).re = 0 := by simpa using congrArg Complex.re h
  linarith [dzoQuartic_ofReal_re_pos σ]

/-- The reciprocal quartic belongs to the exact integral multiplicative degree-zero class. -/
theorem dzoQuartic_mem_class : IntegralMultiplicativeFEClass dzoQuartic := by
  refine ⟨dzoQuarticCoeff, dzoQuarticCoeff_multiplicative,
    dzoQuarticCoeff_integral, fun s => (LSeries_dzoQuarticCoeff s).symm,
    256, by norm_num, fun s => ?_⟩
  have hscale : (256 : ℂ) ^ (1 - 2 * s) = (16 : ℂ) ^ (2 - 4 * s) := by
    rw [cpow256_eq_sq16,
      show ((16 : ℂ) ^ (1 - 2 * s)) ^ 2 =
        (16 : ℂ) ^ ((1 - 2 * s) * (2 : ℕ)) by rw [Complex.cpow_mul_nat]]
    congr 1
    ring
  rw [show ((256 : ℕ) : ℂ) = (256 : ℂ) by norm_num, hscale]
  exact dzoQuartic_fe s

end

end RHTower
