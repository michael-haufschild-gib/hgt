import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour

/-!
# The linear spectral-budget sum rule and the unconditional off-line height floor

Evaluating the difference of the full centered relative-resolvent trace at the
probe pair `±z₄`, `z₄ = -(7/2)i` (the centered image of `s = 4`), cancels the
per-copy `pt⁻¹` subtraction and yields an absolutely convergent sum rule

`Σ'_{q} [(pt_q + z₄)⁻¹ − (pt_q − z₄)⁻¹] = 2·logDeriv XiC z₄ = 2i·logDeriv xi 4`.

The imaginary part of each summand is the strictly positive spectral mass
`P(q) = (7/2−v)/(u²+(7/2−v)²) + (7/2+v)/(u²+(7/2+v)²)` (`u+iv = pt_q`, strip
`|v| < ½`), bounded below by `7/(u²+16)`.  The budget `2·Re logDeriv xi 4` is
certified `≤ 166/375` from the arithmetic identity at `s = 4` (digamma at `2`,
von Mangoldt partial sums, `log π` and Euler–Mascheroni bounds).

Every strict-right Schwarz pair injects four multiplicity-exact divisor copies
(the reflection/conjugation quadruple, one per open quadrant) into the budget,
so each pair costs `4P ≥ 28/(b²+16)` at height `b`.  Consequences, all
unconditional:

* `xiWard_offlinePair_height_sq_ge` — every strict-right pair has
  `b² ≥ 3922/83 > 47`: no off-critical zero below height `6.87`.
* `xiWard_centralWindow_unconditional` — the unit central window is clear,
  discharging the boundary-conditional central clearing hypothesis.
* `re_xiAntiCausalWardBoundarySelfSymbol_le` — the Ward boundary self-symbol
  has real part at most `83/1961 < 0.0424`.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## §1 Elementary numeric bounds -/

theorem exp_point_zero_nine_lt : Real.exp 0.09 < 1.0944 := by
  have hb := Real.exp_bound (x := 0.09) (by norm_num)
    (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (0.09 : ℝ) ^ m / m.factorial =
      1.09405 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have h2 := (abs_le.mp hb).2
  have herr : (|0.09| : ℝ) ^ 3 * ((3 : ℕ).succ /
      ((3 : ℕ).factorial * (3 : ℕ))) ≤ 0.000162 := by
    norm_num [Nat.factorial]
  linarith

theorem log_three_gt : (1.09 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  have h1 : Real.exp 1.09 = Real.exp 1 * Real.exp 0.09 := by
    rw [← Real.exp_add]
    norm_num
  rw [h1]
  have he := Real.exp_one_lt_d9
  have h0 := exp_point_zero_nine_lt
  have hp1 := Real.exp_pos 1
  have hp0 := Real.exp_pos 0.09
  nlinarith

/-- Certified numeric floor for the real von Mangoldt series at `σ = 4`. -/
theorem vonMangoldt_tsum_four_ge :
    (0.062 : ℝ) ≤ ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (4 : ℝ) := by
  have hle := finiteSum_le_tsum_vonMangoldt
    (by norm_num : (1 : ℝ) < 4) ({2, 3, 4, 5, 8, 9} : Finset ℕ)
  refine le_trans ?_ hle
  rw [show ({2, 3, 4, 5, 8, 9} : Finset ℕ) =
      insert 2 (insert 3 (insert 4 (insert 5 (insert 8 {9})))) from rfl]
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have h2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have h5 := ArithmeticFunction.vonMangoldt_apply_prime
    (by norm_num : Nat.Prime 5)
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h9 : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h3]
    norm_num
  rw [h2, h3, h4, h5, h8, h9]
  have hrp : ∀ n : ℕ, ((n : ℝ)) ^ (4 : ℝ) = ((n : ℝ)) ^ (4 : ℕ) := by
    intro n
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [hrp 2, hrp 3, hrp 4, hrp 5, hrp 8, hrp 9]
  have hlog2 := Real.log_two_gt_d9
  have hlog3 := log_three_gt
  have hlog5 := log_five_gt
  push_cast
  nlinarith [hlog2, hlog3, hlog5]

/-- The digamma value at `2`: one Gamma recurrence step from `digamma 1 = -γ`. -/
theorem digamma_two_eq :
    Complex.digamma 2 = 1 - (Real.eulerMascheroniConstant : ℂ) := by
  have hne2 : ∀ m : ℕ, (2 : ℂ) ≠ -m := by
    intro m h
    have hre : (2 : ℝ) = -(m : ℝ) := by
      have := congrArg Complex.re h
      simpa using this
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hne1 : ∀ m : ℕ, (1 : ℂ) ≠ -m := by
    intro m h
    have hre : (1 : ℝ) = -(m : ℝ) := by
      have := congrArg Complex.re h
      simpa using this
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hev : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[nhds (1 : ℂ)]
      fun z : ℂ => z * Complex.Gamma z := by
    have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    refine Filter.eventually_of_mem (hopen.mem_nhds ?_) ?_
    · exact one_ne_zero
    · intro z hz
      exact Complex.Gamma_add_one z hz
  have hkey := logDeriv_congr_of_eventuallyEq hev
  have hlhs : logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) 1 =
      Complex.digamma 2 := by
    have hcomp := logDeriv_comp (f := Complex.Gamma)
      (g := fun z : ℂ => z + 1) (x := (1 : ℂ))
      (by
        show DifferentiableAt ℂ Complex.Gamma ((1 : ℂ) + 1)
        rw [show ((1 : ℂ) + 1) = 2 from by norm_num]
        exact Complex.differentiableAt_Gamma _ hne2)
      ((differentiableAt_id.add_const 1))
    have hd : deriv (fun z : ℂ => z + 1) 1 = 1 :=
      ((hasDerivAt_id (1 : ℂ)).add_const 1).deriv
    rw [show (fun z : ℂ => Complex.Gamma (z + 1)) =
        Complex.Gamma ∘ (fun z : ℂ => z + 1) from rfl, hcomp, hd, mul_one]
    rw [show (1 : ℂ) + 1 = 2 by norm_num]
    rfl
  have hrhs : logDeriv (fun z : ℂ => z * Complex.Gamma z) 1 =
      1 + Complex.digamma 1 := by
    have hmul := logDeriv_mul (1 : ℂ) (f := fun z : ℂ => z)
      (g := Complex.Gamma) one_ne_zero
      (by rw [Complex.Gamma_one]; exact one_ne_zero)
      differentiableAt_id
      (Complex.differentiableAt_Gamma _ hne1)
    rw [hmul]
    have hid : logDeriv (fun z : ℂ => z) 1 = 1 := by
      rw [logDeriv, Pi.div_apply]
      simp
    rw [hid]
    rfl
  rw [hlhs, hrhs, Complex.digamma_one] at hkey
  rw [hkey]
  ring

/-- Certified budget bound: `Re logDeriv xi 4 ≤ 83/375`. -/
theorem re_logDeriv_xi_four_le : (logDeriv xi 4).re ≤ 83 / 375 := by
  have h4 : (1 : ℝ) < ((4 : ℂ)).re := by norm_num
  have h4' : (0 : ℝ) < ((4 : ℂ)).re := by norm_num
  rw [logDeriv_xi_eq h4, logDeriv_completedRiemannZeta_eq h4,
    logDeriv_riemannZeta_eq_neg_LSeries h4, logDeriv_Gammaℝ_eq h4',
    show ((4 : ℂ) / 2) = 2 by norm_num, digamma_two_eq,
    show ((4 : ℂ)) = (((4 : ℝ)) : ℂ) from by norm_num]
  rw [LSeries_vonMangoldt_ofReal]
  have hre : ((((4 : ℝ)) : ℂ)⁻¹ + ((((4 : ℝ)) : ℂ) - 1)⁻¹ +
      (-((Real.log Real.pi : ℂ) / 2) +
        (1 - (Real.eulerMascheroniConstant : ℂ)) / 2 +
      -((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
        (n : ℝ) ^ (4 : ℝ) : ℝ) : ℂ))).re =
      1 / 4 + 1 / 3 - Real.log Real.pi / 2 +
        (1 - Real.eulerMascheroniConstant) / 2 -
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
          (n : ℝ) ^ (4 : ℝ) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.div_re, Complex.inv_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.sub_im,
      Complex.normSq_apply]
    norm_num
    ring
  rw [hre]
  have hπ := log_pi_gt_one_point_one
  have hγ := one_half_lt_gamma
  have hL := vonMangoldt_tsum_four_ge
  linarith

/-! ## §2 The probe and the difference-trace sum rule -/

/-- The budget probe: the centered image of `s = 4`. -/
def xiBudgetProbe : ℂ := -(7 / 2 : ℂ) * Complex.I

theorem xiBudgetProbe_re : xiBudgetProbe.re = 0 := by
  simp [xiBudgetProbe]

theorem xiBudgetProbe_im : xiBudgetProbe.im = -(7 / 2) := by
  simp [xiBudgetProbe]

theorem half_add_probe_mul_I : (1 / 2 : ℂ) + xiBudgetProbe * Complex.I = 4 := by
  rw [xiBudgetProbe, show ((-(7 / 2 : ℂ) * I) * I) = -(7 / 2 : ℂ) * (I * I) from
    by ring, Complex.I_mul_I]
  norm_num

theorem xi_four_ne_zero : xi 4 ≠ 0 := by
  have h := xi_eq_mul_completedRiemannZeta
    (by norm_num : (4 : ℂ) ≠ 0) (by norm_num : (4 : ℂ) ≠ 1)
  rw [h]
  have hΛ : completedRiemannZeta 4 ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re (by norm_num)
  intro hcon
  rcases mul_eq_zero.mp hcon with hc | hc
  · norm_num at hc
  · exact hΛ hc

theorem XiC_xiBudgetProbe_ne_zero : XiC xiBudgetProbe ≠ 0 := by
  rw [XiC, half_add_probe_mul_I]
  exact xi_four_ne_zero

theorem XiC_neg_xiBudgetProbe_ne_zero : XiC (-xiBudgetProbe) ≠ 0 := by
  rw [XiC_even]
  exact XiC_xiBudgetProbe_ne_zero

/-- The rotated logarithmic derivative: `logDeriv XiC z₄ = i·logDeriv xi 4`. -/
theorem logDeriv_XiC_probe_eq : logDeriv XiC xiBudgetProbe =
    logDeriv xi 4 * Complex.I := by
  have hdf : DifferentiableAt ℂ xi
      ((1 / 2 : ℂ) + xiBudgetProbe * Complex.I) := xi_differentiable _
  have hdg : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
      xiBudgetProbe := by
    fun_prop
  have hcomp := logDeriv_comp (f := xi)
    (g := fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
    (x := xiBudgetProbe) hdf hdg
  have hXiC : XiC = xi ∘ (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) := by
    funext w
    rfl
  have hd : deriv (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
      xiBudgetProbe = Complex.I := by
    simp
  rw [hXiC, hcomp, hd]
  show logDeriv xi ((1 / 2 : ℂ) + xiBudgetProbe * Complex.I) * Complex.I =
    logDeriv xi 4 * Complex.I
  rw [half_add_probe_mul_I]

/-- **The difference-trace sum rule.**  The per-copy `pt⁻¹` regularization
cancels between the probes `±z₄`, leaving an absolutely convergent resolvent
difference summing to twice the odd logarithmic derivative. -/
theorem two_logDeriv_XiC_probe_eq_tsum :
    2 * logDeriv XiC xiBudgetProbe =
      ∑' q : XiZeroCopy,
        ((xiSpectralPoint q + xiBudgetProbe)⁻¹ -
          (xiSpectralPoint q - xiBudgetProbe)⁻¹) := by
  have h1 := logDeriv_XiC_eq_relativeResolventTrace XiC_xiBudgetProbe_ne_zero
  have h2 := logDeriv_XiC_eq_relativeResolventTrace
    XiC_neg_xiBudgetProbe_ne_zero
  have hodd := logDeriv_XiC_neg xiBudgetProbe
  have hs1 := summable_xiRelativeResolventTerm XiC_xiBudgetProbe_ne_zero
  have hs2 := summable_xiRelativeResolventTerm XiC_neg_xiBudgetProbe_ne_zero
  have key : xiRelativeResolventTrace xiBudgetProbe -
      xiRelativeResolventTrace (-xiBudgetProbe) =
      2 * logDeriv XiC xiBudgetProbe := by
    rw [← h1, ← h2, hodd]
    ring
  rw [← key, xiRelativeResolventTrace, xiRelativeResolventTrace,
    ← hs1.tsum_sub hs2]
  apply tsum_congr
  intro q
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, sub_neg_eq_add]
  ring

/-! ## §3 The positive spectral mass -/

/-- The per-copy spectral budget mass at the `s = 4` probe. -/
def xiSpectralBudgetMass (q : XiZeroCopy) : ℝ :=
  (7 / 2 - (xiSpectralPoint q).im) /
      ((xiSpectralPoint q).re ^ 2 + (7 / 2 - (xiSpectralPoint q).im) ^ 2) +
    (7 / 2 + (xiSpectralPoint q).im) /
      ((xiSpectralPoint q).re ^ 2 + (7 / 2 + (xiSpectralPoint q).im) ^ 2)

/-- The budget mass is the imaginary part of the difference-resolvent summand. -/
theorem im_budget_summand (q : XiZeroCopy) :
    ((xiSpectralPoint q + xiBudgetProbe)⁻¹ -
      (xiSpectralPoint q - xiBudgetProbe)⁻¹).im = xiSpectralBudgetMass q := by
  have hAre : (xiSpectralPoint q + xiBudgetProbe).re =
      (xiSpectralPoint q).re := by
    rw [Complex.add_re, xiBudgetProbe_re, add_zero]
  have hAim : (xiSpectralPoint q + xiBudgetProbe).im =
      (xiSpectralPoint q).im - 7 / 2 := by
    rw [Complex.add_im, xiBudgetProbe_im]
    ring
  have hBre : (xiSpectralPoint q - xiBudgetProbe).re =
      (xiSpectralPoint q).re := by
    rw [Complex.sub_re, xiBudgetProbe_re, sub_zero]
  have hBim : (xiSpectralPoint q - xiBudgetProbe).im =
      (xiSpectralPoint q).im + 7 / 2 := by
    rw [Complex.sub_im, xiBudgetProbe_im]
    ring
  rw [Complex.sub_im, Complex.inv_im, Complex.inv_im,
    Complex.normSq_apply, Complex.normSq_apply, hAre, hAim, hBre, hBim,
    xiSpectralBudgetMass]
  ring_nf

/-- The strip constraint on the transverse coordinate of every divisor copy. -/
theorem abs_im_xiSpectralPoint_lt_half (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| < 1 / 2 := by
  have hs := abs_re_I_mul_xiSpectralPoint_le_half q
  have hre : (Complex.I * xiSpectralPoint q).re =
      -(xiSpectralPoint q).im := by
    simp [Complex.mul_re]
  rwa [hre, abs_neg] at hs

/-- **Per-copy mass floor**: `7/(u² + 16) ≤ P(q)` at height `u`. -/
theorem xiSpectralBudgetMass_ge (q : XiZeroCopy) :
    7 / ((xiSpectralPoint q).re ^ 2 + 16) ≤ xiSpectralBudgetMass q := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  set u := (xiSpectralPoint q).re
  set v := (xiSpectralPoint q).im
  have h31 : (3 : ℝ) ≤ 7 / 2 - v := by linarith
  have h32 : (3 : ℝ) ≤ 7 / 2 + v := by linarith
  have h41 : 7 / 2 - v ≤ 4 := by linarith
  have h42 : 7 / 2 + v ≤ 4 := by linarith
  have hd1 : (0 : ℝ) < u ^ 2 + (7 / 2 - v) ^ 2 := by nlinarith [sq_nonneg u]
  have hd2 : (0 : ℝ) < u ^ 2 + (7 / 2 + v) ^ 2 := by nlinarith [sq_nonneg u]
  have hD : (0 : ℝ) < u ^ 2 + 16 := by positivity
  have hle1 : u ^ 2 + (7 / 2 - v) ^ 2 ≤ u ^ 2 + 16 := by nlinarith
  have hle2 : u ^ 2 + (7 / 2 + v) ^ 2 ≤ u ^ 2 + 16 := by nlinarith
  have t1 : (7 / 2 - v) / (u ^ 2 + 16) ≤
      (7 / 2 - v) / (u ^ 2 + (7 / 2 - v) ^ 2) :=
    div_le_div_of_nonneg_left (by linarith) hd1 hle1
  have t2 : (7 / 2 + v) / (u ^ 2 + 16) ≤
      (7 / 2 + v) / (u ^ 2 + (7 / 2 + v) ^ 2) :=
    div_le_div_of_nonneg_left (by linarith) hd2 hle2
  have hsum : 7 / (u ^ 2 + 16) =
      (7 / 2 - v) / (u ^ 2 + 16) + (7 / 2 + v) / (u ^ 2 + 16) := by
    field_simp
    ring
  rw [xiSpectralBudgetMass, hsum]
  exact add_le_add t1 t2

theorem xiSpectralBudgetMass_nonneg (q : XiZeroCopy) :
    0 ≤ xiSpectralBudgetMass q :=
  le_trans (by positivity) (xiSpectralBudgetMass_ge q)

theorem summable_budget_summand :
    Summable (fun q : XiZeroCopy =>
      (xiSpectralPoint q + xiBudgetProbe)⁻¹ -
        (xiSpectralPoint q - xiBudgetProbe)⁻¹) := by
  have hs1 := summable_xiRelativeResolventTerm XiC_xiBudgetProbe_ne_zero
  have hs2 := summable_xiRelativeResolventTerm XiC_neg_xiBudgetProbe_ne_zero
  apply (hs1.sub hs2).congr
  intro q
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, sub_neg_eq_add]
  ring

theorem summable_xiSpectralBudgetMass : Summable xiSpectralBudgetMass :=
  ((Complex.hasSum_im summable_budget_summand.hasSum).summable).congr
    fun q => im_budget_summand q

/-- **The spectral-budget sum rule.**  The complete multiplicity-exact Xi
divisor carries total positive mass exactly `2·Re logDeriv xi 4`. -/
theorem tsum_xiSpectralBudgetMass_eq :
    ∑' q : XiZeroCopy, xiSpectralBudgetMass q = 2 * (logDeriv xi 4).re := by
  have him := Complex.im_tsum summable_budget_summand
  have hsum := two_logDeriv_XiC_probe_eq_tsum
  calc ∑' q : XiZeroCopy, xiSpectralBudgetMass q
      = ∑' q : XiZeroCopy,
          ((xiSpectralPoint q + xiBudgetProbe)⁻¹ -
            (xiSpectralPoint q - xiBudgetProbe)⁻¹).im :=
        (tsum_congr fun q => (im_budget_summand q).symm)
    _ = (∑' q : XiZeroCopy,
          ((xiSpectralPoint q + xiBudgetProbe)⁻¹ -
            (xiSpectralPoint q - xiBudgetProbe)⁻¹)).im := him.symm
    _ = (2 * logDeriv XiC xiBudgetProbe).im := by rw [hsum]
    _ = 2 * (logDeriv xi 4).re := by
        rw [logDeriv_XiC_probe_eq]
        simp [Complex.mul_im]

/-- Certified total budget: `Σ' P ≤ 166/375`. -/
theorem tsum_xiSpectralBudgetMass_le :
    ∑' q : XiZeroCopy, xiSpectralBudgetMass q ≤ 166 / 375 := by
  rw [tsum_xiSpectralBudgetMass_eq]
  linarith [re_logDeriv_xi_four_le]

/-! ## §4 The quadrant quadruple of a strict-right pair -/

theorem xiRightUpper_spectral_re_pos (q : XiRightUpperZeroCopy) :
    0 < (xiSpectralPoint q.1.1).re := by
  have h := q.2
  rw [xiRightCenteredZero] at h
  simpa [Complex.mul_im] using h

theorem xiRightUpper_spectral_im_neg (q : XiRightUpperZeroCopy) :
    (xiSpectralPoint q.1.1).im < 0 := by
  have h := q.1.2
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_sub] at h
  linarith

/-- The Klein four-group of divisor symmetries: identity, functional-equation
reflection, Schwarz conjugation, and critical-line reflection. -/
def xiWardQuadPart : Bool → Bool → XiZeroCopy → XiZeroCopy
  | false, false => fun q => q
  | false, true => fun q => xiZeroCopyReflectEquiv q
  | true, false => fun q => xiZeroCopyConjEquiv q
  | true, true => fun q => xiZeroCopyLineConjEquiv q

/-- The four-fold divisor embedding of a strict-right Schwarz pair: one copy in
each open quadrant of the centered spectral plane. -/
def xiWardQuadrupleEmbed
    (p : (Bool × Bool) × XiRightUpperZeroCopy) : XiZeroCopy :=
  xiWardQuadPart p.1.1 p.1.2 p.2.1.1

theorem xiWardQuadrupleEmbed_injective :
    Function.Injective xiWardQuadrupleEmbed := by
  rintro ⟨⟨c, r⟩, q⟩ ⟨⟨c', r'⟩, q'⟩ h
  have hqre := xiRightUpper_spectral_re_pos q
  have hqim := xiRightUpper_spectral_im_neg q
  have hqre' := xiRightUpper_spectral_re_pos q'
  have hqim' := xiRightUpper_spectral_im_neg q'
  cases c <;> cases r <;> cases c' <;> cases r' <;>
    simp only [xiWardQuadrupleEmbed, xiWardQuadPart] at h <;>
    first
      | (refine Prod.ext rfl (Subtype.ext (Subtype.ext ?_))
         first
           | exact h
           | exact xiZeroCopyReflectEquiv.injective h
           | exact xiZeroCopyConjEquiv.injective h
           | exact xiZeroCopyLineConjEquiv.injective h)
      | (exfalso
         first
           | (have hs := congrArg (fun z => (xiSpectralPoint z).re) h
              simp only [xiSpectralPoint_reflect, xiSpectralPoint_copyConj,
                xiSpectralPoint_lineConj, Complex.neg_re,
                Complex.conj_re] at hs
              linarith)
           | (have hs := congrArg (fun z => (xiSpectralPoint z).im) h
              simp only [xiSpectralPoint_reflect, xiSpectralPoint_copyConj,
                xiSpectralPoint_lineConj, Complex.neg_im,
                Complex.conj_im] at hs
              linarith))

theorem mass_lineConj (c : XiZeroCopy) :
    xiSpectralBudgetMass (xiZeroCopyLineConjEquiv c) =
      xiSpectralBudgetMass c := by
  rw [xiSpectralBudgetMass, xiSpectralBudgetMass, xiSpectralPoint_lineConj]
  simp only [Complex.conj_re, Complex.conj_im]
  ring_nf

theorem mass_reflect (c : XiZeroCopy) :
    xiSpectralBudgetMass (xiZeroCopyReflectEquiv c) =
      xiSpectralBudgetMass c := by
  rw [xiSpectralBudgetMass, xiSpectralBudgetMass, xiSpectralPoint_reflect]
  simp only [Complex.neg_re, Complex.neg_im]
  ring_nf

theorem mass_copyConj (c : XiZeroCopy) :
    xiSpectralBudgetMass (xiZeroCopyConjEquiv c) =
      xiSpectralBudgetMass c := by
  rw [xiSpectralBudgetMass, xiSpectralBudgetMass, xiSpectralPoint_copyConj]
  simp only [Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  ring_nf

theorem mass_quadrupleEmbed (p : (Bool × Bool) × XiRightUpperZeroCopy) :
    xiSpectralBudgetMass (xiWardQuadrupleEmbed p) =
      xiSpectralBudgetMass p.2.1.1 := by
  obtain ⟨⟨c, r⟩, q⟩ := p
  cases c <;> cases r <;>
    simp only [xiWardQuadrupleEmbed, xiWardQuadPart, mass_lineConj,
      mass_reflect, mass_copyConj]

theorem summable_pair_base :
    Summable (fun q : XiRightUpperZeroCopy =>
      xiSpectralBudgetMass q.1.1) := by
  have hinj : Function.Injective
      (fun q : XiRightUpperZeroCopy => (q.1.1 : XiZeroCopy)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  exact summable_xiSpectralBudgetMass.comp_injective hinj

/-- **Quadruple counting**: four disjoint divisor copies per strict-right pair
inject into the global budget. -/
theorem tsum_pairs_four_mul_mass_le :
    ∑' q : XiRightUpperZeroCopy, 4 * xiSpectralBudgetMass q.1.1 ≤
      ∑' c : XiZeroCopy, xiSpectralBudgetMass c := by
  have hbase := summable_pair_base
  have hslice : ∀ i : Bool × Bool,
      (fun q : XiRightUpperZeroCopy =>
        xiSpectralBudgetMass (xiWardQuadrupleEmbed (i, q))) =
      fun q : XiRightUpperZeroCopy => xiSpectralBudgetMass q.1.1 :=
    fun i => funext fun q => mass_quadrupleEmbed (i, q)
  have hFsummable : Summable (fun p : (Bool × Bool) × XiRightUpperZeroCopy =>
      xiSpectralBudgetMass (xiWardQuadrupleEmbed p)) := by
    refine (summable_prod_of_nonneg ?_).mpr ⟨?_, ?_⟩
    · intro p
      exact xiSpectralBudgetMass_nonneg _
    · intro i
      rw [hslice i]
      exact hbase
    · apply Summable.of_finite
  have htsumF : ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
      xiSpectralBudgetMass (xiWardQuadrupleEmbed p) =
      4 * ∑' q : XiRightUpperZeroCopy, xiSpectralBudgetMass q.1.1 := by
    rw [hFsummable.tsum_prod' (fun i => by rw [hslice i]; exact hbase)]
    have hinner : ∀ i : Bool × Bool,
        ∑' q : XiRightUpperZeroCopy,
          xiSpectralBudgetMass (xiWardQuadrupleEmbed (i, q)) =
        ∑' q : XiRightUpperZeroCopy, xiSpectralBudgetMass q.1.1 :=
      fun i => by rw [hslice i]
    rw [tsum_fintype, Finset.sum_congr rfl (fun i _ => hinner i),
      Finset.sum_const, nsmul_eq_mul]
    norm_num
  have hcomp : ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
      xiSpectralBudgetMass (xiWardQuadrupleEmbed p) ≤
      ∑' c : XiZeroCopy, xiSpectralBudgetMass c :=
    Summable.tsum_le_tsum_of_inj xiWardQuadrupleEmbed
      xiWardQuadrupleEmbed_injective
      (fun c _ => xiSpectralBudgetMass_nonneg c)
      (fun p => le_rfl)
      hFsummable summable_xiSpectralBudgetMass
  calc ∑' q : XiRightUpperZeroCopy, 4 * xiSpectralBudgetMass q.1.1
      = 4 * ∑' q : XiRightUpperZeroCopy, xiSpectralBudgetMass q.1.1 :=
        tsum_mul_left
    _ = ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
          xiSpectralBudgetMass (xiWardQuadrupleEmbed p) := htsumF.symm
    _ ≤ ∑' c : XiZeroCopy, xiSpectralBudgetMass c := hcomp

/-! ## §5 The unconditional height floor -/

theorem xiRightCenteredZero_im_eq_spectral_re (q : XiRightUpperZeroCopy) :
    (xiRightCenteredZero q.1).im = (xiSpectralPoint q.1.1).re := by
  rw [xiRightCenteredZero]
  simp [Complex.mul_im]

/-- **THE UNCONDITIONAL HEIGHT FLOOR**: every strict-right Schwarz pair has
squared height at least `3922/83 > 47`.  No off-critical Xi zero exists below
height `6.87`. -/
theorem xiWard_offlinePair_height_sq_ge (q : XiRightUpperZeroCopy) :
    (3922 / 83 : ℝ) ≤ ((xiRightCenteredZero q.1).im) ^ 2 := by
  have hbase := summable_pair_base
  have hsummand : Summable (fun q : XiRightUpperZeroCopy =>
      4 * xiSpectralBudgetMass q.1.1) := hbase.mul_left 4
  have h1 : 4 * xiSpectralBudgetMass q.1.1 ≤
      ∑' q' : XiRightUpperZeroCopy, 4 * xiSpectralBudgetMass q'.1.1 :=
    hsummand.le_tsum q fun j _ => by
      have := xiSpectralBudgetMass_nonneg j.1.1
      linarith
  have h2 := tsum_pairs_four_mul_mass_le
  have h3 := tsum_xiSpectralBudgetMass_le
  have h4 := xiSpectralBudgetMass_ge q.1.1
  rw [xiRightCenteredZero_im_eq_spectral_re]
  set u := (xiSpectralPoint q.1.1).re
  have hden : (0 : ℝ) < u ^ 2 + 16 := by positivity
  have hchain : 28 / (u ^ 2 + 16) ≤ 166 / 375 := by
    have hstep : 4 * (7 / (u ^ 2 + 16)) ≤ 4 * xiSpectralBudgetMass q.1.1 :=
      by linarith
    calc 28 / (u ^ 2 + 16) = 4 * (7 / (u ^ 2 + 16)) := by ring
      _ ≤ 4 * xiSpectralBudgetMass q.1.1 := hstep
      _ ≤ ∑' q' : XiRightUpperZeroCopy,
            4 * xiSpectralBudgetMass q'.1.1 := h1
      _ ≤ ∑' c : XiZeroCopy, xiSpectralBudgetMass c := h2
      _ ≤ 166 / 375 := h3
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 375)] at hchain
  linarith

/-- Display form of the floor: squared heights exceed `47`. -/
theorem xiWard_offlinePair_height_sq_gt_fortyseven
    (q : XiRightUpperZeroCopy) :
    (47 : ℝ) < ((xiRightCenteredZero q.1).im) ^ 2 :=
  lt_of_lt_of_le (by norm_num) (xiWard_offlinePair_height_sq_ge q)

/-- **The unconditional central window**: every strict-right pair has height
beyond `1`.  This discharges — with room to spare — the hypothesis of the
boundary-conditional central clearing. -/
theorem xiWard_centralWindow_unconditional (q : XiRightUpperZeroCopy) :
    (1 : ℝ) < ((xiRightCenteredZero q.1).im) ^ 2 :=
  lt_of_lt_of_le (by norm_num) (xiWard_offlinePair_height_sq_ge q)

/-! ## §6 The unconditional boundary-symbol cap -/

theorem re_boundaryPairTerm_eq (q : XiRightUpperZeroCopy) :
    (xiAntiCausalWardBoundaryPairTerm q).re =
      4 * (xiRightCenteredZero q.1).re /
        ((xiRightCenteredZero q.1).re ^ 2 +
          (xiRightCenteredZero q.1).im ^ 2) := by
  rw [xiAntiCausalWardBoundaryPairTerm]
  rw [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.inv_re,
    Complex.inv_re, Complex.inv_im, Complex.inv_im, Complex.normSq_conj,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  simp only [Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- Per-pair domination of the boundary symbol by the quadruple budget mass. -/
theorem re_boundaryPairTerm_le (q : XiRightUpperZeroCopy) :
    (xiAntiCausalWardBoundaryPairTerm q).re ≤
      (375 / 3922) * (4 * xiSpectralBudgetMass q.1.1) := by
  rw [re_boundaryPairTerm_eq]
  have ha1 : 0 < (xiRightCenteredZero q.1).re := xiRightCenteredZero_re_pos q.1
  have ha2 : (xiRightCenteredZero q.1).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hbsq := xiWard_offlinePair_height_sq_ge q
  have hb := xiRightCenteredZero_im_eq_spectral_re q
  have hmass := xiSpectralBudgetMass_ge q.1.1
  set a := (xiRightCenteredZero q.1).re
  set b := (xiRightCenteredZero q.1).im
  have hbpos : (0 : ℝ) < b ^ 2 := lt_of_lt_of_le (by norm_num) hbsq
  have h1 : 4 * a / (a ^ 2 + b ^ 2) ≤ 2 / b ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hbpos]
    nlinarith [sq_nonneg a, hbpos]
  have h2 : 2 / b ^ 2 ≤ (375 / 3922) * (28 / (b ^ 2 + 16)) := by
    rw [show (375 / 3922 : ℝ) * (28 / (b ^ 2 + 16)) =
        (10500 / 3922) / (b ^ 2 + 16) from by ring,
      div_le_div_iff₀ hbpos (by positivity)]
    nlinarith [hbsq]
  have h3 : (375 / 3922 : ℝ) * (28 / (b ^ 2 + 16)) ≤
      (375 / 3922) * (4 * xiSpectralBudgetMass q.1.1) := by
    have hstep : 28 / (b ^ 2 + 16) ≤ 4 * xiSpectralBudgetMass q.1.1 := by
      have hb2 : b ^ 2 = (xiSpectralPoint q.1.1).re ^ 2 := by rw [hb]
      rw [hb2]
      have : 28 / ((xiSpectralPoint q.1.1).re ^ 2 + 16) =
          4 * (7 / ((xiSpectralPoint q.1.1).re ^ 2 + 16)) := by ring
      rw [this]
      linarith
    have hpos : (0 : ℝ) ≤ 375 / 3922 := by norm_num
    exact mul_le_mul_of_nonneg_left hstep hpos
  linarith

/-- **The unconditional boundary-symbol cap**:
`Re(boundarySelfSymbol) ≤ 83/1961 < 0.0424`. -/
theorem re_xiAntiCausalWardBoundarySelfSymbol_le :
    (xiAntiCausalWardBoundarySelfSymbol).re ≤ 83 / 1961 := by
  rw [xiAntiCausalWardBoundarySelfSymbol,
    Complex.re_tsum summable_xiAntiCausalWardBoundaryPairTerm]
  have hσ : Summable (fun q : XiRightUpperZeroCopy =>
      (xiAntiCausalWardBoundaryPairTerm q).re) :=
    (Complex.hasSum_re
      summable_xiAntiCausalWardBoundaryPairTerm.hasSum).summable
  have hrhs : Summable (fun q : XiRightUpperZeroCopy =>
      (375 / 3922 : ℝ) * (4 * xiSpectralBudgetMass q.1.1)) :=
    (summable_pair_base.mul_left 4).mul_left (375 / 3922)
  have hmono : ∑' q : XiRightUpperZeroCopy,
      (xiAntiCausalWardBoundaryPairTerm q).re ≤
      ∑' q : XiRightUpperZeroCopy,
        (375 / 3922 : ℝ) * (4 * xiSpectralBudgetMass q.1.1) := by
    apply Summable.tsum_mono hσ hrhs
    intro q
    exact re_boundaryPairTerm_le q
  have hpull : ∑' q : XiRightUpperZeroCopy,
      (375 / 3922 : ℝ) * (4 * xiSpectralBudgetMass q.1.1) =
      (375 / 3922) * ∑' q : XiRightUpperZeroCopy,
        4 * xiSpectralBudgetMass q.1.1 := tsum_mul_left
  have hcap : ∑' q : XiRightUpperZeroCopy,
      4 * xiSpectralBudgetMass q.1.1 ≤ 166 / 375 :=
    le_trans tsum_pairs_four_mul_mass_le tsum_xiSpectralBudgetMass_le
  have hfinal : (375 / 3922 : ℝ) * ∑' q : XiRightUpperZeroCopy,
      4 * xiSpectralBudgetMass q.1.1 ≤ (375 / 3922) * (166 / 375) :=
    mul_le_mul_of_nonneg_left hcap (by norm_num)
  have hnum : (375 / 3922 : ℝ) * (166 / 375) = 83 / 1961 := by norm_num
  linarith [hmono, hpull ▸ hmono, hfinal, hnum ▸ hfinal]

end

end RHTower
