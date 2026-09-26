import GaloisForLFunctions.RHTower.ThetaChiEightSeries
import GaloisForLFunctions.RHTower.ThetaPowerSaddleIntegral

/-!
# The theta-power form at the wall is the theta series of `χ₈`

At `a = 1/2` the theta-power form is `F_{1/2} = √(θ₂θ₄)`, the unique holomorphic square root that
is positive on the imaginary axis.  With `θ₂θ₄ = ϑ₈²/2` this gives, on the imaginary axis,

`F_{1/2}(iy) = (√2/2) ϑ₈(iy) = (√2/2) ∑_{k ∈ ℤ} χ₈(k) e^{-πyk²/8}`.

The sign is fixed by `ϑ₈(τ) = e^{-πi/8} θ₂((τ+1)/2)`: it makes `ϑ₈` continuous and positive for large
`y`, and `ϑ₈(iy)² = 2F_{1/2}(iy)² > 0` keeps it positive for all `y`.

The axis transform is `1/4` times the Mellin transform of `y ↦ F_{1/2}(iy)` at `s/2`, `s = ½ - iw`.
Termwise Mellin transformation of the character theta series gives, for `Re s > 1`,
`√2 · 8^{s/2} · Γ_ℝ(s) L(s, χ₈)`, and both sides are holomorphic on `|Im w| < 1`.  Hence the transform of
the theta-power form at the wall is, up to the factor `(√2/4) 8^{s/2}`, the completed Dirichlet
`L`-function of `χ₈`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-! ## The Dirichlet character -/

/-- The quadratic character of `ℚ(√2)` as a complex Dirichlet character modulo `8`. -/
def dirichletChiEight : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

theorem dirichletChiEight_nat (n : ℕ) : dirichletChiEight (n : ZMod 8) = (chiEight n : ℂ) := by
  unfold dirichletChiEight chiEight
  rw [MulChar.ringHomComp_apply]
  simp only [Int.cast_natCast, eq_intCast]
  push_cast
  rfl

theorem dirichletChiEight_ne_one : dirichletChiEight ≠ 1 := by
  intro h
  have h3 : dirichletChiEight (3 : ZMod 8) = (1 : DirichletCharacter ℂ 8) (3 : ZMod 8) := by
    rw [h]
  have hu : IsUnit (3 : ZMod 8) := by decide
  rw [MulChar.one_apply hu] at h3
  have : dirichletChiEight (3 : ZMod 8) = -1 := by
    unfold dirichletChiEight; rw [MulChar.ringHomComp_apply]
    have : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
    rw [this]; simp
  rw [this] at h3
  norm_num at h3

theorem dirichletChiEight_even : dirichletChiEight.Even := by
  show dirichletChiEight (-1) = 1
  unfold dirichletChiEight; rw [MulChar.ringHomComp_apply]
  have : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
  rw [this]; simp

/-! ## The theta series on the imaginary axis -/

/-- `ϑ₈(iy)` as a real series. -/
def realChiTheta (y : ℝ) : ℝ := ∑' k : ℤ, chiEight k * Real.exp (-(π * (y / 8) * (k : ℝ) ^ 2))

theorem summable_realChiTheta {y : ℝ} (hy : 0 < y) :
    Summable (fun k : ℤ => chiEight k * Real.exp (-(π * (y / 8) * (k : ℝ) ^ 2))) := by
  refine Summable.of_norm_bounded (summable_gauss_int (c := y / 8) (by positivity)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := abs_chiEight_le k
  nlinarith [Real.exp_pos (-(π * (y / 8) * (k : ℝ) ^ 2))]

theorem thetaChiEight_I_mul (y : ℝ) : thetaChiEight (I * (y : ℂ)) = (realChiTheta y : ℂ) := by
  unfold thetaChiEight realChiTheta
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  push_cast
  congr 1
  congr 1
  ring_nf
  rw [I_sq]
  ring

theorem continuousOn_realChiTheta : ContinuousOn realChiTheta (Ioi 0) := by
  have h : ∀ y : ℝ, realChiTheta y =
      (Complex.exp (-(π * I / 8)) * thetaTwo ((I * (y : ℂ) + 1) / 2)).re := by
    intro y
    rw [← thetaChiEight_eq_thetaTwo, thetaChiEight_I_mul, Complex.ofReal_re]
  have hc : ContinuousOn (fun y : ℝ =>
      (Complex.exp (-(π * I / 8)) * thetaTwo ((I * (y : ℂ) + 1) / 2)).re) (Ioi 0) := by
    intro y hy
    have hy' : 0 < ((I * (y : ℂ) + 1) / 2).im := by
      have : (0 : ℝ) < y := hy
      simp; linarith
    have hcont : Continuous (fun y : ℝ => (I * (y : ℂ) + 1) / 2) :=
      ((continuous_const.mul Complex.continuous_ofReal).add continuous_const).div_const 2
    have h1 : ContinuousAt (fun y : ℝ => thetaTwo ((I * (y : ℂ) + 1) / 2)) y :=
      ContinuousAt.comp (g := thetaTwo) (f := fun y : ℝ => (I * (y : ℂ) + 1) / 2) (x := y)
        (differentiableAt_thetaTwo hy').continuousAt hcont.continuousAt
    exact (Complex.continuous_re.continuousAt.comp
      ((continuousAt_const.mul h1))).continuousWithinAt
  exact hc.congr (fun y _ => h y)

theorem realChiTheta_pos_of_four_le {y : ℝ} (hy : 4 ≤ y) : 0 < realChiTheta y := by
  set τ : ℂ := (I * (y : ℂ) + 1) / 2 with hτ
  have hτim : τ.im = y / 2 := by simp [hτ]
  have hJ := norm_jacobiTheta₂_half_sub_two_le_exp (τ := τ) (by rw [hτim]; linarith)
  rw [hτim] at hJ
  have hsmall : 3 * Real.exp (-(π / 2 * (y / 2))) < 2 := by
    have : Real.exp (-(π / 2 * (y / 2))) ≤ Real.exp (-π) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_pi_lt_twentieth]
  set J : ℂ := jacobiTheta₂ (τ / 2) τ with hJdef
  have hJre : 0 < J.re := by
    have h1 : |J.re - 2| ≤ ‖J - 2‖ := by simpa using Complex.abs_re_le_norm (J - 2)
    have h2 := (abs_lt.mp (h1.trans_lt (hJ.trans_lt hsmall))).1
    linarith
  have hval : (realChiTheta y : ℂ) = (Real.exp (-(π * y / 8)) : ℂ) * J := by
    rw [← thetaChiEight_I_mul, thetaChiEight_eq_thetaTwo, ← hτ]
    unfold thetaTwo
    rw [← hJdef, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_exp]
    congr 2
    rw [hτ]; push_cast; ring_nf; rw [I_sq]; ring
  have hre := congrArg Complex.re hval
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  rw [hre]
  exact mul_pos (Real.exp_pos _) hJre

/-! ## The theta-power form at `a = 1/2` on the imaginary axis -/

theorem thetaThree_I_mul_eq (y : ℝ) :
    thetaThree (I * (y : ℂ)) = ((∑' n : ℤ, Real.exp (-(π * y * (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  unfold thetaThree
  rw [jacobiTheta₂, Complex.ofReal_tsum]
  exact tsum_congr (fun n => jacobiTheta₂_term_zero_I_mul n y)

theorem thetaThree_I_mul_re_pos {y : ℝ} (hy : 0 < y) : 0 < (thetaThree (I * (y : ℂ))).re := by
  rw [thetaThree_I_mul_eq, Complex.ofReal_re]
  exact (summable_gauss_int hy).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

theorem thetaPowerForm_half_I_mul_re_pos {y : ℝ} (hy : 0 < y) :
    0 < (thetaPowerForm (1 / 2) (I * (y : ℂ))).re := by
  have him : 0 < (I * (y : ℂ)).im := by simpa using hy
  have h3 : thetaThree (I * (y : ℂ)) = ((thetaThree (I * (y : ℂ))).re : ℂ) :=
    theta_I_mul_real_eq_re thetaThree_conj y
  have hL : hauptmodulLog (I * (y : ℂ)) = ((hauptmodulLog (I * (y : ℂ))).re : ℂ) := by
    apply Complex.ext <;> simp [hauptmodulLog_I_mul_im hy]
  unfold thetaPowerForm
  rw [h3, hL, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (thetaThree_I_mul_re_pos hy) (Real.exp_pos _)

/-- `F_{1/2}(iy)² = θ₂(iy)θ₄(iy)`. -/
theorem thetaPowerForm_half_sq_I_mul {y : ℝ} (hy : 0 < y) :
    thetaPowerForm (1 / 2) (I * (y : ℂ)) ^ 2 = thetaTwo (I * (y : ℂ)) * thetaFour (I * (y : ℂ)) := by
  have him : 0 < (I * (y : ℂ)).im := by simpa using hy
  set f : ℝ := (thetaPowerForm (1 / 2) (I * (y : ℂ))).re with hf
  have hF : thetaPowerForm (1 / 2) (I * (y : ℂ)) = (f : ℂ) := thetaPowerForm_I_mul_real _ hy
  set c : ℝ := realChiTheta y with hc
  have hprod : thetaTwo (I * (y : ℂ)) * thetaFour (I * (y : ℂ)) = ((c ^ 2 / 2 : ℝ) : ℂ) := by
    rw [thetaTwo_mul_thetaFour_eq_thetaChiEight_sq him, thetaChiEight_I_mul]; push_cast; ring
  have h8 : thetaPowerForm (1 / 2) (I * (y : ℂ)) ^ 8 =
      (thetaTwo (I * (y : ℂ)) * thetaFour (I * (y : ℂ))) ^ 4 := by
    have h3ne := thetaThree_ne_zero_of_im_pos him
    have hexp : Complex.exp ((((1 / 2) / 4 : ℝ) : ℂ) * hauptmodulLog (I * (y : ℂ))) ^ 8 =
        thetaGroupHauptmodul (I * (y : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← exp_hauptmodulLog him]; congr 1; push_cast; ring
    unfold thetaPowerForm
    rw [mul_pow, hexp]
    unfold thetaGroupHauptmodul
    field_simp
  rw [hF, hprod] at h8 ⊢
  have hf0 : 0 ≤ f ^ 2 := sq_nonneg f
  have hc0 : 0 ≤ c ^ 2 / 2 := by positivity
  have hreal : (f ^ 2) ^ 4 = (c ^ 2 / 2) ^ 4 := by
    have : ((f ^ 2) ^ 4 : ℝ) = ((c ^ 2 / 2) ^ 4 : ℝ) := by
      have h := h8
      rw [show ((f : ℂ)) ^ 8 = (((f ^ 2) ^ 4 : ℝ) : ℂ) by push_cast; ring,
        show ((((c ^ 2 / 2 : ℝ)) : ℂ)) ^ 4 = (((c ^ 2 / 2) ^ 4 : ℝ) : ℂ) by push_cast; ring] at h
      exact_mod_cast h
    exact this
  have := (pow_left_inj₀ hf0 hc0 (by norm_num : (4 : ℕ) ≠ 0)).mp hreal
  rw [show ((f : ℂ)) ^ 2 = ((f ^ 2 : ℝ) : ℂ) by push_cast; ring, this]

/-- **`F_{1/2}(iy) = (√2/2) ϑ₈(iy)`.** -/
theorem thetaPowerForm_half_I_mul {y : ℝ} (hy : 0 < y) :
    thetaPowerForm (1 / 2) (I * (y : ℂ)) = ((Real.sqrt 2 / 2 * realChiTheta y : ℝ) : ℂ) := by
  have him : 0 < (I * (y : ℂ)).im := by simpa using hy
  set f : ℝ := (thetaPowerForm (1 / 2) (I * (y : ℂ))).re with hf
  have hF : thetaPowerForm (1 / 2) (I * (y : ℂ)) = (f : ℂ) := thetaPowerForm_I_mul_real _ hy
  have hfpos : 0 < f := thetaPowerForm_half_I_mul_re_pos hy
  -- `c² = 2 f²` at every point of the axis
  have hsq : ∀ x : ℝ, 0 < x → realChiTheta x ^ 2 =
      2 * (thetaPowerForm (1 / 2) (I * (x : ℂ))).re ^ 2 := by
    intro x hx
    have hxim : 0 < (I * (x : ℂ)).im := by simpa using hx
    have h1 := thetaPowerForm_half_sq_I_mul hx
    rw [thetaTwo_mul_thetaFour_eq_thetaChiEight_sq hxim, thetaChiEight_I_mul,
      thetaPowerForm_I_mul_real _ hx] at h1
    have h2 : (((thetaPowerForm (1 / 2) (I * (x : ℂ))).re ^ 2 : ℝ) : ℂ) =
        ((realChiTheta x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; exact h1
    have h3 := Complex.ofReal_injective h2
    linarith
  -- the theta series has no zero on the axis and is positive at `y = 2`
  have hne : ∀ x ∈ Ioi (0 : ℝ), realChiTheta x ≠ 0 := by
    intro x hx h0
    have h := hsq x hx
    rw [h0] at h
    have := thetaPowerForm_half_I_mul_re_pos (y := x) hx
    nlinarith
  have hpos : 0 < realChiTheta y := by
    by_contra hneg
    push Not at hneg
    have hlt : realChiTheta y < 0 := lt_of_le_of_ne hneg (hne y hy)
    have h2 := realChiTheta_pos_of_four_le (le_refl 4)
    rcases le_total y 4 with hy2 | hy2
    · have hcont := continuousOn_realChiTheta.mono (Icc_subset_Ioi_iff hy2 |>.mpr hy)
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hy2 hcont ⟨hlt.le, h2.le⟩
      exact hne z (lt_of_lt_of_le hy hz.1) hz0
    · have hcont := continuousOn_realChiTheta.mono
        (Icc_subset_Ioi_iff hy2 |>.mpr (by norm_num))
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hy2 hcont ⟨hlt.le, h2.le⟩
      exact hne z (lt_of_lt_of_le (by norm_num) hz.1) hz0
  have hy2 := hsq y hy
  rw [← hf] at hy2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt 2 := by positivity
  have key : realChiTheta y = Real.sqrt 2 * f := by
    have h1 : realChiTheta y ^ 2 = (Real.sqrt 2 * f) ^ 2 := by rw [mul_pow, hs2]; exact hy2
    exact (pow_left_inj₀ hpos.le (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  rw [hF]
  congr 1
  rw [key]
  field_simp
  rw [hs2]

/-! ## Change of variables to the Mellin transform -/

theorem image_exp_two_mul_univ : (fun x : ℝ => Real.exp (2 * x)) '' univ = Ioi 0 := by
  ext y
  simp only [image_univ, mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩; exact Real.exp_pos _
  · intro hy
    refine ⟨Real.log y / 2, ?_⟩
    rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]

theorem ofReal_exp_cpow (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp (x * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'), Complex.ofReal_exp,
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

/-- `∫ e^{2zx} g(e^{2x}) dx = (1/2) 𝓜g(z)`. -/
theorem integral_cexp_mul_comp_exp_two (g : ℝ → ℂ) (z : ℂ) :
    ∫ x : ℝ, Complex.exp (2 * z * x) * g (Real.exp (2 * x)) = (1 / 2) * mellin g z := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * x)) univ x := by
    intro x _
    have h := (Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp; ring
  have hinj : InjOn (fun x : ℝ => Real.exp (2 * x)) univ := by
    intro a _ b _ h
    have := Real.exp_injective h
    linarith
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun y : ℝ => ((y : ℂ) ^ (z - 1)) • g y)
  rw [image_exp_two_mul_univ, Measure.restrict_univ] at hcv
  unfold mellin
  rw [hcv, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  rw [abs_of_pos (by positivity), ofReal_exp_cpow]
  push_cast
  have e : (1 / 2 : ℂ) * (2 * Complex.exp (2 * x) * Complex.exp (2 * x * (z - 1))) =
      Complex.exp (2 * z * x) := by
    rw [show (1 / 2 : ℂ) * (2 * Complex.exp (2 * x) * Complex.exp (2 * x * (z - 1))) =
      Complex.exp (2 * x) * Complex.exp (2 * x * (z - 1)) by ring, ← Complex.exp_add]
    congr 1; ring
  rw [← e]; ring

/-- The axis transform is a quarter of the Mellin transform of the form on the imaginary axis. -/
theorem thetaPowerXiC_eq_mellin (a : ℝ) (w : ℂ) :
    thetaPowerXiC a w =
      (1 / 4) * mellin (fun y : ℝ => thetaPowerForm a (I * (y : ℂ))) ((1 / 2 - I * w) / 2) := by
  unfold thetaPowerXiC
  have h := integral_cexp_mul_comp_exp_two (fun y : ℝ => thetaPowerForm a (I * (y : ℂ)))
    ((1 / 2 - I * w) / 2)
  rw [show (1 / 4 : ℂ) * mellin (fun y : ℝ => thetaPowerForm a (I * (y : ℂ))) ((1 / 2 - I * w) / 2)
      = (1 / 2) * ((1 / 2) * mellin (fun y : ℝ => thetaPowerForm a (I * (y : ℂ)))
        ((1 / 2 - I * w) / 2)) by ring, ← h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold modTail modAxisPoint
  simp only [sub_zero]
  rw [Complex.ofReal_exp]
  have e : Complex.exp (-I * w * x) * Complex.exp (x / 2) =
      Complex.exp (2 * ((1 / 2 - I * w) / 2) * x) := by rw [← Complex.exp_add]; ring_nf
  rw [← e]
  push_cast
  ring

/-! ## Termwise Mellin transform of the character theta series -/

theorem ofReal_sq_div_eight_cpow {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    ((((n : ℝ) ^ 2 / 8 : ℝ)) : ℂ) ^ z = (n : ℂ) ^ (2 * z) / (8 : ℂ) ^ z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : ((n : ℝ) ^ 2 / 8 : ℝ) = (n : ℝ) ^ 2 * (8 : ℝ)⁻¹ := by ring
  rw [e1, Complex.ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  have e2 : (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ z = (n : ℂ) ^ (2 * z) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hn' 2).ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hn'.ne')]
    congr 1
    rw [← Complex.ofReal_log (pow_pos hn' 2).le, Real.log_pow,
      show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hn'.le]
    push_cast; ring
  rw [e2, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num)]; exact Real.pi_ne_zero.symm)]
  push_cast
  ring

/-- **The Mellin transform of the character theta series.** -/
theorem mellin_thetaPowerForm_half {z : ℂ} (hz : 1 / 2 < z.re) :
    mellin (fun y : ℝ => thetaPowerForm (1 / 2) (I * (y : ℂ))) z =
      ((Real.sqrt 2 : ℝ) : ℂ) * (8 : ℂ) ^ z *
        DirichletCharacter.completedLFunction dirichletChiEight (2 * z) := by
  set a : ℤ → ℂ := fun k => ((Real.sqrt 2 / 2 * chiEight k : ℝ) : ℂ) with ha
  set q : ℤ → ℝ := fun k => (k : ℝ) ^ 2 / 8 with hq
  have hz0 : 0 < z.re := by linarith
  have hq0 : ∀ k, a k = 0 ∨ 0 < q k := by
    intro k
    by_cases hk : k = 0
    · left; simp [ha, hk, chiEight_eq]
    · right; simp only [hq]; have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun k => a k * ((Real.exp (-π * q k * t) : ℝ) : ℂ))
      (thetaPowerForm (1 / 2) (I * (t : ℂ))) := by
    intro t ht
    rw [thetaPowerForm_half_I_mul ht, realChiTheta, ← tsum_mul_left]
    have hs := (summable_realChiTheta ht).mul_left (Real.sqrt 2 / 2)
    have hh := hs.hasSum
    have hc := (Complex.ofRealCLM.hasSum hh)
    refine hc.congr_fun (fun k => ?_)
    simp only [ha, hq, Complex.ofRealCLM_apply, ← Complex.ofReal_mul]
    congr 1
    rw [show -π * ((k : ℝ) ^ 2 / 8) * t = -(π * (t / 8) * (k : ℝ) ^ 2) by ring]
    ring
  have hsum : Summable (fun k => ‖a k‖ / q k ^ z.re) := by
    have hb : 1 < 2 * z.re := by linarith
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Real.summable_abs_int_rpow hb).mul_left (Real.sqrt 2 / 2 * 8 ^ z.re))
    simp only [ha, hq]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < Real.sqrt 2 / 2)]
    by_cases hk : k = 0
    · simp [hk, chiEight_eq]; positivity
    have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
    have e : ((k : ℝ) ^ 2 / 8) ^ z.re = |(k : ℝ)| ^ (2 * z.re) / 8 ^ z.re := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← sq_abs, ← Real.rpow_natCast,
        ← Real.rpow_mul hk'.le]
      norm_num
    rw [e, div_div_eq_mul_div]
    have h1 := abs_chiEight_le k
    have hpow : 0 < |(k : ℝ)| ^ (2 * z.re) := Real.rpow_pos_of_pos hk' _
    rw [div_le_iff₀ hpow, Real.rpow_neg hk'.le]
    field_simp
    have h8 : 0 < (8 : ℝ) ^ z.re := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 2 * 8 ^ z.re)]
  have hmel := hasSum_mellin_pi_mul hq0 hz0 hF hsum
  rw [← hmel.tsum_eq]
  -- evaluate the Dirichlet series
  have hLs : 1 < (2 * z).re := by simp; linarith
  set g : ℤ → ℂ := fun k => (chiEight k : ℂ) / ((q k : ℝ) : ℂ) ^ z with hg
  have hterm : ∀ k, (π : ℂ) ^ (-z) * Complex.Gamma z * a k / ((q k : ℝ) : ℂ) ^ z =
      (π : ℂ) ^ (-z) * Complex.Gamma z * ((Real.sqrt 2 / 2 : ℝ) : ℂ) * g k := by
    intro k; simp only [ha, hg]; push_cast; ring
  rw [tsum_congr hterm, tsum_mul_left]
  have hag : ∀ k, g k = ((2 / Real.sqrt 2 : ℝ) : ℂ) * (a k / ((q k : ℝ) : ℂ) ^ z) := by
    intro k
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    simp only [hg, ha]
    push_cast
    field_simp
  have hs' : Summable (fun k => a k / ((q k : ℝ) : ℂ) ^ z) := by
    refine Summable.of_norm (hsum.congr (fun k => ?_))
    by_cases hk : k = 0
    · simp [ha, hk, chiEight_eq]
    have hqpos : 0 < q k := by
      simp only [hq]; have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
  have hgs : Summable g := (hs'.mul_left _).congr (fun k => (hag k).symm)
  -- the integer sum is twice the natural sum
  have hneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = g ((n : ℤ) + 1) := by
    intro n; simp only [hg, hq, chiEight_neg, Int.cast_neg, neg_sq]
  have hnat : Summable (fun n : ℕ => g n) := hgs.comp_injective Nat.cast_injective
  have hnat' : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) :=
    hgs.comp_injective (by intro a b h; simp at h; exact_mod_cast h)
  have hZ : ∑' k : ℤ, g k = 2 * ∑' n : ℕ, g n := by
    rw [tsum_of_nat_of_neg_add_one hnat hnat']
    rw [show (fun n : ℕ => g (-((n : ℤ) + 1))) = fun n : ℕ => g ((n + 1 : ℕ) : ℤ) by
      funext n; rw [hneg]; push_cast; ring_nf]
    rw [hnat.tsum_eq_zero_add]
    have h0 : g 0 = 0 := by simp [hg, chiEight_eq]
    simp only [Nat.cast_zero, h0, zero_add]
    ring
  have hLS : ∑' n : ℕ, g n = (8 : ℂ) ^ z *
      LSeries (fun n : ℕ => dirichletChiEight (n : ZMod 8)) (2 * z) := by
    rw [LSeries, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    by_cases hn : n = 0
    · simp [hn, hg, chiEight_eq, LSeries.term_zero]
    rw [LSeries.term_of_ne_zero hn, dirichletChiEight_nat]
    simp only [hg, hq, Int.cast_natCast]
    rw [ofReal_sq_div_eight_cpow hn z]
    have h8 : (8 : ℂ) ^ z ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
    have hnz : (n : ℂ) ^ (2 * z) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hn]
    field_simp
  rw [hZ, hLS, DirichletCharacter.completedLFunction]
  have hγ : Complex.Gammaℝ (2 * z) = (π : ℂ) ^ (-z) * Complex.Gamma z := by
    rw [Complex.Gammaℝ_def]; congr 2 <;> ring
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor dirichletChiEight (2 * z)
    (Or.inr (by norm_num))
  rw [DirichletCharacter.LFunction_eq_LSeries _ hLs, dirichletChiEight_even.gammaFactor_def] at hL
  have hγ0 : Complex.Gammaℝ (2 * z) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcomp : ZMod.completedLFunction (⇑dirichletChiEight) (2 * z) =
      Complex.Gammaℝ (2 * z) * LSeries (fun n : ℕ => dirichletChiEight (n : ZMod 8)) (2 * z) := by
    rw [hL]; unfold DirichletCharacter.completedLFunction; field_simp
  rw [hcomp, ← hγ]
  push_cast
  field_simp

/-! ## The identification -/

/-- The strip where the identity is first proved by absolute convergence. -/
def upperQuarterStrip : Set ℂ := {w : ℂ | 1 / 2 < w.im ∧ w.im < 1}

/-- **The transform at the wall is the completed `L`-function of `χ₈`.**  For `|Im w| < 1`,
`Λ_{1/2}(w) = (√2/4) · 8^{s/2} · Λ(s, χ₈)`, `s = ½ - iw`. -/
theorem thetaPowerXiC_half_eq_completedLFunction {w : ℂ} (hw : |w.im| < 1) :
    thetaPowerXiC (1 / 2) w = ((Real.sqrt 2 / 4 : ℝ) : ℂ) * (8 : ℂ) ^ ((1 / 2 - I * w) / 2) *
      DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 - I * w) := by
  set G : ℂ → ℂ := fun w => ((Real.sqrt 2 / 4 : ℝ) : ℂ) * (8 : ℂ) ^ ((1 / 2 - I * w) / 2) *
      DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 - I * w) with hG
  have hGd : Differentiable ℂ G := by
    intro w
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (8 : ℂ) ^ ((1 / 2 - I * w) / 2)) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
    have h2 : DifferentiableAt ℂ (fun w : ℂ =>
        DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 - I * w)) w :=
      ((DirichletCharacter.differentiable_completedLFunction dirichletChiEight_ne_one) _).comp w
        (by fun_prop)
    exact ((differentiableAt_const _).mul h1).mul h2
  have hF := differentiableOn_thetaPowerXiC (a := 1 / 2) (by norm_num)
  have hanF := hF.analyticOnNhd isOpen_unitStripSet
  have hanG : AnalyticOnNhd ℂ G unitStripSet :=
    (hGd.differentiableOn).analyticOnNhd isOpen_unitStripSet
  have hconv : Convex ℝ unitStripSet := by
    intro x hx y hy s' t' hs ht hst
    show |(s' • x + t' • y).im| < 1
    have hx' : |x.im| < 1 := hx
    have hy' : |y.im| < 1 := hy
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    calc |s' * x.im + t' * y.im| ≤ s' * |x.im| + t' * |y.im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ < 1 := by
          rcases eq_or_lt_of_le hs with h0 | h0
          · subst h0; simp at hst; subst hst; simpa using hy'
          · nlinarith [mul_lt_mul_of_pos_left hx' h0, mul_le_mul_of_nonneg_left hy'.le ht]
  set w₀ : ℂ := (3 / 4 : ℝ) * I with hw₀
  have hw₀mem : w₀ ∈ unitStripSet := by show |w₀.im| < 1; simp [hw₀]; norm_num
  have heq : ∀ w ∈ upperQuarterStrip, thetaPowerXiC (1 / 2) w = G w := by
    intro w hw
    have hre : 1 / 2 < ((1 / 2 - I * w) / 2).re := by
      have : ((1 / 2 - I * w) / 2).re = (1 / 2 + w.im) / 2 := by simp
      rw [this]; linarith [hw.1]
    rw [thetaPowerXiC_eq_mellin, mellin_thetaPowerForm_half hre]
    simp only [hG]
    rw [show 2 * ((1 / 2 - I * w) / 2) = 1 / 2 - I * w by ring]
    push_cast
    ring
  have hopen : IsOpen upperQuarterStrip :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hw₀q : w₀ ∈ upperQuarterStrip := by
    show 1 / 2 < w₀.im ∧ w₀.im < 1; simp [hw₀]; norm_num
  have hev : thetaPowerXiC (1 / 2) =ᶠ[𝓝 w₀] G :=
    Filter.eventually_of_mem (hopen.mem_nhds hw₀q) heq
  exact hanF.eqOn_of_preconnected_of_eventuallyEq hanG hconv.isPreconnected hw₀mem hev hw

/-- **On the critical line.** -/
theorem thetaPowerXi_half_eq_completedLFunction (u : ℝ) :
    thetaPowerXi (1 / 2) u = ((Real.sqrt 2 / 4 : ℝ) : ℂ) * (8 : ℂ) ^ ((1 / 2 - I * u) / 2) *
      DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 - I * u) := by
  rw [← thetaPowerXiC_ofReal]
  exact thetaPowerXiC_half_eq_completedLFunction (by simp)

/-- The real zeros of the transform at the wall are exactly the critical zeros of `L(s, χ₈)`. -/
theorem thetaPowerXi_half_eq_zero_iff (u : ℝ) :
    thetaPowerXi (1 / 2) u = 0 ↔
      DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 - I * u) = 0 := by
  rw [thetaPowerXi_half_eq_completedLFunction]
  have h1 : ((Real.sqrt 2 / 4 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 / 4 := by positivity
    exact_mod_cast this.ne'
  have h2 : (8 : ℂ) ^ ((1 / 2 - I * u) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
  simp

end

end RHTower
