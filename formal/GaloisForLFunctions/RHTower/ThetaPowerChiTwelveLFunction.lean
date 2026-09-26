import GaloisForLFunctions.RHTower.ThetaChiTwelveSeries
import GaloisForLFunctions.RHTower.ThetaPowerChiEightLFunction
import GaloisForLFunctions.Bottcher.ThetaDiscriminant

/-!
# The theta-power form at `a = 1/3` is the theta series of `χ₁₂`

At `a = 1/3` the theta-power form is `F_{1/3} = (θ₂θ₃θ₄)^{1/3}`, so `F_{1/3}^{24} = (θ₂θ₃θ₄)^8 = 256 Δ`.
The character theta series `ϑ₁₂ = ∑ χ₁₂(n) e^{πiτn²/12}` has exactly the weight-`½` inversion law
and `ϑ₁₂(τ+1) = e^{πi/12} ϑ₁₂(τ)`, so `ϑ₁₂^{24}` is a level-one cusp form of weight `12`, hence a
multiple `cΔ`.  The multiple is nonzero because the Mellin transform of `ϑ₁₂` on the imaginary axis
is `2 · 12^{s/2} Λ(s, χ₁₂)`, which does not vanish at `s = 2`.  Therefore `F_{1/3}/ϑ₁₂` is a
holomorphic function on the upper half-plane with constant `24`-th power, hence a nonzero constant
`κ`, and

`Λ_{1/3}(w) = (κ/2) · 12^{s/2} · Λ(s, χ₁₂)`,  `s = ½ - iw`,  `|Im w| < 1`.

Consequently a zero of `Λ_{1/3}` off the critical line in this strip is the same thing as a zero of
the completed `L(s, χ₁₂)` off the critical line: the interior point `a = 1/3` of the holomorphic
segment is an Euler product.
-/

open Complex MeasureTheory Set Filter Topology
open Matrix ModularGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

namespace RHTower

noncomputable section

open Bottcher

/-! ## The Dirichlet character -/

/-- `χ₁₂` as a multiplicative character of `ZMod 12`. -/
def chiTwelveChar : MulChar (ZMod 12) ℤ where
  toFun a :=
    match a with
    | 0 | 2 | 3 | 4 | 6 | 8 | 9 | 10 => 0
    | 1 | 11 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The character of `ℚ(√3)` as a complex Dirichlet character modulo `12`. -/
def dirichletChiTwelve : DirichletCharacter ℂ 12 := chiTwelveChar.ringHomComp (Int.castRingHom ℂ)

theorem dirichletChiTwelve_nat (n : ℕ) : dirichletChiTwelve (n : ZMod 12) = (chiTwelve n : ℂ) := by
  have hmod : ((n % 12 : ℕ) : ZMod 12) = (n : ZMod 12) := ZMod.natCast_mod n 12
  have hchi : chiTwelve (n : ℤ) = chiTwelve ((n % 12 : ℕ) : ℤ) := by
    unfold chiTwelve; push_cast
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [← hmod, hchi]
  have hr : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  generalize n % 12 = r at hr
  unfold dirichletChiTwelve
  rw [MulChar.ringHomComp_apply]
  interval_cases r <;> simp [chiTwelveChar, chiTwelve]

theorem dirichletChiTwelve_ne_one : dirichletChiTwelve ≠ 1 := by
  intro h
  have h5 : dirichletChiTwelve (5 : ZMod 12) = (1 : DirichletCharacter ℂ 12) (5 : ZMod 12) := by
    rw [h]
  have hu : IsUnit (5 : ZMod 12) := by decide
  rw [MulChar.one_apply hu] at h5
  have : dirichletChiTwelve (5 : ZMod 12) = -1 := by
    unfold dirichletChiTwelve; rw [MulChar.ringHomComp_apply]
    have : chiTwelveChar (5 : ZMod 12) = -1 := by decide
    rw [this]; simp
  rw [this] at h5
  norm_num at h5

theorem dirichletChiTwelve_even : dirichletChiTwelve.Even := by
  show dirichletChiTwelve (-1) = 1
  unfold dirichletChiTwelve; rw [MulChar.ringHomComp_apply]
  have : chiTwelveChar (-1 : ZMod 12) = 1 := by decide
  rw [this]; simp

/-! ## The Mellin transform of `ϑ₁₂` on the imaginary axis -/

theorem summable_chiTwelve_gauss {y : ℝ} (hy : 0 < y) :
    Summable (fun k : ℤ => chiTwelve k * Real.exp (-(π * (y / 12) * (k : ℝ) ^ 2))) := by
  refine Summable.of_norm_bounded (summable_gauss_int (c := y / 12) (by positivity)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := abs_chiTwelve_le k
  nlinarith [Real.exp_pos (-(π * (y / 12) * (k : ℝ) ^ 2))]

theorem thetaChiTwelve_I_mul (y : ℝ) :
    thetaChiTwelve (I * (y : ℂ)) =
      ((∑' k : ℤ, chiTwelve k * Real.exp (-(π * (y / 12) * (k : ℝ) ^ 2)) : ℝ) : ℂ) := by
  unfold thetaChiTwelve
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  push_cast
  congr 1
  congr 1
  ring_nf
  rw [I_sq]
  ring

theorem ofReal_sq_div_twelve_cpow {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    ((((n : ℝ) ^ 2 / 12 : ℝ)) : ℂ) ^ z = (n : ℂ) ^ (2 * z) / (12 : ℂ) ^ z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : ((n : ℝ) ^ 2 / 12 : ℝ) = (n : ℝ) ^ 2 * (12 : ℝ)⁻¹ := by ring
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

/-- **The Mellin transform of `ϑ₁₂`.** -/
theorem mellin_thetaChiTwelve {z : ℂ} (hz : 1 / 2 < z.re) :
    mellin (fun y : ℝ => thetaChiTwelve (I * (y : ℂ))) z =
      2 * (12 : ℂ) ^ z * DirichletCharacter.completedLFunction dirichletChiTwelve (2 * z) := by
  set a : ℤ → ℂ := fun k => (chiTwelve k : ℂ) with ha
  set q : ℤ → ℝ := fun k => (k : ℝ) ^ 2 / 12 with hq
  have hz0 : 0 < z.re := by linarith
  have hq0 : ∀ k, a k = 0 ∨ 0 < q k := by
    intro k
    by_cases hk : k = 0
    · left; simp [ha, hk, chiTwelve_zero]
    · right; simp only [hq]; have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun k => a k * ((Real.exp (-π * q k * t) : ℝ) : ℂ))
      (thetaChiTwelve (I * (t : ℂ))) := by
    intro t ht
    rw [thetaChiTwelve_I_mul]
    have hc := Complex.ofRealCLM.hasSum (summable_chiTwelve_gauss ht).hasSum
    refine hc.congr_fun (fun k => ?_)
    simp only [ha, hq, Complex.ofRealCLM_apply, ← Complex.ofReal_mul]
    congr 1
    rw [show -π * ((k : ℝ) ^ 2 / 12) * t = -(π * (t / 12) * (k : ℝ) ^ 2) by ring]
  have hsum : Summable (fun k => ‖a k‖ / q k ^ z.re) := by
    have hb : 1 < 2 * z.re := by linarith
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Real.summable_abs_int_rpow hb).mul_left (12 ^ z.re))
    simp only [ha, hq]
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hk : k = 0
    · simp [hk, chiTwelve_zero]; positivity
    have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
    have e : ((k : ℝ) ^ 2 / 12) ^ z.re = |(k : ℝ)| ^ (2 * z.re) / 12 ^ z.re := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← sq_abs, ← Real.rpow_natCast,
        ← Real.rpow_mul hk'.le]
      norm_num
    rw [e, div_div_eq_mul_div]
    have h1 := abs_chiTwelve_le k
    have hpow : 0 < |(k : ℝ)| ^ (2 * z.re) := Real.rpow_pos_of_pos hk' _
    rw [div_le_iff₀ hpow, Real.rpow_neg hk'.le]
    field_simp
    have h12 : 0 < (12 : ℝ) ^ z.re := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h12.le]
  have hmel := hasSum_mellin_pi_mul hq0 hz0 hF hsum
  rw [← hmel.tsum_eq]
  have hLs : 1 < (2 * z).re := by simp; linarith
  set g : ℤ → ℂ := fun k => (chiTwelve k : ℂ) / ((q k : ℝ) : ℂ) ^ z with hg
  have hterm : ∀ k, (π : ℂ) ^ (-z) * Complex.Gamma z * a k / ((q k : ℝ) : ℂ) ^ z =
      (π : ℂ) ^ (-z) * Complex.Gamma z * g k := by
    intro k; simp only [ha, hg]; ring
  rw [tsum_congr hterm, tsum_mul_left]
  have hs' : Summable (fun k => a k / ((q k : ℝ) : ℂ) ^ z) := by
    refine Summable.of_norm (hsum.congr (fun k => ?_))
    by_cases hk : k = 0
    · simp [ha, hk, chiTwelve_zero]
    have hqpos : 0 < q k := by
      simp only [hq]; have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
  have hgs : Summable g := hs'.congr (fun k => by simp only [ha, hg])
  have hneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = g ((n : ℤ) + 1) := by
    intro n; simp only [hg, hq, chiTwelve_neg, Int.cast_neg, neg_sq]
  have hnat : Summable (fun n : ℕ => g n) := hgs.comp_injective Nat.cast_injective
  have hnat' : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) :=
    hgs.comp_injective (by intro a b h; simp at h; exact_mod_cast h)
  have hZ : ∑' k : ℤ, g k = 2 * ∑' n : ℕ, g n := by
    rw [tsum_of_nat_of_neg_add_one hnat hnat']
    rw [show (fun n : ℕ => g (-((n : ℤ) + 1))) = fun n : ℕ => g ((n + 1 : ℕ) : ℤ) by
      funext n; rw [hneg]; push_cast; ring_nf]
    rw [hnat.tsum_eq_zero_add]
    have h0 : g 0 = 0 := by simp [hg, chiTwelve_zero]
    simp only [Nat.cast_zero, h0, zero_add]
    ring
  have hLS : ∑' n : ℕ, g n = (12 : ℂ) ^ z *
      LSeries (fun n : ℕ => dirichletChiTwelve (n : ZMod 12)) (2 * z) := by
    rw [LSeries, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    by_cases hn : n = 0
    · simp [hn, hg, chiTwelve_zero, LSeries.term_zero]
    rw [LSeries.term_of_ne_zero hn, dirichletChiTwelve_nat]
    simp only [hg, hq, Int.cast_natCast]
    rw [ofReal_sq_div_twelve_cpow hn z]
    have h12 : (12 : ℂ) ^ z ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
    have hnz : (n : ℂ) ^ (2 * z) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hn]
    field_simp
  rw [hZ, hLS, DirichletCharacter.completedLFunction]
  have hγ : Complex.Gammaℝ (2 * z) = (π : ℂ) ^ (-z) * Complex.Gamma z := by
    rw [Complex.Gammaℝ_def]; congr 2 <;> ring
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor dirichletChiTwelve (2 * z)
    (Or.inr (by norm_num))
  rw [DirichletCharacter.LFunction_eq_LSeries _ hLs, dirichletChiTwelve_even.gammaFactor_def] at hL
  have hγ0 : Complex.Gammaℝ (2 * z) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcomp : ZMod.completedLFunction (⇑dirichletChiTwelve) (2 * z) =
      Complex.Gammaℝ (2 * z) * LSeries (fun n : ℕ => dirichletChiTwelve (n : ZMod 12)) (2 * z) := by
    rw [hL]; unfold DirichletCharacter.completedLFunction; field_simp
  rw [hcomp, ← hγ]
  ring

/-- `ϑ₁₂` is not identically zero on the imaginary axis. -/
theorem exists_thetaChiTwelve_I_mul_ne_zero : ∃ y : ℝ, 0 < y ∧ thetaChiTwelve (I * (y : ℂ)) ≠ 0 := by
  by_contra h
  push Not at h
  have hm := mellin_thetaChiTwelve (z := 1) (by norm_num)
  have hzero : mellin (fun y : ℝ => thetaChiTwelve (I * (y : ℂ))) 1 = 0 := by
    unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) (fun y hy => by
      simp only; rw [h y hy, smul_zero])]
    simp
  rw [hzero] at hm
  have hL : DirichletCharacter.completedLFunction dirichletChiTwelve (2 * 1) ≠ 0 := by
    intro h0
    have hL0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor dirichletChiTwelve (2 * 1)
      (Or.inr (by norm_num))
    rw [h0, zero_div] at hL0
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re dirichletChiTwelve
      (Or.inl dirichletChiTwelve_ne_one) (by norm_num) hL0
  have h12 : (12 : ℂ) ^ (1 : ℂ) ≠ 0 := by norm_num
  have := mul_ne_zero (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) h12) hL
  exact this hm.symm

/-! ## `ϑ₁₂^{24}` is a multiple of the discriminant -/

/-- `ϑ₁₂^{24}` on the upper half-plane. -/
def thetaChiTwelvePow24H : ℍ → ℂ := fun z => thetaChiTwelve z ^ 24

theorem thetaChiTwelvePow24H_mdiff : MDiff thetaChiTwelvePow24H := by
  rw [mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := by simpa using hz
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => thetaChiTwelve w ^ 24) z :=
    (differentiableAt_thetaChiTwelve hz').pow 24
  refine hdiff.differentiableWithinAt.congr (fun w hw => ?_) ?_
  · show thetaChiTwelve ((ofComplex w : ℍ) : ℂ) ^ 24 = thetaChiTwelve w ^ 24
    rw [ofComplex_apply_of_im_pos (by simpa using hw)]
  · show thetaChiTwelve ((ofComplex z : ℍ) : ℂ) ^ 24 = thetaChiTwelve z ^ 24
    rw [ofComplex_apply_of_im_pos hz']

theorem thetaChiTwelvePow24H_slash_S :
    thetaChiTwelvePow24H ∣[(12 : ℤ)] ModularGroup.S = thetaChiTwelvePow24H := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaChiTwelvePow24H, thetaChiTwelvePow24H]
  have hact : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg]
  rw [hact, show denom ModularGroup.S z = (z : ℂ) from denom_S z, _root_.zpow_neg,
    thetaChiTwelve_S z.im_pos]
  have hpow : ((-I * (z : ℂ)) ^ (1 / 2 : ℂ)) ^ 24 = (z : ℂ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul,
      show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow _ (by norm_num)]
    rw [mul_pow]
    have : (-I) ^ 12 = (1 : ℂ) := by
      rw [show (-I : ℂ) ^ 12 = (I ^ 2) ^ 6 by ring, I_sq]; norm_num
    rw [this, one_mul]
  rw [mul_pow, hpow, show (((z : ℂ) ^ (12 : ℤ)) : ℂ) = (z : ℂ) ^ 12 by norm_cast]
  field_simp [z.ne_zero]

theorem thetaChiTwelvePow24H_slash_T :
    thetaChiTwelvePow24H ∣[(12 : ℤ)] ModularGroup.T = thetaChiTwelvePow24H := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaChiTwelvePow24H, thetaChiTwelvePow24H]
  have hact : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]
    push_cast
    ring
  have hden : denom ModularGroup.T z = 1 := by simp [ModularGroup.T, denom_apply]
  rw [hact, hden, _root_.one_zpow, mul_one, thetaChiTwelve_add_one, mul_pow]
  have : Complex.exp (π * I / 12) ^ 24 = 1 := by
    rw [← Complex.exp_nat_mul]
    rw [show ((24 : ℕ) : ℂ) * (π * I / 12) = ((1 : ℕ) : ℂ) * (2 * π * I) by push_cast; ring]
    rw [Complex.exp_nat_mul_two_pi_mul_I]
  rw [this, one_mul]

theorem thetaChiTwelvePow24H_slash_SL2Z (γ : SL(2, ℤ)) :
    thetaChiTwelvePow24H ∣[(12 : ℤ)] γ = thetaChiTwelvePow24H := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [thetaChiTwelvePow24H_slash_S, thetaChiTwelvePow24H_slash_T]
  | one => exact SlashAction.slash_one 12 thetaChiTwelvePow24H
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ih =>
    have h : thetaChiTwelvePow24H ∣[(12 : ℤ)] x⁻¹ =
        (thetaChiTwelvePow24H ∣[(12 : ℤ)] x) ∣[(12 : ℤ)] x⁻¹ := by rw [ih]
    rw [h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

/-- `ϑ₁₂` tends to zero at the cusp `∞`. -/
theorem tendsto_thetaChiTwelve_atImInfty :
    Tendsto (fun z : ℍ => thetaChiTwelve z) atImInfty (𝓝 0) := by
  set S : ℝ := ∑' k : ℤ, Real.exp (-(π * (1 / 12) * (k : ℝ) ^ 2)) with hS
  have hSs := summable_gauss_int (c := 1 / 12) (by norm_num)
  have hbound : ∀ z : ℍ, 1 ≤ z.im →
      ‖thetaChiTwelve z‖ ≤ S * Real.exp (-(π / 12 * (z.im - 1))) := by
    intro z hz
    have hzs := summable_thetaChiTwelve_norm (τ := (z : ℂ)) z.im_pos
    unfold thetaChiTwelve
    refine (norm_tsum_le_tsum_norm hzs).trans ?_
    rw [hS, ← tsum_mul_right]
    refine hzs.tsum_le_tsum (fun k => ?_) (hSs.mul_right _)
    by_cases hk : k = 0
    · simp [hk, chiTwelve_zero]; positivity
    refine (norm_thetaChiTwelve_term_le (z : ℂ) k).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      have h2 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast this
      nlinarith [sq_abs (k : ℝ)]
    have hzim : ((z : ℂ)).im = z.im := rfl
    rw [hzim]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hk1 (by linarith : (0 : ℝ) ≤ z.im - 1)]
  have hlim : Tendsto (fun z : ℍ => S * Real.exp (-(π / 12 * (z.im - 1)))) atImInfty (𝓝 0) := by
    have : Tendsto (fun z : ℍ => z.im) atImInfty atTop := tendsto_iff_comap.mpr le_rfl
    have h1 : Tendsto (fun z : ℍ => -(π / 12 * (z.im - 1))) atImInfty atBot := by
      apply Filter.tendsto_neg_atTop_atBot.comp
      exact Filter.Tendsto.const_mul_atTop (by positivity)
        (Filter.tendsto_atTop_add_const_right _ (-1) this)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul S
  refine squeeze_zero_norm' ?_ hlim
  have : ∀ᶠ z : ℍ in atImInfty, 1 ≤ z.im :=
    (UpperHalfPlane.atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩
  filter_upwards [this] with z hz using hbound z hz

theorem thetaChiTwelvePow24H_zeroAtImInfty : IsZeroAtImInfty thetaChiTwelvePow24H := by
  change Tendsto (fun z : ℍ => thetaChiTwelve z ^ 24) atImInfty (𝓝 0)
  simpa using tendsto_thetaChiTwelve_atImInfty.pow 24

/-- `ϑ₁₂^{24}` as a weight-twelve level-one cusp form. -/
def thetaChiTwelvePow24Cusp : CuspForm 𝒮ℒ 12 where
  toFun := thetaChiTwelvePow24H
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact thetaChiTwelvePow24H_slash_SL2Z γ
  holo' := thetaChiTwelvePow24H_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [thetaChiTwelvePow24H_slash_SL2Z γ]
    exact thetaChiTwelvePow24H_zeroAtImInfty

/-- **`ϑ₁₂^{24} = cΔ` with `c ≠ 0`.** -/
theorem exists_thetaChiTwelve_pow_eq_discriminant :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℍ, thetaChiTwelve z ^ 24 = c * ModularForm.discriminant z := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve thetaChiTwelvePow24Cusp
  have hc_pw : ∀ z : ℍ, thetaChiTwelve z ^ 24 = c * ModularForm.discriminant z := by
    intro z
    have h := DFunLike.congr_fun hc z
    rw [show (c • CuspForm.discriminant : CuspForm _ _) z =
      c * ModularForm.discriminant z from rfl] at h
    exact h.symm
  refine ⟨c, fun h0 => ?_, hc_pw⟩
  obtain ⟨y, hy, hne⟩ := exists_thetaChiTwelve_I_mul_ne_zero
  have him : 0 < (I * (y : ℂ)).im := by simpa using hy
  have := hc_pw ⟨I * (y : ℂ), him⟩
  rw [h0, zero_mul] at this
  exact hne (pow_eq_zero_iff (by norm_num) |>.mp this)

/-! ## `F_{1/3}` is a multiple of `ϑ₁₂` -/

theorem thetaPowerForm_third_pow24 {τ : ℂ} (hτ : 0 < τ.im) :
    thetaPowerForm (1 / 3) τ ^ 24 = (thetaTwo τ * thetaThree τ * thetaFour τ) ^ 8 := by
  have h3ne := thetaThree_ne_zero_of_im_pos hτ
  have hexp : Complex.exp ((((1 / 3) / 4 : ℝ) : ℂ) * hauptmodulLog τ) ^ 24 =
      thetaGroupHauptmodul τ ^ 2 := by
    rw [← Complex.exp_nat_mul, ← exp_hauptmodulLog hτ, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold thetaPowerForm
  rw [mul_pow, hexp]
  unfold thetaGroupHauptmodul
  field_simp

/-- **`F_{1/3} = κ ϑ₁₂` with a nonzero constant `κ`.** -/
theorem exists_thetaPowerForm_third_eq :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℂ, 0 < τ.im → thetaPowerForm (1 / 3) τ = κ * thetaChiTwelve τ := by
  obtain ⟨c, hc0, hc⟩ := exists_thetaChiTwelve_pow_eq_discriminant
  have hϑne : ∀ τ : ℂ, 0 < τ.im → thetaChiTwelve τ ≠ 0 := by
    intro τ hτ h0
    have h := hc ⟨τ, hτ⟩
    simp only at h
    rw [h0, zero_pow (by norm_num)] at h
    exact mul_ne_zero hc0 (ModularForm.discriminant_ne_zero ⟨τ, hτ⟩) h.symm
  set κf : ℂ → ℂ := fun τ => thetaPowerForm (1 / 3) τ / thetaChiTwelve τ with hκf
  have hpow : ∀ τ ∈ modUpperSet, κf τ ^ 24 = 256 / c := by
    intro τ hτ
    have hτ' : 0 < τ.im := hτ
    simp only [hκf]
    rw [div_pow, thetaPowerForm_third_pow24 hτ', hc ⟨τ, hτ'⟩]
    have hD := thetaProductPow8_discriminant_identity ⟨τ, hτ'⟩
    simp only at hD ⊢
    have hP : thetaTwo τ * thetaThree τ * thetaFour τ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (thetaTwo_ne_zero_of_im_pos hτ') (thetaThree_ne_zero_of_im_pos hτ'))
        (thetaFour_ne_zero_of_im_pos hτ')
    rw [hD]
    field_simp
    exact div_self hP
  have hdiff : DifferentiableOn ℂ κf modUpperSet := by
    intro τ hτ
    have hτ' : 0 < τ.im := hτ
    exact (((differentiableOn_thetaPowerForm (1 / 3)) τ hτ).differentiableAt
      (isOpen_modUpperSet.mem_nhds hτ)).div (differentiableAt_thetaChiTwelve hτ')
      (hϑne τ hτ') |>.differentiableWithinAt
  have hderiv : Set.EqOn (deriv κf) 0 modUpperSet := by
    intro τ hτ
    show deriv κf τ = 0
    have hτ' : 0 < τ.im := hτ
    have hne : κf τ ≠ 0 := by
      simp only [hκf]
      exact div_ne_zero (thetaPowerForm_ne_zero _ hτ') (hϑne τ hτ')
    have hd : HasDerivAt κf (deriv κf τ) τ :=
      (hdiff.differentiableAt (isOpen_modUpperSet.mem_nhds hτ)).hasDerivAt
    have hd24 := hd.pow 24
    have hloc : (fun z => κf z ^ 24) =ᶠ[𝓝 τ] fun _ => 256 / c :=
      Filter.eventually_of_mem (isOpen_modUpperSet.mem_nhds hτ) hpow
    have hconstd : HasDerivAt (fun z => κf z ^ 24) 0 τ :=
      (hasDerivAt_const τ (256 / c)).congr_of_eventuallyEq hloc
    have h0 := hd24.unique hconstd
    have h24 : ((24 : ℕ) : ℂ) * κf τ ^ (24 - 1) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _ hne)
    exact (mul_eq_zero.mp h0).resolve_left h24
  set κ : ℂ := κf I with hκ
  have hconst : ∀ τ ∈ modUpperSet, κf τ = κ := fun τ hτ =>
    isOpen_modUpperSet.is_const_of_deriv_eq_zero isPreconnected_modUpperSet hdiff hderiv hτ
      I_mem_modUpperSet
  refine ⟨κ, ?_, fun τ hτ => ?_⟩
  · rw [hκ]; simp only [hκf]
    exact div_ne_zero (thetaPowerForm_ne_zero _ (by simp)) (hϑne I (by simp))
  · have h := hconst τ hτ
    simp only [hκf] at h
    rw [← h]
    field_simp [hϑne τ hτ]

/-! ## The identification with `L(s, χ₁₂)` -/

/-- **The transform at `a = 1/3` is the completed `L`-function of `χ₁₂`.** -/
theorem exists_thetaPowerXiC_third_eq_completedLFunction :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ w : ℂ, |w.im| < 1 →
      thetaPowerXiC (1 / 3) w = κ * (12 : ℂ) ^ ((1 / 2 - I * w) / 2) *
        DirichletCharacter.completedLFunction dirichletChiTwelve (1 / 2 - I * w) := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_thetaPowerForm_third_eq
  refine ⟨κ / 2, div_ne_zero hκ0 two_ne_zero, fun w hw => ?_⟩
  set G : ℂ → ℂ := fun w => κ / 2 * (12 : ℂ) ^ ((1 / 2 - I * w) / 2) *
      DirichletCharacter.completedLFunction dirichletChiTwelve (1 / 2 - I * w) with hG
  have hGd : Differentiable ℂ G := by
    intro w
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (12 : ℂ) ^ ((1 / 2 - I * w) / 2)) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
    have h2 : DifferentiableAt ℂ (fun w : ℂ =>
        DirichletCharacter.completedLFunction dirichletChiTwelve (1 / 2 - I * w)) w :=
      ((DirichletCharacter.differentiable_completedLFunction dirichletChiTwelve_ne_one) _).comp w
        (by fun_prop)
    exact ((differentiableAt_const _).mul h1).mul h2
  have hF := differentiableOn_thetaPowerXiC (a := 1 / 3) (by norm_num)
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
  have hmel : ∀ z : ℂ, mellin (fun y : ℝ => thetaPowerForm (1 / 3) (I * (y : ℂ))) z =
      κ * mellin (fun y : ℝ => thetaChiTwelve (I * (y : ℂ))) z := by
    intro z
    rw [← smul_eq_mul, ← mellin_const_smul]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have him : 0 < (I * (y : ℂ)).im := by simpa using hy
    simp only [smul_eq_mul]
    rw [hκ _ him]
  have heq : ∀ w ∈ upperQuarterStrip, thetaPowerXiC (1 / 3) w = G w := by
    intro w hw
    have hre : 1 / 2 < ((1 / 2 - I * w) / 2).re := by
      have : ((1 / 2 - I * w) / 2).re = (1 / 2 + w.im) / 2 := by simp
      rw [this]; linarith [hw.1]
    rw [thetaPowerXiC_eq_mellin, hmel, mellin_thetaChiTwelve hre]
    simp only [hG]
    rw [show 2 * ((1 / 2 - I * w) / 2) = 1 / 2 - I * w by ring]
    ring
  have hopen : IsOpen upperQuarterStrip :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hw₀q : w₀ ∈ upperQuarterStrip := by
    show 1 / 2 < w₀.im ∧ w₀.im < 1; simp [hw₀]; norm_num
  have hev : thetaPowerXiC (1 / 3) =ᶠ[𝓝 w₀] G :=
    Filter.eventually_of_mem (hopen.mem_nhds hw₀q) heq
  exact hanF.eqOn_of_preconnected_of_eventuallyEq hanG hconv.isPreconnected hw₀mem hev hw

/-- **The interior point `a = 1/3` is an Euler product.**  In the strip `|Im w| < 1`, the transform of
`F_{1/3}` has a zero off the critical line exactly when the completed `L(s, χ₁₂)` has a zero off the
critical line with `|Re s - ½| < 1`. -/
theorem thetaPowerXiC_third_offline_zero_iff :
    (∃ w : ℂ, w.im ≠ 0 ∧ |w.im| < 1 ∧ thetaPowerXiC (1 / 3) w = 0) ↔
      (∃ s : ℂ, s.re ≠ 1 / 2 ∧ |s.re - 1 / 2| < 1 ∧
        DirichletCharacter.completedLFunction dirichletChiTwelve s = 0) := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_thetaPowerXiC_third_eq_completedLFunction
  have h12 : ∀ w : ℂ, (12 : ℂ) ^ ((1 / 2 - I * w) / 2) ≠ 0 := by
    intro w; rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
  constructor
  · rintro ⟨w, hw0, hw1, hz⟩
    refine ⟨1 / 2 - I * w, ?_, ?_, ?_⟩
    · simp; exact hw0
    · simpa using hw1
    · rw [hκ w hw1] at hz
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hκ0 (h12 w))
  · rintro ⟨s, hs0, hs1, hz⟩
    set w : ℂ := I * (s - 1 / 2) with hw
    have hsw : 1 / 2 - I * w = s := by rw [hw]; ring_nf; rw [I_sq]; ring
    have hwim : w.im = s.re - 1 / 2 := by simp [hw]
    refine ⟨w, ?_, ?_, ?_⟩
    · rw [hwim]; intro h; apply hs0; linarith
    · rwa [hwim]
    · rw [hκ w (by rwa [hwim]), hsw, hz, mul_zero]

end

end RHTower
