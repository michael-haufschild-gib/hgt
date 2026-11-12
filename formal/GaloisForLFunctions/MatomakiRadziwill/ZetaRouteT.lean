import GaloisForLFunctions.MatomakiRadziwill.LadderRouteT
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistRouteTSharp
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

/-!
# Route T for `ζ` above polylogarithmic heights

`λ = λχ₁` for the character `χ₁` mod 1, so the twisted von Mangoldt coefficients are
`Λ(n)n^{-iτ}` (`twistedVM_trivial`).  The corpus contour bound
(`Sieve.exists_norm_partialSum_vonMangoldtTwist_routeT_le`) carries the pole of `ζ` as a term
`K(log K)²/|τ|`; with the smoothing `H = K/ℓ^6`, `ℓ = log X`, and the zero-free width
`w(γ) ≥ 1/(450 C ℓ^{0.9} (log ℓ)²)` (`zfw_ge`, from `Sieve.routeTZeroFreeDelta_polylog_lower`), every
term is `≤ Kℓ^{-5}` once `ℓ^{19} ≤ |τ| ≤ X` and `log K ≥ ℓ^{0.92}` (`exists_zetaChebyshev_le`):

`|Σ_{n≤K} Λ(n)n^{-iτ}| ≤ K/(log X)^4`.

The saving `(3K)^{-w} ≤ exp(−ℓ^{0.02}/(900C(log ℓ)²)) ≤ ℓ^{-40}` (`eventually_exp_decay_le`) needs
`log K ≥ ℓ^θ` with `θ > 9/10`.  Abel summation gives the prime blocks
(`exists_zetaPrimeBlock_le`) and the top-scale blocks of `λ` (`exists_norm_blockQ_liouville_le`):
`|Q_v(w)| ≤ (log X)^{-3}` for `ℓ^{19} ≤ 2π|w| ≤ X`.
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The character mod 1 is identically one. -/
theorem trivialChar_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

theorem twistedVM_trivial (τ : ℝ) (n : ℕ) :
    twistedVM (1 : DirichletCharacter ℂ 1) τ n = vonMangoldtTwist τ n := by
  rw [twistedVM, trivialChar_apply, one_mul, vonMangoldtTwist]

theorem sum_Icc_twistedVM_trivial (τ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, twistedVM (1 : DirichletCharacter ℂ 1) τ n
      = ∑ n ∈ Finset.range (N + 1), vonMangoldtTwist τ n := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), vonMangoldtTwist_zero,
    zero_add, ← Finset.Ico_add_one_right_eq_Icc]
  exact sum_congr rfl fun n _ => twistedVM_trivial τ n

theorem log_five_ge : (3 / 2 : ℝ) ≤ Real.log 5 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
  have h2 := exp_half_lt
  have h3 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  rw [h1]
  nlinarith

theorem log_five_le : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]; nlinarith

/-- **The zero-free width at heights up to `X`.** -/
theorem zfw_ge (A : ℝ) {X τ : ℝ} (hX : 7 ≤ X) (hℓ5 : 5 ≤ Real.log X)
    (hτ1 : 16 * Real.pi / 3 ≤ |τ|) (hτX : |τ| ≤ X) :
    1 / (450 * routeTZeroFreeDeltaEnvelopeConstant A * Real.log X ^ (9 / 10 : ℝ)
        * Real.log (Real.log X) ^ 2)
      ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := by
  set ℓ := Real.log X with hℓdef
  set Cδ := routeTZeroFreeDeltaEnvelopeConstant A with hCδ
  have hC0 : 0 < Cδ := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hX0 : 0 < X := by linarith
  have hγ : 8 * Real.pi + 1 ≤ 3 * |τ| / 2 + 1 := by linarith
  have hδ := routeTZeroFreeDelta_polylog_lower (A := A) hγ
  set Z := routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) with hZdef
  have hZ1 : 1 ≤ Z := routeTLogHeightEnvelope_one_le (by positivity)
  have hZ5 : Z ≤ 5 * ℓ := by
    have h1 : 4 * (3 * |τ| / 2 + 1) + 2 ≤ X ^ 2 := by nlinarith
    have h2 : Real.log (4 * (3 * |τ| / 2 + 1) + 2) ≤ 2 * ℓ := by
      calc Real.log (4 * (3 * |τ| / 2 + 1) + 2) ≤ Real.log (X ^ 2) :=
            Real.log_le_log (by positivity) h1
        _ = 2 * ℓ := by rw [Real.log_pow]; push_cast; ring
    rw [hZdef, routeTLogHeightEnvelope]
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hZ09 : Z ^ (9 / 10 : ℝ) ≤ 5 * ℓ ^ (9 / 10 : ℝ) := by
    have h1 : Z ^ (9 / 10 : ℝ) ≤ (5 * ℓ) ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hZ5 (by norm_num)
    have h2 : (5 * ℓ) ^ (9 / 10 : ℝ) = (5 : ℝ) ^ (9 / 10 : ℝ) * ℓ ^ (9 / 10 : ℝ) :=
      Real.mul_rpow (by norm_num) hℓ0.le
    have h3 : (5 : ℝ) ^ (9 / 10 : ℝ) ≤ 5 := by
      calc (5 : ℝ) ^ (9 / 10 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 5 := Real.rpow_one 5
    have h4 : 0 ≤ ℓ ^ (9 / 10 : ℝ) := Real.rpow_nonneg hℓ0.le _
    nlinarith
  have hlogZ : 1 + Real.log Z ≤ 3 * Real.log ℓ := by
    have h1 : Real.log Z ≤ Real.log (5 * ℓ) := Real.log_le_log (by linarith) hZ5
    have h2 : Real.log (5 * ℓ) = Real.log 5 + Real.log ℓ :=
      Real.log_mul (by norm_num) hℓ0.ne'
    have h3 : Real.log 5 ≤ Real.log ℓ := Real.log_le_log (by norm_num) hℓ5
    have h4 := log_five_ge
    have h5 := log_five_le
    linarith
  have hlogZ0 : 0 ≤ 1 + Real.log Z := by have := Real.log_nonneg hZ1; linarith
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hden : Cδ * Z ^ (9 / 10 : ℝ) * (1 + Real.log Z) ^ 2
      ≤ 45 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2 := by
    have h1 : (1 + Real.log Z) ^ 2 ≤ 9 * Real.log ℓ ^ 2 := by
      have := pow_le_pow_left₀ hlogZ0 hlogZ 2
      nlinarith
    have hZ0 : 0 ≤ Z ^ (9 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc Cδ * Z ^ (9 / 10 : ℝ) * (1 + Real.log Z) ^ 2
        ≤ Cδ * (5 * ℓ ^ (9 / 10 : ℝ)) * (9 * Real.log ℓ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hZ09 hC0.le) h1 (sq_nonneg _)
            (by have := Real.rpow_nonneg hℓ0.le (9 / 10 : ℝ); positivity)
      _ = 45 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2 := by ring
  have hden0 : 0 < Cδ * Z ^ (9 / 10 : ℝ) * (1 + Real.log Z) ^ 2 := by
    have : 0 < Z ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have : 0 < 1 + Real.log Z := by have := Real.log_nonneg hZ1; linarith
    positivity
  have hstep : 1 / (45 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2)
      ≤ routeTZeroFreeDelta A (3 * |τ| / 2 + 1) :=
    le_trans (one_div_le_one_div_of_le hden0 hden) hδ
  rw [routeTZeroFreeWidth]
  have e : 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2)
      = 1 / (45 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) / 10 := by
    rw [div_div]; ring_nf
  rw [e]
  exact div_le_div_of_nonneg_right hstep (by norm_num)

/-- **The super-polylogarithmic saving.**  For large `ℓ`,
`exp(−ℓ^{0.02}/(900C(log ℓ)²)) ≤ ℓ^{-40}`. -/
theorem eventually_exp_decay_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ ℓ : ℝ in atTop,
      Real.exp (-(ℓ ^ (2 / 100 : ℝ) / (900 * C * Real.log ℓ ^ 2))) ≤ 1 / ℓ ^ 40 := by
  set c : ℝ := (1 / (36000 * C)) ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 < c := by positivity
  have hc3 : c ^ 3 = 1 / (36000 * C) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 150)).bound hc0,
    eventually_gt_atTop (3 : ℝ)] with ℓ hb hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hlog1 : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓ0]
    linarith [Real.exp_one_lt_d9]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (Real.rpow_nonneg hℓ0.le _)] at hb
  -- `(log ℓ)³ ≤ ℓ^{0.02}/(36000 C)`
  have hcube : Real.log ℓ ^ 3 ≤ ℓ ^ (2 / 100 : ℝ) / (36000 * C) := by
    have h1 := pow_le_pow_left₀ (by linarith) hb 3
    have h2 : (c * ℓ ^ (1 / 150 : ℝ)) ^ 3 = c ^ 3 * ℓ ^ (2 / 100 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (ℓ ^ (1 / 150 : ℝ)), ← Real.rpow_mul hℓ0.le]; norm_num
    rw [h2, hc3] at h1
    calc Real.log ℓ ^ 3 ≤ 1 / (36000 * C) * ℓ ^ (2 / 100 : ℝ) := h1
      _ = ℓ ^ (2 / 100 : ℝ) / (36000 * C) := by ring
  -- so the exponent is at least `40 log ℓ`
  have hexp : 40 * Real.log ℓ ≤ ℓ ^ (2 / 100 : ℝ) / (900 * C * Real.log ℓ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : 40 * Real.log ℓ * (900 * C * Real.log ℓ ^ 2) = 36000 * C * Real.log ℓ ^ 3 := by ring
    rw [this]
    have h := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 36000 * C)
    rwa [mul_div_cancel₀ _ (by positivity)] at h
  have h40 : Real.exp (40 * Real.log ℓ) = ℓ ^ 40 := by
    rw [show (40 : ℝ) * Real.log ℓ = ((40 : ℕ) : ℝ) * Real.log ℓ by norm_num, Real.exp_nat_mul,
      Real.exp_log hℓ0]
  calc Real.exp (-(ℓ ^ (2 / 100 : ℝ) / (900 * C * Real.log ℓ ^ 2)))
      ≤ Real.exp (-(40 * Real.log ℓ)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / ℓ ^ 40 := by rw [Real.exp_neg, h40, one_div]

/-- The numerical conditions of the `ζ` Chebyshev bound, eventually in `ℓ = log X`. -/
theorem eventually_zeta_conditions (Ctot Cδ delta τ₀ : ℝ) (hCδ : 0 < Cδ) (hdelta : 0 < delta) :
    ∀ᶠ ℓ : ℝ in atTop, 5 ≤ ℓ ∧ Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) + 2 ≤ ℓ
      ∧ τ₀ ≤ ℓ ^ 19 ∧ 16 * Real.pi / 3 ≤ ℓ ^ 19 ∧ 9 ≤ ℓ ^ (92 / 100 : ℝ)
      ∧ 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) ≤ delta
      ∧ Real.exp (-(ℓ ^ (2 / 100 : ℝ) / (900 * Cδ * Real.log ℓ ^ 2))) ≤ 1 / ℓ ^ 40 := by
  have hpow19 := (tendsto_pow_atTop (by norm_num : (19 : ℕ) ≠ 0) : Tendsto (fun ℓ : ℝ => ℓ ^ 19)
    atTop atTop)
  have hden : Tendsto (fun ℓ : ℝ => 450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) atTop atTop := by
    have h1 : Tendsto (fun ℓ : ℝ => 450 * Cδ * ℓ ^ (9 / 10 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)
    refine h1.atTop_mul_atTop₀ ?_
    exact (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hsmall : ∀ᶠ ℓ : ℝ in atTop, 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) ≤ delta := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
    exact this.eventually (ge_mem_nhds hdelta)
  filter_upwards [eventually_ge_atTop 5,
    eventually_ge_atTop (Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) + 2),
    hpow19.eventually_ge_atTop τ₀, hpow19.eventually_ge_atTop (16 * Real.pi / 3),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 92 / 100)).eventually_ge_atTop 9, hsmall,
    eventually_exp_decay_le hCδ] with ℓ h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The arithmetic of the `ζ` Chebyshev bound, in abstract variables. -/
theorem cheb_assembly {K H ℓ τa LN M E LKH Ctot Cδ : ℝ} (hK : 0 < K) (hH : H = K / ℓ ^ 6)
    (hℓ : 5 ≤ ℓ) (hτa : ℓ ^ 19 ≤ τa) (hLN0 : 0 ≤ LN) (hLN : LN ≤ ℓ) (hM0 : 0 ≤ M)
    (hM : M ≤ (1 + 900 * Cδ) * ℓ ^ 4) (hE0 : 0 ≤ E) (hE : E ≤ 1 / ℓ ^ 40) (hLKH : LKH ≤ 2 * ℓ)
    (hℓC : Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) + 2 ≤ ℓ) (hCtot : 0 < Ctot)
    (hCδ : 0 < Cδ) :
    Ctot * K * (K / H) ^ 2 * (LN ^ 2 / τa + M * (E + 1 / τa ^ 2)) / (2 * Real.pi) + LKH * H
      ≤ K / ℓ ^ 4 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith
  have hτ0 : 0 < τa := lt_of_lt_of_le (by positivity) hτa
  have hKH : (K / H) ^ 2 = ℓ ^ 12 := by rw [hH, div_div_cancel₀ hK.ne']; ring
  -- the pole term
  have ht1 : LN ^ 2 / τa ≤ 1 / ℓ ^ 17 := by
    rw [div_le_div_iff₀ hτ0 (by positivity)]
    have h1 : LN ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hLN0 hLN 2
    have h3 : LN ^ 2 * ℓ ^ 17 ≤ ℓ ^ 2 * ℓ ^ 17 := mul_le_mul_of_nonneg_right h1 (by positivity)
    have h2 : ℓ ^ 2 * ℓ ^ 17 = ℓ ^ 19 := by ring
    linarith
  -- the zero-free term
  have hb2 : 1 / τa ^ 2 ≤ 1 / ℓ ^ 38 := by
    have : ℓ ^ 38 ≤ τa ^ 2 := by
      calc ℓ ^ 38 = (ℓ ^ 19) ^ 2 := by ring
        _ ≤ τa ^ 2 := pow_le_pow_left₀ (by positivity) hτa 2
    exact one_div_le_one_div_of_le (by positivity) this
  have hEb : E + 1 / τa ^ 2 ≤ 2 / ℓ ^ 38 := by
    have : 1 / ℓ ^ 40 ≤ 1 / ℓ ^ 38 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hℓ1 (by norm_num))
    have e : (2 : ℝ) / ℓ ^ 38 = 1 / ℓ ^ 38 + 1 / ℓ ^ 38 := by ring
    linarith
  have hME : M * (E + 1 / τa ^ 2) ≤ 2 * (1 + 900 * Cδ) / ℓ ^ 17 := by
    have h1 := mul_le_mul hM hEb (by positivity) (by positivity)
    have h2 : (1 + 900 * Cδ) * ℓ ^ 4 * (2 / ℓ ^ 38) = 2 * (1 + 900 * Cδ) / ℓ ^ 34 := by
      field_simp
    have h3 : 2 * (1 + 900 * Cδ) / ℓ ^ 34 ≤ 2 * (1 + 900 * Cδ) / ℓ ^ 17 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hℓ1 (by norm_num))
    linarith
  have hinner : LN ^ 2 / τa + M * (E + 1 / τa ^ 2) ≤ (1 + 2 * (1 + 900 * Cδ)) / ℓ ^ 17 := by
    have e : (1 + 2 * (1 + 900 * Cδ)) / ℓ ^ 17 = 1 / ℓ ^ 17 + 2 * (1 + 900 * Cδ) / ℓ ^ 17 := by
      ring
    linarith
  have hC0 : 0 ≤ Ctot * K * (K / H) ^ 2 / (2 * Real.pi) := by
    rw [hKH]; positivity
  have hmain : Ctot * K * (K / H) ^ 2 * (LN ^ 2 / τa + M * (E + 1 / τa ^ 2)) / (2 * Real.pi)
      ≤ Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) * K / ℓ ^ 5 := by
    have e1 : Ctot * K * (K / H) ^ 2 * (LN ^ 2 / τa + M * (E + 1 / τa ^ 2)) / (2 * Real.pi)
        = Ctot * K * (K / H) ^ 2 / (2 * Real.pi) * (LN ^ 2 / τa + M * (E + 1 / τa ^ 2)) := by
      ring
    rw [e1]
    refine le_trans (mul_le_mul_of_nonneg_left hinner hC0) (le_of_eq ?_)
    rw [hKH]; field_simp
  -- the smoothing
  have hH0 : 0 < H := by rw [hH]; positivity
  have hLKH0 : LKH * H ≤ 2 * K / ℓ ^ 5 := by
    calc LKH * H ≤ 2 * ℓ * H := mul_le_mul_of_nonneg_right hLKH hH0.le
      _ = 2 * K / ℓ ^ 5 := by rw [hH]; field_simp
  have hfin : Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) * K / ℓ ^ 5 + 2 * K / ℓ ^ 5
      ≤ K / ℓ ^ 4 := by
    rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hNℓ : (Ctot / (2 * Real.pi) * (1 + 2 * (1 + 900 * Cδ)) + 2) * K ≤ ℓ * K :=
      mul_le_mul_of_nonneg_right hℓC hK.le
    have h4 : (0 : ℝ) ≤ ℓ ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right hNℓ h4
    have e : ℓ ^ 5 = ℓ * ℓ ^ 4 := by ring
    rw [e]
    linarith
  linarith

/-- The zero-free bracket `1/|τ| + log(3|τ|/2)/w(3|τ|/2+1) ≤ (1 + 900C)ℓ⁴`. -/
theorem bracket_le {A X τ Cδ : ℝ} (hX7 : 7 ≤ X) (hℓ5 : 5 ≤ Real.log X) (hτ1 : 1 ≤ |τ|)
    (hτX : |τ| ≤ X) (hCδ : 0 < Cδ)
    (hz : 1 / (450 * Cδ * Real.log X ^ (9 / 10 : ℝ) * Real.log (Real.log X) ^ 2)
      ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1)) :
    1 / |τ| + Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)
      ≤ (1 + 900 * Cδ) * Real.log X ^ 4 := by
  set ℓ := Real.log X with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hX0 : 0 < X := by linarith
  have hτ0 : 0 < |τ| := by linarith
  set z := 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) with hzdef
  have hlogℓ1 : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓ0]; linarith [Real.exp_one_lt_d9]
  have hz0 : 0 < z := by
    have := Real.rpow_pos_of_pos hℓ0 (9 / 10 : ℝ); positivity
  have h1 : 1 / |τ| ≤ 1 := by rw [div_le_one hτ0]; exact hτ1
  have hlog0 : 0 ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
  have hX2 : 7 * X ≤ X * X := mul_le_mul_of_nonneg_right hX7 hX0.le
  have hlog2 : Real.log (3 * |τ| / 2) ≤ 2 * ℓ := by
    have : 3 * |τ| / 2 ≤ X ^ 2 := by rw [sq]; linarith
    calc Real.log (3 * |τ| / 2) ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * ℓ := by rw [Real.log_pow]; push_cast; ring
  have h2 : Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1) ≤ 2 * ℓ / z :=
    div_le_div₀ (by linarith) hlog2 hz0 hz
  have h3 : 2 * ℓ / z = 900 * Cδ * ℓ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2 := by
    rw [hzdef]; field_simp; ring
  have h4 : ℓ ^ (9 / 10 : ℝ) ≤ ℓ := by
    calc ℓ ^ (9 / 10 : ℝ) ≤ ℓ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = ℓ := Real.rpow_one ℓ
  have h5 : Real.log ℓ ≤ ℓ := le_trans (Real.log_le_sub_one_of_pos hℓ0) (by linarith)
  have h6 : Real.log ℓ ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by linarith) h5 2
  have h7 : 900 * Cδ * ℓ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2 ≤ 900 * Cδ * ℓ ^ 4 := by
    have hr0 : 0 ≤ ℓ ^ (9 / 10 : ℝ) := Real.rpow_nonneg hℓ0.le _
    have : ℓ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2 ≤ ℓ * ℓ * ℓ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h4 hℓ0.le) h6 (sq_nonneg _) (by positivity)
    have e : ℓ * ℓ * ℓ ^ 2 = ℓ ^ 4 := by ring
    calc 900 * Cδ * ℓ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2
        = 900 * Cδ * (ℓ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) := by ring
      _ ≤ 900 * Cδ * (ℓ * ℓ * ℓ ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 900 * Cδ * ℓ ^ 4 := by rw [e]
  have h8 : (1 : ℝ) ≤ ℓ ^ 4 := one_le_pow₀ (by linarith)
  linarith

/-- The saving `(3K)^{-w} ≤ ℓ^{-40}` once the width is at least half the zero-free lower bound. -/
theorem rpow_saving_le {K ℓ Cδ w' : ℝ} (hK : 0 < K) (hℓ5 : 5 ≤ ℓ) (hCδ : 0 < Cδ)
    (hlogK : ℓ ^ (92 / 100 : ℝ) ≤ Real.log K)
    (hw' : 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) / 2 ≤ w')
    (hexp : Real.exp (-(ℓ ^ (2 / 100 : ℝ) / (900 * Cδ * Real.log ℓ ^ 2))) ≤ 1 / ℓ ^ 40) :
    (3 * K) ^ (-w') ≤ 1 / ℓ ^ 40 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ1 : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓ0]; linarith [Real.exp_one_lt_d9]
  set z := 1 / (450 * Cδ * ℓ ^ (9 / 10 : ℝ) * Real.log ℓ ^ 2) with hzdef
  have hz0 : 0 < z := by
    have := Real.rpow_pos_of_pos hℓ0 (9 / 10 : ℝ); positivity
  have hw0 : 0 ≤ w' := by linarith
  have h1 : (3 * K) ^ (-w') ≤ K ^ (-w') :=
    Real.rpow_le_rpow_of_nonpos hK (by linarith) (by linarith)
  have h2 : K ^ (-w') = Real.exp (-(w' * Real.log K)) := by
    rw [Real.rpow_def_of_pos hK]; ring_nf
  have h3 : z / 2 * ℓ ^ (92 / 100 : ℝ) ≤ w' * Real.log K :=
    mul_le_mul hw' hlogK (Real.rpow_nonneg hℓ0.le _) hw0
  have h4 : z / 2 * ℓ ^ (92 / 100 : ℝ) = ℓ ^ (2 / 100 : ℝ) / (900 * Cδ * Real.log ℓ ^ 2) := by
    have hsplit : ℓ ^ (92 / 100 : ℝ) = ℓ ^ (9 / 10 : ℝ) * ℓ ^ (2 / 100 : ℝ) := by
      rw [← Real.rpow_add hℓ0]; norm_num
    rw [hzdef, hsplit]
    have : 0 < ℓ ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hℓ0 _
    field_simp
    ring
  calc (3 * K) ^ (-w') ≤ K ^ (-w') := h1
    _ = Real.exp (-(w' * Real.log K)) := h2
    _ ≤ Real.exp (-(ℓ ^ (2 / 100 : ℝ) / (900 * Cδ * Real.log ℓ ^ 2))) :=
        Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / ℓ ^ 40 := hexp

/-- **The twisted Chebyshev bound for `ζ` above polylogarithmic heights.** -/
theorem exists_zetaChebyshev_le :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ τ : ℝ, Real.log X ^ 19 ≤ |τ| → |τ| ≤ X → ∀ N : ℕ,
      Real.log X ^ (92 / 100 : ℝ) ≤ Real.log N → (N : ℝ) ≤ X →
        ‖∑ n ∈ Finset.Icc 1 N, twistedVM (1 : DirichletCharacter ℂ 1) τ n‖
          ≤ N / Real.log X ^ 4 := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, -, hdelta, hCtot, -, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_le
  set Cδ := routeTZeroFreeDeltaEnvelopeConstant A with hCδdef
  have hCδ : 0 < Cδ := routeTZeroFreeDeltaEnvelopeConstant_pos A
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_zeta_conditions Ctot Cδ delta τ₀ hCδ hdelta))
  refine ⟨max X₂ 7, fun X hX τ hτlo hτhi N hlogN hNX => ?_⟩
  obtain ⟨hℓ5, hℓC, hτ₀ℓ, hτπ, hℓ9, hzδ, hexp⟩ := hX₂ X (le_trans (le_max_left _ _) hX)
  have hX7 : 7 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hℓ0 : 0 < Real.log X := by linarith
  -- `N ≥ e⁹`
  have hlogN9 : 9 ≤ Real.log N := le_trans hℓ9 hlogN
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at hlogN9
    linarith
  have hN9 : Real.exp 9 ≤ N := by
    rw [← Real.exp_log hN0]; exact Real.exp_le_exp.mpr hlogN9
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN9
  set H : ℝ := N / Real.log X ^ 6 with hHdef
  have hℓ6 : 1 ≤ Real.log X ^ 6 := one_le_pow₀ (by linarith)
  have hH0 : 0 < H := by positivity
  have hHN : H ≤ N := div_le_self hN0.le hℓ6
  have hτ₀ : τ₀ ≤ |τ| := le_trans hτ₀ℓ hτlo
  have hb := hbound N H τ hN9 hH0 hHN hτ₀
  rw [sum_Icc_twistedVM_trivial]
  refine le_trans hb ?_
  have hτ1 : 1 ≤ |τ| := le_trans (one_le_pow₀ (by linarith)) hτlo
  have hz := zfw_ge A hX7 hℓ5 (le_trans hτπ hτlo) hτhi
  have hM := bracket_le hX7 hℓ5 hτ1 hτhi hCδ hz
  have hM0 : 0 ≤ 1 / |τ| + Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := by
    have : 0 ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
    have := routeTZeroFreeWidth_pos A (3 * |τ| / 2 + 1)
    positivity
  have hw' : 1 / (450 * Cδ * Real.log X ^ (9 / 10 : ℝ) * Real.log (Real.log X) ^ 2) / 2
      ≤ routeTUniformRegWidth A delta (3 * |τ| / 2) := by
    rw [routeTUniformRegWidth]
    have : 1 / (450 * Cδ * Real.log X ^ (9 / 10 : ℝ) * Real.log (Real.log X) ^ 2)
        ≤ min delta (routeTZeroFreeWidth A (3 * |τ| / 2 + 1)) := le_min hzδ hz
    linarith
  have hE := rpow_saving_le hN0 hℓ5 hCδ hlogN hw' hexp
  have hE0 : 0 ≤ (3 * (N : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.rpow_nonneg (by positivity) _
  have hlogNℓ : Real.log N ≤ Real.log X := Real.log_le_log hN0 hNX
  have hX2 : 7 * X ≤ X * X := mul_le_mul_of_nonneg_right hX7 hX0.le
  have hLKH : Real.log ((N : ℝ) + H) ≤ 2 * Real.log X := by
    have : (N : ℝ) + H ≤ X ^ 2 := by rw [sq]; linarith
    calc Real.log ((N : ℝ) + H) ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  exact cheb_assembly hN0 hHdef hℓ5 hτlo (by linarith) hlogNℓ hM0 hM hE0 hE hLKH hℓC hCtot hCδ

/-- **Prime blocks for `ζ` above polylogarithmic heights.** -/
theorem exists_zetaPrimeBlock_le :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ τ : ℝ, Real.log X ^ 19 ≤ |τ| → |τ| ≤ X → ∀ P Q : ℕ,
      Real.log X ^ (92 / 100 : ℝ) ≤ Real.log P → P ≤ Q → Q ≤ 2 * P → (Q : ℝ) ≤ X →
        ‖∑ p ∈ (Ioc P Q).filter Nat.Prime,
            (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-(1 + (τ : ℂ) * I))‖
          ≤ 1 / Real.log X ^ 3 := by
  obtain ⟨X₁, hX₁⟩ := exists_zetaChebyshev_le
  have hev : ∀ᶠ ℓ : ℝ in atTop, 6 ≤ ℓ ∧
      18 * ℓ ^ (3 : ℝ) * Real.exp (-((1 / 2) * ℓ ^ (92 / 100 : ℝ))) ≤ 1
      ∧ 1 ≤ ℓ ^ (92 / 100 : ℝ) :=
    (eventually_ge_atTop 6).and ((eventually_mul_rpow_mul_exp_le_one (κ := 1 / 2)
      (η := 92 / 100) (K := 18) (p := 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 92 / 100)).eventually_ge_atTop 1))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually hev)
  refine ⟨max (max X₁ X₂) 1, fun X hX τ hτlo hτ P Q hlogP hPQ hQP hQX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  obtain ⟨hℓ6, hexp, hℓθ1⟩ := hX₂ X hX2
  set ℓ : ℝ := Real.log X with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hlogP1 : 1 ≤ Real.log P := le_trans hℓθ1 hlogP
  have hP : 2 ≤ P := by
    by_contra h
    have h01 : P = 0 ∨ P = 1 := by omega
    rcases h01 with h0 | h0 <;> rw [h0] at hlogP1 <;> norm_num at hlogP1
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hS : ∀ t : ℕ, P ≤ t → t ≤ Q →
      ‖∑ n ∈ Finset.Icc 1 t, twistedVM (1 : DirichletCharacter ℂ 1) τ n‖ ≤ t / ℓ ^ 4 := by
    intro t hPt htQ
    exact hX₁ X hX1 τ hτlo hτ t
      (le_trans hlogP (Real.log_le_log (by linarith) (by exact_mod_cast hPt)))
      (le_trans (by exact_mod_cast htQ) hQX)
  have hIoc : ∀ t : ℕ, P ≤ t → ∑ m ∈ Ioc P t, twistedVM (1 : DirichletCharacter ℂ 1) τ m
      = ∑ n ∈ Finset.Icc 1 t, twistedVM (1 : DirichletCharacter ℂ 1) τ n
        - ∑ n ∈ Finset.Icc 1 P, twistedVM (1 : DirichletCharacter ℂ 1) τ n := by
    intro t hPt
    have e1 : Finset.Icc 1 t = Finset.Ioc 0 t := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e2 : Finset.Icc 1 P = Finset.Ioc 0 P := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le P) hPt]
    ring
  have hL4 : 0 < ℓ ^ 4 := by positivity
  have hB : ∀ t, P ≤ t → t ≤ Q →
      ‖∑ m ∈ Ioc P t, twistedVM (1 : DirichletCharacter ℂ 1) τ m‖ ≤ (3 * P) / ℓ ^ 4 := by
    intro t hPt htQ
    rw [hIoc t hPt]
    have h1 := hS t hPt htQ
    have h2 := hS P le_rfl hPQ
    have htQ' : (t : ℝ) ≤ 2 * P := by exact_mod_cast le_trans htQ hQP
    calc ‖∑ n ∈ Finset.Icc 1 t, twistedVM (1 : DirichletCharacter ℂ 1) τ n
          - ∑ n ∈ Finset.Icc 1 P, twistedVM (1 : DirichletCharacter ℂ 1) τ n‖
        ≤ t / ℓ ^ 4 + P / ℓ ^ 4 := le_trans (norm_sub_le _ _) (add_le_add h1 h2)
      _ = (t + P) / ℓ ^ 4 := by ring
      _ ≤ (3 * P) / ℓ ^ 4 := div_le_div_of_nonneg_right (by linarith) hL4.le
  have hblock := norm_sum_primeBlock_le (1 : DirichletCharacter ℂ 1) τ hP hPQ hB
  have hpp := psi_sub_theta_mul_primeWeight_le hP hPQ hQP
  have hw : primeWeight P ≤ 1 / P := by
    unfold primeWeight
    have : (P : ℝ) ≤ P * Real.log P := le_mul_of_one_le_right (by linarith) hlogP1
    exact one_div_le_one_div_of_le (by linarith) this
  have hterm1 : (3 * P) / ℓ ^ 4 * primeWeight P ≤ 1 / (2 * ℓ ^ 3) := by
    have h1 : (3 * P) / ℓ ^ 4 * primeWeight P ≤ (3 * P) / ℓ ^ 4 * (1 / P) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 : (3 * P) / ℓ ^ 4 * (1 / P) = 3 / (ℓ ^ 3 * ℓ) := by field_simp
    have h3 : 3 / (ℓ ^ 3 * ℓ) ≤ 1 / (2 * ℓ ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (0 : ℝ) < ℓ ^ 3 := by positivity
      nlinarith
    linarith
  have hsqrtP : 18 * ℓ ^ (3 : ℝ) ≤ Real.sqrt P := by
    have hsq : Real.sqrt P = Real.exp (Real.log P / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1
      ring
    have h1 : 18 * ℓ ^ (3 : ℝ) ≤ Real.exp ((1 / 2) * ℓ ^ (92 / 100 : ℝ)) := by
      have hE := Real.exp_pos ((1 / 2) * ℓ ^ (92 / 100 : ℝ))
      have hid : 18 * ℓ ^ (3 : ℝ)
          = 18 * ℓ ^ (3 : ℝ) * Real.exp (-((1 / 2) * ℓ ^ (92 / 100 : ℝ)))
            * Real.exp ((1 / 2) * ℓ ^ (92 / 100 : ℝ)) := by
        rw [mul_assoc (18 * ℓ ^ (3 : ℝ)), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      rw [hid]
      calc 18 * ℓ ^ (3 : ℝ) * Real.exp (-((1 / 2) * ℓ ^ (92 / 100 : ℝ)))
            * Real.exp ((1 / 2) * ℓ ^ (92 / 100 : ℝ))
          ≤ 1 * Real.exp ((1 / 2) * ℓ ^ (92 / 100 : ℝ)) := mul_le_mul_of_nonneg_right hexp hE.le
        _ = Real.exp ((1 / 2) * ℓ ^ (92 / 100 : ℝ)) := one_mul _
    rw [hsq]
    exact le_trans h1 (Real.exp_le_exp.mpr (by linarith))
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3r] at hsqrtP
  have hterm2 : 9 / Real.sqrt P ≤ 1 / (2 * ℓ ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have htotal : (3 * P / ℓ ^ 4 + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P
      ≤ 1 / ℓ ^ 3 := by
    have e : (3 * P / ℓ ^ 4 + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P
        = 3 * P / ℓ ^ 4 * primeWeight P
          + (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P := by ring
    have e2 : 1 / (2 * ℓ ^ 3) + 1 / (2 * ℓ ^ 3) = 1 / ℓ ^ 3 := by field_simp; ring
    rw [e]
    linarith
  exact le_trans hblock htotal

/-- **Route T for `λ` at the top scale, above polylogarithmic frequencies.** -/
theorem exists_norm_blockQ_liouville_le :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ (Pa Pb : ℕ) (H : ℝ), 2 ≤ H →
      Real.log X ^ (92 / 100 : ℝ) ≤ Real.log Pa → (Pb : ℝ) ≤ X → ∀ v : ℕ, ∀ w : ℝ,
        Real.log X ^ 19 ≤ 2 * Real.pi * |w| → 2 * Real.pi * |w| ≤ X →
          ‖blockQ (twLiouville (1 : DirichletCharacter ℂ 1)) ((Ioc Pa Pb).filter Nat.Prime) H v w‖
            ≤ 1 / Real.log X ^ (3 : ℝ) := by
  obtain ⟨X₀, hX₀⟩ := exists_zetaPrimeBlock_le
  have hev : ∀ᶠ ℓ : ℝ in atTop, 4 ≤ ℓ ∧ 3 ≤ ℓ ^ (92 / 100 : ℝ) :=
    (eventually_ge_atTop 4).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 92 / 100)).eventually_ge_atTop 3)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually hev)
  refine ⟨max X₀ X₂, fun X hX Pa Pb H hH hlogPa hPbX v w hwlo hw => ?_⟩
  have hX1 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨hlogX, hθ3⟩ := hX₂ X (le_trans (le_max_right _ _) hX)
  have hH0 : (0 : ℝ) < H := by linarith
  -- `Pa ≥ 8`
  have hPa : 8 ≤ Pa := by
    have hlog3 : 3 ≤ Real.log Pa := le_trans hθ3 hlogPa
    have hPa0 : 0 < Pa := by
      by_contra h0
      have : Pa = 0 := by omega
      rw [this] at hlog3
      simp at hlog3
      linarith
    have hpos : (0 : ℝ) < Pa := by exact_mod_cast hPa0
    have h1 : Real.exp 3 ≤ Pa := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hlog3
    have h2 : (8 : ℝ) < Real.exp 3 := by
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h5 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
        pow_lt_pow_left₀ h4 (by norm_num) (by norm_num)
      rw [h3]; norm_num at h5 ⊢; linarith
    have : (8 : ℝ) < Pa := lt_of_lt_of_le h2 h1
    have : 8 < Pa := by exact_mod_cast this
    omega
  have hprimes : ∀ p ∈ (Ioc Pa Pb).filter Nat.Prime, p.Prime := fun p hp => (mem_filter.mp hp).2
  rw [blockQ_twLiouville_eq _ _ hprimes H v w, norm_neg, block_eq_Ioc hH0 v]
  have hτ : |(-(2 * Real.pi * w))| = 2 * Real.pi * |w| := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hL0 : 0 ≤ 1 / Real.log X ^ (3 : ℝ) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log X) (3 : ℝ)
    positivity
  have h3r : Real.log X ^ (3 : ℝ) = Real.log X ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hQ2 := block_Q_le_two_P hPa hH v Pb
  by_cases hPQ : max Pa (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1)
      ≤ min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1)
  · rw [h3r]
    refine hX₀ X hX1 _ (by rw [hτ]; exact hwlo) (by rw [hτ]; exact hw) _ _ ?_ hPQ hQ2 ?_
    · have hPa0 : (0 : ℝ) < Pa := by exact_mod_cast (show 0 < Pa by omega)
      exact le_trans hlogPa (Real.log_le_log hPa0 (by exact_mod_cast le_max_left _ _))
    · exact le_trans (by exact_mod_cast min_le_left _ _) hPbX
  · have hempty : (Ioc (max Pa (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1))
        (min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1))).filter Nat.Prime = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp
      rw [mem_Ioc] at hp
      omega
    rw [hempty, sum_empty, norm_zero]
    exact hL0

end

end GaloisForLFunctions.MatomakiRadziwill
