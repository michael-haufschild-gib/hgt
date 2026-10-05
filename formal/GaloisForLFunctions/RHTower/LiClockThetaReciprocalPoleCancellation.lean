import GaloisForLFunctions.RHTower.LiClockThetaReciprocalDegreeTilt
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor

/-!
# Completed pole cancellation of the reciprocal logarithm for `1 < p < 2`

Fix `1 < p < 2`, `d = 2 - p` and `s(u) = 1/2 + 1/(p-u)`, so `s(0) > 1`.  On `Re s > 1`,
`ξ(s) = (s-1) π^{-s/2} Γ(1+s/2) ζ(s)` (A10), so the logarithmic coefficients
`b_n = (-1)^n H^{(n)}(p)/n!` of the reciprocal germ split as `b_n = α_n + ζ_n` into the Taylor
coefficients of the completion logarithm and of `log ζ(s(u))`.

* (A11) `log((s(u)-1)/(s(0)-1)) = log(1 + u/d) - log(1 - u/p)`;
* (A12) `n d^n α_n - (-1)^{n+1} → 0`: eventually `α_n` has the sign `(-1)^{n+1}`;
* (A14) `ξ(s) = π^{-s/2} Γ(1+s/2) U(s)` on `Re s > 0` with the filled residue unit `U`, and on
  `|u| ≤ d`: `Re s(u) ≥ 1`, `ξ(s(u)) ≠ 0`, `U(s(u)) ≠ 0`;
* (A15) `n d^n b_n → 0` and `n d^n ζ_n - (-1)^n → 0`: the two leading pole terms cancel exactly.
-/

open Set Filter Topology Complex GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal
local notation "b" => liClockReciprocalLogCoeff

/-- `s_p(u) = 1/2 + 1/(p-u)`. -/
def liClockReciprocalPoleArgument (p u : ℝ) : ℝ := 1 / 2 + 1 / (p - u)

/-- The completion `C(s) = (s-1) π^{-s/2} Γ(1 + s/2)`. -/
def liClockReciprocalCompletion (s : ℝ) : ℝ := (s - 1) * Real.pi ^ (-s / 2) * Real.Gamma (1 + s / 2)

/-- The completion logarithm `log C(s(u))`. -/
def liClockReciprocalCompletionLog (p u : ℝ) : ℝ := Real.log (liClockReciprocalCompletion (liClockReciprocalPoleArgument p u))

/-- The Euler logarithm `log ζ(s(u))`. -/
def liClockReciprocalEulerLog (p u : ℝ) : ℝ := Real.log (riemannZeta (liClockReciprocalPoleArgument p u : ℂ)).re

/-- The completion coefficients `α_n = (log C ∘ s)^{(n)}(0)/n!`. -/
def liClockReciprocalCompletionCoeff (p : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (liClockReciprocalCompletionLog p) 0 / n.factorial

/-- The Euler coefficients `ζ_n = (log ζ ∘ s)^{(n)}(0)/n!`. -/
def liClockReciprocalEulerCoeff (p : ℝ) (n : ℕ) : ℝ := iteratedDeriv n (liClockReciprocalEulerLog p) 0 / n.factorial

local notation "σ" => liClockReciprocalPoleArgument
local notation "𝒞" => liClockReciprocalCompletion

/-! ## (A10) The completed factorization on the real axis -/

theorem liClockReciprocalCompletion_pos {s : ℝ} (hs : 1 < s) : 0 < 𝒞 s := by
  unfold liClockReciprocalCompletion
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < Real.pi ^ (-s / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h3 : 0 < Real.Gamma (1 + s / 2) := Real.Gamma_pos_of_pos (by linarith)
  positivity

/-- **(A10)** `ξ(s) = (s-1) π^{-s/2} Γ(1+s/2) ζ(s)` for real `s > 1`. -/
theorem xi_ofReal_eq_completion_mul_riemannZeta {s : ℝ} (hs : 1 < s) :
    xi (s : ℂ) = (𝒞 s : ℂ) * riemannZeta s := by
  rw [xi_eq_four_factors (by simpa using hs)]
  have hs2 : ((s : ℂ) / 2) ≠ 0 := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
    exact div_ne_zero this two_ne_zero
  have hΓ : Complex.Gamma (1 + (s : ℂ) / 2) = (s : ℂ) / 2 * Complex.Gamma ((s : ℂ) / 2) := by
    rw [add_comm, Complex.Gamma_add_one _ hs2]
  have hcpow : ((Real.pi ^ (-s / 2) : ℝ) : ℂ) = (Real.pi : ℂ) ^ (-(s : ℂ) / 2) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  unfold liClockReciprocalCompletion
  push_cast
  rw [hcpow, show ((Real.Gamma (1 + s / 2) : ℝ) : ℂ) = Complex.Gamma (1 + (s : ℂ) / 2) by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf, hΓ]
  ring

theorem xi_half_eq_rawEvenMoment : xi (1 / 2) = (thetaCuspRawEvenMoment 0 : ℂ) := by
  have h := iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  simp only [mul_zero, iteratedDeriv_zero, pow_zero, one_mul] at h
  rw [← h]
  simp [XiC]

/-- `ζ(s) = Φ(s - 1/2) R₀/C(s)` for real `s > 1`; in particular it is real and positive. -/
theorem riemannZeta_ofReal_eq {s : ℝ} (hs : 1 < s) :
    riemannZeta s = ((Φ (s - 1 / 2) * thetaCuspRawEvenMoment 0 / 𝒞 s : ℝ) : ℂ) := by
  have hC := liClockReciprocalCompletion_pos hs
  have hΦ := liClockThetaGeneratorReal_eq_xi (s - 1 / 2)
  have hR := thetaCuspRawEvenMoment_pos 0
  rw [xi_half_eq_rawEvenMoment] at hΦ
  have hR0 : (thetaCuspRawEvenMoment 0 : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [eq_div_iff hR0, show (1 / 2 : ℂ) + ((s - 1 / 2 : ℝ) : ℂ) = (s : ℂ) by push_cast; ring,
    xi_ofReal_eq_completion_mul_riemannZeta hs] at hΦ
  have hC0 : (𝒞 s : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff hC0]
  linear_combination (-1 : ℂ) * hΦ

theorem re_riemannZeta_ofReal_pos {s : ℝ} (hs : 1 < s) : 0 < (riemannZeta (s : ℂ)).re := by
  rw [riemannZeta_ofReal_eq hs, Complex.ofReal_re]
  have := thetaCuspRawEvenMoment_pos 0
  have := liClockReciprocalCompletion_pos hs
  have : 0 < Φ (s - 1 / 2) := lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal _)
  positivity

/-- `log Φ(s - 1/2) = log C(s) + log ζ(s) - log R₀` for real `s > 1`. -/
theorem log_liClockThetaGeneratorReal_eq {s : ℝ} (hs : 1 < s) :
    Real.log (Φ (s - 1 / 2)) = Real.log (𝒞 s) + Real.log (riemannZeta (s : ℂ)).re -
      Real.log (thetaCuspRawEvenMoment 0) := by
  have hC := liClockReciprocalCompletion_pos hs
  have hR := thetaCuspRawEvenMoment_pos 0
  have hΦ : 0 < Φ (s - 1 / 2) := lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal _)
  rw [riemannZeta_ofReal_eq hs, Complex.ofReal_re, Real.log_div (by positivity) hC.ne',
    Real.log_mul hΦ.ne' hR.ne']
  ring

theorem liClockReciprocalPoleArgument_gt_one {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    1 < σ p u := by
  unfold liClockReciprocalPoleArgument
  have hq : 0 < p - u := by linarith
  rw [← sub_pos, show 1 / 2 + 1 / (p - u) - 1 = (2 - (p - u)) / (2 * (p - u)) by field_simp; ring]
  exact div_pos (by linarith) (by positivity)

/-- **(A10)** On `p - 2 < u < p` the reciprocal logarithmic germ is the completion logarithm plus
the Euler logarithm, up to their values at `u = 0`. -/
theorem liClockReciprocalLogGerm_eq_completion_add_euler {p u : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hu : p - 2 < u) (hup : u < p) :
    liClockReciprocalLogGerm p⁻¹ u = liClockReciprocalCompletionLog p u + liClockReciprocalEulerLog p u -
      (liClockReciprocalCompletionLog p 0 + liClockReciprocalEulerLog p 0) := by
  have hp0 : 0 < p := by linarith
  have hσu := liClockReciprocalPoleArgument_gt_one hu hup
  have hσ0 := liClockReciprocalPoleArgument_gt_one (by linarith) hp0
  have e1 : p⁻¹ / (1 - p⁻¹ * u) = σ p u - 1 / 2 := by
    unfold liClockReciprocalPoleArgument
    have : p - u ≠ 0 := by linarith
    field_simp
    ring
  have e0 : p⁻¹ = σ p 0 - 1 / 2 := by unfold liClockReciprocalPoleArgument; simp
  unfold liClockReciprocalLogGerm liClockThetaLogGenerator liClockReciprocalCompletionLog liClockReciprocalEulerLog
  rw [e1, log_liClockThetaGeneratorReal_eq hσu]
  conv_lhs => rw [show Real.log (Φ p⁻¹) = Real.log (Φ (σ p 0 - 1 / 2)) by rw [← e0]]
  rw [log_liClockThetaGeneratorReal_eq hσ0]
  ring

/-! ## (A11) The elementary pole factor -/

/-- **(A11)** `log((s(u)-1)/(s(0)-1)) = log(1 + u/d) - log(1 - u/p)` for `-d < u < p`. -/
theorem log_liClockReciprocalPoleArgument_sub_one {p u : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hu : p - 2 < u)
    (hup : u < p) :
    Real.log (σ p u - 1) - Real.log (σ p 0 - 1) =
      Real.log (1 + u / (2 - p)) - Real.log (1 - u / p) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < 2 - p := by linarith
  have hq : 0 < p - u := by linarith
  have hσ : ∀ v, v < p → σ p v - 1 = (2 - p + v) / (2 * (p - v)) := fun v hv => by
    unfold liClockReciprocalPoleArgument
    have : p - v ≠ 0 := by linarith
    field_simp
    ring
  have hdu : 0 < 2 - p + u := by linarith
  rw [hσ u hup, hσ 0 hp0, Real.log_div hdu.ne' (by positivity), Real.log_div (by positivity)
    (by positivity), Real.log_mul two_ne_zero hq.ne', Real.log_mul two_ne_zero (by positivity),
    show 1 + u / (2 - p) = (2 - p + u) / (2 - p) by field_simp,
    show 1 - u / p = (p - u) / p by field_simp, Real.log_div hdu.ne' hd.ne',
    Real.log_div hq.ne' hp0.ne']
  simp only [add_zero, sub_zero]
  ring

/-! ## (A14) The filled factorization and the domain of nonvanishing -/

/-- **(A14)** `ξ(s) = π^{-s/2} Γ(1+s/2) U(s)` on `Re s > 0`, `U` the filled residue unit. -/
theorem xi_eq_cpow_mul_Gamma_mul_zetaResidueUnit {s : ℂ} (hs : 0 < s.re) :
    xi s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (1 + s / 2) * zetaResidueUnit s := by
  rw [xi_eq_half_mul_Gammaℝ_mul_zetaResidueUnit hs, Complex.Gammaℝ_def]
  have hs2 : s / 2 ≠ 0 := div_ne_zero (fun h => by simp [h] at hs) two_ne_zero
  rw [add_comm (1 : ℂ), Complex.Gamma_add_one _ hs2]
  ring

/-- The complex pole argument `S(w) = 1/2 + 1/(p - w)`. -/
def liClockReciprocalPoleArgumentC (p : ℝ) (w : ℂ) : ℂ := 1 / 2 + 1 / ((p : ℂ) - w)

local notation "S" => liClockReciprocalPoleArgumentC

/-- `Re(1/(p - w)) ≥ 1/(p + ρ)` on `‖w‖ ≤ ρ < p`. -/
theorem re_one_div_sub_ge {p ρ : ℝ} (hρ : 0 ≤ ρ) (hρp : ρ < p) {w : ℂ} (hw : ‖w‖ ≤ ρ) :
    1 / (p + ρ) ≤ (1 / ((p : ℂ) - w)).re := by
  have hwre : |w.re| ≤ ρ := (Complex.abs_re_le_norm w).trans hw
  have hx : -ρ ≤ w.re := by linarith [neg_abs_le w.re]
  have hq : 0 < p - w.re := by linarith [le_abs_self w.re]
  have hnorm : Complex.normSq ((p : ℂ) - w) = (p - w.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ ρ ^ 2 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  have hpos : 0 < Complex.normSq ((p : ℂ) - w) := by rw [hnorm]; positivity
  rw [show (1 / ((p : ℂ) - w)) = ((p : ℂ) - w)⁻¹ from one_div _, Complex.inv_re]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [div_le_div_iff₀ (by linarith) hpos, one_mul, hnorm]
  nlinarith

theorem one_le_re_liClockReciprocalPoleArgumentC {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {w : ℂ}
    (hw : ‖w‖ ≤ 2 - p) : 1 ≤ (S p w).re := by
  have h := re_one_div_sub_ge (p := p) (ρ := 2 - p) (by linarith) (by linarith) hw
  unfold liClockReciprocalPoleArgumentC
  simp only [Complex.add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
  rw [show p + (2 - p) = 2 by ring] at h
  linarith

/-- **(A15 domain)** On `‖w‖ ≤ d`: `ξ(S(w)) ≠ 0` and `U(S(w)) ≠ 0`. -/
theorem xi_liClockReciprocalPoleArgumentC_ne_zero {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {w : ℂ}
    (hw : ‖w‖ ≤ 2 - p) : xi (S p w) ≠ 0 ∧ zetaResidueUnit (S p w) ≠ 0 := by
  have hre := one_le_re_liClockReciprocalPoleArgumentC hp1 hp2 hw
  have hxi := xi_ne_zero_of_one_le_re hre
  refine ⟨hxi, fun hU => hxi ?_⟩
  rw [xi_eq_cpow_mul_Gamma_mul_zetaResidueUnit (by linarith), hU, mul_zero]

/-! ## The real log-derivatives and their holomorphic extensions -/

/-- `C'/C(s(u)) s'(u)` along the real axis. -/
def liClockReciprocalCompletionLogDeriv (p u : ℝ) : ℝ :=
  1 / (p - u) ^ 2 * (1 / (σ p u - 1) - Real.log Real.pi / 2 +
    deriv Real.Gamma (1 + σ p u / 2) / (2 * Real.Gamma (1 + σ p u / 2)))

/-- `ζ'/ζ(s(u)) s'(u)` along the real axis. -/
def liClockReciprocalEulerLogDeriv (p u : ℝ) : ℝ :=
  1 / (p - u) ^ 2 * ((deriv riemannZeta (σ p u : ℂ)).re / (riemannZeta (σ p u : ℂ)).re)

/-- The holomorphic pole part `1/(w + d) + 1/(p - w)`. -/
def liClockReciprocalPoleDeriv (p : ℝ) (w : ℂ) : ℂ := 1 / (w + (2 - p)) + 1 / ((p : ℂ) - w)

/-- The holomorphic Gamma part `(p-w)^{-2} (-(log π)/2 + Γ'(W)/(2Γ(W)))`, `W = 1 + S(w)/2`. -/
def liClockReciprocalGammaDeriv (p : ℝ) (w : ℂ) : ℂ :=
  (1 / ((p : ℂ) - w)) ^ 2 * (-(Real.log Real.pi : ℂ) / 2 +
    deriv Complex.Gamma (1 + S p w / 2) / (2 * Complex.Gamma (1 + S p w / 2)))

/-- The holomorphic Euler part `(p-w)^{-2} ζ'/ζ(S(w))`. -/
def liClockReciprocalZetaDeriv (p : ℝ) (w : ℂ) : ℂ :=
  (1 / ((p : ℂ) - w)) ^ 2 * (deriv riemannZeta (S p w) / riemannZeta (S p w))

local notation "hPole" => liClockReciprocalPoleDeriv
local notation "hGamma" => liClockReciprocalGammaDeriv
local notation "hZeta" => liClockReciprocalZetaDeriv

theorem liClockReciprocalPoleArgumentC_ofReal (p u : ℝ) : S p (u : ℂ) = (σ p u : ℂ) := by
  unfold liClockReciprocalPoleArgumentC liClockReciprocalPoleArgument
  push_cast
  ring

theorem hasDerivAt_liClockReciprocalPoleArgument {p u : ℝ} (hu : u < p) :
    HasDerivAt (σ p) (1 / (p - u) ^ 2) u := by
  have hne : p - u ≠ 0 := by linarith
  have h := (((hasDerivAt_const u p).sub (hasDerivAt_id u)).inv hne).const_add (1 / 2)
  have e : σ p = fun x => 1 / 2 + (p - id x)⁻¹ := funext fun x => by
    simp only [liClockReciprocalPoleArgument, one_div, id]
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, id]
  ring

theorem hasDerivAt_liClockReciprocalPoleArgumentC (p : ℝ) {w : ℂ} (hw : (p : ℂ) - w ≠ 0) :
    HasDerivAt (S p) ((1 / ((p : ℂ) - w)) ^ 2) w := by
  have h := (((hasDerivAt_const w (p : ℂ)).sub (hasDerivAt_id w)).inv hw).const_add (1 / 2)
  have e : S p = fun x => 1 / 2 + ((p : ℂ) - id x)⁻¹ := funext fun x => by
    simp only [liClockReciprocalPoleArgumentC, one_div, id]
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, id]
  rw [div_pow, one_pow]
  ring

theorem deriv_Real_Gamma_eq_re {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re := by
  have hd := (Complex.differentiableAt_Gamma (x : ℂ) fun m hm => by
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).hasDerivAt.real_of_complex
  have e : (fun y : ℝ => (Complex.Gamma (y : ℂ)).re) = Real.Gamma := funext fun y => by
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [e] at hd
  exact hd.deriv

theorem re_one_div_sub_pos {p : ℝ} {w : ℂ} (hw : ‖w‖ < p) : 0 < (1 / ((p : ℂ) - w)).re := by
  have h := re_one_div_sub_ge (norm_nonneg w) hw le_rfl
  exact lt_of_lt_of_le (by have := (norm_nonneg w).trans_lt hw; positivity) h

private theorem re_gammaArg_pos {p : ℝ} {w : ℂ} (hw : ‖w‖ < p) : 0 < (1 + S p w / 2).re := by
  have h := re_one_div_sub_pos hw
  have e : 1 + S p w / 2 = (5 / 4 : ℂ) + (1 / ((p : ℂ) - w)) / 2 := by
    unfold liClockReciprocalPoleArgumentC; ring
  have h54 : ((5 / 4 : ℂ)).re = 5 / 4 := by norm_num
  rw [e, Complex.add_re, h54, Complex.div_ofNat_re]
  linarith

private theorem liClockReciprocal_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m :=
  fun m hm => by
    rw [hm] at hz
    simp at hz
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

private theorem differentiableOn_deriv_Gamma :
    DifferentiableOn ℂ (deriv Complex.Gamma) {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (liClockReciprocal_ne_neg_nat hz)).differentiableWithinAt
  exact hG.deriv hU

/-- `hGamma` is holomorphic on the disk `‖w‖ < p`. -/
theorem differentiableOn_liClockReciprocalGammaDeriv (p : ℝ) :
    DifferentiableOn ℂ (hGamma p) (Metric.ball 0 p) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hne : (p : ℂ) - w ≠ 0 := by
    intro h
    have := re_one_div_sub_pos hw
    rw [h] at this
    simp at this
  have hW := re_gammaArg_pos hw
  have hS := hasDerivAt_liClockReciprocalPoleArgumentC p hne
  have hWd : DifferentiableAt ℂ (fun w => 1 + S p w / 2) w :=
    (hS.differentiableAt.div_const 2).const_add 1
  have hΓ := Complex.differentiableAt_Gamma _ (liClockReciprocal_ne_neg_nat hW)
  have hΓ' : DifferentiableAt ℂ (deriv Complex.Gamma) (1 + S p w / 2) :=
    differentiableOn_deriv_Gamma.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hW)
  have hΓne := Complex.Gamma_ne_zero (liClockReciprocal_ne_neg_nat hW)
  have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / ((p : ℂ) - w)) w :=
    (differentiableAt_const _).div (by fun_prop) hne
  have hA := hΓ'.comp w hWd
  have hB := hΓ.comp w hWd
  have hq := hA.div ((differentiableAt_const (2 : ℂ)).mul hB) (mul_ne_zero two_ne_zero hΓne)
  exact ((hinv.pow 2).mul ((differentiableAt_const _).add hq)).differentiableWithinAt

/-- On `‖w‖ < d`, `Re S(w) > 1`. -/
theorem one_lt_re_liClockReciprocalPoleArgumentC {p : ℝ} (hp1 : 1 < p) {w : ℂ}
    (hw : ‖w‖ < 2 - p) : 1 < (S p w).re := by
  have h := re_one_div_sub_ge (p := p) (norm_nonneg w) (by linarith) le_rfl (w := w)
  unfold liClockReciprocalPoleArgumentC
  simp only [Complex.add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
  have : 1 / 2 < 1 / (p + ‖w‖) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
  linarith

/-- `hZeta` is holomorphic on the disk `‖w‖ < d`. -/
theorem differentiableOn_liClockReciprocalZetaDeriv {p : ℝ} (hp1 : 1 < p) :
    DifferentiableOn ℂ (hZeta p) (Metric.ball 0 (2 - p)) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hre := one_lt_re_liClockReciprocalPoleArgumentC hp1 hw
  have hne : (p : ℂ) - w ≠ 0 := by
    intro h
    have := re_one_div_sub_pos (show ‖w‖ < p by linarith)
    rw [h] at this
    simp at this
  have hS := hasDerivAt_liClockReciprocalPoleArgumentC p hne
  have hS1 : S p w ≠ 1 := fun h => by rw [h] at hre; simp at hre
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hζ : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hζ' : DifferentiableAt ℂ (deriv riemannZeta) (S p w) :=
    (hζ.deriv hU).differentiableAt (hU.mem_nhds hS1)
  have hζ0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / ((p : ℂ) - w)) w :=
    (differentiableAt_const _).div (by fun_prop) hne
  have hA := hζ'.comp w hS.differentiableAt
  have hB := (differentiableAt_riemannZeta hS1).comp w hS.differentiableAt
  exact ((hinv.pow 2).mul (hA.div hB hζ0)).differentiableWithinAt

/-- `hPole` is holomorphic on the disk `‖w‖ < d`. -/
theorem differentiableOn_liClockReciprocalPoleDeriv {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    DifferentiableOn ℂ (hPole p) (Metric.ball 0 (2 - p)) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have h1 : w + (2 - p : ℂ) ≠ 0 := by
    intro h
    have : ‖w‖ = 2 - p := by
      rw [show w = -((2 - p : ℝ) : ℂ) by push_cast; linear_combination h, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have h2 : (p : ℂ) - w ≠ 0 := by
    intro h
    have : ‖w‖ = p := by
      rw [show w = (p : ℂ) by linear_combination -h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    linarith
  have hA : DifferentiableAt ℂ (fun w : ℂ => 1 / (w + (2 - p : ℂ))) w :=
    (differentiableAt_const _).div (by fun_prop) h1
  have hB : DifferentiableAt ℂ (fun w : ℂ => 1 / ((p : ℂ) - w)) w :=
    (differentiableAt_const _).div (by fun_prop) h2
  exact (hA.add hB).differentiableWithinAt

/-! ## Real derivatives of the two logarithms -/

theorem liClockReciprocalCompletionLog_eq {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    liClockReciprocalCompletionLog p u = Real.log (σ p u - 1) - σ p u / 2 * Real.log Real.pi +
      Real.log (Real.Gamma (1 + σ p u / 2)) := by
  have hσ := liClockReciprocalPoleArgument_gt_one hu hup
  have h1 : 0 < σ p u - 1 := by linarith
  have h2 : 0 < Real.pi ^ (-σ p u / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h3 : 0 < Real.Gamma (1 + σ p u / 2) := Real.Gamma_pos_of_pos (by linarith)
  unfold liClockReciprocalCompletionLog liClockReciprocalCompletion
  rw [Real.log_mul (by positivity) h3.ne', Real.log_mul h1.ne' h2.ne',
    Real.log_rpow Real.pi_pos]
  ring

theorem hasDerivAt_liClockReciprocalCompletionLog {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    HasDerivAt (liClockReciprocalCompletionLog p) (liClockReciprocalCompletionLogDeriv p u) u := by
  have hσ := liClockReciprocalPoleArgument_gt_one hu hup
  have hs := hasDerivAt_liClockReciprocalPoleArgument hup
  have hw : 0 < 1 + σ p u / 2 := by linarith
  have hΓ := (Real.differentiableAt_Gamma (s := 1 + σ p u / 2) fun m hm => by
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).hasDerivAt
  have hΓpos := Real.Gamma_pos_of_pos hw
  have h1 := (hs.sub_const 1).log (by linarith)
  have h2 := (hs.div_const 2).mul_const (Real.log Real.pi)
  have h3 := (hΓ.comp u ((hs.div_const 2).const_add 1)).log
    (show (Real.Gamma ∘ fun x => 1 + σ p x / 2) u ≠ 0 from hΓpos.ne')
  have hF := (h1.sub h2).add h3
  have hev : liClockReciprocalCompletionLog p =ᶠ[𝓝 u] fun x => Real.log (σ p x - 1) -
      σ p x / 2 * Real.log Real.pi + Real.log (Real.Gamma (1 + σ p x / 2)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hu hup) fun x hx =>
      liClockReciprocalCompletionLog_eq hx.1 hx.2
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold liClockReciprocalCompletionLogDeriv
  simp only [Function.comp_apply]
  field_simp

theorem hasDerivAt_liClockReciprocalEulerLog {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    HasDerivAt (liClockReciprocalEulerLog p) (liClockReciprocalEulerLogDeriv p u) u := by
  have hσ := liClockReciprocalPoleArgument_gt_one hu hup
  have hne : (p : ℂ) - (u : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast (show p - u ≠ 0 by linarith)
  have hS := hasDerivAt_liClockReciprocalPoleArgumentC p hne
  have hS1 : S p (u : ℂ) ≠ 1 := by
    rw [liClockReciprocalPoleArgumentC_ofReal]
    exact_mod_cast hσ.ne'
  have hζ := (differentiableAt_riemannZeta hS1).hasDerivAt.comp (u : ℂ) hS
  have hre := hζ.real_of_complex
  have hpos := re_riemannZeta_ofReal_pos hσ
  have e : (fun x : ℝ => ((riemannZeta ∘ S p) (x : ℂ)).re) =
      fun x => (riemannZeta (σ p x : ℂ)).re := funext fun x => by
    simp only [Function.comp_apply, liClockReciprocalPoleArgumentC_ofReal]
  rw [e] at hre
  have hlog := hre.log hpos.ne'
  unfold liClockReciprocalEulerLog
  refine hlog.congr_deriv ?_
  unfold liClockReciprocalEulerLogDeriv
  rw [liClockReciprocalPoleArgumentC_ofReal]
  have e2 : (1 / ((p : ℂ) - (u : ℂ))) ^ 2 = ((1 / (p - u) ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [div_pow, one_pow]
  rw [e2, mul_comm, Complex.re_ofReal_mul]
  ring

/-! ## Real parts of the holomorphic extensions -/

theorem liClockReciprocalCompletionLogDeriv_eq_re {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    liClockReciprocalCompletionLogDeriv p u = (hPole p u + hGamma p u).re := by
  have hσ := liClockReciprocalPoleArgument_gt_one hu hup
  have hw : 0 < 1 + σ p u / 2 := by linarith
  have hq : p - u ≠ 0 := by linarith
  have hd : u + (2 - p) ≠ 0 := by linarith
  have hd' : 2 - p + u ≠ 0 := by linarith
  have hpole : (hPole p u).re = 1 / (p - u) ^ 2 * (1 / (σ p u - 1)) := by
    unfold liClockReciprocalPoleDeriv
    rw [show (1 / ((u : ℂ) + (2 - p)) + 1 / ((p : ℂ) - u)) =
      ((1 / (u + (2 - p)) + 1 / (p - u) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    have hσ1 : σ p u - 1 = (2 - p + u) / (2 * (p - u)) := by
      unfold liClockReciprocalPoleArgument; field_simp; ring
    rw [hσ1]
    field_simp
    ring
  have hG : Complex.Gamma (1 + S p u / 2) = (Real.Gamma (1 + σ p u / 2) : ℂ) := by
    rw [liClockReciprocalPoleArgumentC_ofReal, ← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG' : (deriv Complex.Gamma (1 + S p u / 2)).re = deriv Real.Gamma (1 + σ p u / 2) := by
    rw [deriv_Real_Gamma_eq_re hw, liClockReciprocalPoleArgumentC_ofReal]; push_cast; ring_nf
  have hgam : (hGamma p u).re = 1 / (p - u) ^ 2 * (-Real.log Real.pi / 2 +
      deriv Real.Gamma (1 + σ p u / 2) / (2 * Real.Gamma (1 + σ p u / 2))) := by
    unfold liClockReciprocalGammaDeriv
    rw [hG, show (1 / ((p : ℂ) - u)) ^ 2 = ((1 / (p - u) ^ 2 : ℝ) : ℂ) by
      push_cast; rw [div_pow, one_pow],
      Complex.re_ofReal_mul, Complex.add_re,
      show (2 : ℂ) * (Real.Gamma (1 + σ p u / 2) : ℂ) = ((2 * Real.Gamma (1 + σ p u / 2) : ℝ) : ℂ)
        by push_cast; ring, Complex.div_ofReal_re, hG']
    simp
  rw [Complex.add_re, hpole, hgam]
  unfold liClockReciprocalCompletionLogDeriv
  ring

theorem liClockReciprocalEulerLogDeriv_eq_re {p u : ℝ} (hu : p - 2 < u) (hup : u < p) :
    liClockReciprocalEulerLogDeriv p u = (hZeta p u).re := by
  have hσ := liClockReciprocalPoleArgument_gt_one hu hup
  unfold liClockReciprocalZetaDeriv liClockReciprocalEulerLogDeriv
  rw [liClockReciprocalPoleArgumentC_ofReal, show (1 / ((p : ℂ) - u)) ^ 2 =
    ((1 / (p - u) ^ 2 : ℝ) : ℂ) by push_cast; rw [div_pow, one_pow], Complex.re_ofReal_mul]
  congr 1
  rw [riemannZeta_ofReal_eq hσ, Complex.div_ofReal_re, Complex.ofReal_re]

/-! ## (A10) The coefficient split `b_n = α_n + ζ_n` -/

private theorem ball_props {p : ℝ} (hp1 : 1 < p) {y : ℝ}
    (hy : y ∈ Ioo (p - 2) (2 - p)) : (y : ℂ) ∈ Metric.ball (0 : ℂ) (2 - p) ∧ p - 2 < y ∧ y < p := by
  refine ⟨?_, hy.1, by linarith [hy.2]⟩
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith [hy.1], hy.2⟩

private theorem differentiableOn_completionDeriv {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    DifferentiableOn ℂ (fun w => hPole p w + hGamma p w) (Metric.ball 0 (2 - p)) :=
  (differentiableOn_liClockReciprocalPoleDeriv hp1 hp2).add
    ((differentiableOn_liClockReciprocalGammaDeriv p).mono (Metric.ball_subset_ball (by linarith)))

private theorem contDiffAt_zero_of_ball {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) (m : ℕ) : ContDiffAt ℂ m h 0 :=
  (hh.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.ball_mem_nhds 0 hR)

theorem iteratedDeriv_succ_liClockReciprocalCompletionLog {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (m : ℕ) : iteratedDeriv (m + 1) (liClockReciprocalCompletionLog p) 0 =
      (iteratedDeriv m (fun w => hPole p w + hGamma p w) 0).re := by
  have hev : deriv (liClockReciprocalCompletionLog p) =ᶠ[𝓝 0]
      liClockReciprocalCompletionLogDeriv p :=
    Filter.eventually_of_mem (Ioo_mem_nhds (show p - 2 < 0 by linarith)
      (show (0 : ℝ) < 2 - p by linarith)) fun y hy =>
      (hasDerivAt_liClockReciprocalCompletionLog (ball_props hp1 hy).2.1
        (ball_props hp1 hy).2.2).deriv
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have h := iteratedDeriv_eq_re_of_differentiableOn (f := liClockReciprocalCompletionLogDeriv p)
    Metric.isOpen_ball (differentiableOn_completionDeriv hp1 hp2) isOpen_Ioo
    (fun y hy => (ball_props hp1 hy).1)
    (fun y hy => liClockReciprocalCompletionLogDeriv_eq_re (ball_props hp1 hy).2.1
        (ball_props hp1 hy).2.2)
    m (x := 0) ⟨by linarith, by linarith⟩
  rw [h, Complex.ofReal_zero]

theorem iteratedDeriv_succ_liClockReciprocalEulerLog {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (m : ℕ) : iteratedDeriv (m + 1) (liClockReciprocalEulerLog p) 0 =
      (iteratedDeriv m (hZeta p) 0).re := by
  have hev : deriv (liClockReciprocalEulerLog p) =ᶠ[𝓝 0] liClockReciprocalEulerLogDeriv p :=
    Filter.eventually_of_mem (Ioo_mem_nhds (show p - 2 < 0 by linarith)
      (show (0 : ℝ) < 2 - p by linarith)) fun y hy =>
      (hasDerivAt_liClockReciprocalEulerLog (ball_props hp1 hy).2.1
        (ball_props hp1 hy).2.2).deriv
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have h := iteratedDeriv_eq_re_of_differentiableOn (f := liClockReciprocalEulerLogDeriv p)
    Metric.isOpen_ball (differentiableOn_liClockReciprocalZetaDeriv hp1) isOpen_Ioo
    (fun y hy => (ball_props hp1 hy).1)
    (fun y hy => liClockReciprocalEulerLogDeriv_eq_re (ball_props hp1 hy).2.1
        (ball_props hp1 hy).2.2)
    m (x := 0) ⟨by linarith, by linarith⟩
  rw [h, Complex.ofReal_zero]

theorem iteratedDeriv_succ_liClockReciprocalLogGerm {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (m : ℕ) : iteratedDeriv (m + 1) (liClockReciprocalLogGerm p⁻¹) 0 =
      (iteratedDeriv m (fun w => hPole p w + hGamma p w) 0).re +
        (iteratedDeriv m (hZeta p) 0).re := by
  have hd0 : (0 : ℝ) < 2 - p := by linarith
  have hderiv : ∀ y ∈ Ioo (p - 2) (2 - p), deriv (liClockReciprocalLogGerm p⁻¹) y =
      liClockReciprocalCompletionLogDeriv p y + liClockReciprocalEulerLogDeriv p y := by
    intro y hy
    have hev : liClockReciprocalLogGerm p⁻¹ =ᶠ[𝓝 y] fun x => liClockReciprocalCompletionLog p x +
        liClockReciprocalEulerLog p x -
          (liClockReciprocalCompletionLog p 0 + liClockReciprocalEulerLog p 0) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun x hx =>
        liClockReciprocalLogGerm_eq_completion_add_euler hp1 hp2 (ball_props hp1 hx).2.1
          (ball_props hp1 hx).2.2
    rw [hev.deriv_eq]
    exact (((hasDerivAt_liClockReciprocalCompletionLog (ball_props hp1 hy).2.1
      (ball_props hp1 hy).2.2).add (hasDerivAt_liClockReciprocalEulerLog
        (ball_props hp1 hy).2.1 (ball_props hp1 hy).2.2)).sub_const _).deriv
  have hev : deriv (liClockReciprocalLogGerm p⁻¹) =ᶠ[𝓝 0]
      fun y => liClockReciprocalCompletionLogDeriv p y + liClockReciprocalEulerLogDeriv p y :=
    Filter.eventually_of_mem (Ioo_mem_nhds (show p - 2 < 0 by linarith) hd0) hderiv
  have hdiff : DifferentiableOn ℂ (fun w => (hPole p w + hGamma p w) + hZeta p w)
      (Metric.ball 0 (2 - p)) :=
    (differentiableOn_completionDeriv hp1 hp2).add (differentiableOn_liClockReciprocalZetaDeriv hp1)
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have h := iteratedDeriv_eq_re_of_differentiableOn
    (f := fun y => liClockReciprocalCompletionLogDeriv p y + liClockReciprocalEulerLogDeriv p y)
    Metric.isOpen_ball hdiff isOpen_Ioo
    (fun y hy => (ball_props hp1 hy).1)
    (fun y hy => by
      rw [Complex.add_re, liClockReciprocalCompletionLogDeriv_eq_re (ball_props hp1 hy).2.1
        (ball_props hp1 hy).2.2, liClockReciprocalEulerLogDeriv_eq_re
          (ball_props hp1 hy).2.1 (ball_props hp1 hy).2.2])
    m (x := 0) ⟨by linarith, by linarith⟩
  rw [h, Complex.ofReal_zero, iteratedDeriv_fun_add
    (contDiffAt_zero_of_ball hd0 (differentiableOn_completionDeriv hp1 hp2) m)
    (contDiffAt_zero_of_ball hd0 (differentiableOn_liClockReciprocalZetaDeriv hp1) m),
    Complex.add_re]

/-- **(A10)** `b_n = α_n + ζ_n` for every `n ≥ 1`. -/
theorem liClockReciprocalLogCoeff_eq_completion_add_euler {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    {n : ℕ} (hn : 1 ≤ n) :
    b p⁻¹ n = liClockReciprocalCompletionCoeff p n + liClockReciprocalEulerCoeff p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold liClockReciprocalLogCoeff liClockReciprocalCompletionCoeff liClockReciprocalEulerCoeff
  rw [iteratedDeriv_succ_liClockReciprocalLogGerm hp1 hp2,
    iteratedDeriv_succ_liClockReciprocalCompletionLog hp1 hp2,
    iteratedDeriv_succ_liClockReciprocalEulerLog hp1 hp2, add_div]

/-! ## (A12) The completion coefficients -/

theorem iteratedDeriv_liClockReciprocalPoleDeriv_zero {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (m : ℕ) : iteratedDeriv m (hPole p) 0 =
      ((-1) ^ m * m.factorial / (2 - p) ^ (m + 1) + m.factorial / p ^ (m + 1) : ℝ) := by
  have hd : (2 - p : ℂ) ≠ 0 := by exact_mod_cast (show (2 - p : ℝ) ≠ 0 by linarith)
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have e : hPole p = fun w => (1 * w + (2 - p : ℂ))⁻¹ + ((-1) * w + (p : ℂ))⁻¹ := by
    funext w; unfold liClockReciprocalPoleDeriv; simp only [one_div]; ring_nf
  have h1 : ContDiffAt ℂ m (fun w : ℂ => (1 * w + (2 - p : ℂ))⁻¹) 0 :=
    (contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const).inv (by simpa using hd)
  have h2 : ContDiffAt ℂ m (fun w : ℂ => ((-1) * w + (p : ℂ))⁻¹) 0 :=
    (contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const).inv (by simpa using hpc)
  rw [e, iteratedDeriv_fun_add h1 h2, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iter_deriv_inv_linear, iter_deriv_inv_linear]
  simp only [mul_zero, zero_add, one_pow, mul_one]
  rw [show (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg,
    zpow_natCast, zpow_natCast]
  push_cast
  have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  simp only [div_eq_mul_inv]
  linear_combination ((m.factorial : ℂ) * ((p : ℂ) ^ (m + 1))⁻¹) * hsq

/-- The Gamma coefficients `γ_n = Re (hGamma)^{(n-1)}(0)/n!`. -/
def liClockReciprocalGammaCoeff (p : ℝ) (n : ℕ) : ℝ :=
  (iteratedDeriv (n - 1) (hGamma p) 0).re / n.factorial

/-- **(A12)** `α_n = (-1)^{n+1}/(n d^n) + 1/(n p^n) + γ_n` for `n ≥ 1`. -/
theorem liClockReciprocalCompletionCoeff_eq {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {n : ℕ}
    (hn : 1 ≤ n) : liClockReciprocalCompletionCoeff p n =
      (-1) ^ (n + 1) / (n * (2 - p) ^ n) + 1 / (n * p ^ n) + liClockReciprocalGammaCoeff p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd0 : (0 : ℝ) < 2 - p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  unfold liClockReciprocalCompletionCoeff liClockReciprocalGammaCoeff
  rw [iteratedDeriv_succ_liClockReciprocalCompletionLog hp1 hp2, iteratedDeriv_fun_add
    (contDiffAt_zero_of_ball hd0 (differentiableOn_liClockReciprocalPoleDeriv hp1 hp2) m)
    (contDiffAt_zero_of_ball hd0 ((differentiableOn_liClockReciprocalGammaDeriv p).mono
      (Metric.ball_subset_ball (by linarith))) m),
    Complex.add_re, iteratedDeriv_liClockReciprocalPoleDeriv_zero hp1 hp2, Complex.ofReal_re,
    show m + 1 - 1 = m by omega, Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp
  ring

/-- The Gamma coefficients are `O(1/n)`: `|γ_n| ≤ C/n`. -/
theorem exists_abs_liClockReciprocalGammaCoeff_le {p : ℝ} (hp1 : 1 < p) :
    ∃ C, 0 ≤ C ∧ ∀ n, 1 ≤ n → |liClockReciprocalGammaCoeff p n| ≤ C / n := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedDeriv_le_of_differentiableOn_ball
    (differentiableOn_liClockReciprocalGammaDeriv p) one_pos hp1
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold liClockReciprocalGammaCoeff
  rw [show m + 1 - 1 = m by omega, abs_div, Nat.abs_cast, Nat.factorial_succ]
  have hb := (Complex.abs_re_le_norm _).trans (hbound m)
  rw [one_pow, div_one] at hb
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **(A12)** `n d^n α_n - (-1)^{n+1} → 0`. -/
theorem tendsto_liClockReciprocalCompletionCoeff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Tendsto (fun n : ℕ => n * (2 - p) ^ n * liClockReciprocalCompletionCoeff p n -
      (-1) ^ (n + 1)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_liClockReciprocalGammaCoeff_le hp1
  have hd0 : (0 : ℝ) < 2 - p := by linarith
  have hd1 : 2 - p < 1 := by linarith
  have hratio : Tendsto (fun n : ℕ => ((2 - p) / p) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 (by linarith))
  have hgam : Tendsto (fun n : ℕ => n * (2 - p) ^ n * liClockReciprocalGammaCoeff p n) atTop
      (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => C * (2 - p) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hd0.le hd1).const_mul C
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hb := hbound n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast, abs_of_pos (pow_pos hd0 n)]
    calc (n : ℝ) * (2 - p) ^ n * |liClockReciprocalGammaCoeff p n| ≤
        n * (2 - p) ^ n * (C / n) := by gcongr
      _ = C * (2 - p) ^ n := by field_simp
  have h := hratio.add hgam
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [liClockReciprocalCompletionCoeff_eq hp1 hp2 hn]
  have hd : (2 - p) ^ n ≠ 0 := pow_ne_zero _ hd0.ne'
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  rw [div_pow]
  field_simp
  ring

/-! ## (A15) Exact cancellation of the two pole terms -/

private theorem exists_le_of_gt_of_tendsto_cofinite {ι : Type*} {f : ι → ℝ} {d L : ℝ}
    (hf : ∀ i, d < f i) (hdL : d < L) (hlim : Tendsto f cofinite (𝓝 L)) :
    ∃ m, d < m ∧ ∀ i, m ≤ f i := by
  classical
  have hfin : {i | f i ≤ (d + L) / 2}.Finite := by
    have h := hlim.eventually (lt_mem_nhds (show (d + L) / 2 < L by linarith))
    rw [Filter.eventually_cofinite] at h
    simpa [not_lt] using h
  obtain ⟨m0, hm0d, hm0⟩ : ∃ m0, d < m0 ∧ ∀ i ∈ hfin.toFinset, m0 ≤ f i := by
    by_cases hne : hfin.toFinset.Nonempty
    · obtain ⟨i0, -, hmin⟩ := hfin.toFinset.exists_min_image f hne
      exact ⟨f i0, hf i0, fun i hi => hmin i hi⟩
    · exact ⟨(d + L) / 2, by linarith, fun i hi => (hne ⟨i, hi⟩).elim⟩
  refine ⟨min m0 ((d + L) / 2), lt_min hm0d (by linarith), fun i => ?_⟩
  by_cases hi : f i ≤ (d + L) / 2
  · exact (min_le_left _ _).trans (hm0 i (hfin.mem_toFinset.2 hi))
  · exact (min_le_right _ _).trans (le_of_lt (not_le.1 hi))

private theorem liClockReciprocalPoleArgumentC_spectral (p : ℝ) (q : XiZeroCopy) :
    S p ((p : ℂ) + I * (xiSpectralPoint q)⁻¹) = 1 / 2 + xiSpectralPoint q * I ∧
      S p ((p : ℂ) - I * (xiSpectralPoint q)⁻¹) = 1 - (1 / 2 + xiSpectralPoint q * I) := by
  have hα := xiSpectralPoint_ne_zero q
  unfold liClockReciprocalPoleArgumentC
  constructor
  · rw [show (p : ℂ) - ((p : ℂ) + I * (xiSpectralPoint q)⁻¹) = -(I * (xiSpectralPoint q)⁻¹) by ring]
    field_simp
    linear_combination (-2 * xiSpectralPoint q) * I_sq
  · rw [show (p : ℂ) - ((p : ℂ) - I * (xiSpectralPoint q)⁻¹) = I * (xiSpectralPoint q)⁻¹ by ring]
    field_simp
    linear_combination (2 * xiSpectralPoint q) * I_sq

private theorem xi_spectral_eq_zero (q : XiZeroCopy) : xi (1 / 2 + xiSpectralPoint q * I) = 0 := by
  have h := (XiC_eq_zero_iff_exists_xiZeroCopy (xiSpectralPoint q)).2 ⟨q, rfl⟩
  simpa [XiC] using h

/-- **(A15 domain)** The shifts `p ± i w_q` stay a uniform distance `m > d` from the origin. -/
theorem exists_liClockReciprocal_gap {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ m, 2 - p < m ∧ m ≤ p ∧ ∀ q, m ≤ ‖(p : ℂ) - I * (xiSpectralPoint q)⁻¹‖ ∧
      m ≤ ‖(p : ℂ) + I * (xiSpectralPoint q)⁻¹‖ := by
  set f := fun q : XiZeroCopy =>
    min ‖(p : ℂ) - I * (xiSpectralPoint q)⁻¹‖ ‖(p : ℂ) + I * (xiSpectralPoint q)⁻¹‖
  have hf : ∀ q, 2 - p < f q := by
    intro q
    obtain ⟨hplus, hminus⟩ := liClockReciprocalPoleArgumentC_spectral p q
    refine lt_min (not_le.1 fun h => ?_) (not_le.1 fun h => ?_)
    · have := (xi_liClockReciprocalPoleArgumentC_ne_zero hp1 hp2 h).1
      rw [hminus, xi_one_sub] at this
      exact this (xi_spectral_eq_zero q)
    · have := (xi_liClockReciprocalPoleArgumentC_ne_zero hp1 hp2 h).1
      rw [hplus] at this
      exact this (xi_spectral_eq_zero q)
  have hlim : Tendsto f cofinite (𝓝 p) := by
    have h := tendsto_inv_xiSpectralPoint_cofinite
    have h1 := ((tendsto_const_nhds (x := (p : ℂ))).sub
      ((tendsto_const_nhds (x := I)).mul h)).norm
    have h2 := ((tendsto_const_nhds (x := (p : ℂ))).add
      ((tendsto_const_nhds (x := I)).mul h)).norm
    simpa [abs_of_pos (show (0 : ℝ) < p by linarith)] using h1.min h2
  obtain ⟨m, hm, hle⟩ := exists_le_of_gt_of_tendsto_cofinite hf (by linarith) hlim
  exact ⟨min m p, lt_min hm (by linarith), min_le_right _ _, fun q =>
    ⟨(min_le_left _ _).trans ((hle q).trans (min_le_left _ _)),
      (min_le_left _ _).trans ((hle q).trans (min_le_right _ _))⟩⟩

/-- **(A15 domain)** `ξ(S(w)) ≠ 0` and `U(S(w)) ≠ 0` on a disk of radius `r > d`. -/
theorem exists_liClockReciprocal_nonvanishing_radius {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ r, 2 - p < r ∧ ∀ w : ℂ, ‖w‖ < r → xi (S p w) ≠ 0 ∧ zetaResidueUnit (S p w) ≠ 0 := by
  obtain ⟨m, hm, hmp, hgap⟩ := exists_liClockReciprocal_gap hp1 hp2
  refine ⟨m, hm, fun w hw => ?_⟩
  have hxi : xi (S p w) ≠ 0 := by
    intro h0
    have hpw : (p : ℂ) - w ≠ 0 := by
      intro h
      have : w = (p : ℂ) := by linear_combination -h
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hw
      linarith
    have hX : XiC ((1 / ((p : ℂ) - w)) * (-I)) = 0 := by
      unfold XiC
      rw [show 1 / 2 + 1 / ((p : ℂ) - w) * -I * I = S p w by
        unfold liClockReciprocalPoleArgumentC; rw [mul_assoc, show -I * I = 1 by rw [neg_mul,
          I_mul_I, neg_neg]]; ring]
      exact h0
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).1 hX
    have hα := xiSpectralPoint_ne_zero q
    have hw' : w = (p : ℂ) + I * (xiSpectralPoint q)⁻¹ := by
      rw [hq]
      field_simp
      ring
    have := (hgap q).2
    rw [← hw'] at this
    linarith
  refine ⟨hxi, fun hU => hxi ?_⟩
  have hre : 0 < (S p w).re := by
    have := re_one_div_sub_pos (show ‖w‖ < p by linarith)
    unfold liClockReciprocalPoleArgumentC
    simp only [Complex.add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    linarith
  rw [xi_eq_cpow_mul_Gamma_mul_zetaResidueUnit hre, hU, mul_zero]

/-- `b_n = T_n(p)/n`, `T_n` the single-damping coefficient. -/
theorem liClockReciprocalLogCoeff_eq_stripCoefficient_div {p : ℝ} (hp : 0 < p) {n : ℕ}
    (hn : 1 ≤ n) : b p⁻¹ n = liClockStripCoefficient n p / n := by
  rw [liClockReciprocalLogCoeff_eq (inv_pos.2 hp) hn, inv_inv]
  unfold liClockStripCoefficient
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, Nat.factorial_succ]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  push_cast
  field_simp

/-- **(A15)** `n d^n b_n → 0`: the completed logarithm has no singularity on `|u| ≤ d`. -/
theorem tendsto_liClockReciprocalLogCoeff_mul {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Tendsto (fun n : ℕ => n * (2 - p) ^ n * b p⁻¹ n) atTop (𝓝 0) := by
  obtain ⟨m, hm, hmp, hgap⟩ := exists_liClockReciprocal_gap hp1 hp2
  have hp0 : 0 < p := by linarith
  have hm0 : 0 < m := by linarith
  set A := ∑' q, ‖(xiSpectralPoint q)⁻¹‖ ^ 2
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  have hsumA := summable_norm_inv_xiSpectralPoint_sq
  have hT : ∀ n, 1 ≤ n → |liClockStripCoefficient n p| ≤ n ^ 2 * A / m ^ (n + 2) := by
    intro n hn
    have hs := hasSum_liClockStripCoefficient hp0 hn
    have hpm : m ≤ ‖(p : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]; exact hmp
    have hb : ∀ q, |(liClockStripAtom n p (xiSpectralPoint q)⁻¹).re / 2| ≤
        n ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / m ^ (n + 2) := fun q => by
      have h := norm_liClockStripAtom_le n hm0 hpm (hgap q).1 (hgap q).2
      rw [abs_div, abs_two]
      calc |(liClockStripAtom n p (xiSpectralPoint q)⁻¹).re| / 2 ≤
          ‖liClockStripAtom n p (xiSpectralPoint q)⁻¹‖ / 2 := by
            gcongr; exact Complex.abs_re_le_norm _
        _ ≤ 2 * n ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / m ^ (n + 2) / 2 := by gcongr
        _ = _ := by ring
    have hg : HasSum (fun q => n ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / m ^ (n + 2))
        (n ^ 2 * A / m ^ (n + 2)) := by
      have := (hsumA.hasSum.mul_left ((n : ℝ) ^ 2)).div_const (m ^ (n + 2))
      simpa only [mul_div_assoc] using this
    rw [abs_le]
    exact ⟨by simpa using hasSum_le (fun q => neg_le_of_abs_le (hb q)) hg.neg hs,
      hasSum_le (fun q => le_of_abs_le (hb q)) hs hg⟩
  have hr : |(2 - p) / m| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hm0]; exact hm
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr).const_mul (A / m ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [liClockReciprocalLogCoeff_eq_stripCoefficient_div hp0 hn, Real.norm_eq_abs, abs_mul,
    abs_mul, Nat.abs_cast, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < 2 - p) n), abs_div,
    Nat.abs_cast]
  calc (n : ℝ) * (2 - p) ^ n * (|liClockStripCoefficient n p| / n) =
      (2 - p) ^ n * |liClockStripCoefficient n p| := by field_simp
    _ ≤ (2 - p) ^ n * (n ^ 2 * A / m ^ (n + 2)) := by gcongr; exact hT n hn
    _ = A / m ^ 2 * ((n : ℝ) ^ 2 * ((2 - p) / m) ^ n) := by
      rw [div_pow, pow_add]; field_simp

/-- **(A15)** `n d^n ζ_n - (-1)^n → 0`: the Euler pole term exactly cancels the completion pole. -/
theorem tendsto_liClockReciprocalEulerCoeff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Tendsto (fun n : ℕ => n * (2 - p) ^ n * liClockReciprocalEulerCoeff p n - (-1) ^ n) atTop
      (𝓝 0) := by
  have h := (tendsto_liClockReciprocalLogCoeff_mul hp1 hp2).sub
    (tendsto_liClockReciprocalCompletionCoeff hp1 hp2)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [liClockReciprocalLogCoeff_eq_completion_add_euler hp1 hp2 hn, pow_succ]
  ring

/-- **(A12)** Eventually `(-1)^{n+1} α_n > 0`: the completion component alternates. -/
theorem eventually_liClockReciprocalCompletionCoeff_sign {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∀ᶠ n : ℕ in atTop, 0 < (-1) ^ (n + 1) * liClockReciprocalCompletionCoeff p n := by
  have h := tendsto_liClockReciprocalCompletionCoeff hp1 hp2
  filter_upwards [(tendsto_order.1 (tendsto_norm_zero.comp h)).2 1 one_pos,
    eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  have hsq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hd : 0 < (n : ℝ) * (2 - p) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    have : (0 : ℝ) < 2 - p := by linarith
    positivity
  have key : (-1) ^ (n + 1) * (n * (2 - p) ^ n * liClockReciprocalCompletionCoeff p n -
      (-1) ^ (n + 1)) = n * (2 - p) ^ n * ((-1) ^ (n + 1) * liClockReciprocalCompletionCoeff p n) - 1 := by
    linear_combination (-1 : ℝ) * hsq
  have habs : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp
  have : |n * (2 - p) ^ n * ((-1) ^ (n + 1) * liClockReciprocalCompletionCoeff p n) - 1| < 1 := by
    rw [← key, abs_mul, habs, one_mul]; exact hn
  have := (abs_lt.1 this).1
  have : 0 < n * (2 - p) ^ n * ((-1) ^ (n + 1) * liClockReciprocalCompletionCoeff p n) := by linarith
  exact pos_of_mul_pos_right this hd.le

/-- **(A15)** Eventually `(-1)^n ζ_n > 0`: the Euler component alternates oppositely. -/
theorem eventually_liClockReciprocalEulerCoeff_sign {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∀ᶠ n : ℕ in atTop, 0 < (-1) ^ n * liClockReciprocalEulerCoeff p n := by
  have h := tendsto_liClockReciprocalEulerCoeff hp1 hp2
  filter_upwards [(tendsto_order.1 (tendsto_norm_zero.comp h)).2 1 one_pos,
    eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hd : 0 < (n : ℝ) * (2 - p) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    have : (0 : ℝ) < 2 - p := by linarith
    positivity
  have key : (-1) ^ n * (n * (2 - p) ^ n * liClockReciprocalEulerCoeff p n - (-1) ^ n) =
      n * (2 - p) ^ n * ((-1) ^ n * liClockReciprocalEulerCoeff p n) - 1 := by
    linear_combination (-1 : ℝ) * hsq
  have habs : |(-1 : ℝ) ^ n| = 1 := by simp
  have : |n * (2 - p) ^ n * ((-1) ^ n * liClockReciprocalEulerCoeff p n) - 1| < 1 := by
    rw [← key, abs_mul, habs, one_mul]; exact hn
  have := (abs_lt.1 this).1
  have : 0 < n * (2 - p) ^ n * ((-1) ^ n * liClockReciprocalEulerCoeff p n) := by linarith
  exact pos_of_mul_pos_right this hd.le

end RHTower
