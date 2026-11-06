import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinWavePacket

/-!
# The field is smooth across the future horizon

In the ingoing coordinate `v = t + x_*`, the hyperboloidal time is `τ = v - log(2r/(r+1))`, which makes
sense for every `r > 0`. The packet is smooth in `τ`, because its `k`-th time derivative is the packet with
symbol `E (iξ)^k`. So the Neumann and Dirichlet fields, written in `(v, r)`, extend smoothly through the
horizon `r = 1`. For the Dirichlet field, `tanh x_* = -1/r`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Smoothness of the packet in time -/

/-- The packet with symbol `E (iξ)^k`. -/
def wavePacketPower (ε ξ₀ x Y : ℝ) (k : ℕ) (τ : ℝ) : ℂ :=
  packet ε ξ₀ (fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y * (I * (ξ : ℂ)) ^ k) τ

theorem hasDerivAt_wavePacketPower {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y) (k : ℕ)
    (τ : ℝ) :
    HasDerivAt (wavePacketPower ε ξ₀ x Y k) (wavePacketPower ε ξ₀ x Y (k + 1) τ) τ := by
  have h := hasDerivAt_packet_time hε ξ₀ (packetSymbol_eisenstein_mul hε x hY k) τ
  refine h.congr_deriv ?_
  simp only [wavePacketPower]
  congr 1
  funext ξ
  ring

theorem wavePacketPower_zero (ε ξ₀ x Y : ℝ) :
    wavePacketPower ε ξ₀ x Y 0 = fun τ => wavePacket ε ξ₀ τ x Y := by
  funext τ
  simp only [wavePacketPower, wavePacket, pow_zero, mul_one]

theorem iteratedDeriv_wavePacket {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y) (k : ℕ) :
    iteratedDeriv k (fun τ => wavePacket ε ξ₀ τ x Y) = wavePacketPower ε ξ₀ x Y k := by
  induction k with
  | zero => rw [iteratedDeriv_zero, wavePacketPower_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    exact (hasDerivAt_wavePacketPower hε ξ₀ x hY k τ).deriv

/-- **The packet is smooth in time.** -/
theorem contDiff_wavePacket_time {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ContDiff ℝ ∞ (fun τ => wavePacket ε ξ₀ τ x Y) := by
  refine contDiff_of_differentiable_iteratedDeriv fun k _ => ?_
  rw [iteratedDeriv_wavePacket hε ξ₀ x hY]
  exact fun τ => (hasDerivAt_wavePacketPower hε ξ₀ x hY k τ).differentiableAt

/-! ### The ingoing chart -/

/-- The hyperboloidal time in the ingoing chart. -/
def ingoingTime (v r : ℝ) : ℝ := v - Real.log (2 * r / (r + 1))

theorem hyperboloidalTime_eq_ingoingTime (t : ℝ) {r : ℝ} (hr : 1 < r) :
    hyperboloidalTime t (tortoise r) = ingoingTime (t + tortoise r) r :=
  hyperboloidalTime_tortoise t hr

/-- `tanh x_* = -1/r` on the exterior. -/
theorem tanh_tortoise {r : ℝ} (hr : 1 < r) : Real.tanh (tortoise r) = -1 / r := by
  have hpos : 0 < r := by linarith
  have hexp := exp_two_mul_tortoise hr
  have hsq : Real.exp (tortoise r) * Real.exp (tortoise r) = (r - 1) / (r + 1) := by
    rw [← Real.exp_add, ← hexp]
    congr 1
    ring
  have hE := Real.exp_pos (tortoise r)
  have hne : r + 1 ≠ 0 := by linarith
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  field_simp
  field_simp at hsq
  nlinarith

/-- The Neumann field in the ingoing chart. -/
def neumannIngoing (ε ξ₀ v r x y : ℝ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * (ingoingTime v r : ℂ)) * wavePacket ε ξ₀ (ingoingTime v r) x y / (r : ℂ)

/-- The Dirichlet field in the ingoing chart. -/
def dirichletIngoing (ε ξ₀ v r x y : ℝ) : ℂ :=
  -(Complex.exp (-(3 / 2 : ℂ) * (ingoingTime v r : ℂ)) * wavePacket ε ξ₀ (ingoingTime v r) x y) /
    (r : ℂ) ^ 2

theorem conformalScalar_neumannProfile_eq_ingoing (ε ξ₀ t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    conformalScalar (neumannProfile ε ξ₀) t r x y = neumannIngoing ε ξ₀ (t + tortoise r) r x y := by
  simp only [conformalScalar, neumannProfile, neumannLift, dampedProfile, neumannIngoing,
    hyperboloidalTime_eq_ingoingTime t hr]

theorem conformalScalar_dirichletProfile_eq_ingoing (ε ξ₀ t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    conformalScalar (dirichletProfile ε ξ₀) t r x y =
      dirichletIngoing ε ξ₀ (t + tortoise r) r x y := by
  have hrC : (r : ℂ) ≠ 0 := by
    have : r ≠ 0 := by linarith
    exact_mod_cast this
  simp only [conformalScalar, dirichletProfile, dirichletLift, dampedProfile, dirichletIngoing,
    hyperboloidalTime_eq_ingoingTime t hr, tanh_tortoise hr]
  push_cast
  field_simp

theorem contDiffAt_ingoingTime {v r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ingoingTime p.1 p.2) (v, r) := by
  have hden : (r + 1) ≠ 0 := by linarith
  have hq : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => 2 * p.2 / (p.2 + 1)) (v, r) :=
    ContDiffAt.div (contDiffAt_const.mul contDiffAt_snd) (contDiffAt_snd.add contDiffAt_const) hden
  have hpos : 2 * r / (r + 1) ≠ 0 := by positivity
  exact contDiffAt_fst.sub (hq.log hpos)

/-- **The Neumann field is smooth across the future horizon**: in `(v, r)` it is smooth at every `r > 0`,
in particular at `r = 1`. -/
theorem contDiffAt_neumannIngoing {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {y : ℝ} (hy : 0 < y) {v r : ℝ}
    (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => neumannIngoing ε ξ₀ p.1 p.2 x y) (v, r) := by
  have hτ := contDiffAt_ingoingTime (v := v) hr
  have hτC : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((ingoingTime p.1 p.2 : ℝ) : ℂ)) (v, r) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (v, r) hτ
  have hE : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      Complex.exp (-(1 / 2 : ℂ) * ((ingoingTime p.1 p.2 : ℝ) : ℂ))) (v, r) :=
    (contDiffAt_const.mul hτC).cexp
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => wavePacket ε ξ₀ (ingoingTime p.1 p.2) x y) (v, r) :=
    (contDiff_wavePacket_time hε ξ₀ x hy).contDiffAt.comp (v, r) hτ
  have hrC : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) (v, r) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (v, r) contDiffAt_snd
  have hne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  exact ((hE.mul hF).mul (hrC.inv hne)).congr_of_eventuallyEq
    (Eventually.of_forall fun p => div_eq_mul_inv _ _)

/-- **The Dirichlet field is smooth across the future horizon.** -/
theorem contDiffAt_dirichletIngoing {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {y : ℝ} (hy : 0 < y) {v r : ℝ}
    (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => dirichletIngoing ε ξ₀ p.1 p.2 x y) (v, r) := by
  have hτ := contDiffAt_ingoingTime (v := v) hr
  have hτC : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((ingoingTime p.1 p.2 : ℝ) : ℂ)) (v, r) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (v, r) hτ
  have hE : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      Complex.exp (-(3 / 2 : ℂ) * ((ingoingTime p.1 p.2 : ℝ) : ℂ))) (v, r) :=
    (contDiffAt_const.mul hτC).cexp
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => wavePacket ε ξ₀ (ingoingTime p.1 p.2) x y) (v, r) :=
    (contDiff_wavePacket_time hε ξ₀ x hy).contDiffAt.comp (v, r) hτ
  have hrC : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) (v, r) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (v, r) contDiffAt_snd
  have hne : ((r : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hr.ne')
  exact ((hE.mul hF).neg.mul ((hrC.pow 2).inv hne)).congr_of_eventuallyEq
    (Eventually.of_forall fun p => div_eq_mul_inv _ _)

end GaloisForLFunctions.BlackHoleRingdown

end
