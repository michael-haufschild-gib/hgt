import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Positive hyperbolic modes cannot represent the literal theta potential

A positive summable cosh-mode source with finite exponential leading coefficient has no
active frequency above the leading rate. Its mass at the edge is exactly twice that
coefficient, giving a pointwise lower bound by the edge mode.

For the literal theta source Phi, V(x)=log(Phi(0))-log(Phi(x)) instead obeys
exp(-2x)*V(x) -> pi and (V(x)-2*pi*(cosh(2x)-1))/x -> -9/2.
Thus V has no nonnegative-quadratic plus positive summable cosh-mode representation,
even after a sublinear signed correction. Any correction negligible at the leading
exponential scale must carry at least this negative linear charge.

This tests one exact source representation. It asserts neither a Lee--Yang theorem
for arbitrary positive cosh potentials nor a Riemann-hypothesis conclusion.
-/

open Filter Topology
noncomputable section
namespace RHTower.PositiveCoshEdge

def mode (b x : ℝ) : ℝ := Real.cosh (b*x)-1

theorem mode_nonneg (b x : ℝ) : 0 ≤ mode b x :=
  sub_nonneg.mpr (Real.one_le_cosh _)

theorem scaled_mode_eq (b c x : ℝ) :
    Real.exp (-c*x)*mode b x =
      (Real.exp ((b-c)*x)+Real.exp ((-b-c)*x))/2-Real.exp (-c*x) := by
  rw [mode, Real.cosh_eq]
  have h1 : Real.exp (-c*x)*Real.exp (b*x) = Real.exp ((b-c)*x) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-c*x)*Real.exp (-(b*x)) = Real.exp ((-b-c)*x) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith

theorem exp_neg_rate {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c*x)) atTop (𝓝 0) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hc) using 1
  simp only [Function.comp_def, id_eq]; funext x; congr 1; ring

theorem scaled_power_limit {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (-c*x)*x^k) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (c^k)⁻¹
  convert h using 1
  · funext x; simp only [Function.comp_def, id_eq, mul_pow]
    rw [show -(c*x) = -c*x by ring]
    field_simp [hc.ne']
  · simp

theorem scaled_mode_limit {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (hbc : b ≤ c) :
    Tendsto (fun x : ℝ => Real.exp (-c*x)*mode b x) atTop
      (𝓝 (if b=c then (1/2:ℝ) else 0)) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp ((b-c)*x)) atTop
      (𝓝 (if b=c then (1:ℝ) else 0)) := by
    by_cases he : b=c
    · subst b; simp
    · simpa only [show -(c-b)=b-c by ring, if_neg he] using
        exp_neg_rate (sub_pos.mpr (lt_of_le_of_ne hbc he))
  have h2 : Tendsto (fun x : ℝ => Real.exp ((-b-c)*x)) atTop (𝓝 0) := by
    simpa only [show -(b+c)=-b-c by ring] using exp_neg_rate (by linarith : 0<b+c)
  have h := ((h1.add h2).div_const 2).sub (exp_neg_rate hc)
  convert h using 1
  · funext x; exact scaled_mode_eq b c x
  · split_ifs <;> norm_num

theorem scaled_mode_le_one {c b x : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hbc : b ≤ c) (hx : 0 ≤ x) :
    Real.exp (-c*x)*mode b x ≤ 1 := by
  rw [scaled_mode_eq]
  have h1 : Real.exp ((b-c)*x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbc) hx
  have h2 : Real.exp ((-b-c)*x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
  have := Real.exp_pos (-c*x)
  linarith


/-- A nonnegative mode faster than the finite leading rate must have zero weight. -/
theorem active_frequency_le {F : ℝ → ℝ} {a b c C : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 ≤ b)
    (hF : Tendsto (fun x => Real.exp (-c*x)*F x) atTop (𝓝 C))
    (hdom : ∀ x, 0 ≤ x → a*mode b x ≤ F x) : b ≤ c := by
  by_contra hbc
  have hcb : c < b := lt_of_not_ge hbc
  have hb0 : 0 < b := lt_trans hc hcb
  have hfast : Tendsto (fun x => Real.exp (-b*x)*F x) atTop (𝓝 0) := by
    have h := hF.mul (exp_neg_rate (sub_pos.mpr hcb))
    convert h using 1
    · funext x
      rw [show -(b-c)*x=(c-b)*x by ring]
      calc
        Real.exp (-b*x)*F x =
            (Real.exp (-c*x)*Real.exp ((c-b)*x))*F x := by
          rw [← Real.exp_add]; congr 2; ring
        _ = _ := by ring
    · simp
  have hmode : Tendsto (fun x => a*(Real.exp (-b*x)*mode b x)) atTop
      (𝓝 (a*(1/2:ℝ))) := by
    simpa using (scaled_mode_limit hb0 hb le_rfl).const_mul a
  have hle : a*(1/2:ℝ) ≤ 0 := le_of_tendsto_of_tendsto hmode hfast (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have h := mul_le_mul_of_nonneg_left (hdom x hx) (Real.exp_pos (-b*x)).le
    simpa only [mul_left_comm, mul_assoc] using h)
  linarith

def edgeMass (a b : ℕ → ℝ) (c : ℝ) : ℝ :=
  ∑' n, if b n=c then a n else 0

/-- Exact exponential edge mass of a positive, summable hyperbolic-mode source. -/
theorem mode_sum_scaled_limit {a b : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hs : Summable a) (hedge : ∀ n, a n ≠ 0 → b n ≤ c) :
    Tendsto (fun x => Real.exp (-c*x)*(∑' n, a n*mode (b n) x)) atTop
      (𝓝 (edgeMass a b c/2)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕:=atTop) hs
    (f := fun x : ℝ => fun n => a n*(Real.exp (-c*x)*mode (b n) x))
    (g := fun n => (if b n=c then a n else 0)/2) (fun n => ?_) ?_
  · convert h using 1
    · funext x; rw [← tsum_mul_left]
      apply tsum_congr; intro n; ring
    · rw [edgeMass, tsum_div_const]
  · by_cases haz : a n=0
    · simp [haz]
    · have h := (scaled_mode_limit hc (hb n) (hedge n haz)).const_mul (a n)
      convert h using 1
      split_ifs <;> ring
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n)
      (mul_nonneg (Real.exp_pos _).le (mode_nonneg _ _)))]
    by_cases haz : a n=0
    · simp [haz]
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (scaled_mode_le_one hc.le (hb n) (hedge n haz) hx) (ha n)

/-- A positive mode source with leading rate `c` and coefficient `C` must contain
exactly `2*C` mass at that rate and stay above its edge mode at every nonnegative point. -/
theorem edge_mass_and_floor {F : ℝ → ℝ} {a b : ℕ → ℝ} {q c C : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hs : Summable a)
    (hm : ∀ x, 0 ≤ x → Summable (fun n => a n*mode (b n) x))
    (hrep : ∀ x, 0 ≤ x → F x = q*x^2+∑' n, a n*mode (b n) x)
    (hF : Tendsto (fun x => Real.exp (-c*x)*F x) atTop (𝓝 C)) :
    edgeMass a b c=2*C ∧ ∀ x, 0 ≤ x → 2*C*mode c x ≤ F x := by
  have hdom (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : a n*mode (b n) x ≤ F x := by
    rw [hrep x hx]
    have h := (hm x hx).le_tsum n (fun j _ => mul_nonneg (ha j) (mode_nonneg _ _))
    nlinarith [mul_nonneg hq (sq_nonneg x)]
  have hedge (n : ℕ) (han : a n ≠ 0) : b n ≤ c :=
    active_frequency_le hc (lt_of_le_of_ne (ha n) (Ne.symm han)) (hb n) hF (hdom n)
  have hsum := mode_sum_scaled_limit hc ha hb hs hedge
  have hqterm := (scaled_power_limit hc 2).const_mul q
  have htotal := hqterm.add hsum
  have htotalF : Tendsto (fun x => Real.exp (-c*x)*F x) atTop
      (𝓝 (edgeMass a b c/2)) := by
    convert htotal.congr' (show
      (fun x => q*(Real.exp (-c*x)*x^2)+
        Real.exp (-c*x)*(∑' n, a n*mode (b n) x)) =ᶠ[atTop]
        (fun x => Real.exp (-c*x)*F x) from by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      rw [hrep x hx]; ring) using 1
    simp
  have he : edgeMass a b c=2*C := by
    have := tendsto_nhds_unique htotalF hF
    linarith
  refine ⟨he, ?_⟩
  intro x hx
  have hweights : Summable (fun n => if b n=c then a n else 0) :=
    hs.of_nonneg_of_le (fun n => by split_ifs; exact ha n; exact le_rfl)
      (fun n => by split_ifs; exact le_rfl; exact ha n)
  have hle := (hweights.mul_right (mode c x)).tsum_le_tsum
    (fun n => (show (if b n=c then a n else 0)*mode c x ≤ a n*mode (b n) x from by
      split_ifs with h
      · rw [h]
      · simpa using mul_nonneg (ha n) (mode_nonneg (b n) x))) (hm x hx)
  rw [tsum_mul_right, ← edgeMass, he] at hle
  rw [hrep x hx]
  nlinarith [mul_nonneg hq (sq_nonneg x)]

end RHTower.PositiveCoshEdge


namespace RHTower.ThetaCoshPotential
open HedenmalmThetaSource PositiveCoshEdge

def potential (x : ℝ) : ℝ := Real.log (thetaCuspFullSource 0)-Real.log (thetaCuspFullSource x)
def lowerConstant : ℝ := Real.log (thetaCuspFullSource 0)-Real.log thetaEnvelopeUpper
def upperConstant : ℝ := Real.log (thetaCuspFullSource 0)-Real.log thetaEnvelopeLower

/-- The literal source keeps the negative linear term in its logarithmic potential. -/
theorem potential_bounds {x : ℝ} (hx : 0 < x) :
    Real.pi*Real.exp (2*x)-9*x/2+lowerConstant ≤ potential x ∧
    potential x ≤ Real.pi*Real.exp (2*x)-9*x/2+upperConstant := by
  have he : Real.log (thetaEnvelope x)=9*x/2-Real.pi*Real.exp (2*x) := by
    simp [thetaEnvelope, Real.log_mul, Real.exp_ne_zero, sub_eq_add_neg]
  have hlpos : 0 < thetaEnvelopeLower*thetaEnvelope x :=
    mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos x)
  have hp : 0 < thetaCuspFullSource x := lt_of_lt_of_le hlpos (thetaCuspFullSource_ge_envelope hx)
  have hu := Real.log_le_log hp (thetaCuspFullSource_le_envelope hx.le)
  have hl := Real.log_le_log hlpos (thetaCuspFullSource_ge_envelope hx)
  rw [Real.log_mul thetaEnvelopeUpper_pos.ne' (thetaEnvelope_pos x).ne', he] at hu
  rw [Real.log_mul thetaEnvelopeLower_pos.ne' (thetaEnvelope_pos x).ne', he] at hl
  dsimp [potential, lowerConstant, upperConstant]
  constructor <;> linarith

private theorem model_limit (C : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-2*x)*(Real.pi*Real.exp (2*x)-9*x/2+C)) atTop
      (𝓝 Real.pi) := by
  have h1 := (scaled_power_limit (by norm_num : (0:ℝ)<2) 1).const_mul (9/2:ℝ)
  have h0 := (exp_neg_rate (by norm_num : (0:ℝ)<2)).const_mul C
  have h := ((tendsto_const_nhds (x:=Real.pi) (f:=atTop)).sub h1).add h0
  convert h using 1
  · funext x
    simp only [pow_one]
    have he : Real.exp (-2*x)*Real.exp (2*x)=1 := by
      rw [← Real.exp_add]; ring_nf; simp
    linear_combination Real.pi * he
  · simp

/-- Exact leading exponential coefficient of the actual normalized theta potential. -/
theorem scaled_potential_limit :
    Tendsto (fun x => Real.exp (-2*x)*potential x) atTop (𝓝 Real.pi) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (model_limit lowerConstant) (model_limit upperConstant)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (potential_bounds hx).1 (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (potential_bounds hx).2 (Real.exp_pos _).le

/-- The actual source is strictly below the positive edge-mode floor somewhere. -/
theorem exists_potential_below_edge :
    ∃ x : ℝ, 0 < x ∧ potential x < 2*Real.pi*mode 2 x := by
  let x : ℝ := |upperConstant+2*Real.pi|+1
  have hx : 0 < x := by dsimp [x]; positivity
  refine ⟨x, hx, ?_⟩
  have h := (potential_bounds hx).2
  have hab := le_abs_self (upperConstant+2*Real.pi)
  have hn := abs_nonneg (upperConstant+2*Real.pi)
  have he := mul_pos Real.pi_pos (Real.exp_pos (-(2*x)))
  rw [mode, Real.cosh_eq]
  dsimp [x] at *
  nlinarith

/-- No nonnegative quadratic plus positive summable cosh-mode representation of the
literal normalized theta potential exists. All source hypotheses are discharged. -/
theorem no_positive_cosh_representation :
    ¬ ∃ (q : ℝ) (a b : ℕ → ℝ), 0 ≤ q ∧ (∀ n, 0 ≤ a n) ∧
      (∀ n, 0 ≤ b n) ∧ Summable a ∧
      (∀ x, 0 ≤ x → Summable (fun n => a n*mode (b n) x)) ∧
      (∀ x, 0 ≤ x → potential x=q*x^2+∑' n, a n*mode (b n) x) := by
  rintro ⟨q,a,b,hq,ha,hb,hs,hm,hrep⟩
  have h := edge_mass_and_floor (by norm_num : (0:ℝ)<2) hq ha hb hs hm hrep
    scaled_potential_limit
  obtain ⟨x,hx,hbad⟩ := exists_potential_below_edge
  exact (not_lt_of_ge (h.2 x hx.le)) hbad


private theorem model_residual_limit (C : ℝ) :
    Tendsto (fun x : ℝ =>
      (Real.pi*Real.exp (2*x)-9*x/2+C-2*Real.pi*mode 2 x)/x) atTop
      (𝓝 (-(9/2:ℝ))) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ((tendsto_const_nhds (x:=-(9/2:ℝ)) (f:=atTop)).add
    (hinv.const_mul (C+2*Real.pi))).sub
    (((exp_neg_rate (by norm_num : (0:ℝ)<2)).mul hinv).const_mul Real.pi)
  have he : (fun x : ℝ => -(9/2:ℝ)+(C+2*Real.pi)*x⁻¹-
      Real.pi*(Real.exp (-2*x)*x⁻¹)) =ᶠ[atTop]
      (fun x => (Real.pi*Real.exp (2*x)-9*x/2+C-2*Real.pi*mode 2 x)/x) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [mode, Real.cosh_eq, show -(2*x)=-2*x by ring]
    field_simp
    ring
  simpa using h.congr' he

/-- The full source has an exact negative linear remainder after removing its leading edge mode. -/
theorem potential_edge_linear_limit :
    Tendsto (fun x => (potential x-2*Real.pi*mode 2 x)/x) atTop
      (𝓝 (-(9/2:ℝ))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (model_residual_limit lowerConstant) (model_residual_limit upperConstant)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact div_le_div_of_nonneg_right (sub_le_sub_right (potential_bounds hx).1 _) hx.le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact div_le_div_of_nonneg_right (sub_le_sub_right (potential_bounds hx).2 _) hx.le

/-- Any repair that is negligible at the leading exponential scale must carry at least the
literal negative linear charge; positivity of the mode sector cannot absorb it. -/
theorem correction_eventually_le_linear {a b : ℕ → ℝ} {q : ℝ} {r : ℝ → ℝ}
    (hq : 0 ≤ q) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hs : Summable a)
    (hm : ∀ x, 0 ≤ x → Summable (fun n => a n*mode (b n) x))
    (hrep : ∀ x, 0 ≤ x → potential x=q*x^2+(∑' n, a n*mode (b n) x)+r x)
    (hr : Tendsto (fun x => Real.exp (-2*x)*r x) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, r x/x < -(9/2:ℝ)+eps := by
  have hlim : Tendsto (fun x => Real.exp (-2*x)*(potential x-r x)) atTop
      (𝓝 Real.pi) := by
    convert scaled_potential_limit.sub hr using 1
    · funext x; ring
    · simp
  have hf := edge_mass_and_floor (F:=fun x => potential x-r x)
    (by norm_num : (0:ℝ)<2) hq ha hb hs hm
    (fun x hx => by rw [hrep x hx]; ring) hlim
  have hstrict := potential_edge_linear_limit.eventually
    (gt_mem_nhds (by linarith : -(9/2:ℝ)< -(9/2:ℝ)+eps))
  filter_upwards [hstrict, eventually_gt_atTop (0:ℝ)] with x hx hxpos
  have hfloor := hf.2 x hxpos.le
  have hle : r x ≤ potential x-2*Real.pi*mode 2 x := by linarith
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hle hxpos.le) hx


/-- Even a sublinear signed correction cannot repair the positive-mode ansatz for theta. -/
theorem no_sublinear_positive_cosh_representation :
    ¬ ∃ (q : ℝ) (a b : ℕ → ℝ) (r : ℝ → ℝ), 0 ≤ q ∧ (∀ n, 0 ≤ a n) ∧
      (∀ n, 0 ≤ b n) ∧ Summable a ∧
      (∀ x, 0 ≤ x → Summable (fun n => a n*mode (b n) x)) ∧
      (∀ x, 0 ≤ x → potential x=q*x^2+(∑' n, a n*mode (b n) x)+r x) ∧
      Tendsto (fun x => r x/x) atTop (𝓝 0) := by
  rintro ⟨q,a,b,r,hq,ha,hb,hs,hm,hrep,hr⟩
  have hsmall : Tendsto (fun x => Real.exp (-2*x)*r x) atTop (𝓝 0) := by
    have h := (scaled_power_limit (by norm_num : (0:ℝ)<2) 1).mul hr
    have he : (fun x => (Real.exp (-2*x)*x^1)*(r x/x)) =ᶠ[atTop]
        (fun x => Real.exp (-2*x)*r x) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      simp only [pow_one]
      field_simp
    simpa using h.congr' he
  have hneg := correction_eventually_le_linear hq ha hb hs hm hrep hsmall
    (by norm_num : (0:ℝ)<1)
  have hle : (0:ℝ) ≤ -(9/2:ℝ)+1 := le_of_tendsto hr (hneg.mono (fun _ hx => hx.le))
  norm_num at hle

end RHTower.ThetaCoshPotential
