import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundarySelection
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-! # All-order kinetic and deficit decay of the actual complete modular orbit. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology


private theorem decay_of_deriv_le_neg (f f' : ℝ → ℝ) (a : ℝ)
    (hd : ∀ x, a≤x → HasDerivAt f (f' x) x)
    (h0 : ∀ x, a≤x → 0≤f x)
    (hneg : ∀ x, a≤x → f' x≤ -f x) : Tendsto f atTop (𝓝 0) := by
  have hb (b : ℝ) (hab : a≤b) : f b≤f a*Real.exp (-(b-a)) := by
    have h := le_gronwallBound_of_liminf_deriv_right_le
      (f := f) (f' := f') (a := a) (b := b) (δ := f a) (K := -1) (ε := 0)
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
      (fun x hx r hr => (show HasDerivWithinAt f (f' x) (Ici x) x from
        (hd x hx.1).hasDerivWithinAt).liminf_right_slope_le hr)
      le_rfl (fun x hx => by simpa using hneg x hx.1) b ⟨hab,le_rfl⟩
    simpa only [gronwallBound_ε0,neg_one_mul] using h
  have he : Tendsto (fun x => f a*Real.exp (-(x-a))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (f a*Real.exp a)
    convert h using 1
    · funext x
      rw [show -(x-a)=a+(-x) by ring,Real.exp_add]
      ring
    · ring
  apply squeeze_zero' ?_ ?_ he
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact h0 x hx
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact hb x hx

def weightedKinetic (n : ℕ) (x : ℝ) : ℝ := k x^(n+2)*t x

def weightedKineticVelocity (n : ℕ) (x : ℝ) : ℝ :=
  k x^(n+1)*t x*(2*(n+2:ℕ)*(k x+1/3)*J x-2*u x*k x^2)

theorem dWeightedKinetic (n : ℕ) {x : ℝ} (hx : 0≤x) :
    HasDerivAt (weightedKinetic n) (weightedKineticVelocity n x) x := by
  have hd := ((dk hx).pow (n+2)).mul (dt hx)
  have hp : k x^(n+2)=k x^(n+1)*k x := by
    rw [show n+2=(n+1)+1 by omega,pow_succ]
  convert hd using 1 <;> first | rfl | skip
  simp only [weightedKineticVelocity,Pi.pow_apply,show n+2-1=n+1 by omega,hp]
  ring

theorem weightedKineticVelocity_le_neg (n : ℕ) {x : ℝ} (hx : 1≤x)
    (hkN : (n+2:ℕ)≤k x) (hkU : 1/u 1≤k x) :
    weightedKineticVelocity n x≤ -weightedKinetic n x := by
  have hx0 : 0≤x := by linarith
  have hu1 : 0<u 1 := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (by norm_num))
  have hum : u 1≤u x := u_mono (show (0:ℝ)≤1 by norm_num) hx0 hx
  have hu : 0<u x := hu1.trans_le hum
  have hm2 : (2:ℝ)≤((n+2:ℕ):ℝ) := by norm_cast; omega
  have hk : 0<k x := by linarith only [hm2,hkN]
  have hm : 0≤((n+2:ℕ):ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hkN (show 0≤k x+1/3 by linarith)
  have hquad := mul_nonneg hk.le (show 0≤k x-2/3 by linarith only [hm2,hkN])
  have hpoly : (2/3)*(n+2:ℕ)*(k x+1/3)≤k x^2 := by
    nlinarith only [hprod,hquad]
  have hj := mul_le_mul_of_nonneg_left (J_le_third_drift hx0)
    (show 0≤2*(n+2:ℕ)*(k x+1/3) by positivity)
  have hpu := mul_le_mul_of_nonneg_left hpoly hu.le
  have hku := (div_le_iff₀ hu1).mp hkU
  have humk := mul_le_mul_of_nonneg_right hum hk.le
  have huk : 1≤u x*k x := by nlinarith only [hku,humk]
  have hukk := mul_le_mul_of_nonneg_right huk hk.le
  have hA : 2*(n+2:ℕ)*(k x+1/3)*J x-2*u x*k x^2≤ -k x := by
    nlinarith only [hj,hpu,hukk]
  have hscale : 0≤k x^(n+1)*t x := mul_nonneg (pow_nonneg hk.le _) (t_pos hx0).le
  have he := mul_le_mul_of_nonneg_left hA hscale
  have hp : k x^(n+2)=k x^(n+1)*k x := by
    rw [show n+2=(n+1)+1 by omega,pow_succ]
  simpa only [weightedKineticVelocity,weightedKinetic,hp,mul_neg,neg_mul,mul_assoc,
    mul_left_comm,mul_comm] using he

/-- The actual kinetic gap is flat to every fixed algebraic order in the inverse ratio. -/
theorem kineticGap_superpolynomialDecay : Asymptotics.SuperpolynomialDecay atTop k kineticGap := by
  intro n
  have hK := (tendsto_atTop.1 k_tendsto_atTop) (max ((n+2:ℕ):ℝ) (1/u 1))
  obtain ⟨N,hN⟩ := eventually_atTop.1 hK
  have he : Tendsto (weightedKinetic n) atTop (𝓝 0) := by
    apply decay_of_deriv_le_neg (weightedKinetic n) (weightedKineticVelocity n) (max 1 N)
    · intro x hx
      exact dWeightedKinetic n (by linarith [le_max_left (1:ℝ) N])
    · intro x hx
      have hx0 : 0≤x := by linarith [le_max_left (1:ℝ) N]
      have hk : 0<k x := lt_trans (by norm_num) (k_gt hx0)
      exact mul_nonneg (pow_nonneg hk.le _) (t_pos hx0).le
    · intro x hx
      have hx1 : 1≤x := (le_max_left 1 N).trans hx
      have hNk := hN x ((le_max_right 1 N).trans hx)
      exact weightedKineticVelocity_le_neg n hx1
        ((le_max_left _ _).trans hNk) ((le_max_right _ _).trans hNk)
  convert he using 1
  funext x
  simp only [weightedKinetic,kineticGap,pow_add]
  ring


/-- The second compactified source coordinate is equally flat at every order. -/
theorem compactifiedDeficit_superpolynomialDecay :
    Asymptotics.SuperpolynomialDecay atTop k (fun x => k x*(1-3*J x/u x)) := by
  intro n
  have hzero : Tendsto (fun x => k x^n*kineticGap x*boundaryRatio x) atTop (𝓝 0) := by
    simpa using (kineticGap_superpolynomialDecay n).mul boundaryRatio_tendsto
  apply hzero.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : 0<x := by linarith
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx0))
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx0.le))
  have ht : t x≠0 := (t_pos hx0.le).ne'
  simp only [kineticGap,boundaryRatio]
  field_simp [hu,hk,ht]

end
end RHTower.ThetaCuspModularRatio
