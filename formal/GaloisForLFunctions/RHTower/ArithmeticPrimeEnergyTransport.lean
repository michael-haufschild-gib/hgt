import GaloisForLFunctions.RHTower.ArithmeticFiniteZeroDisplacement
import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling

/-!
# Prime-clock energy transport along the actual finite-zero motion

An independent relative estimate for the complete finite prime sum controls logarithmically
small perturbations at every noncritical center. Applied to the exact finite-zero displacement
law, motion energy around the limiting zero tends to zero, while critical-line energy retains
the original center: it vanishes at a critical zero and diverges at a hypothetical off-line zero.
The normalized energy used by the RH receiver also retains a positive square-displacement floor.
These source estimates do not provide an independent critical-line energy bound or prove RH.
-/

noncomputable section
open Complex Set Filter Metric
open scoped Topology BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Relative error for the actual prime-clock source under logarithmically small motion. -/
def primeEnergyTransportError (c b : ℝ) : ℝ :=
  Real.cosh b-1+(1+1/c)*Real.sinh b

/-- The source error is nonnegative on its intended domain. -/
theorem primeEnergyTransportError_nonneg {c b : ℝ} (hc : 0<c) (hb : 0≤b) :
    0≤primeEnergyTransportError c b := by
  unfold primeEnergyTransportError
  have hcosh := Real.one_le_cosh b
  have hsinh : 0≤Real.sinh b := hb.trans (Real.self_le_sinh_iff.mpr hb)
  exact add_nonneg (by linarith) (mul_nonneg (by positivity) hsinh)

/-- Every prime amplitude has a uniform relative perturbation estimate away from the center. -/
theorem abs_sinh_add_sub_le_transport {c b x y : ℝ} (hc : 0<c) (hb : 0≤b)
    (hx : c≤|x|) (hy : |y|≤b) :
    |Real.sinh (x+y)-Real.sinh x| ≤ primeEnergyTransportError c b*|Real.sinh x| := by
  have hs : c≤|Real.sinh x| := by
    rw [Real.abs_sinh]
    exact hx.trans (Real.self_le_sinh_iff.mpr (abs_nonneg x))
  have hcosh : Real.cosh x≤|Real.sinh x|+1 := by
    have he := Real.cosh_sub_sinh (x:=|x|)
    have hb := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
    rw [Real.cosh_abs,←Real.abs_sinh] at he
    linarith
  have hratio : Real.cosh x≤(1+1/c)*|Real.sinh x| := by
    have h1 : 1≤|Real.sinh x|/c := (le_div_iff₀ hc).mpr (by simpa using hs)
    calc
      _ ≤ |Real.sinh x|+1 := hcosh
      _ ≤ |Real.sinh x|+|Real.sinh x|/c := by linarith
      _ = _ := by ring
  have hcy : Real.cosh y≤Real.cosh b :=
    Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hb])
  have hsy : |Real.sinh y|≤Real.sinh b := by
    rw [Real.abs_sinh]
    exact Real.sinh_le_sinh.mpr hy
  have heq : Real.sinh (x+y)-Real.sinh x=
      Real.sinh x*(Real.cosh y-1)+Real.cosh x*Real.sinh y := by
    rw [Real.sinh_add]
    ring
  rw [heq]
  calc
    _ ≤ |Real.sinh x*(Real.cosh y-1)|+|Real.cosh x*Real.sinh y| := abs_add_le _ _
    _ = |Real.sinh x| *(Real.cosh y-1)+Real.cosh x*|Real.sinh y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh y)),
        abs_of_pos (Real.cosh_pos x)]
    _ ≤ |Real.sinh x| *(Real.cosh b-1)+((1+1/c)*|Real.sinh x|)*Real.sinh b := by
      exact add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub_right hcy 1) (abs_nonneg _))
        (mul_le_mul hratio hsy (abs_nonneg _) (by positivity))
    _ = _ := by unfold primeEnergyTransportError; ring

/-- A relative amplitude error controls its complete square, including the cross term. -/
theorem abs_sq_sub_sq_le_transport {u v a : ℝ} (ha : 0≤a) (h : |u-v|≤a*|v|) :
    |u^(2 : ℕ)-v^(2 : ℕ)|≤a*(2+a)*v^(2 : ℕ) := by
  have hs : |u+v|≤(a+2)*|v| := by
    have he : u+v=(u-v)+(v+v) := by ring
    rw [he]
    have hb := abs_add_le (u-v) (v+v)
    have hc := abs_add_le v v
    nlinarith
  calc
    _ = |u-v| *|u+v| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (a*|v|)*((a+2)*|v|) := mul_le_mul h hs (abs_nonneg _) (by positivity)
    _ = _ := by rw [show (a*|v|)*((a+2)*|v|)=a*(2+a)*|v|^(2 : ℕ) by ring,sq_abs]

/-- The full literal prime energy has a relative source estimate; no zero premise is used. -/
theorem abs_primeClockCutoffEnergy_sub_le_transport {N : ℕ} (hN : 2≤N)
    {e c : ℝ} (hc : 0<c) (he : c≤|e| *Real.log 2) (h : ℝ) :
    |primeClockCutoffEnergy N (e+h)-primeClockCutoffEnergy N e| ≤
      primeEnergyTransportError c (|h| *Real.log N)*
      (2+primeEnergyTransportError c (|h| *Real.log N))*primeClockCutoffEnergy N e := by
  have hlogN : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  let a := primeEnergyTransportError c (|h| *Real.log N)
  have ha : 0≤a := primeEnergyTransportError_nonneg hc (mul_nonneg (abs_nonneg _) hlogN)
  rw [primeClockCutoffEnergy_eq_sinh,primeClockCutoffEnergy_eq_sinh,
    ←Finset.sum_sub_distrib,Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N,
      |4*Real.sinh ((e+h)*Real.log p)^(2 : ℕ)/(p:ℝ)-4*Real.sinh (e*Real.log p)^(2 : ℕ)/(p:ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpd := Nat.mem_primesLE.mp hp
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpd.2.pos
      have hlp : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast hpd.2.one_le)
      have hl2 : Real.log 2≤Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hpd.2.two_le)
      have hlN : Real.log p≤Real.log N := Real.log_le_log hp0 (by exact_mod_cast hpd.1)
      have hx : c≤|e*Real.log p| := by
        rw [abs_mul,abs_of_nonneg hlp]
        exact he.trans (mul_le_mul_of_nonneg_left hl2 (abs_nonneg e))
      have hy : |h*Real.log p|≤|h| *Real.log N := by
        rw [abs_mul,abs_of_nonneg hlp]
        exact mul_le_mul_of_nonneg_left hlN (abs_nonneg h)
      have hb := abs_sinh_add_sub_le_transport hc (mul_nonneg (abs_nonneg h) hlogN) hx hy
      rw [←add_mul] at hb
      have hs := abs_sq_sub_sq_le_transport ha hb
      have heq : 4*Real.sinh ((e+h)*Real.log p)^(2 : ℕ)/(p:ℝ)-4*Real.sinh (e*Real.log p)^(2 : ℕ)/(p:ℝ)=
          (4/(p:ℝ))*(Real.sinh ((e+h)*Real.log p)^(2 : ℕ)-Real.sinh (e*Real.log p)^(2 : ℕ)) := by ring
      rw [heq,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤4/(p:ℝ))]
      calc
        _ ≤ (4/(p:ℝ))*(a*(2+a)*Real.sinh (e*Real.log p)^(2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by dsimp [a]; ring

/-- The prime two makes the actual off-center energy strictly positive. -/
theorem primeClockCutoffEnergy_pos {N : ℕ} (hN : 2≤N) {e : ℝ} (he : e≠0) :
    0<primeClockCutoffEnergy N e := by
  rw [primeClockCutoffEnergy_eq_sinh]
  have hne : Real.sinh (e*Real.log 2)≠0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero he (Real.log_pos (by norm_num)).ne')
  have hpos : 0<4*Real.sinh (e*Real.log 2)^(2 : ℕ)/(2:ℝ) := by positivity
  apply hpos.trans_le
  simpa using (Finset.single_le_sum (f:=fun p : ℕ => 4*Real.sinh (e*Real.log p)^(2 : ℕ)/(p:ℝ))
    (fun p hp => by positivity) (Nat.mem_primesLE.mpr ⟨hN,Nat.prime_two⟩))

/-- Logarithmically small perturbations preserve the full off-center prime energy relatively. -/
theorem tendsto_primeClockEnergy_ratio_of_log_motion {e : ℝ} (he : e≠0)
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {h : ℕ→ℝ}
    (hlog : Tendsto (fun j => h j*Real.log (K j)) atTop (𝓝 0)) :
    Tendsto (fun j => primeClockCutoffEnergy (K j) (e+h j)/primeClockCutoffEnergy (K j) e)
      atTop (𝓝 1) := by
  let c := |e| * Real.log 2
  have hc : 0<c := mul_pos (abs_pos.mpr he) (Real.log_pos (by norm_num))
  have hb : Tendsto (fun j => |h j| * Real.log (K j)) atTop (𝓝 0) := by
    have ha := hlog.abs
    simp only [abs_zero] at ha
    apply ha.congr'
    filter_upwards [hK.eventually (eventually_ge_atTop 1)] with j hN
    rw [abs_mul,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))]
  have hcont : Continuous (primeEnergyTransportError c) := by
    unfold primeEnergyTransportError
    fun_prop
  have ha : Tendsto (fun j => primeEnergyTransportError c (|h j| * Real.log (K j))) atTop (𝓝 0) := by
    simpa [primeEnergyTransportError,Function.comp_def] using (hcont.tendsto 0).comp hb
  have haa := ha.mul (ha.const_add 2)
  simp only [zero_mul] at haa
  have hbnd : ∀ᶠj in atTop,
      |primeClockCutoffEnergy (K j) (e+h j)/primeClockCutoffEnergy (K j) e-1| ≤
        primeEnergyTransportError c (|h j| * Real.log (K j))*
          (2+primeEnergyTransportError c (|h j| * Real.log (K j))) := by
    filter_upwards [hK.eventually (eventually_ge_atTop 2)] with j hN
    have hE := primeClockCutoffEnergy_pos hN he
    have heq : primeClockCutoffEnergy (K j) (e+h j)/primeClockCutoffEnergy (K j) e-1=
        (primeClockCutoffEnergy (K j) (e+h j)-primeClockCutoffEnergy (K j) e)/
          primeClockCutoffEnergy (K j) e := by field_simp
    rw [heq,abs_div,abs_of_pos hE]
    exact (div_le_iff₀ hE).mpr (abs_primeClockCutoffEnergy_sub_le_transport hN hc (le_refl _) (h j))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbnd haa

/-- Cofinal critical-center motion with vanishing logarithmic size has vanishing full energy. -/
theorem tendsto_primeClockEnergy_zero_of_cofinal_log_motion
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {h : ℕ→ℝ}
    (hlog : Tendsto (fun j => h j*Real.log (K j)) atTop (𝓝 0)) :
    Tendsto (fun j => primeClockCutoffEnergy (K j) (h j)) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => (h j*Real.log (K j))^(2 : ℕ)) atTop (𝓝 0) := by simpa using hlog.pow 2
  have hratio := tendsto_primeClockSusceptibility_div_log_sq.comp hK
  have hu := (hs.mul hratio).const_mul (4*Real.cosh 1^(2 : ℕ))
  simp only [zero_mul,mul_zero] at hu
  have hwindow : ∀ᶠj in atTop, |h j| * Real.log (K j)≤1 := by
    have ha := (tendsto_order.1 hlog.abs).2 1 (by norm_num)
    filter_upwards [ha,hK.eventually (eventually_ge_atTop 1)] with j ha hN
    have hl : 0≤Real.log (K j) := Real.log_nonneg (by exact_mod_cast hN)
    simpa only [abs_mul,abs_of_nonneg hl] using ha.le
  apply squeeze_zero' (Eventually.of_forall (fun _ => primeClockCutoffEnergy_nonneg _ _)) ?_ hu
  filter_upwards [hwindow,hK.eventually (eventually_ge_atTop 2)] with j hw hN
  have hb := primeClockCutoffEnergy_quadratic_upper (K j) (h j) 1 (by norm_num) hw
  have hn : Real.log (K j)≠0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  convert hb using 1
  dsimp only [Function.comp_apply]
  field_simp

/-- Every fixed noncritical center has diverging prime energy under logarithmically small motion. -/
theorem tendsto_primeClockEnergy_atTop_of_log_motion {e : ℝ} (he : e≠0)
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {h : ℕ→ℝ}
    (hlog : Tendsto (fun j => h j*Real.log (K j)) atTop (𝓝 0)) :
    Tendsto (fun j => primeClockCutoffEnergy (K j) (e+h j)) atTop atTop := by
  have hbase : Tendsto (fun N : ℕ => primeClockCutoffEnergy N e) atTop atTop := by
    apply tendsto_primeClockCutoffEnergy_atTop_of_scaled_tendsto_atTop (fun _ => e)
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (abs_pos.mpr he)
  have hr := tendsto_primeClockEnergy_ratio_of_log_motion he hK hlog
  have hp := hr.pos_mul_atTop (by norm_num : (0:ℝ)<1) (hbase.comp hK)
  apply hp.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 2)] with j hN
  dsimp only [Function.comp_apply]
  exact div_mul_cancel₀ _ (primeClockCutoffEnergy_pos hN he).ne'

/-- Any convergent nonzero center retains a positive floor in the normalized energy
used by the finite-prime RH receiver. -/
theorem eventually_center_sq_le_normalized_primeEnergy {K : ℕ→ℕ} (hK : Tendsto K atTop atTop)
    {e : ℕ→ℝ} {a : ℝ} (he : Tendsto e atTop (𝓝 a)) :
    ∀ᶠj in atTop, a^(2 : ℕ)≤primeClockCutoffEnergy (K j) (e j)/Real.log (K j)^(2 : ℕ) := by
  by_cases ha : a=0
  · subst a
    exact Eventually.of_forall (fun j => by
      simpa using div_nonneg (primeClockCutoffEnergy_nonneg (K j) (e j)) (sq_nonneg _))
  have hs := (he.pow 2).mul (tendsto_primeClockSusceptibility_div_log_sq.comp hK)
  have hh := hs.const_mul 4
  have hn : Tendsto (fun j => 4*(e j)^(2 : ℕ)*(primeClockSusceptibility (K j)/Real.log (K j)^(2 : ℕ)))
      atTop (𝓝 (2*a^(2 : ℕ))) := by
    have hh' : Tendsto (fun j => 4*(e j)^(2 : ℕ)*(primeClockSusceptibility (K j)/Real.log (K j)^(2 : ℕ)))
        atTop (𝓝 (4*(a^(2 : ℕ)*(1/2)))) := by
      apply hh.congr'
      exact Eventually.of_forall (fun j => by dsimp only [Function.comp_apply]; ring)
    have heq : (4:ℝ)*(a^(2 : ℕ)*(1/2))=2*a^(2 : ℕ) := by ring
    rwa [heq] at hh'
  have hl := (tendsto_order.1 hn).1 (a^(2 : ℕ)) (by nlinarith [sq_pos_of_ne_zero ha])
  filter_upwards [hl] with j hj
  apply hj.le.trans
  have hb := div_le_div_of_nonneg_right (primeClockCutoffEnergy_quadratic_lower (K j) (e j))
    (sq_nonneg (Real.log (K j)))
  calc
    _ = (4*(e j)^(2 : ℕ)*primeClockSusceptibility (K j))/Real.log (K j)^(2 : ℕ) := by ring
    _ ≤ _ := hb

/-- Actual finite-head zero motion has vanishing prime energy relative to its limiting zero.
Critical-line energy vanishes only in the critical-center branch; the off-line branch retains
its nonzero center energy, diverges, and has a positive normalized floor. -/
theorem finite_zero_primeEnergy_transport (rho : RiemannGaussian.NontrivialZetaZero)
    {K : ℕ→ℕ} (hK : Tendsto K atTop atTop) {z : ℕ→ℂ} (hz : Tendsto z atTop (𝓝 rho.1))
    (hzero : ∀ᶠj in atTop, finiteCutoffResidual (K j) (z j)=0) :
    Tendsto (fun j => primeClockCutoffEnergy (K j) ((z j).re-rho.1.re)) atTop (𝓝 0) ∧
    (rho.1.re=1/2 →
      Tendsto (fun j => primeClockCutoffEnergy (K j) ((z j).re-1/2)) atTop (𝓝 0)) ∧
    (rho.1.re≠1/2 →
      Tendsto (fun j => primeClockCutoffEnergy (K j) ((z j).re-1/2)/
        primeClockCutoffEnergy (K j) (rho.1.re-1/2)) atTop (𝓝 1) ∧
      Tendsto (fun j => primeClockCutoffEnergy (K j) ((z j).re-1/2)) atTop atTop) ∧
    (∀ᶠj in atTop, (rho.1.re-1/2)^(2 : ℕ)≤
      primeClockCutoffEnergy (K j) ((z j).re-1/2)/Real.log (K j)^(2 : ℕ)) := by
  obtain ⟨g,hg,hg0,hfactor,_,_⟩ := exists_finite_zero_displacement_coefficient rho
  have hrho := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hmove := tendsto_moving_scaled_finite_zero hrho rho.2.2.2 hg.continuousAt hg0 hfactor hK hz hzero
  have hdrift := tendsto_finite_zero_log_drift (RiemannGaussian.analyticZetaZeroMultiplicity_positive rho)
    hK hz hrho hmove
  have hlog : Tendsto (fun j => ((z j).re-rho.1.re)*Real.log (K j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.zero_re,mul_zero,sub_zero] using
      (Complex.continuous_re.tendsto 0).comp hdrift
  have hlocal := tendsto_primeClockEnergy_zero_of_cofinal_log_motion hK hlog
  refine ⟨hlocal,?_,?_,?_⟩
  · intro hcrit
    simpa only [hcrit] using hlocal
  · intro hne
    have hr := tendsto_primeClockEnergy_ratio_of_log_motion (sub_ne_zero.mpr hne) hK hlog
    have hd := tendsto_primeClockEnergy_atTop_of_log_motion (sub_ne_zero.mpr hne) hK hlog
    have heq (j : ℕ) : rho.1.re-1/2+((z j).re-rho.1.re)=(z j).re-1/2 := by ring
    exact ⟨by simpa only [heq] using hr,by simpa only [heq] using hd⟩
  · exact eventually_center_sq_le_normalized_primeEnergy hK
      ((Complex.continuous_re.tendsto rho.1 |>.comp hz).sub_const (1/2))

/-- Every nontrivial zero has actual cofinal finite-head zeros whose motion energy vanishes
while the normalized critical-line energy retains the exact center's positive-square floor. -/
theorem exists_cofinal_finite_zero_primeEnergy_transport (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃ (K : ℕ→ℕ) (z : ℕ→ℂ), Tendsto K atTop atTop ∧ Tendsto z atTop (𝓝 rho.1) ∧
      (∀j, j≤K j ∧ z j≠rho.1 ∧ finiteCutoffResidual (K j) (z j)=0) ∧
      Tendsto (fun j => primeClockCutoffEnergy (K j) ((z j).re-rho.1.re)) atTop (𝓝 0) ∧
      (∀ᶠj in atTop, (rho.1.re-1/2)^(2 : ℕ)≤
        primeClockCutoffEnergy (K j) ((z j).re-1/2)/Real.log (K j)^(2 : ℕ)) := by
  obtain ⟨K,z,_,hK,hz,hzero,_,_⟩ := exists_cofinal_finite_zero_displacement_limit rho
  have h := finite_zero_primeEnergy_transport rho hK hz (Eventually.of_forall (fun j => (hzero j).2.2))
  exact ⟨K,z,hK,hz,hzero,h.1,h.2.2.2⟩

end RHTower.DeletionMixedRefinement
