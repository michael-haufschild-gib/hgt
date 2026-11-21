import GaloisForLFunctions.MultiplicativePositivityGeometry.TheEquilibriumOfTheThreeSitePrimeGram
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Energy saved by signed masses on coalescing prime sites

The response of the m-th difference divided by t^(2m) tends to the
2m-th prime-log moment. For three sites this gives two distinct scales
for the Hessian and the obstacle price. Allowing signed masses lowers
the limiting minimum energy by the square of the second moment divided
by the fourth moment.
-/

noncomputable section
open Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Squared response of the m-th forward difference on the prime spectrum. -/
def primeDifferenceEnergy (h t : ℝ) (m : ℕ) : ℝ :=
  ∑' n, zetaBoundaryWeight h n*(2*(1-Real.cos (logFrequency n*t)))^m

private theorem log_even_nonneg (n m : ℕ) : 0≤(logFrequency n)^(2*m) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

private theorem sini (x : ℝ) : x*Real.sinc x=Real.sin x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

private theorem diff_eq_sinc (a t : ℝ) :
    2*(1-Real.cos (a*t))=t^2*a^2*Real.sinc (a*t/2)^2 := by
  have hc := Real.cos_two_mul (a*t/2)
  rw [show 2*(a*t/2)=a*t by ring] at hc
  have hs := Real.sin_sq_add_cos_sq (a*t/2)
  rw [←sini (a*t/2)] at hs
  linear_combination -2*hc -4*hs

/-- Every even logarithmic moment can be read from the collapsing
finite-difference energy, with its exact coefficient. -/
theorem coalescing_prime_difference {h : ℝ} (hh : 0<h) (m : ℕ) :
    Tendsto (fun t => primeDifferenceEnergy h t m/t^(2*m)) (𝓝[≠] 0)
      (𝓝 (RHTower.vonMangoldtWeightLogMoment (2*m) (1+h))) := by
  let μ := fun n => zetaBoundaryWeight h n*logFrequency n^(2*m)
  have hs : Summable μ := RHTower.summable_vonMangoldt_logPow (by linarith only [hh] : 1<1+h) _
  have hμ (n : ℕ) : 0≤μ n := mul_nonneg (zetaBoundaryWeight_nonneg _ _) (log_even_nonneg _ _)
  have hc : Tendsto (fun t : ℝ => ∑' n, μ n*(Real.sinc (logFrequency n*t/2))^(2*m))
      (𝓝 0) (𝓝 (∑' n, μ n)) := by
    apply tendsto_tsum_of_dominated_convergence (bound:=μ) hs
    · intro n
      have hu : Tendsto (fun t : ℝ => logFrequency n*t/2) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).const_mul (logFrequency n) |>.div_const 2
      simpa using ((Real.continuous_sinc.tendsto 0).comp hu).pow (2*m) |>.const_mul (μ n)
    · exact Eventually.of_forall fun t n => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hμ n),abs_pow]
        exact mul_le_of_le_one_right (hμ n) (pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _))
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t≠0 := ht
  rw [primeDifferenceEnergy,←tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [diff_eq_sinc,eq_div_iff (pow_ne_zero _ hne)]
  simp only [μ,mul_pow,pow_mul]
  ring

private theorem moment_pos {h : ℝ} (hh : 0<h) (m : ℕ) :
    0<RHTower.vonMangoldtWeightLogMoment (2*m) (1+h) := by
  have hs := RHTower.summable_vonMangoldt_logPow (by linarith only [hh] : 1<1+h) (2*m)
  have hp : 0<zetaBoundaryWeight h 2*logFrequency 2^(2*m) := by
    simp only [zetaBoundaryWeight,logFrequency,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,Nat.cast_ofNat]
    exact mul_pos (mul_pos (Real.log_pos (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _))
      (pow_pos (Real.log_pos (by norm_num)) _)
  exact hp.trans_le (hs.le_tsum 2 (fun n _ => mul_nonneg (zetaBoundaryWeight_nonneg _ _) (log_even_nonneg _ _)))

private def fDiff (h t : ℝ) := zetaRealLogDeriv (1+h) 0-2*zetaRealLogDeriv (1+h) t+zetaRealLogDeriv (1+h) (2*t)
private def dDiff (h t : ℝ) := 3*zetaRealLogDeriv (1+h) 0-4*zetaRealLogDeriv (1+h) t+zetaRealLogDeriv (1+h) (2*t)

private theorem first_two_differences {h : ℝ} (hh : 0<h) (t : ℝ) :
    primeDifferenceEnergy h t 1=dDiff h t-fDiff h t ∧
    primeDifferenceEnergy h t 2=2*dDiff h t := by
  let w := zetaBoundaryWeight h
  let b := fun (t : ℝ) n => w n*Real.cos (logFrequency n*t)
  have hs (u : ℝ) : HasSum (b u) (zetaRealLogDeriv (1+h) u) := by
    rw [zetaRealLogDeriv_eq_cosineTrace hh]
    exact (summable_cosineTrace_terms (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh) _ _).hasSum
  constructor
  · have hf := ((hs 0).sub (hs t)).mul_left 2
    rw [show dDiff h t-fDiff h t=2*(zetaRealLogDeriv (1+h) 0-zetaRealLogDeriv (1+h) t) by dsimp only [fDiff,dDiff]; ring,←hf.tsum_eq]
    apply tsum_congr
    intro n
    simp only [b,w,mul_zero,Real.cos_zero,mul_one,pow_one]
    ring
  · have hd := ((((hs 0).mul_left 3).sub ((hs t).mul_left 4)).add (hs (2*t))).mul_left 2
    change _=2*(3*_-4*_+_)
    rw [←hd.tsum_eq]
    apply tsum_congr
    intro n
    simp only [b,w,mul_zero,Real.cos_zero,mul_one]
    rw [show logFrequency n*(2*t)=2*(logFrequency n*t) by ring,Real.cos_two_mul]
    ring

/-- At fixed damping the obstacle contrast has a negative quadratic leading
term. The independent curvature has a strictly positive quartic leading term. -/
theorem coalescing_three_site_scales {h : ℝ} (hh : 0<h) :
    let f := zetaRealLogDeriv (1+h)
    Tendsto (fun t => (f 0-2*f t+f (2*t))/t^2) (𝓝[≠] 0) (𝓝 (-RHTower.vonMangoldtWeightLogMoment 2 (1+h))) ∧
    Tendsto (fun t => (3*f 0-4*f t+f (2*t))/t^4) (𝓝[≠] 0) (𝓝 (RHTower.vonMangoldtWeightLogMoment 4 (1+h)/2)) := by
  have h₁ := coalescing_prime_difference hh 1
  have h₂ := coalescing_prime_difference hh 2
  norm_num only [Nat.reduceMul] at h₁ h₂
  have hd : Tendsto (fun t => dDiff h t/t^4) (𝓝[≠] 0) (𝓝 (RHTower.vonMangoldtWeightLogMoment 4 (1+h)/2)) :=
    (h₂.div_const 2).congr fun t => by rw [(first_two_differences hh t).2]; ring
  refine ⟨?_,hd⟩
  have ht : Tendsto (fun t : ℝ => t^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_pow 2).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hscaled := (hd.mul ht).sub h₁
  simp only [mul_zero,zero_sub] at hscaled
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t≠0 := ht
  change _=fDiff h t/t^2
  rw [(first_two_differences hh t).1]
  field_simp <;> ring

/-- The unconstrained signed equilibrium and its minimum energy. -/
theorem signed_three_site_minimum {h t : ℝ} (hh : 0<h) (ht : t≠0) :
    let f := zetaRealLogDeriv (1+h)
    let F := f 0-2*f t+f (2*t)
    let D := 3*f 0-4*f t+f (2*t)
    let e := (f 0+f (2*t))/2-F^2/(2*D)
    let v := F/D
    threeSiteEnergy h t ((1-v)/2) v ((1-v)/2)=e ∧
      ∀ a b c : ℝ, a+b+c=1 → e≤threeSiteEnergy h t a b c := by
  intro f F D e v
  have hd : 0<D := (three_site_contrasts_pos hh ht).2.2
  have ha : 0<f 0-f (2*t) := (three_site_contrasts_pos hh ht).2.1
  have hid (a b c : ℝ) (hs : a+b+c=1) :
      threeSiteEnergy h t a b c-e=D/2*(b-v)^2+(f 0-f (2*t))/2*(a-c)^2 := by
    rw [show c=1-a-b by linarith only [hs]]
    dsimp only [e,v]
    field_simp [hd.ne']
    dsimp only [threeSiteEnergy,F,D,f]
    ring
  constructor
  · apply sub_eq_zero.mp
    rw [hid _ _ _ (by ring),sub_self,sub_self]
    ring
  · intro a b c hs
    exact sub_nonneg.mp ((hid a b c hs).symm ▸ add_nonneg
      (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) (sq_nonneg _)))

/-- The positive-simplex minimum exceeds the signed minimum by an amount
which tends to M₂²/M₄ > 0, even though all three sites approach one point. -/
theorem coalescing_sign_constraint_price {h : ℝ} (hh : 0<h) :
    let f := zetaRealLogDeriv (1+h)
    Tendsto (fun t => let v := equilibriumMiddle h t
      threeSiteEnergy h t ((1-v)/2) v ((1-v)/2)-
      ((f 0+f (2*t))/2-(f 0-2*f t+f (2*t))^2/(2*(3*f 0-4*f t+f (2*t)))))
      (𝓝[≠] 0) (𝓝 (RHTower.vonMangoldtWeightLogMoment 2 (1+h)^2/RHTower.vonMangoldtWeightLogMoment 4 (1+h))) := by
  intro f
  obtain ⟨hF,hD⟩ := coalescing_three_site_scales hh
  have h₂ := moment_pos hh 1
  have h₄ := moment_pos hh 2
  norm_num only [Nat.reduceMul] at h₂ h₄
  have hlim := (hF.pow 2).div (hD.const_mul 2) (by positivity)
  simp only [neg_sq] at hlim
  rw [show 2*(RHTower.vonMangoldtWeightLogMoment 4 (1+h)/2)=RHTower.vonMangoldtWeightLogMoment 4 (1+h) by ring] at hlim
  apply hlim.congr'
  filter_upwards [hF.eventually_lt_const (neg_lt_zero.mpr h₂),self_mem_nhdsWithin] with t hsmall ht
  have hn : t≠0 := ht
  have hf : fDiff h t<0 := by
    by_contra hc
    exact (not_lt.mpr (div_nonneg (le_of_not_gt hc) (sq_nonneg t))) hsmall
  have hzero : equilibriumMiddle h t=0 := by
    change max (fDiff h t) 0/_=0
    rw [max_eq_right hf.le,zero_div]
  rw [hzero]
  change (fDiff h t/t^2)^2/(2*(dDiff h t/t^4))=_
  have hd : dDiff h t≠0 := (three_site_contrasts_pos hh hn).2.2.ne'
  dsimp only [threeSiteEnergy,f]
  dsimp only [fDiff,dDiff] at *
  field_simp <;> ring

end GaloisForLFunctions.MultiplicativePositivityGeometry
