import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeHardyTheorem
import GaloisForLFunctions.FiniteFreeProbability.ImaginaryPartDichotomy
import GaloisForLFunctions.HTGeometry.SuperGaussianMonomialization
import Mathlib.Analysis.Calculus.DSlope

/-!
# The inverse-degree expansion of the unshifted Jensen operator

Absolute coefficient estimates on disks, as in analytic Wiener composition,
give a hierarchy of effective Jensen approximations. Every remainder has a
positive coefficient kernel, including beyond the truncation degree. At a
simple zero the first correction gives the bounded displacement of the
extreme reversed root from its limiting ray.
-/

noncomputable section
open Filter Topology Complex Metric
open RHTower GaloisForLFunctions.HTGeometry
namespace FiniteFreeProbability.JensenExpansion

/-- Multiplier of the Taylor coefficient of degree k. -/
def damping (d k : ℕ) : ℝ := d.descFactorial k/(d:ℝ)^k

private theorem damping_mem (d k : ℕ) : damping d k ∈ Set.Icc 0 1 := by
  refine ⟨by unfold damping; positivity,?_⟩
  have h := norm_descFactorial_div_pow_le d k
  simpa only [norm_div,norm_pow,Complex.norm_natCast,damping] using h

private theorem damping_step {d : ℕ} (hd : 0 < d) (k : ℕ) :
    d*(damping d k-damping d (k+1)) = k*damping d k := by
  by_cases hk : k ≤ d
  · simp only [damping,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub hk,pow_succ]
    field_simp [show (d:ℝ) ≠ 0 by exact_mod_cast hd.ne'] <;> ring
  · have hz := Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hk)
    simp only [damping,Nat.descFactorial_succ,hz,mul_zero,Nat.cast_zero,zero_div,sub_zero]

/-- One summation records the choice of the largest index in an elementary
symmetric function of the integers strictly below the Taylor degree. -/
def prefixMoment : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, w, k => w k
  | n+1, w, k => ∑ j ∈ Finset.range k,(j:ℝ)*prefixMoment n w j

private theorem moment_mono {v w : ℕ → ℝ} (h : ∀ k, v k ≤ w k) (n k : ℕ) :
    prefixMoment n v k ≤ prefixMoment n w k := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih => exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (Nat.cast_nonneg j)

private theorem moment_nonneg {w : ℕ → ℝ} (h : ∀ k, 0 ≤ w k) (n k : ℕ) :
    0 ≤ prefixMoment n w k := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih => exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg j) (ih j)

private theorem moment_bound (n k : ℕ) :
    prefixMoment n (fun _ => 1) k ≤ ((k:ℝ)+1)^(2*n) := by
  induction n generalizing k with
  | zero => simp [prefixMoment]
  | succ n ih =>
    calc
      _ ≤ ∑ _j ∈ Finset.range k, ((k:ℝ)+1)*((k:ℝ)+1)^(2*n) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : (j:ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
        exact mul_le_mul (by linarith only [hjk]) ((ih j).trans
          (pow_le_pow_left₀ (by positivity) (by linarith only [hjk]) _))
          (moment_nonneg (fun _ => zero_le_one) n j) (by positivity)
      _ ≤ ((k:ℝ)+1)*(((k:ℝ)+1)*((k:ℝ)+1)^(2*n)) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [Nat.mul_succ,pow_add]; ring

private theorem moment_geometric {w : ℕ → ℝ} (hw : ∀ j, w j ≤ 1) (n k : ℕ) :
    prefixMoment n w k ≤ ((2:ℝ)^(2*n))^k := by
  have hnat : k+1 ≤ 2^k := k.lt_two_pow_self
  have hk : (k:ℝ)+1 ≤ 2^k := by exact_mod_cast hnat
  refine ((moment_mono hw n k).trans (moment_bound n k)).trans ?_
  rw [←pow_mul (2:ℝ) (2*n) k, Nat.mul_comm (2*n) k, pow_mul (2:ℝ) k (2*n)]
  exact pow_le_pow_left₀ (by positivity) hk _

private theorem prefix_difference {d : ℕ} (hd : 0 < d) (n k : ℕ) :
    (d:ℝ)*(prefixMoment n (fun _ => 1) k-prefixMoment n (damping d) k) =
      prefixMoment (n+1) (damping d) k := by
  induction n generalizing k with
  | zero =>
    change d*(1-damping d k)=∑ j ∈ Finset.range k,(j:ℝ)*damping d j
    induction k with
    | zero => simp [damping]
    | succ k ih => rw [Finset.sum_range_succ,← ih]; linear_combination damping_step hd k
  | succ n ih =>
    have e (w : ℕ → ℝ) (m : ℕ) :
        prefixMoment (n+1) w m = ∑ j ∈ Finset.range m,(j:ℝ)*prefixMoment n w j := rfl
    have e2 : prefixMoment (n+2) (damping d) k =
        ∑ j ∈ Finset.range k,(j:ℝ)*prefixMoment (n+1) (damping d) j := rfl
    rw [e2,e (fun _ => 1) k,e (damping d) k,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← ih j]
    ring

/-- Taylor observation at one order of the degree expansion. -/
def observation (n : ℕ) (w : ℕ → ℝ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, f k*(prefixMoment n w k : ℂ)*z^k

/-- The unrestricted coefficient at order n in inverse degree. -/
def coefficient (n : ℕ) (f : ℕ → ℂ) (z : ℂ) := observation n (fun _ => 1) f z

private theorem term_bound {w : ℕ → ℝ} (hw : ∀ k, w k ∈ Set.Icc 0 1)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    ‖f k*(prefixMoment n w k : ℂ)*z^k‖ ≤ ‖f k‖*(((2:ℝ)^(2*n))*R)^k := by
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (moment_nonneg (fun j => (hw j).1) n k),mul_pow,←mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (moment_geometric (fun j => (hw j).2) n k) (norm_nonneg _))
    (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) (by positivity)

private theorem summable_moment {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖*R^k)
    {w : ℕ → ℝ} (hw : ∀ k,w k ∈ Set.Icc 0 1) (n : ℕ) (z : ℂ) :
    Summable fun k => f k*(prefixMoment n w k : ℂ)*z^k :=
  Summable.of_norm_bounded (hf _) (term_bound hw le_rfl n f)

private theorem observation_step {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖*R^k)
    {d : ℕ} (hd : 0 < d) (n : ℕ) (z : ℂ) :
    (d:ℂ)*(coefficient n f z-observation n (damping d) f z)=observation (n+1) (damping d) f z := by
  unfold coefficient observation
  rw [← (summable_moment hf (fun _ => ⟨zero_le_one,le_rfl⟩) n z).tsum_sub
    (summable_moment hf (damping_mem d) n z),← tsum_mul_left]
  apply tsum_congr
  intro k
  have he : (d:ℂ)*((prefixMoment n (fun _ => 1) k:ℂ)-(prefixMoment n (damping d) k:ℂ)) =
    (prefixMoment (n+1) (damping d) k:ℂ) := by exact_mod_cast prefix_difference hd n k
  rw [← he]
  ring

private theorem damped_zero (d : ℕ) (f : ℕ → ℂ) (z : ℂ) :
    observation 0 (damping d) f z=scaledJensen f d z := by
  unfold observation scaledJensen
  rw [tsum_eq_sum (s := Finset.range (d+1)) fun k hk => by
    simp only [prefixMoment,damping,Nat.descFactorial_eq_zero_iff_lt.mpr (by simpa using hk),
      Nat.cast_zero,zero_div,Complex.ofReal_zero,mul_zero,zero_mul]]
  simp only [prefixMoment,damping,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow]

/-- Every finite inverse-degree expansion has an exact remainder with
nonnegative coefficient multipliers, even on Taylor degrees exceeding d. -/
theorem degree_expansion {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖*R^k)
    {d : ℕ} (hd : 0 < d) (n : ℕ) (z : ℂ) :
    scaledJensen f d z = (∑ j ∈ Finset.range n, (-(d:ℂ)⁻¹)^j*coefficient j f z) +
      (-(d:ℂ)⁻¹)^n*observation n (damping d) f z := by
  induction n with
  | zero => simp [damped_zero]
  | succ n ih =>
    rw [ih,Finset.sum_range_succ,pow_succ,add_assoc]
    apply congrArg (_ + ·)
    have h := observation_step hf hd n z
    have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [show observation n (damping d) f z =
        coefficient n f z-(d:ℂ)⁻¹*observation (n+1) (damping d) f z from by
      rw [← h,← mul_assoc,inv_mul_cancel₀ hd',one_mul]; ring]
    ring

/-- Uniform error on every closed disk at any expansion order. The
constant is an absolute Taylor majorant at a larger, explicit radius. -/
theorem disk_remainder_bound {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖*R^k)
    {d : ℕ} (hd : 0 < d) {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖scaledJensen f d z-∑ j ∈ Finset.range n, (-(d:ℂ)⁻¹)^j*coefficient j f z‖ ≤
      ((d:ℝ)⁻¹)^n*(∑' k, ‖f k‖*((2^(2*n):ℝ)*R)^k) := by
  rw [degree_expansion hf hd n,add_sub_cancel_left,norm_mul,norm_pow,norm_neg,norm_inv,Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_tsum_le_tsum_norm (summable_moment hf (damping_mem d) n z).norm).trans
    ((summable_moment hf (damping_mem d) n z).norm.tsum_le_tsum (term_bound (damping_mem d) hz n f) (hf _))


private theorem damping_tendsto (k : ℕ) : Tendsto (fun d => damping d k) atTop (𝓝 1) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_descFactorial_div_pow k)
  simpa only [Function.comp_def,Complex.one_re,damping,← Complex.ofReal_natCast,
    ← Complex.ofReal_pow,← Complex.ofReal_div,Complex.ofReal_re] using h

private theorem moment_tendsto (n k : ℕ) : Tendsto (fun d => prefixMoment n (damping d) k)
    atTop (𝓝 (prefixMoment n (fun _ => 1) k)) := by
  induction n generalizing k with
  | zero => exact damping_tendsto k
  | succ n ih => exact tendsto_finsetSum _ fun j _ => (ih j).const_mul _

/-- Every order is asymptotically exact along arbitrary convergent
evaluation points. Absolute summation is uniform over spatial disks. -/
theorem observation_tendsto {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖*R^k)
    {u : ℕ → ℂ} {a : ℂ} (hu : Tendsto u atTop (𝓝 a)) (n : ℕ) :
    Tendsto (fun d => observation n (damping d) f (u d)) atTop (𝓝 (coefficient n f a)) := by
  let R := ‖a‖+1
  have hr : ∀ᶠ d : ℕ in atTop, ‖u d‖ < R := hu.norm.eventually_lt_const (by dsimp [R]; linarith)
  apply tendsto_tsum_of_dominated_convergence (bound := fun k => ‖f k‖*(2^(2*n)*R)^k) (hf _)
  · intro k
    have hw := (Complex.continuous_ofReal.tendsto _).comp (moment_tendsto n k)
    exact (tendsto_const_nhds.mul hw).mul (hu.pow k)
  · exact hr.mono fun d hd k => term_bound (damping_mem d) hd.le n f k

private theorem coeff_xiSeries (k : ℕ) : PowerSeries.coeff k xiSeries = xiCoeff k := by
  rw [← mk_xiCoeff, PowerSeries.coeff_mk]

private theorem xi_summable : ∀ R : ℝ, Summable fun k => ‖xiCoeff k‖*R^k :=
  summable_norm_mul_pow_of_summable fun z => by
    simpa only [coeff_xiSeries] using (hasSum_xiSeries z).summable

private theorem first_multiplier (k : ℕ) :
    prefixMoment 1 (fun _ => 1) k=(k:ℝ)*(k-1)/2 := by
  change (∑ j ∈ Finset.range k, (j:ℝ)*1)=_
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih,Nat.cast_succ]; ring

private theorem xi_coefficient_zero (z : ℂ) : coefficient 0 xiCoeff z=XiC z := by
  simpa only [coefficient,observation,prefixMoment,Complex.ofReal_one,mul_one] using (show
    (∑' k, xiCoeff k*z^k) = XiC z by simpa only [coeff_xiSeries] using (hasSum_xiSeries z).tsum_eq)

/-- The first correction is the second derivative times half the squared
coordinate. The constant and linear Taylor terms contribute zero. -/
theorem xi_coefficient_one (z : ℂ) : coefficient 1 xiCoeff z=z^2*iteratedDeriv 2 XiC z/2 := by
  have hcoeff (k : ℕ) : iteratedDeriv k XiC 0=(k.factorial:ℂ)*xiCoeff k := by
    rw [xiCoeff,ofReal_realTaylorCoeff (fun w => XiC_conj w),←mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast k.factorial_ne_zero),one_mul]
  have hs := hasSum_iteratedDeriv_taylor XiC_differentiable hcoeff 2 z
  let A := fun k : ℕ => xiCoeff k*(prefixMoment 1 (fun _ => 1) k:ℂ)*z^k
  have hA : Summable A := summable_moment xi_summable (fun _ => ⟨zero_le_one,le_rfl⟩) 1 z
  have hsmall : ∑ k ∈ Finset.range 2,A k=0 := by simp [A,Finset.sum_range_succ,first_multiplier]
  have hshift := hA.sum_add_tsum_nat_add 2
  rw [hsmall,zero_add] at hshift
  change ∑' k,A k = _
  rw [← hshift,← hs.tsum_eq,show z^2*(∑' i, (((i+2).descFactorial 2:ℕ):ℂ)*xiCoeff (i+2)*z^i)/2 =
      (z^2/2)*(∑' i, (((i+2).descFactorial 2:ℕ):ℂ)*xiCoeff (i+2)*z^i) by ring,←tsum_mul_left]
  apply tsum_congr
  intro i
  have hfac : (i+2).descFactorial 2=(i+1)*(i+2) := by simp [Nat.descFactorial_succ]
  simp only [A,first_multiplier,hfac,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_natCast,
    Complex.ofReal_one,Complex.ofReal_ofNat,pow_add]
  ring

/-- Along every root converging to a simple zero a, the first displacement
in the scaled variable is a² Ξ″(a)/(2 Ξ′(a)). -/
theorem scaled_simple_zero_displacement {a : ℂ} (ha : XiC a=0) (hsimple : deriv XiC a ≠ 0)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 a))
    (hroot : ∀ᶠ d : ℕ in atTop, scaledJensen xiCoeff d (u d)=0) :
    Tendsto (fun d : ℕ => (d:ℂ)*(u d-a)) atTop
      (𝓝 (a^2*iteratedDeriv 2 XiC a/(2*deriv XiC a))) := by
  have h := observation_tendsto xi_summable hu 1
  rw [xi_coefficient_one] at h
  have hs := (continuousAt_dslope_same.mpr (XiC_differentiable a)).tendsto.comp hu
  rw [dslope_same] at hs
  have hh := h.div hs hsimple
  rw [div_div] at hh
  refine hh.congr' ?_
  filter_upwards [hroot,eventually_gt_atTop 0,hs.eventually_ne hsimple] with d hd hd₀ hd'
  have he := observation_step xi_summable hd₀ 0 (u d)
  rw [xi_coefficient_zero,damped_zero,hd,sub_zero] at he
  have hv : (u d-a)*dslope XiC a (u d)=XiC (u d) := by
    simpa only [smul_eq_mul,ha,sub_zero] using sub_smul_dslope XiC a (u d)
  change observation 1 (damping d) xiCoeff (u d)/dslope XiC a (u d) = _
  have hd'' : dslope XiC a (u d) ≠ 0 := hd'
  rw [←he,←hv,div_eq_iff hd'',mul_assoc]

/-- In the reversed polynomial the error is bounded and has a universal
limit. It is minus the logarithmic derivative of Ξ′ divided by two. -/
theorem reversed_simple_zero_intercept {a : ℂ} (ha : XiC a=0) (hsimple : deriv XiC a ≠ 0)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 a))
    (hroot : ∀ᶠ d : ℕ in atTop, scaledJensen xiCoeff d (u d)=0) :
    Tendsto (fun d : ℕ => (d:ℂ)/u d-d/a) atTop
      (𝓝 (-iteratedDeriv 2 XiC a/(2*deriv XiC a))) := by
  have ha₀ : a ≠ 0 := fun h => XiC_zero_ne (h ▸ ha)
  have hd := scaled_simple_zero_displacement ha hsimple hu hroot
  have hh := hd.neg.div (hu.mul_const a) (mul_ne_zero ha₀ ha₀)
  have hlim : -(a^2*iteratedDeriv 2 XiC a/(2*deriv XiC a))/(a*a) =
      -iteratedDeriv 2 XiC a/(2*deriv XiC a) := by
    field_simp <;> ring
  rw [hlim] at hh
  refine hh.congr' ?_
  filter_upwards [hu.eventually_ne ha₀] with d hd
  simp only [Pi.div_apply]
  field_simp <;> ring


/-- Each simple Ξ zero supplies an extreme root at every sufficiently
large degree with the stated intercept. The polynomial is unshifted. -/
theorem exists_reversed_root_with_intercept {a : ℂ} (ha : XiC a=0) (hsimple : deriv XiC a ≠ 0) :
    ∃ z : ℕ → ℂ, (∀ᶠ d : ℕ in atTop,(jensenRev d xiSeries).IsRoot (z d)) ∧
      Tendsto (fun d : ℕ => z d-d/a) atTop (𝓝 (-iteratedDeriv 2 XiC a/(2*deriv XiC a))) := by
  classical
  let S := fun d : ℕ => closedBall a 1 ∩ {w | scaledJensen xiCoeff d w=0}
  have hC (d : ℕ) : IsCompact (S d) := (isCompact_closedBall _ _).inter_right
    (isClosed_eq (by unfold scaledJensen; fun_prop) continuous_const)
  have select (d : ℕ) : ∃ u : ℂ, (S d).Nonempty →
      u ∈ S d ∧ ∀ w ∈ S d,dist u a ≤ dist w a := by
    by_cases hn : (S d).Nonempty
    · obtain ⟨u,hu,hmin⟩ := (hC d).exists_isMinOn hn (continuous_id.dist continuous_const).continuousOn
      exact ⟨u,fun _ => ⟨hu,fun _ hw => hmin hw⟩⟩
    · exact ⟨a,fun h => (hn h).elim⟩
  choose u hu using select
  have h₀ : xiCoeff 0 ≠ 0 := by
    rw [xiCoeff,ofReal_realTaylorCoeff (fun w => XiC_conj w)]
    simpa using XiC_zero_ne
  have near (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ d : ℕ in atTop,u d ∈ S d ∧ dist (u d) a < ε := by
    have he := eventually_exists_zero_scaledJensen xi_summable h₀
      ((show (∑' k,xiCoeff k*a^k)=XiC a by simpa only [coeff_xiSeries] using (hasSum_xiSeries a).tsum_eq).trans ha)
      (lt_min hε zero_lt_one)
    filter_upwards [he] with d ⟨w,hw,hz⟩
    have hw' : dist w a < min ε 1 := hw
    have hS : w ∈ S d := ⟨hw'.le.trans (min_le_right _ _),hz⟩
    obtain ⟨hu',hle⟩ := hu d ⟨w,hS⟩
    exact ⟨hu',(hle w hS).trans_lt (hw'.trans_le (min_le_left _ _))⟩
  have hlim : Tendsto u atTop (𝓝 a) := Metric.tendsto_nhds.mpr fun ε hε => (near ε hε).mono fun _ h => h.2
  have hroot := (near 1 one_pos).mono fun _ h => h.1.2
  refine ⟨fun d => d/u d,?_,reversed_simple_zero_intercept ha hsimple hlim hroot⟩
  have ha₀ : a ≠ 0 := fun h => XiC_zero_ne (h ▸ ha)
  filter_upwards [hroot,hlim.eventually_ne ha₀,eventually_gt_atTop 0] with d hd hu₀ hd₀
  rw [Polynomial.IsRoot,←mk_xiCoeff,eval_jensenRev_div _ hd₀ hu₀,hd,mul_zero]

end FiniteFreeProbability.JensenExpansion
