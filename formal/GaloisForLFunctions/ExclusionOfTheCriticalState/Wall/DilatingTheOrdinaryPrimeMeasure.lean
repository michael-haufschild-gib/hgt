import GaloisForLFunctions.RHTower.RobinLcmCriterion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Dilating the ordinary-prime counting measure

For measurable tests of quadratic decay continuous almost everywhere, the scaled
log-weighted prime measure converges to Lebesgue measure on the positive ray. Partition the mass
axis into cells of length `log p`. The prime number theorem puts the prime
of each rescaled cell asymptotically at its mass coordinate.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private theorem theta_nat_succ_atTop :
    Tendsto (fun n : ℕ => Chebyshev.theta (n+1)) atTop atTop := by
  have h := tendsto_theta_div_self.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hθ : Tendsto Chebyshev.theta atTop atTop := h.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact div_mul_cancel₀ _ hx.ne')
  exact hθ.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

private theorem exists_theta_crossing (v : ℝ) : ∃ n : ℕ, v < Chebyshev.theta (n+1) :=
  (theta_nat_succ_atTop.eventually_gt_atTop v).exists

/-- Bin containing a point of the positive real line when prime $p$ is given length $\log p$. -/
private def primeMassBin (v : ℝ) : ℕ := Nat.find (exists_theta_crossing v)

private theorem primeMassBin_spec (v : ℝ) : v < Chebyshev.theta (primeMassBin v+1) :=
  Nat.find_spec (exists_theta_crossing v)

private theorem monotone_primeMassBin : Monotone primeMassBin := by
  intro u v huv
  exact Nat.find_min' _ (huv.trans_lt (primeMassBin_spec v))

private theorem theta_primeMassBin_le {v : ℝ} (hv : 0 ≤ v) :
    Chebyshev.theta (primeMassBin v) ≤ v := by
  cases hn : primeMassBin v with
  | zero => simpa only [Nat.cast_zero,Chebyshev.theta_zero] using hv
  | succ k =>
    have hk : k < Nat.find (exists_theta_crossing v) := by change k < primeMassBin v; omega
    have h := le_of_not_gt (Nat.find_min (exists_theta_crossing v) hk)
    simpa only [Nat.cast_succ] using h

private theorem primeMassBin_atTop : Tendsto primeMassBin atTop atTop := by
  rw [tendsto_atTop]
  intro n
  filter_upwards [eventually_ge_atTop (Chebyshev.theta (n:ℝ))] with v hv
  by_contra! hh
  have hk : primeMassBin v + 1 ≤ n := by omega
  have hh' : (primeMassBin v:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hk
  exact (primeMassBin_spec v).not_ge ((Chebyshev.theta_mono hh').trans hv)

/-- The two Chebyshev readings bracketing a bin have the same asymptotic size. -/
private theorem bin_scale_tendsto :
    Tendsto (fun v : ℝ => ((primeMassBin v:ℝ)+1)/v) atTop (𝓝 1) := by
  let B := fun v : ℝ => (primeMassBin v:ℝ)
  have hB : Tendsto B atTop atTop := tendsto_natCast_atTop_atTop.comp primeMassBin_atTop
  have hB' : Tendsto (fun v => B v+1) atTop atTop := tendsto_atTop_add_const_right _ 1 hB
  have h1 : Tendsto (fun v => B v/(B v+1)) atTop (𝓝 1) := by
    have hzero := tendsto_inv_atTop_zero.comp hB'
    have hh : Tendsto (fun v => 1-(B v+1)⁻¹) atTop (𝓝 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub hzero : Tendsto (fun v => 1-(B v+1)⁻¹) atTop (𝓝 (1-0)))
    apply hh.congr'
    filter_upwards [hB'.eventually_gt_atTop 0] with v hv
    field_simp [hv.ne']; ring
  have hlo : Tendsto (fun v => Chebyshev.theta (B v)/(B v+1)) atTop (𝓝 1) := by
    have hh := (tendsto_theta_div_self.comp hB).mul h1
    rw [one_mul] at hh
    apply hh.congr'
    filter_upwards [hB.eventually_gt_atTop 0] with v hv
    change Chebyshev.theta (B v)/B v*(B v/(B v+1)) = _
    field_simp [hv.ne',show B v+1 ≠ 0 by linarith]
  have hhi := tendsto_theta_div_self.comp hB'
  have hm : Tendsto (fun v => v/(B v+1)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_ge_atTop (0:ℝ), hB'.eventually_gt_atTop 0] with v hv hl
      exact div_le_div_of_nonneg_right (theta_primeMassBin_le hv) hl.le
    · filter_upwards [hB'.eventually_gt_atTop 0] with v hl
      exact div_le_div_of_nonneg_right (primeMassBin_spec v).le hl.le
  simpa only [inv_div,inv_one] using hm.inv₀ (by norm_num : (1:ℝ) ≠ 0)

private def scaledPrimeBin (x : ℝ) (n : ℕ) : Set ℝ :=
  Ico (Chebyshev.theta (n:ℝ) / x) (Chebyshev.theta (n+1) / x)

private theorem mem_scaledPrimeBin {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    y ∈ scaledPrimeBin x (primeMassBin (x*y)) := by
  constructor
  · rw [div_le_iff₀ hx, mul_comm y]
    exact theta_primeMassBin_le (mul_nonneg hx.le hy)
  · rw [lt_div_iff₀ hx, mul_comm y]
    exact primeMassBin_spec (x*y)

private theorem scaledPrimeBin_disjoint {x : ℝ} (hx : 0 < x) :
    Pairwise (Function.onFun Disjoint (scaledPrimeBin x)) := by
  intro n m hnm
  have hd {i j : ℕ} (hij : i < j) : Disjoint (scaledPrimeBin x i) (scaledPrimeBin x j) := by
    apply Set.disjoint_left.mpr
    intro t hi hj
    have h : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
    exact (hi.2.trans_le ((div_le_div_of_nonneg_right (Chebyshev.theta_mono h) hx.le).trans hj.1)).false
  exact (lt_or_gt_of_ne hnm).elim hd (fun h => (hd h).symm)

private theorem iUnion_scaledPrimeBin {x : ℝ} (hx : 0 < x) :
    ⋃ n, scaledPrimeBin x n = Ici 0 := by
  ext y
  constructor
  · rintro ⟨_, ⟨n,rfl⟩,h⟩
    exact (div_nonneg (Chebyshev.theta_nonneg _) hx.le).trans h.1
  · intro hy
    exact mem_iUnion.mpr ⟨_, mem_scaledPrimeBin hx hy⟩

private def binReading (x : ℝ) (y : ℝ) : ℝ := ((primeMassBin (x*y):ℝ)+1)/x

private theorem measurable_binReading (x : ℝ) : Measurable (binReading x) := by
  have hn : Measurable (fun y : ℝ => primeMassBin (x*y)) :=
    monotone_primeMassBin.measurable.comp (measurable_const.mul measurable_id)
  have hr : Measurable (fun y : ℝ => (primeMassBin (x*y):ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hn
  exact (hr.add_const 1).div_const x

private theorem tendsto_binReading {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x => binReading x y) atTop (𝓝 y) := by
  have hh := (bin_scale_tendsto.comp (tendsto_id.atTop_mul_const hy)).mul_const y
  rw [one_mul] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  change (((primeMassBin (x*y):ℝ)+1)/(x*y))*y = ((primeMassBin (x*y):ℝ)+1)/x
  field_simp [hx.ne',hy.ne']

private theorem binReading_on {x y : ℝ} {n : ℕ} (hx : 0 < x) (hy : y ∈ scaledPrimeBin x n) :
    binReading x y = ((n:ℝ)+1)/x := by
  have hy0 : 0 ≤ y := (div_nonneg (Chebyshev.theta_nonneg _) hx.le).trans hy.1
  have he : primeMassBin (x*y) = n := by
    by_contra hn
    exact Set.disjoint_left.mp (scaledPrimeBin_disjoint hx hn) (mem_scaledPrimeBin hx hy0) hy
  simp only [binReading,he]

/-- The global Chebyshev upper bound supplies an integrable majorant uniform in the dilation. -/
private theorem binReading_domination {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) {x : ℝ} (hx : 0 < x) {y : ℝ} (hy : 0 ≤ y) :
    |g (binReading x y)| ≤ (C*(1+(Real.log 4)^2))*(1+y^2)⁻¹ := by
  let u := binReading x y
  have hu : 0 ≤ u := div_nonneg (by positivity) hx.le
  have hxy := (primeMassBin_spec (x*y)).le.trans (Chebyshev.theta_le_log4_mul_x
    (show (0:ℝ) ≤ (primeMassBin (x*y):ℝ)+1 by positivity))
  have hle : y ≤ Real.log 4 * u := by
    dsimp [u,binReading]
    rw [← mul_div_assoc,le_div_iff₀ hx, mul_comm y]
    exact hxy
  have hsq := pow_le_pow_left₀ hy hle 2
  rw [mul_pow] at hsq
  have he : 1+y^2 ≤ (1+(Real.log 4)^2)*(1+u^2) := by
    nlinarith only [hsq, sq_nonneg u, sq_nonneg (Real.log 4)]
  apply (hg u hu).trans
  rw [← div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
  exact (mul_le_mul_of_nonneg_left he hC).trans_eq (by ring)

private theorem integrable_binReading {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => g (binReading x y)) (Ici 0) := by
  refine (integrable_inv_one_add_sq.const_mul (C*(1+(Real.log 4)^2))).integrableOn.mono'
    (hg.comp (measurable_binReading x)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
  exact binReading_domination hC hb hx hy

private theorem hasSum_prime_bins {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => ((Chebyshev.theta (n+1) - Chebyshev.theta n)/x)*g (((n:ℝ)+1)/x))
      (∫ y in Ici (0:ℝ), g (binReading x y)) := by
  have hi := integrable_binReading hg hC hb hx
  rw [← iUnion_scaledPrimeBin hx] at hi ⊢
  apply (hasSum_integral_iUnion (fun _ => measurableSet_Ico) (scaledPrimeBin_disjoint hx) hi).congr_fun
  intro n
  symm
  have he : (∫ y in scaledPrimeBin x n, g (binReading x y)) =
      ∫ _y in scaledPrimeBin x n, g (((n:ℝ)+1)/x) := by
    apply setIntegral_congr_fun measurableSet_Ico
    exact fun y hy => congrArg g (binReading_on hx hy)
  change (∫ y in scaledPrimeBin x n, g (binReading x y)) = _
  rw [he,setIntegral_const,scaledPrimeBin,Real.volume_real_Ico,smul_eq_mul,
    max_eq_left (sub_nonneg.mpr (div_le_div_of_nonneg_right
      (Chebyshev.theta_mono (by linarith : (n:ℝ) ≤ n+1)) hx.le)), sub_div]

/-- Testing the dilated Chebyshev measure against an almost everywhere continuous function of quadratic decay
gives its Lebesgue integral. The prime number theorem locates each rescaled mass bin. -/
private theorem tendsto_prime_bin_sum {g : ℝ → ℝ} (hg : Measurable g)
    (hc : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ContinuousAt g y) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) :
    Tendsto (fun x : ℝ => ∑' n : ℕ, ((Chebyshev.theta (n+1)-Chebyshev.theta n)/x)*g (((n:ℝ)+1)/x))
      atTop (𝓝 (∫ y in Ici (0:ℝ), g y)) := by
  have hd : Tendsto (fun x : ℝ => ∫ y in Ici (0:ℝ), g (binReading x y)) atTop
      (𝓝 (∫ y in Ici (0:ℝ), g y)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => (C*(1+(Real.log 4)^2))*(1+y^2)⁻¹)
    · exact Eventually.of_forall fun x => (hg.comp (measurable_binReading x)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
      exact binReading_domination hC hb hx hy
    · exact (integrable_inv_one_add_sq.const_mul _).integrableOn
    · rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi,hc] with y hy hcy
      exact hcy.tendsto.comp (tendsto_binReading hy)
  refine hd.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact (hasSum_prime_bins hg hC hb hx).tsum_eq.symm

private theorem theta_nat_jump (n : ℕ) :
    Chebyshev.theta ((n:ℝ)+1) - Chebyshev.theta n =
      if (n+1).Prime then Real.log (n+1) else 0 := by
  rw [← Nat.cast_succ,Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log,
    Nat.primesLE_succ]
  by_cases hp : (n+1).Prime
  · have hn : n+1 ∉ Nat.primesLE n := by simp [Nat.mem_primesLE]
    simp [hp,Finset.sum_insert hn,Nat.cast_succ]
  · simp [hp]

/-- The dilates of the log-weighted ordinary-prime measure, divided by the
dilation factor, converge on quadratically decaying tests continuous at almost every positive point.
This includes bounded tests with jumps at reciprocal square roots. -/
theorem tendsto_dilated_ordinary_prime_sum_ae {g : ℝ → ℝ} (hg : Measurable g)
    (hc : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ContinuousAt g y) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes, Real.log (p:ℕ)*g ((p:ℕ)/x))/x)
      atTop (𝓝 (∫ y in Ici (0:ℝ), g y)) := by
  refine (tendsto_prime_bin_sum hg hc hC hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  let f := fun n : ℕ => if n.Prime then Real.log n*g ((n:ℝ)/x)/x else 0
  have he (n : ℕ) : ((Chebyshev.theta (n+1)-Chebyshev.theta n)/x)*g (((n:ℝ)+1)/x) = f (n+1) := by
    rw [theta_nat_jump]
    by_cases hp : (n+1).Prime
    · simp only [f,hp,if_true,Nat.cast_succ]; ring
    · simp [f,hp]
  have hsum := (hasSum_prime_bins hg hC hb hx).summable.congr he
  have hf : Summable f := (summable_nat_add_iff 1).mp hsum
  have hs := hf.sum_add_tsum_nat_add 1
  have hf0 : f 0 = 0 := by simp [f]
  simp only [Finset.sum_range_one,hf0,zero_add] at hs
  have hsub : (∑' p : Nat.Primes, f p) = ∑' n, f n := by
    apply tsum_subtype_eq_of_support_subset (s := {n : ℕ | n.Prime})
    intro n hn
    by_contra hp
    exact hn (by simp [f,show ¬ n.Prime from hp])
  rw [tsum_congr he,hs,← hsub,← tsum_div_const]
  exact tsum_congr fun p => by simp [f,p.property]

/-- Continuous tests of quadratic decay satisfy the dilated ordinary-prime limit. -/
theorem tendsto_dilated_ordinary_prime_sum {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C/(1+u^2)) :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes, Real.log (p:ℕ)*g ((p:ℕ)/x))/x)
      atTop (𝓝 (∫ y in Ici (0:ℝ), g y)) :=
  tendsto_dilated_ordinary_prime_sum_ae hg.measurable (Eventually.of_forall fun _ => hg.continuousAt) hC hb

#print axioms tendsto_dilated_ordinary_prime_sum_ae
#print axioms tendsto_dilated_ordinary_prime_sum

end GaloisForLFunctions.ExclusionOfTheCriticalState
