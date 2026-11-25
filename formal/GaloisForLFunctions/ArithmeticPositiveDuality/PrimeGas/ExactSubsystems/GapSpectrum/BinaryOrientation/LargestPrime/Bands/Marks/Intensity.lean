import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.FiniteEnergy
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.MovingCutoff

/-! # Reciprocal prime intensity on a moving band of physical energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory _root_.RHTower _root_.RHTower.BAGTrace

/-- Scaled one-prime energy. -/
def location (h : Ioi (0:ℝ)) (p : Nat.Primes) := h.val*squarefreePrimeEnergy p

theorem mem_initial (b : ℝ) (h : Ioi (0:ℝ)) (p : Nat.Primes) :
    p ∈ initial b h ↔ location h p ≤ b := by
  change p ∈ Sieve.primeSubtypeLE (primeCut b h) ↔ h.val*Real.log (p.val:ℝ) ≤ b
  rw [Sieve.mem_primeSubtypeLE,primeCut,Nat.le_floor_iff (Real.exp_pos _).le,
    ← Real.log_le_log_iff (Nat.cast_pos.mpr p.property.pos) (Real.exp_pos _),Real.log_exp,
    le_div_iff₀ h.property,mul_comm]

theorem mem_added (c d : ℝ) (h : Ioi (0:ℝ)) (p : Nat.Primes) :
    p ∈ added c d h ↔ c < location h p ∧ location h p ≤ d := by
  simp only [added,Finset.mem_sdiff,mem_initial,not_le,and_comm]

private def coord (N : ℕ) (p : Nat.Primes) := squarefreePrimeEnergy p/Real.log N

private def weight (N : ℕ) (p : Nat.Primes) := coord N p/(p.val:ℝ)

private def average (N : ℕ) (g : ℝ → ℂ) :=
  ∑ p ∈ Window.packet N, g (coord N p)*(weight N p:ℂ)

private theorem fixed_average (g : ℝ → ℂ) (hg : Continuous g) :
    Tendsto (fun N => average N g) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  apply (criticalComplexPrimeWindow_tendsto hg.continuousOn).congr
  intro N
  let f (n : ℕ) := g (Real.log n/Real.log N)*((Real.log n/Real.log N/(n:ℝ):ℝ):ℂ)
  have hS : (∑ p ∈ Window.packet N, f p.val) = ∑ n ∈ N.primesLE, f n :=
    Finset.sum_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)
  change _ = ∑ p ∈ Window.packet N, f p.val
  rw [hS,show N.primesLE = (Finset.Icc 0 N).filter Nat.Prime by
    ext n; simp [Finset.mem_Icc,Nat.mem_primesLE],Finset.sum_filter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [mertensPrimeWeight,hp,if_pos,f,Complex.ofReal_div]
    ring
  · simp [mertensPrimeWeight,hp]

private theorem coord_mem {N : ℕ} (hN : 2 ≤ N) {p : Nat.Primes} (hp : p ∈ Window.packet N) :
    coord N p ∈ Icc (0:ℝ) 1 := by
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N from hN))
  change Real.log (p.val:ℝ)/Real.log N ∈ Icc (0:ℝ) 1
  refine ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_le)) hL.le,?_⟩
  exact (div_le_one hL).mpr (Real.log_le_log (Nat.cast_pos.mpr p.property.pos)
    (by exact_mod_cast Sieve.mem_primeSubtypeLE.mp hp))

/-- Varying the physical scale changes the test uniformly on the entire unit interval. -/
private def testFamily (g : ℝ → ℂ) (hg : Continuous g) : C(ℝ,C(Icc (0:ℝ) 1,ℂ)) :=
  (⟨fun u : ℝ × Icc (0:ℝ) 1 => g (u.1*u.2.val),
    hg.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))⟩ :
      C(ℝ × Icc (0:ℝ) 1,ℂ)).curry

private theorem moving_average {b : ℝ} (hb : 0 < b) (g : ℝ → ℂ) (hg : Continuous g) :
    Tendsto (fun h => average (primeCut b h) (fun t => g (cutoffScale b h*t)))
      criticalApproach (𝓝 (∫ t in (0:ℝ)..1, g (b*t))) := by
  let A := testFamily g hg
  have hA := (A.continuous.tendsto b).comp (cutoffScale_limit hb)
  have hD : Tendsto (fun h => ‖A (cutoffScale b h)-A b‖) criticalApproach (𝓝 0) := by
    simpa only [Function.comp_apply,sub_self,norm_zero] using (hA.sub_const (A b)).norm
  let W (h : Ioi (0:ℝ)) := ∑ p ∈ initial b h, weight (primeCut b h) p
  have hW : Tendsto W criticalApproach (𝓝 1) := by
    have H := (Complex.continuous_re.tendsto _).comp ((fixed_average (fun _ => 1) continuous_const).comp
      (primeCut_atTop hb))
    simpa [W,average,Function.comp_def,← Complex.ofReal_sum] using H
  let F (h : Ioi (0:ℝ)) := average (primeCut b h) (fun t => g (cutoffScale b h*t))
  let G (h : Ioi (0:ℝ)) := average (primeCut b h) (fun t => g (b*t))
  have hdiff : Tendsto (fun h => ‖F h-G h‖) criticalApproach (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun h => ‖A (cutoffScale b h)-A b‖*W h) _ (𝓝 0) by
        simpa only [zero_mul] using hD.mul hW)
    filter_upwards [(primeCut_atTop hb).eventually_ge_atTop 2] with h hN
    let N := primeCut b h
    change ‖(∑ p ∈ Window.packet N, _)-(∑ p ∈ Window.packet N, _)‖ ≤ _
    rw [← Finset.sum_sub_distrib,show ‖A (cutoffScale b h)-A b‖*W h =
      ∑ p ∈ Window.packet N, ‖A (cutoffScale b h)-A b‖*weight N p by rw [← Finset.mul_sum]]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
    have ht := coord_mem hN hp
    have hw : 0 ≤ weight N p := div_nonneg ht.1 (Nat.cast_nonneg _)
    rw [← sub_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right ((A (cutoffScale b h)-A b).norm_coe_le_norm ⟨coord N p,ht⟩) hw
  have hG := (fixed_average (fun t => g (b*t)) (hg.comp (continuous_const.mul continuous_id))).comp
    (primeCut_atTop hb)
  change Tendsto G criticalApproach (𝓝 (∫ t in (0:ℝ)..1, g (b*t))) at hG
  change Tendsto F criticalApproach _
  have H := (tendsto_zero_iff_norm_tendsto_zero.mpr hdiff).add hG
  simpa only [zero_add,sub_add_cancel] using H

/-- The log-weighted physical prime measure on an initial interval tends to Lebesgue measure. -/
theorem initial_weighted_limit {b : ℝ} (hb : 0 < b) (g : ℝ → ℂ) (hg : Continuous g) :
    Tendsto (fun h => ∑ p ∈ initial b h, g (location h p)*((location h p/(p.val:ℝ):ℝ):ℂ))
      criticalApproach (𝓝 (∫ v in (0:ℝ)..b, g v)) := by
  have H := ((Complex.continuous_ofReal.tendsto _).comp (cutoffScale_limit hb)).mul (moving_average hb g hg)
  have hi : (b:ℂ)*(∫ t in (0:ℝ)..1,g (b*t)) = ∫ v in (0:ℝ)..b,g v := by
    rw [intervalIntegral.integral_comp_mul_left g hb.ne',mul_zero,mul_one,Complex.real_smul,
      Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'),one_mul]
  rw [hi] at H
  apply H.congr'
  filter_upwards [(primeCut_atTop hb).eventually_ge_atTop 2] with h hN
  have hL : Real.log (primeCut b h:ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < primeCut b h from hN))).ne'
  change (cutoffScale b h:ℂ)*average (primeCut b h) _ = _
  rw [average,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hv : cutoffScale b h*coord (primeCut b h) p = location h p := by
    unfold cutoffScale coord location
    field_simp [hL]
  simp only [← hv,weight,Complex.ofReal_div,Complex.ofReal_mul]
  ring

/-- Every continuous mark has reciprocal prime intensity dv/v on a positive bounded band. -/
theorem intensity_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (f : ℝ → ℂ) (hf : Continuous f) :
    Tendsto (fun h => ∑ p ∈ added c d h, f (location h p)/(p.val:ℂ)) criticalApproach
      (𝓝 (∫ v in c..d, f v/(v:ℂ))) := by
  let g (v : ℝ) := f v/(max c v:ℝ)
  have hg : Continuous g := hf.div (Complex.continuous_ofReal.comp (continuous_const.max continuous_id))
    (fun v => Complex.ofReal_ne_zero.mpr (hc.trans_le (le_max_left c v)).ne')
  have H := (initial_weighted_limit (hc.trans hcd) g hg).sub (initial_weighted_limit hc g hg)
  have hi : (∫ v in (0:ℝ)..d,g v)-(∫ v in (0:ℝ)..c,g v) = ∫ v in c..d, f v/(v:ℂ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (μ := volume) 0 c)
      (hg.intervalIntegrable c d),add_sub_cancel_left]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hcd.le] at hv
    simp only [g,max_eq_right hv.1]
  rw [hi] at H
  apply H.congr
  intro h
  rw [← Finset.sum_sdiff_eq_sub (initial_subset hcd.le h)]
  apply Finset.sum_congr rfl
  intro p hp
  have hv := ((mem_added c d h p).mp hp).1
  simp only [g,max_eq_right hv.le,Complex.ofReal_div,Complex.ofReal_natCast]
  field_simp [Complex.ofReal_ne_zero.mpr (hc.trans hv).ne']

#print axioms mem_initial
#print axioms mem_added
#print axioms initial_weighted_limit
#print axioms intensity_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
