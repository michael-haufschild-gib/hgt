import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.ScalarProbes
import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture

/-! # Exponential law for the number of late prime observations before a scalar fit -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation
noncomputable section

private theorem small_arc_mass {x : ℝ} (hx : x∈Ioo (0:ℝ) 1) :
    let D (k : ℕ) := (2:ℕ)^(k+3)
    Tendsto (fun k => (D k:ℝ)*x^(D k-1)) atTop (𝓝 0) := by
  intro D
  have hd : Tendsto D atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ))).comp
    (tendsto_add_atTop_nat 3)
  have hh := ((tendsto_self_mul_const_pow_of_lt_one hx.1.le hx.2).comp hd).div_const x
  rw [zero_div] at hh
  apply hh.congr
  intro k
  change (D k:ℝ)*x^(D k)/x=_
  have he : x^(D k)=x^(D k-1)*x := by rw [←pow_succ,Nat.sub_add_cancel (Nat.one_le_two_pow)]
  rw [he,←mul_assoc,mul_div_cancel_right₀ _ hx.1.ne']

/-- Bernoulli survival at a fixed multiple of its inverse success probability. -/
private theorem scaled_miss_limit (p : ℕ→ℝ) (hp : ∀ k, 0<p k)
    (hz : Tendsto p atTop (𝓝 0)) {a : ℝ} (ha : 0≤a) :
    let q (k : ℕ) := ⌊a/p k⌋₊
    Tendsto (fun k => (1-p k)^(q k)) atTop (𝓝 (Real.exp (-a))) := by
  intro q
  have hq : Tendsto (fun k => (q k:ℝ)*p k) atTop (𝓝 a) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa only [sub_zero] using hz.const_sub a) tendsto_const_nhds
    · intro k
      have hh := (div_lt_iff₀ (hp k)).mp (Nat.lt_floor_add_one (a/p k))
      linarith only [hh]
    · intro k
      exact (le_div_iff₀ (hp k)).mp (Nat.floor_le (div_nonneg ha (hp k).le))
  have hl := (hq.div (hz.const_sub 1) (by norm_num : (1:ℝ)-0≠0)).neg
  have hu := hq.neg
  simp only [sub_zero,div_one] at hl
  have hlog : Tendsto (fun k => (q k:ℝ)*Real.log (1-p k)) atTop (𝓝 (-a)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    all_goals filter_upwards [hz.eventually_lt_const zero_lt_one] with k hk
    · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hk))
      rw [Real.log_inv] at h
      have hid : (1-p k)⁻¹-1=p k/(1-p k) := by field_simp [(sub_pos.mpr hk).ne']; ring
      rw [hid] at h
      have h' := mul_le_mul_of_nonneg_left (neg_le.mp h) (Nat.cast_nonneg (q k))
      change -((q k:ℝ)*p k/(1-p k)) ≤ (q k:ℝ)*Real.log (1-p k)
      simpa only [mul_neg,mul_div_assoc] using h'
    · have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hk)
      have h' : Real.log (1-p k)≤ -p k := by linarith only [h]
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg (q k))
  apply (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr'
  filter_upwards [hz.eventually_lt_const zero_lt_one] with k hk
  exact (Real.exp_nat_mul _ _).trans (by rw [Real.exp_log (sub_pos.mpr hk)])

/-- At q=floor(a/p) distinct prime delays after the actual crossing or
first low-budget return, the conditional probability of no scalar fit
tends to exp(-a). Delay tends to infinity before register length. -/
theorem exponential_first_scalar_reading (r : ℕ) (afterReturn : Bool) {ε a : ℝ}
    (hε : ε∈Ioo (0:ℝ) (Real.sqrt 2)) (ha : 0≤a) :
    let D (k : ℕ) := (2:ℕ)^(k+3)
    let p (k : ℕ) := (D k:ℝ)*physicalArc ε^(D k-1)
    ∃ L : ℕ→ℝ, Tendsto L atTop (𝓝 (Real.exp (-a))) ∧
      ∀ k : ℕ, let n := k+1
        let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
        let P := nearHilbertContinuousCircuitBudget (k+3)
        let σ := crossingOrigin n P (9/80)
        let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
        ∀ S : Finset Nat.Primes, S.card=⌊a/p k⌋₊ →
          ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
          Tendsto (fun t => μ.real (B ∩ {x | ∀ j : S,
            ε<pathGateDistance n 0 x (o x+Real.log ((j.val:ℕ):ℝ)*t)})) atTop (𝓝 (μ.real B*L k)) := by
  classical
  intro D p
  have hx := (physicalArc_spec hε.1 hε.2).1
  have hp (k : ℕ) : 0<p k := mul_pos (by exact_mod_cast Nat.two_pow_pos (k+3)) (pow_pos hx.1 _)
  have hz : Tendsto p atTop (𝓝 0) := small_arc_mass ⟨hx.1,hx.2.trans (by norm_num)⟩
  refine ⟨_,scaled_miss_limit p hp hz ha,?_⟩
  intro k n μ P σ o S hS B hB
  let c (j : S) := Real.log ((j.val:ℕ):ℝ)
  have hc : RationallyIndependentFrequency c := rationallyIndependentFrequency_of_linearIndependent_int
    (GaloisForLFunctions.logPrime_linearIndependent_int.comp Subtype.val Subtype.val_injective)
  have h := scalar_probe_pattern k r hε c hc afterReturn (fun _ => false) B hB
  simpa only [Bool.false_eq_true,iff_false,not_le,if_false,Finset.prod_const,Finset.card_univ,Fintype.card_coe,hS] using h

#print axioms exponential_first_scalar_reading
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
