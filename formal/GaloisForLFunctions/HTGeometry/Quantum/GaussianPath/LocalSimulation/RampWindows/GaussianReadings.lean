import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.AffordableFraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.GaussianBoxMass

/-! # Fixed-date Gaussian tests on a physical time octave -/

open Filter Set Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
open PrescribedTimes PrescribedTimes.ResonantDraws SharpOccupation
open private mass_of_increments scalar_increment slope_le_radius from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.AffordableFraction
noncomputable section

/-- Equally spaced multipliers from one to two. -/
def readingScale (m : ℕ) (i : Fin (m+1)) : ℝ := 1+(i.val:ℝ)/m

private theorem upper_reading {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Icc (1:ℝ) 2) :
    ∃ i : Fin (m+1), u ≤ readingScale m i ∧ (m:ℝ)*(readingScale m i/u-1) ≤ 1 := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  let z := (u-1)*m
  have hz : 0 ≤ z := mul_nonneg (sub_nonneg.mpr hu.1) hm'.le
  have hzm : z ≤ (m:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith only [hu.2] : u-1 ≤ 1) hm'.le
  let i : Fin (m+1) := ⟨⌈z⌉₊, Nat.lt_succ_of_le (Nat.ceil_le.mpr hzm)⟩
  have hp : z ≤ (i.val:ℝ) := Nat.le_ceil _
  have hq : (i.val:ℝ) ≤ z+1 := (Nat.ceil_lt_add_one hz).le
  have h₁ : u-1 ≤ (i.val:ℝ)/m := (le_div_iff₀ hm').mpr hp
  refine ⟨i,by change u ≤ 1+(i.val:ℝ)/m; linarith only [h₁],?_⟩
  have hu' := zero_lt_one.trans_le hu.1
  change (m:ℝ)*((1+(i.val:ℝ)/m)/u-1) ≤ 1
  apply (le_of_mul_le_mul_right _ hu')
  field_simp [hm'.ne',hu'.ne']
  dsimp only [z] at hq
  nlinarith only [hq,hu.1]

private theorem sampled_ray_mean {ι : Type*} [Fintype ι] (E : Set (ι → ℝ))
    (hE : MeasurableSet E) :
    let m := Fintype.card ι + 1
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∃ i : Fin (m+1), (∫ x, rayMass 2 E x ∂μ) ≤
      exp 1 * μ.real ((fun x : ι → ℝ => readingScale m i • x) ⁻¹' E) := by
  classical
  intro m μ
  let q (u : ℝ) := μ.real ((fun x : ι → ℝ => u • x) ⁻¹' E)
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin (m+1) => q (readingScale m i)) Finset.univ_nonempty
  refine ⟨i,?_⟩
  let ν := volume.restrict (Icc (1:ℝ) 2)
  let S := (fun p : (ι → ℝ) × ℝ => p.2 • p.1) ⁻¹' E
  have hS : MeasurableSet S := hE.preimage (measurable_snd.smul measurable_fst)
  have hq : Integrable q ν := Integrable.of_bound
    (measurable_measure_prodMk_right (μ:=μ) hS).ennreal_toReal.aestronglyMeasurable 1
    (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg (μ:=μ))]
      exact measureReal_le_one)
  have he : ∀ᵐ u ∂ν, q u ≤ exp 1 * q (readingScale m i) := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Icc (a:=(1:ℝ)) (b:=2))] with u hu
    obtain ⟨j,hlo,hgap⟩ := upper_reading (m:=m) (Nat.succ_pos _) hu
    let c := readingScale m j/u
    have hu' := zero_lt_one.trans_le hu.1
    have hc : 1 ≤ c := (one_le_div hu').mpr hlo
    have hpow : c^(Fintype.card ι) ≤ exp 1 := by
      have hmajor := Real.add_one_le_exp (c-1)
      rw [sub_add_cancel] at hmajor
      refine (pow_le_pow_left₀ (zero_le_one.trans hc) hmajor _).trans ?_
      rw [← Real.exp_nat_mul, exp_le_exp]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ (Fintype.card ι) :
        (Fintype.card ι:ℝ) ≤ m) (sub_nonneg.mpr hc)).trans hgap
    let B := (fun x : ι → ℝ => u • x) ⁻¹' E
    have hpre : (fun x : ι → ℝ => c • x) ⁻¹' B = (fun x : ι → ℝ => readingScale m j • x) ⁻¹' E := by
      ext x
      change u • c • x ∈ E ↔ _
      rw [smul_smul,show u*c = readingScale m j by dsimp [c]; field_simp]
      rfl
    have hd := gaussian_dilation_comparison hc B (hE.preimage (measurable_id.const_smul u))
    rw [hpre] at hd
    exact hd.trans (mul_le_mul hpow (hi j (Finset.mem_univ _)) measureReal_nonneg (exp_pos _).le)
  have hmean := integral_mono_ae hq (integrable_const (exp 1*q (readingScale m i))) he
  have hunit : ν.real univ = 1 := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  rw [integral_const, hunit, one_smul] at hmean
  rw [integral_rayMass 2 E hE]
  exact hmean

private theorem capped_fraction {n d s : ℕ} (u : PathShell n)
    (hd : 128 ≤ d.sqrt) (hbox : ∀ l, |u l| ≤ 2*(d:ℝ)) {T a : ℝ}
    (hT : 0 < T) (ha : a ∈ Ioc (0:ℝ) 1) (hvol : ((n+2:ℕ):ℝ)*(1+T) ≤ (2:ℝ)^d) :
    let N := n+2
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    let b := ⌈a*(N:ℝ)*T⌉₊
    let m := Fintype.card (PathLabel n)
    (visitSet H s (1/10) ∩ Icc T (T+T)).Nonempty →
      a/(200*(1+(m:ℝ)*(2*d))*(2:ℝ)^(5*d.sqrt+17)) ≤ visitFraction H (s+b) (11/100) T (T+T) := by
  intro N H b m hit
  let F := (2:ℝ)^(5*d.sqrt+17)
  have hn : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hnorm : ‖H.val‖ ≤ (m:ℝ)*(2*d) := by
    change ‖pathHamiltonian u‖ ≤ _
    rw [pathHamiltonian_eq_sum]
    apply (norm_sum_le _ _).trans
    have hbound := Finset.sum_le_sum (s:=Finset.univ) fun l _ => hbox l
    simpa only [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hbound
  have hden : 200*(1+‖H.val‖)*F ≤ 200*(1+(m:ℝ)*(2*d))*F := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add (le_rfl : (1:ℝ) ≤ 1) hnorm) (by norm_num)) hF.le
  refine (div_le_div_of_nonneg_left ha.1.le (by positivity) hden).trans
    ((slope_le_radius (by dsimp [N]; omega) H ha hT d).trans ?_)
  let r := transportRadius H b d T
  have hr : 0 ≤ r := le_min hT.le
    ((by positivity : 0 ≤ 1/(100*(1+‖H.val‖))).trans (le_max_left ..))
  apply mass_of_increments H hT hr (min_le_left ..) _ hit
  intro v hv
  have hcur := hv.trans (min_le_right ..)
  rcases le_max_iff.mp hcur with hs | hl
  · exact approx_enlarge (scalar_increment H hs) le_rfl (Nat.zero_le _)
  · have hvT := hv.trans (min_le_left ..)
    obtain ⟨p,j,hj,he,hcost⟩ := binary_patch_schedule N d |v| (2*d) (abs_nonneg v)
      ((mul_le_mul_of_nonneg_left (add_le_add (le_rfl : (1:ℝ) ≤ 1) hvT) hn.le).trans hvol)
      hd (by positivity) le_rfl
    change |v| ≤ (b:ℝ)/(N*F)-1 at hl
    have hcap := (le_div_iff₀ (mul_pos hn hF)).mp (show 1+|v| ≤ (b:ℝ)/(N*F) by linarith only [hl])
    change ((j*(N*patchGateCost p 21):ℕ):ℝ) ≤ (N:ℝ)*(1+|v|)*F at hcost
    have hjb : j*(N*patchGateCost p 21) ≤ b := by
      exact_mod_cast (hcost.trans (show (N:ℝ)*(1+|v|)*F ≤ b by linarith only [hcap]))
    exact approx_enlarge (path_patch_circuit_abs u (2*d) (by positivity) hbox p j hj v) he hjb

/-- The probability of any short circuit anywhere in the octave is bounded
by a Gaussian coefficient tail and one of a fixed grid of single-date
probabilities. The number of dates is the coefficient dimension plus two. -/
theorem gaussian_ramp_window_probability (n s d : ℕ) (hd : 128 ≤ d.sqrt) {T a : ℝ}
    (hT : 0 < T) (ha : a ∈ Ioc (0:ℝ) 1) (hvol : ((n+2:ℕ):ℝ)*(1+T) ≤ (2:ℝ)^d) :
    let N := n+2
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let m := Fintype.card (PrefixIndex n)+1
    let b := ⌈a*(N:ℝ)*T⌉₊
    let L := 200*(1+(Fintype.card (PathLabel n):ℝ)*(2*d))*(2:ℝ)^(5*d.sqrt+17)
    ∃ i : Fin (m+1), μ.real (prescribedWindowEvent n s T T) ≤
      2*(Fintype.card (PrefixIndex n):ℝ)*exp (-2*(d:ℝ)^2) + L/a*exp 1*
        μ.real {x | pathGateDistance n (s+b) x (readingScale m i*T) ≤ 11/100} := by
  classical
  intro N μ m b L
  let E := {x | pathGateDistance n (s+b) x T ≤ 11/100}
  have hE : MeasurableSet E := measurableSet_Iic.preimage (continuous_distance_at_time n (s+b) T).measurable
  let A : Set (PrefixIndex n → ℝ) := {x | ∃ j, 2*(d:ℝ) < |x j|}
  let W := prescribedWindowEvent n s T T
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨i,hi⟩ := sampled_ray_mean E hE
  refine ⟨i,?_⟩
  let f := rayMass 2 E
  have hunit : (volume.restrict (Icc (1:ℝ) 2)).real univ = 1 := by
    rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  have hf₀ (x) : 0 ≤ f x := measureReal_nonneg
  have hfi : Integrable f μ := Integrable.of_bound (measurable_rayMass 2 hE).aestronglyMeasurable 1
    (ae_of_all _ fun x => (Real.norm_of_nonneg (hf₀ x)).le.trans ((measureReal_mono (subset_univ _)).trans_eq hunit))
  have hsubset : W ⊆ A ∪ {x | a/L ≤ f x} := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    right
    let u : PathShell n := WithLp.toLp 2 fun l => x ((pathCoeffEquiv n).symm l)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    have hgen : numberedGenerator n x = H.val := by
      simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
    have hbox (l) : |u l| ≤ 2*(d:ℝ) := le_of_not_gt fun h => hxA ⟨_,h⟩
    obtain ⟨t,ht,hfit⟩ := hx
    rw [hgen] at hfit
    have hmass := capped_fraction (s:=s) u hd hbox hT ha hvol ⟨t,hfit,ht⟩
    have hcov (c : ℝ) (_ : 0<c) (_ : PrefixIndex n → ℝ) : c*(0:ℝ)=0 := mul_zero _
    have he : f x = visitFraction H (s+b) (11/100) T (T+T) := by
      have hr := rayMass_of_covariant_origin n (s+b) (fun _ => 0) hcov x 2 T (11/100)
      simp only [zero_add] at hr
      rw [dilation_interval_volume _ _ _ hT, one_mul, two_mul] at hr
      have hset : {v | pathGateDistance n (s+b) x v ≤ 11/100} = visitSet H (s+b) (11/100) := by
        ext v
        change pathGateDistance n (s+b) x v ≤ 11/100 ↔
          HasProjectiveCircuitApproximation N (11/100) (s+b) (unitaryEvolution H.val v)
        rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hgen]
      rw [hset] at hr
      simpa only [f,E,visitFraction,add_sub_cancel_left,div_eq_inv_mul] using hr
    change a/L ≤ f x
    rw [he]
    exact hmass
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hf₀) hfi (a/L)
  have hp : μ.real {x | a/L ≤ f x} ≤ L/a*(∫ x, f x ∂μ) := by
    have hi' := mul_le_mul_of_nonneg_left hmark (div_nonneg hL.le ha.1.le)
    rwa [← mul_assoc,show L/a*(a/L)=1 by field_simp [ha.1.ne',hL.ne'],one_mul] at hi'
  have heq : (fun x : PrefixIndex n → ℝ => readingScale m i • x) ⁻¹' E =
      {x | pathGateDistance n (s+b) x (readingScale m i*T) ≤ 11/100} := by
    ext x
    exact congrArg (· ≤ 11/100) (distance_dilate n (s+b) _ x T) |>.to_iff
  rw [heq] at hi
  have htail : μ.real A ≤ 2*(Fintype.card (PrefixIndex n):ℝ)*exp (-2*(d:ℝ)^2) := by
    let B (j : PrefixIndex n) := {x : PrefixIndex n → ℝ | 2*(d:ℝ) ≤ |x j|}
    have hB (j : PrefixIndex n) : μ.real (B j) ≤ 2*exp (-2*(d:ℝ)^2) := by
      have hmap := measurePreserving_eval (fun _ : PrefixIndex n => gaussianReal 0 1) j
      have h := measureReal_abs_ge_le_of_standardGaussian hmap.measurable.aemeasurable hmap.map_eq
        (by positivity : 0 ≤ 2*(d:ℝ))
      rwa [show -(2*(d:ℝ))^2/2 = -2*(d:ℝ)^2 by ring] at h
    have hsub : A ⊆ ⋃ j, B j := fun _ ⟨j,hj⟩ => mem_iUnion.mpr ⟨j,hj.le⟩
    refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le B).trans
      ((Finset.sum_le_sum (s:=Finset.univ) fun j _ => hB j).trans_eq ?_))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add htail (hp.trans ((mul_le_mul_of_nonneg_left hi (div_nonneg hL.le ha.1.le)).trans_eq
      (mul_assoc ..).symm))))

#print axioms gaussian_ramp_window_probability

end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
