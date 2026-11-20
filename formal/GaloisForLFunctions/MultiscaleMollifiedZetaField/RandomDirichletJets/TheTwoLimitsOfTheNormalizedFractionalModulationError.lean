import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheContinuousProfileOfTheFractionalModulationEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The fraction of the worst-case modulation energy seen by the Möbius row

At small relative bandwidth the normalized symbol approaches the linear
function t. At large bandwidth it approaches t^s. The squarefree modes
sample the uniform logarithmic coordinate. Their mean-square error thus
occupies one third or 1/(2s+1) of the worst possible value in these two
limits.
-/

noncomputable section
open Filter Topology MeasureTheory Set
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

private def gain (s q t : ℝ) := (1+q*t)^s-1
private def shape (s q t : ℝ) := (gain s q t/gain s q 1)^2

private theorem gain_top_pos {s q : ℝ} (hs : 0 < s) (hq : 0 < q) : 0 < gain s q 1 := by
  simp only [gain,mul_one,sub_pos]
  exact Real.one_lt_rpow (by linarith only [hq]) hs

private theorem shape_integral_limit {l : Filter ℝ} [l.IsCountablyGenerated] {s : ℝ} (hs : 0 < s)
    (hpos : ∀ᶠ q in l, 0 < q) (f : ℝ → ℝ)
    (hlim : ∀ t ∈ Icc (0:ℝ) 1, Tendsto (fun q => gain s q t/gain s q 1) l (𝓝 (f t))) :
    Tendsto (fun q => ∫ t in (0:ℝ)..1, shape s q t) l (𝓝 (∫ t in (0:ℝ)..1, (f t)^2)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
  · exact Eventually.of_forall fun q => by
      have hbase : Continuous (fun t : ℝ => 1+q*t) := by fun_prop
      have hc : Continuous (fun t : ℝ => (((1+q*t)^s-1)/gain s q 1)^2) :=
        (((hbase.rpow_const (fun _ => Or.inr hs.le)).sub (continuous_const (y:=(1:ℝ)))).div_const
          (gain s q 1)).pow 2
      exact hc.aestronglyMeasurable
  · filter_upwards [hpos] with q hq
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hden := gain_top_pos hs hq
    have h0 := Real.one_le_rpow (le_add_of_nonneg_right (mul_nonneg hq.le ht.1.le)) hs.le
    have hm : gain s q t ≤ gain s q 1 := sub_le_sub_right (Real.rpow_le_rpow
      (add_nonneg zero_le_one (mul_nonneg hq.le ht.1.le))
      (add_le_add (le_refl (1:ℝ)) (mul_le_mul_of_nonneg_left ht.2 hq.le)) hs.le) _
    have hr0 : 0 ≤ gain s q t/gain s q 1 := div_nonneg (sub_nonneg.mpr h0) hden.le
    rw [shape,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ hr0 ((div_le_one hden).mpr hm)
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    exact (hlim t ⟨ht.1.le,ht.2⟩).pow 2

private theorem gain_deriv (s t : ℝ) : HasDerivAt (fun q => gain s q t) (t*s) 0 := by
  have hl : HasDerivAt (fun q : ℝ => 1+q*t) t 0 := by
    simpa only [one_mul] using ((hasDerivAt_id' (0:ℝ)).mul_const t).const_add 1
  have h := (hl.rpow_const (p:=s) (Or.inl (by norm_num))).sub_const 1
  simpa only [gain,zero_mul,add_zero,Real.one_rpow,mul_one] using h

private theorem shape_small_bandwidth {s : ℝ} (hs : 0 < s) :
    Tendsto (fun q => ∫ t in (0:ℝ)..1, shape s q t) (𝓝[>] 0) (𝓝 (1/3)) := by
  have h (t : ℝ) : Tendsto (fun q : ℝ => q⁻¹*gain s q t) (𝓝[>] 0) (𝓝 (t*s)) := by
    simpa only [zero_add,smul_eq_mul,show gain s 0 t=0 by simp [gain],sub_zero] using (gain_deriv s t).tendsto_slope_zero_right
  have hlim (t : ℝ) (_ : t ∈ Icc (0:ℝ) 1) : Tendsto (fun q => gain s q t/gain s q 1) (𝓝[>] 0) (𝓝 t) := by
    have hh := (h t).div (h 1) (mul_ne_zero one_ne_zero hs.ne')
    simp only [one_mul,mul_div_cancel_right₀ _ hs.ne'] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin (a:=0) (s:=Ioi (0:ℝ))] with q hq
    exact mul_div_mul_left _ _ (inv_ne_zero hq.ne')
  have H := shape_integral_limit (l:=𝓝[>] (0:ℝ)) hs self_mem_nhdsWithin id hlim
  have hi : (∫ t in (0:ℝ)..1,t^2)=(1/3:ℝ) := by norm_num [integral_pow]
  simpa only [id_eq,hi] using H

private theorem shape_large_bandwidth {s : ℝ} (hs : 0 < s) :
    Tendsto (fun q => ∫ t in (0:ℝ)..1, shape s q t) atTop (𝓝 (1/(2*s+1))) := by
  have hq : Tendsto (fun q : ℝ => q⁻¹) atTop (𝓝 0) := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).inv_tendsto_atTop
  have ht (t : ℝ) : Tendsto (fun q : ℝ => (q⁻¹+t)^s-(q⁻¹)^s) atTop (𝓝 (t^s)) := by
    have H := ((hq.add_const t).rpow_const (p:=s) (Or.inr hs.le)).sub (hq.rpow_const (p:=s) (Or.inr hs.le))
    simpa only [zero_add,Real.zero_rpow hs.ne',sub_zero] using H
  have hlim (t : ℝ) (hu : t ∈ Icc (0:ℝ) 1) : Tendsto (fun q => gain s q t/gain s q 1) atTop (𝓝 (t^s)) := by
    have H := (ht t).div (ht 1) (by rw [Real.one_rpow]; exact one_ne_zero)
    simp only [Real.one_rpow,div_one] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq0
    have he (u : ℝ) (hu0 : 0 ≤ u) : gain s q u=q^s*((q⁻¹+u)^s-(q⁻¹)^s) := by
      rw [gain,mul_sub,←Real.mul_rpow hq0.le (add_nonneg (inv_nonneg.mpr hq0.le) hu0),
        ←Real.mul_rpow hq0.le (inv_nonneg.mpr hq0.le),mul_add,mul_inv_cancel₀ hq0.ne',Real.one_rpow]
    rw [Pi.div_apply,he t hu.1,he 1 zero_le_one,mul_div_mul_left _ _ (Real.rpow_pos_of_pos hq0 s).ne']
  have H := shape_integral_limit hs (eventually_gt_atTop (0:ℝ)) (fun t => t^s) hlim
  have he : (∫ t in (0:ℝ)..1,(t^s)^2)=∫ t in (0:ℝ)..1,t^(2*s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    calc (t^s)^2 = t^(s*(2:ℕ)) := by rw [Real.rpow_mul ht.1,Real.rpow_natCast]
      _ = t^(2*s) := by congr 1; push_cast; ring
  have hh : 0 < 2*s+1 := by positivity
  rw [he,integral_rpow (Or.inl (by linarith only [hs] : -1 < 2*s)),Real.one_rpow,Real.zero_rpow hh.ne',sub_zero] at H
  exact H

/-- At every positive finite limiting bandwidth, the full continuum
profile persists when carrier, section length and fractional order move together. -/
theorem moebius_modulation_limit_of_order_and_bandwidth (M N : ℕ → ℕ) (order : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 2 ≤ N k) (hcutoff : Tendsto N atTop atTop)
    (ho : ∀ k, 0 ≤ order k) {s q : ℝ} (hq : 0 < q)
    (hs' : Tendsto order atTop (𝓝 s))
    (hq' : Tendsto (fun k => Real.log (N k)/Real.log (M k)) atTop (𝓝 q)) :
    Tendsto (fun k => relativeMoebiusModulationEnergy (order k) (M k) (N k)) atTop
      (𝓝 (((1+q)^(2*s+1)-1)/(q*(2*s+1))-2*(((1+q)^(s+1)-1)/(q*(s+1)))+1)) := by
  let Q (k : ℕ) := Real.log (N k)/Real.log (M k)
  let J (k : ℕ) := ∫ t in (0:ℝ)..1, modulationResponse (order k) (Q k) t
  have hs : 0 ≤ s := ge_of_tendsto hs' (Eventually.of_forall ho)
  have hQ (k : ℕ) : 0 < Q k := div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < N k by have := hN k; omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < M k by have := hM k; omega)))
  have hb : 1+q ≠ 0 := (add_pos zero_lt_one hq).ne'
  have hbase : Tendsto (fun k => 1+Q k) atTop (𝓝 (1+q)) :=
    (tendsto_const_nhds (x:=(1:ℝ))).add hq'
  let F (a b : ℝ) := ((1+b)^(a+1)-1)/(b*(a+1))
  have hf (p : ℕ → ℝ) {v : ℝ} (hv : 0 ≤ v) (hp : Tendsto p atTop (𝓝 v)) :
      Tendsto (fun k => F (p k) (Q k)) atTop (𝓝 (F v q)) :=
    ((hbase.rpow (hp.add_const 1) (Or.inl hb)).sub_const 1).div (hq'.mul (hp.add_const 1))
      (mul_pos hq (by positivity)).ne'
  have hJ := ((hf (fun k => 2*order k) (mul_nonneg zero_le_two hs) (hs'.const_mul 2)).sub
    ((hf order hs hs').const_mul 2)).add_const 1
  have hD := tendsto_squarefree_harmonic_diagonal_atTop N (fun k => by have := hN k; omega) hcutoff
  have htop := ((hbase.rpow hs' (Or.inl hb)).sub_const 1).pow 2
  have hzero := (hD.inv_tendsto_atTop.const_mul (24+|squarefreeHarmonicConstant|)).mul htop
  have he : Tendsto (fun k => relativeMoebiusModulationEnergy (order k) (M k) (N k)-J k) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_) (by simpa only [mul_zero,zero_mul] using hzero)
    simpa only [J,Q,Real.norm_eq_abs,Pi.inv_apply,div_eq_mul_inv,fractionalModulationLoss] using
      moebius_modulation_continuum_error (ho k) (hM k) (hN k)
  have H := he.add (hJ.congr (f₂:=J) fun k => (modulation_response_integral (ho k) (hQ k)).symm)
  simpa only [zero_add,sub_add_cancel,F] using H

/-- The actual arithmetic row occupies a definite fraction of the
worst-case mean-square error at both ends of the bandwidth scale. -/
theorem normalized_moebius_modulation_extremes {s : ℝ} (hs : 0 < s) (M N : ℕ → ℕ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 2 ≤ N k) (hcutoff : Tendsto N atTop atTop) :
    let q := fun k => Real.log (N k)/Real.log (M k)
    let E := fun k => relativeMoebiusModulationEnergy s (M k) (N k)/(fractionalModulationLoss s (M k) (N k))^2
    (Tendsto q atTop (𝓝 0) → Tendsto E atTop (𝓝 (1/3))) ∧
    (Tendsto q atTop atTop → Tendsto E atTop (𝓝 (1/(2*s+1)))) := by
  intro q E
  let A (k : ℕ) := ∫ t in (0:ℝ)..1, shape s (q k) t
  have hq (k : ℕ) : 0 < q k := div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < N k by have := hN k; omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < M k by have := hM k; omega)))
  have hH := tendsto_squarefree_harmonic_diagonal_atTop N (fun k => by have := hN k; omega) hcutoff
  have hdiff : Tendsto (fun k => E k-A k) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (by simpa only [mul_zero] using hH.inv_tendsto_atTop.const_mul (24+|squarefreeHarmonicConstant|))
    intro k
    let r := fractionalModulationLoss s (M k) (N k)
    have hr : gain s (q k) 1=r := by simp only [gain,mul_one,q,r,fractionalModulationLoss]
    have hpos : 0 < r^2 := sq_pos_of_pos (hr ▸ gain_top_pos hs (hq k))
    have ha : A k=(∫ t in (0:ℝ)..1, modulationResponse s (q k) t)/r^2 := by
      calc A k = (∫ t in (0:ℝ)..1, (gain s (q k) t)^2)/(gain s (q k) 1)^2 := by
             simp only [A,shape,div_pow,intervalIntegral.integral_div]
        _ = _ := congrArg (fun z : ℝ => (∫ t in (0:ℝ)..1, (gain s (q k) t)^2)/z^2) hr
    change ‖relativeMoebiusModulationEnergy s (M k) (N k)/r^2-A k‖ ≤ _
    rw [ha,←sub_div,Real.norm_eq_abs,abs_div,abs_of_pos hpos,div_le_iff₀ hpos]
    simpa only [q,r,Pi.inv_apply,div_eq_mul_inv] using moebius_modulation_continuum_error hs.le (hM k) (hN k)
  constructor
  · intro h
    have h' : Tendsto q atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h,Eventually.of_forall hq⟩
    have hd := hdiff.add (shape_small_bandwidth hs |>.comp h')
    simpa only [zero_add,sub_add_cancel,Function.comp_apply,A] using hd
  · intro h
    have hd := hdiff.add (shape_large_bandwidth hs |>.comp h)
    simpa only [zero_add,sub_add_cancel,Function.comp_apply,A] using hd

#print axioms moebius_modulation_limit_of_order_and_bandwidth
#print axioms normalized_moebius_modulation_extremes

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
