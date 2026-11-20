import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheSquarefreeDistributionOfTheModulationError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Continuous profile of the critical Möbius modulation energy

Each squarefree mode is an atom at log n / log N. Integrating the
discrepancy of their cumulative distribution against the derivative of a
response transfers the quantile estimate to the observed energy. The
error is relative to the range of the response and is uniform in carrier
and fractional order.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

/-- Integrating a finite cumulative distribution against a nonnegative
slope controls every increasing absolutely continuous response by its range. -/
private theorem mean_error_of_quantile_bound {ι : Type*} (S : Finset ι) (a x : ι → ℝ)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc (0:ℝ) 1) (ha : ∑ i ∈ S, a i = 1) {ε : ℝ}
    (hε : ∀ u ∈ Set.Icc (0:ℝ) 1, |(∑ i ∈ S.filter (fun i => x i ≤ u), a i)-u| ≤ ε)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Icc 0 1))
    (hw0 : ∀ u ∈ Set.Icc (0:ℝ) 1, 0 ≤ w u) :
    |(∑ i ∈ S, a i*(∫ u in (0:ℝ)..x i, w u)) - (∫ u in (0:ℝ)..1, (1-u)*w u)| ≤
      ε*(∫ u in (0:ℝ)..1, w u) := by
  classical
  let f (i : ι) (t : ℝ) := a i*(Set.Iio (x i)).indicator w t
  let g (t : ℝ) := (1-t)*w t
  have hwI := hw.intervalIntegrable_of_Icc (μ:=volume) zero_le_one
  have hfI (i : ι) : IntervalIntegrable (f i) volume 0 1 :=
    (intervalIntegrable_iff.mpr (hwI.def'.indicator measurableSet_Iio)).const_mul (a i)
  have hgI : IntervalIntegrable g volume 0 1 := ((continuous_const.sub continuous_id).continuousOn.mul hw).intervalIntegrable_of_Icc zero_le_one
  have hi (i : ι) (hi : i ∈ S) : (∫ t in (0:ℝ)..1, f i t) = a i*(∫ t in (0:ℝ)..x i, w t) := by
    rw [show (∫ t in (0:ℝ)..1, f i t)=a i*(∫ t in (0:ℝ)..1, (Set.Iio (x i)).indicator w t) from
      intervalIntegral.integral_const_mul _ _]
    congr 1
    refine (intervalIntegral.integral_congr_ae ?_).trans (intervalIntegral.integral_indicator (hx i hi))
    filter_upwards [MeasureTheory.Iio_ae_eq_Iic (a:=x i) (μ:=volume)] with t ht
    intro _
    change (Set.Iio (x i)).indicator w t = (Set.Iic (x i)).indicator w t
    by_cases h : t ∈ Set.Iio (x i)
    · have h' : t ∈ Set.Iic (x i) := ht.mp h
      rw [Set.indicator_of_mem h,Set.indicator_of_mem h']
    · have h' : t ∉ Set.Iic (x i) := fun hh => h (ht.mpr hh)
      rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h']
  have hrep : (∑ i ∈ S, a i*(∫ t in (0:ℝ)..x i, w t)) = ∫ t in (0:ℝ)..1, ∑ i ∈ S, f i t := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hfI i)]
    exact sum_congr rfl fun i hi' => (hi i hi').symm
  have hsumI : IntervalIntegrable (fun t => ∑ i ∈ S, f i t) volume 0 1 := by
    rw [show (fun t => ∑ i ∈ S, f i t) = ∑ i ∈ S, f i by
      funext t
      exact (Finset.sum_apply t S f).symm]
    exact IntervalIntegrable.sum S (fun i _ => hfI i)
  rw [hrep]
  change |(∫ t in (0:ℝ)..1, ∑ i ∈ S, f i t)-(∫ t in (0:ℝ)..1, g t)| ≤ _
  rw [←intervalIntegral.integral_sub hsumI hgI,←intervalIntegral.integral_const_mul,←Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ (hwI.const_mul ε)
  apply Eventually.of_forall
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  let P := S.filter (fun i => x i ≤ t)
  let Q := S.filter (fun i => ¬x i ≤ t)
  have hPQ : (∑ i ∈ P, a i) + ∑ i ∈ Q, a i = 1 :=
    (sum_filter_add_sum_filter_not S _ a).trans ha
  have hsum : (∑ i ∈ S, f i t) = (∑ i ∈ Q, a i)*w t := by
    rw [sum_mul,sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases h : t < x i
    · simp only [f,Set.indicator_of_mem (show t ∈ Set.Iio (x i) from h),if_pos (not_le.mpr h)]
    · simp only [f,Set.indicator_of_notMem (show t ∉ Set.Iio (x i) from h),mul_zero,
        if_neg (not_not_intro (le_of_not_gt h))]
  rw [hsum,Real.norm_eq_abs]
  have he : (∑ i ∈ Q, a i)*w t - g t = (t-(∑ i ∈ P, a i))*w t := by
    dsimp only [g]
    rw [show (∑ i ∈ Q, a i)=1-∑ i ∈ P, a i by linarith only [hPQ]]
    ring
  rw [he,abs_mul,abs_of_nonneg (hw0 t ht'),abs_sub_comm]
  exact mul_le_mul_of_nonneg_right (hε t ht') (hw0 t ht')

/-- Logarithmic coordinate of an arithmetic mode within the section. -/
private def position (N n : ℕ) := Real.log n/Real.log N

private theorem pos_le {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n) (t : ℝ) :
    position N n ≤ t ↔ (n:ℝ) ≤ (N:ℝ)^t := by
  have h := Real.log_pos (by exact_mod_cast (show 1 < N by omega) : (1:ℝ)<N)
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  rw [position,div_le_iff₀ h,←Real.log_rpow hN0,Real.log_le_log_iff hn0 (Real.rpow_pos_of_pos hN0 _)]

/-- Every increasing response of the logarithmic frequency has the uniform
continuum average, with an error bounded by its total variation times
the inverse squarefree harmonic mass. -/
theorem squarefree_response_average (N : ℕ) (hN : 2 ≤ N) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Icc 0 1)) (hw0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ w t) :
    |(∑ n ∈ Icc 1 N, (criticalMoebiusMass n/harmonicMoebiusDiagonal N)*
      (∫ u in (0:ℝ)..(Real.log n/Real.log N), w u)) - (∫ u in (0:ℝ)..1,(1-u)*w u)| ≤
      ((24+|squarefreeHarmonicConstant|)/harmonicMoebiusDiagonal N)*(∫ u in (0:ℝ)..1, w u) := by
  let H := harmonicMoebiusDiagonal N
  have hN1 : 1 ≤ N := by omega
  have hH : 0 < H := harmonicMoebiusDiagonal_pos_of_one_le hN1
  apply mean_error_of_quantile_bound (Icc 1 N) (fun n => criticalMoebiusMass n/H) (position N) _ _ _ w hw hw0
  · intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hR := Real.log_nonneg (Nat.one_le_cast.mpr hn1)
    exact ⟨div_nonneg hR (Real.log_nonneg (Nat.one_le_cast.mpr hN1)),
      (pos_le hN hn1 1).mpr (by rw [Real.rpow_one]; exact_mod_cast (mem_Icc.mp hn).2)⟩
  · rw [←sum_div,←harmonicMoebiusDiagonal_at_nat,div_self hH.ne']
  · intro t ht
    have hD := (uniform_squarefree_quantile_discrepancy (s:=1) zero_lt_one (M:=2) le_rfl hN1).2 t ht
    have hN' := (Nat.one_le_cast (α:=ℝ)).mpr hN1
    have htop := Real.rpow_le_self_of_one_le hN' ht.2
    have h0 := Real.rpow_nonneg (zero_le_one.trans hN') t
    have hfilter : (Icc 1 N).filter (fun n => position N n ≤ t)=Icc 1 ⌊(N:ℝ)^t⌋₊ := by
      apply Finset.ext
      intro n
      simp only [mem_filter,mem_Icc]
      constructor
      · rintro ⟨⟨h,_⟩,hh⟩
        exact ⟨h,(Nat.le_floor_iff h0).mpr ((pos_le hN h t).mp hh)⟩
      · rintro ⟨h,hh⟩
        have ha := (Nat.le_floor_iff h0).mp hh
        exact ⟨⟨h,Nat.cast_le.mp (ha.trans htop)⟩,(pos_le hN h t).mpr ha⟩
    rw [squarefree_modulation_quantile _ zero_lt_one le_rfl hN1 ht] at hD
    rw [←sum_div,hfilter]
    exact hD

/-- Squared multiplier response on the unit interval at relative bandwidth q. -/
def modulationResponse (s q t : ℝ) := ((1+q*t)^s-1)^2

private def responseSlope (s q t : ℝ) :=
  2*((1+q*t)^s-1)*(q*s*(1+q*t)^(s-1))

private theorem response_deriv {s q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    HasDerivAt (modulationResponse s q) (responseSlope s q t) t := by
  have hb : 0 < 1+q*t := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq ht)
  have hlin : HasDerivAt (fun x : ℝ => 1+q*x) q t := by
    simpa only [mul_one] using ((hasDerivAt_id' t).const_mul q).const_add 1
  have h := (((hlin.rpow_const (p:=s) (Or.inl hb.ne')).sub_const 1).pow 2)
  have hf : ((fun x : ℝ => (1+q*x)^s-1)^2)=modulationResponse s q := by
    funext x
    exact Pi.pow_apply _ _ _
  rw [hf] at h
  simpa only [responseSlope,Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one] using h

/-- Relative error in the observed energy is at most the squarefree
quantile discrepancy times the largest possible squared multiplier loss.
The estimate remains valid when both fractional order and carrier vary. -/
theorem moebius_modulation_continuum_error {s : ℝ} (hs : 0 ≤ s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 2 ≤ N) :
    let q := Real.log N/Real.log M
    |relativeMoebiusModulationEnergy s M N-(∫ t in (0:ℝ)..1, modulationResponse s q t)| ≤
      (24+|squarefreeHarmonicConstant|)/harmonicMoebiusDiagonal N*(fractionalModulationLoss s M N)^2 := by
  intro q
  have hLM := Real.log_pos (by exact_mod_cast (show 1 < M by omega) : (1:ℝ)<M)
  have hLN := Real.log_pos (by exact_mod_cast (show 1 < N by omega) : (1:ℝ)<N)
  have hq : 0 ≤ q := (div_pos hLN hLM).le
  let F := modulationResponse s q
  let w := responseSlope s q
  have hbase (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 1 ≤ 1+q*t := le_add_of_nonneg_right (mul_nonneg hq ht.1)
  have hlin : Continuous (fun t : ℝ => 1+q*t) := by fun_prop
  have hcont (v : ℝ) : ContinuousOn (fun t : ℝ => (1+q*t)^v) (Set.Icc 0 1) :=
    hlin.continuousOn.rpow_const fun t ht => Or.inl (zero_lt_one.trans_le (hbase t ht)).ne'
  have hw : ContinuousOn w (Set.Icc 0 1) :=
    (continuousOn_const.mul ((hcont s).sub continuousOn_const)).mul (continuousOn_const.mul (hcont (s-1)))
  have hw0 (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ w t :=
    mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr (Real.one_le_rpow (hbase t ht) hs)))
      (mul_nonneg (mul_nonneg hq hs) (Real.rpow_nonneg (zero_le_one.trans (hbase t ht)) _))
  have hF0 : F 0=0 := by simp [F,modulationResponse]
  have hF1 : F 1=(fractionalModulationLoss s M N)^2 := by simp only [F,modulationResponse,q,mul_one,fractionalModulationLoss]
  have hF (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : (∫ u in (0:ℝ)..t,w u)=F t := by
    have hsub : Set.Icc 0 t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc_right ht.2
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (f:=F)
      (f':=w) (fun u hu => response_deriv hq ((Set.uIcc_of_le ht.1 ▸ hu).1))
      ((hw.mono hsub).intervalIntegrable_of_Icc ht.1)
    simpa only [hF0,sub_zero] using h
  have hint := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a:=0) (b:=1)
    (u:=fun t : ℝ => 1-t) (u':=fun _ => -1) (v:=F) (v':=w)
    (continuous_const.sub continuous_id).continuousOn
    (by rw [Set.uIcc_of_le zero_le_one]; exact ((hcont s).sub continuousOn_const).pow 2)
    (fun t _ => by simpa only [neg_one_mul] using (hasDerivAt_id' t).const_sub 1)
    (fun t ht => response_deriv hq (by simpa only [min_eq_left zero_le_one] using ht.1.le))
    intervalIntegrable_const (hw.intervalIntegrable_of_Icc zero_le_one)
  simp only [sub_self,zero_mul,sub_zero,one_mul,hF0,neg_one_mul,intervalIntegral.integral_neg,zero_sub,neg_neg] at hint
  have ha := squarefree_response_average N hN w hw hw0
  have he (n : ℕ) (hn : n ∈ Icc 1 N) : (∫ u in (0:ℝ)..(Real.log n/Real.log N),w u) =
      (fractionalModulationLoss s M n)^2 := by
    have hh := mem_Icc.mp hn
    have hx : position N n ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hh.1)) hLN.le,
      (pos_le hN hh.1 1).mpr (by rw [Real.rpow_one]; exact_mod_cast hh.2)⟩
    rw [hF (Real.log n/Real.log N) hx]
    have hcancel : q*(Real.log n/Real.log N)=Real.log n/Real.log M := by
      dsimp only [q]; field_simp
    simp only [F,modulationResponse,hcancel,fractionalModulationLoss]
  have hsum : (∑ n ∈ Icc 1 N, criticalMoebiusMass n/harmonicMoebiusDiagonal N*
      (∫ u in (0:ℝ)..(Real.log n/Real.log N),w u)) = relativeMoebiusModulationEnergy s M N := by
    rw [relativeMoebiusModulationEnergy,fractional_modulation_energy s hM,sum_div]
    exact sum_congr rfl fun n hn => by rw [he n hn,criticalMoebiusAmplitude_norm_sq]; ring
  rw [hsum,hint,hF 1 ⟨zero_le_one,le_rfl⟩,hF1] at ha
  exact ha

/-- Mean of an affine real power over the unit logarithmic band. -/
private def affinePowerMean (p q : ℝ) := ((1+q)^(p+1)-1)/(q*(p+1))

private theorem affine_power_mean {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (∫ t in (0:ℝ)..1, (1+q*t)^p)=affinePowerMean p q := by
  let G (t : ℝ) := (1+q*t)^(p+1)/(q*(p+1))
  have hden : q*(p+1) ≠ 0 := (mul_pos hq (by positivity)).ne'
  have hbase (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 < 1+q*t :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq.le ht.1)
  have hlin : Continuous (fun t : ℝ => 1+q*t) := by fun_prop
  have hi : IntervalIntegrable (fun t : ℝ => (1+q*t)^p) volume 0 1 :=
    (hlin.continuousOn.rpow_const (fun t ht => Or.inl (hbase t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hg (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) : HasDerivAt G ((1+q*t)^p) t := by
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hl : HasDerivAt (fun x : ℝ => 1+q*x) q t := by
      simpa only [mul_one] using ((hasDerivAt_id' t).const_mul q).const_add 1
    have h := (hl.rpow_const (p:=p+1) (Or.inl (hbase t ht).ne')).div_const (q*(p+1))
    have he : q*(p+1)*(1+q*t)^(p+1-1)/(q*(p+1))=(1+q*t)^p := by
      rw [add_sub_cancel_right]
      field_simp
    exact he ▸ h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hg hi]
  simp only [G,affinePowerMean,mul_one,mul_zero,add_zero,Real.one_rpow,sub_div]

/-- Closed continuum profile for all positive bandwidths and nonnegative
orders. The two affine power means come from the squared symbol. -/
theorem modulation_response_integral {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    (∫ t in (0:ℝ)..1, modulationResponse s q t) =
      ((1+q)^(2*s+1)-1)/(q*(2*s+1))-2*(((1+q)^(s+1)-1)/(q*(s+1)))+1 := by
  let f (v t : ℝ) := (1+q*t)^v
  have hbase (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 < 1+q*t :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq.le ht.1)
  have hlin : Continuous (fun t : ℝ => 1+q*t) := by fun_prop
  have hi (v : ℝ) : IntervalIntegrable (f v) volume 0 1 :=
    (hlin.continuousOn.rpow_const (fun t ht => Or.inl (hbase t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hrep : (∫ t in (0:ℝ)..1, modulationResponse s q t) =
      ∫ t in (0:ℝ)..1, (f (2*s) t-2*f s t)+1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    dsimp only [f,modulationResponse]
    rw [two_mul s,Real.rpow_add (hbase t ht)]
    ring
  rw [hrep,intervalIntegral.integral_add ((hi (2*s)).sub ((hi s).const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_sub (hi (2*s)) ((hi s).const_mul 2),intervalIntegral.integral_const_mul]
  dsimp only [f]
  rw [affine_power_mean (mul_nonneg zero_le_two hs) hq,affine_power_mean hs hq,intervalIntegral.integral_const]
  simp only [affinePowerMean,sub_zero,smul_eq_mul,mul_one]

/-- On the arithmetic progression of cutoffs N=M^j, the actual random
Möbius energy converges to the continuum profile at bandwidth j. -/
theorem moebius_modulation_limit_at_power {s : ℝ} (hs : 0 ≤ s) {j : ℕ} (hj : 0 < j) :
    Tendsto (fun M : ℕ => relativeMoebiusModulationEnergy s M (M^j)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, modulationResponse s j t)) := by
  let K := (24+|squarefreeHarmonicConstant|)*((1+(j:ℝ))^s-1)^2
  have hcutoff : Tendsto (fun M : ℕ => M^j) atTop atTop :=
    tendsto_atTop_mono (f:=id) (fun M => Nat.le_self_pow hj.ne' M) tendsto_id
  have hD : Tendsto (fun M : ℕ => harmonicMoebiusDiagonal (M^j)) atTop atTop := by
    have h := tendsto_squarefree_harmonic_diagonal_atTop (fun M : ℕ => max 1 (M^j))
      (fun _ => le_max_left _ _) (tendsto_atTop_mono (fun _ => le_max_right _ _) hcutoff)
    apply h.congr'
    filter_upwards [hcutoff.eventually_ge_atTop 1] with M hM
    rw [max_eq_right hM,Nat.cast_pow]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [mul_zero] using hD.inv_tendsto_atTop.const_mul K)
  filter_upwards [eventually_ge_atTop (2:ℕ),hcutoff.eventually_ge_atTop 2] with M hM hN
  have hL := Real.log_pos (by exact_mod_cast (show 1 < M by omega) : (1:ℝ)<M)
  have h := moebius_modulation_continuum_error hs hM hN
  dsimp only at h
  rw [Nat.cast_pow,Real.log_pow,mul_div_cancel_right₀ _ hL.ne',fractional_modulation_loss_at_power s hM] at h
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by dsimp only [K,Pi.inv_apply]; ring)

#print axioms moebius_modulation_limit_at_power
#print axioms modulation_response_integral
#print axioms moebius_modulation_continuum_error
#print axioms squarefree_response_average

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
