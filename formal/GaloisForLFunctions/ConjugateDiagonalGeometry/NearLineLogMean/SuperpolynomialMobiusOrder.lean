import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheHybridHeightBoundForSharpMoebiusSections

/-!
# The zero width along every superpolynomial Möbius section

For each exponent below the zero width, a fixed positive height window
forces all sufficiently long pure Möbius sections to have large energy.
The translated Mellin upper bound then identifies the ordinary growth
rate along every schedule whose length grows faster than all powers of
height, even if the integer cutoffs and the heights are irregular.
-/

noncomputable section
open Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_eq_zetaZeroAbscissa_sub_half)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Energy of a section with an independently chosen integer cutoff. -/
def sectionHeightEnergy (N : ℕ) (A B : ℝ) : ℝ :=
  ∫ u in A..B, ‖moebiusPoly N (linePoint u)‖^2

private theorem positive_half_near_zero {d : ℝ} (hd : 0 < d) (hsmall : d ≤ zetaZeroWidth) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1/2 < ρ.re ∧ ρ.re < 1 ∧
      1/2+zetaZeroWidth-d < ρ.re ∧ 0 ≤ ρ.im := by
  have habs : 1/2+zetaZeroWidth = _root_.RHTower.zetaZeroAbscissa := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]; ring
  obtain ⟨z,hz,hr,h⟩ := _root_.RHTower.exists_zetaZero_mem_openStrip_lt_re
    (b := 1/2+zetaZeroWidth-d) (by rw [habs]; linarith)
  have hlo : 1/2 < z.re := by linarith
  rcases le_total 0 z.im with hi | hi
  · exact ⟨z,hz,hlo,hr,h,hi⟩
  · exact ⟨conj z,by rw [riemannZeta_conj,hz,map_zero],by simpa using hlo,by simpa using hr,
      by simpa using h,by simpa using hi⟩

private theorem weighted_error_le_section (ρ : ℂ) (hr : 1/2 < ρ.re) (hi : 0 ≤ ρ.im) :
    ∃ K : ℝ, 0 < K ∧ ∀ N, ∫ u in Set.Icc (1+ρ.im) (2+ρ.im),
      zeroPoisson ρ u*‖lineError (moebiusPoly N) u‖^2 ≤ K*(1+sectionHeightEnergy N (1+ρ.im) (2+ρ.im)) := by
  let d := ρ.re-1/2
  let M := 18*(3+ρ.im)
  let P := 1/(Real.pi*d)
  have hd : 0 < d := sub_pos.mpr hr
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hP : 0 < P := by dsimp only [P]; positivity
  let K := 2*P*M^2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,fun N => ?_⟩
  let A := 1+ρ.im
  let B := 2+ρ.im
  let S := Set.Icc A B
  let f := fun u => ‖moebiusPoly N (linePoint u)‖^2
  have hf : Continuous f := ((differentiable_moebiusPoly N).continuous.comp continuous_linePoint).norm.pow 2
  have hhi (u : ℝ) : zeroPoisson ρ u ≤ P := by
    dsimp only [zeroPoisson,HTGeometry.halfPlanePoisson,P]
    change d/(Real.pi*(d^2+(u-ρ.im)^2)) ≤ 1/(Real.pi*d)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg Real.pi_pos.le (sq_nonneg (u-ρ.im))]
  have hrow (u : ℝ) (hu : u ∈ S) :
      zeroPoisson ρ u*‖lineError (moebiusPoly N) u‖^2 ≤ K*(1+f u) := by
    have hu0 : 0 ≤ u := (by dsimp only [A]; linarith : 0 ≤ A).trans hu.1
    have hz := norm_zeta_linePoint_le u
    rw [abs_of_nonneg hu0] at hz
    have hzu : ‖riemannZeta (linePoint u)‖ ≤ M := hz.trans (by dsimp only [M]; linarith only [hu.2])
    let m := ‖moebiusPoly N (linePoint u)‖
    have hm : 0 ≤ m := norm_nonneg _
    have ht : ‖lineError (moebiusPoly N) u‖ ≤ M*m+1 := by
      unfold lineError
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul,norm_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hzu hm) le_rfl
    have hsq := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hM2 : 1 ≤ M^2 := by nlinarith only [hM,sq_nonneg (M-1)]
    have haux : (M*m+1)^2 ≤ 2*M^2*(1+m^2) := by nlinarith only [sq_nonneg (M*m-1),hM2]
    exact (mul_le_mul (hhi u) (hsq.trans haux) (sq_nonneg _) hP.le).trans_eq (by dsimp only [K,f,m]; ring)
  have hmeas := (integrable_zeroPoisson_mul_normSq_lineError hr N).integrableOn (s := S)
  have hint := setIntegral_mono_on hmeas ((continuous_const.mul (continuous_const.add hf)).integrableOn_Icc)
    measurableSet_Icc hrow
  simp only [Pi.mul_apply,Pi.add_apply] at hint
  rw [integral_const_mul,integral_add continuous_const.integrableOn_Icc hf.integrableOn_Icc,
    setIntegral_const,Real.volume_real_Icc_of_le (by dsimp [A,B]; linarith),
    smul_eq_mul,mul_one] at hint
  change _ ≤ K*(1+∫ u in A..B, f u)
  rw [intervalIntegral.integral_of_le (by dsimp only [A,B]; linarith), ←integral_Icc_eq_integral_Ioc]
  simpa only [A,B,S,show 2+ρ.im-(1+ρ.im)=1 by ring] using hint

/-- Beyond each subcritical length power, one fixed positive unit window
has larger pure Möbius energy at every sufficiently large integer cutoff. -/
theorem fixed_window_pays_each_subcritical_length_power {b : ℝ} (hb : 0 ≤ b) (hbw : b < zetaZeroWidth) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ N : ℕ in atTop, (N:ℝ)^(2*b) < sectionHeightEnergy N A (A+1) := by
  obtain ⟨k,hbk,hkw⟩ := exists_between hbw
  have hw : 0 < zetaZeroWidth := hb.trans_lt hbw
  let p := (zetaZeroWidth/2)/(Real.pi*(1/4+4))
  have hp : 0 < p := by dsimp only [p]; positivity
  let e := min (zetaZeroWidth/2) (p*(zetaZeroWidth-k)/4)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hew := min_le_left (zetaZeroWidth/2) (p*(zetaZeroWidth-k)/4)
  have hek := min_le_right (zetaZeroWidth/2) (p*(zetaZeroWidth-k)/4)
  obtain ⟨ρ,hz,hr,hr1,hnear,hi⟩ := positive_half_near_zero he (hew.trans (by linarith))
  let A := 1+ρ.im
  let B := 2+ρ.im
  let S := Set.Icc A B
  have hA : 1 ≤ A := le_add_of_nonneg_right hi
  have hAB : A ≤ B := by dsimp only [A,B]; linarith
  have hδ : 0 < ρ.re-1/2 := sub_pos.mpr hr
  have hdl : zetaZeroWidth/2 ≤ ρ.re-1/2 := by change 1/2+zetaZeroWidth-e < ρ.re at hnear; linarith only [hew,hnear]
  have hds : (ρ.re-1/2)^2 ≤ 1/4 := by nlinarith only [mul_nonneg (show 0 ≤ ρ.re by linarith) (show 0 ≤ 1-ρ.re by linarith)]
  have hpoint (u : ℝ) (hu : u ∈ S) : p ≤ zeroPoisson ρ u := by
    have hu' : |u-ρ.im| ≤ 2 := by
      obtain ⟨h₁,h₂⟩ := hu
      dsimp only [A,B] at h₁ h₂
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    apply le_trans _ (poisson_lower_bound hδ hu')
    exact div_le_div₀ hδ.le hdl (by positivity)
      (by nlinarith only [mul_le_mul_of_nonneg_left hds Real.pi_pos.le])
  have hmass : p ≤ ∫ u in S, zeroPoisson ρ u := by
    have h := setIntegral_mono_on (integrableOn_const (by simp [S])) (integrable_zeroPoisson hr).integrableOn
      measurableSet_Icc hpoint
    simpa only [S,setIntegral_const,Real.volume_real_Icc_of_le hAB,A,B,show 2+ρ.im-(1+ρ.im)=1 by ring,
      one_smul] using h
  have hprice : (zetaZeroWidth-(ρ.re-1/2))/(zetaZeroWidth-k) ≤ p/4 := by
    apply (div_le_iff₀ (sub_pos.mpr hkw)).mpr
    change 1/2+zetaZeroWidth-e < ρ.re at hnear
    linarith only [hek,hnear]
  obtain ⟨K,hK,hupper⟩ := weighted_error_le_section ρ hr hi
  have hhigh := eventually_restricted_secondMoment_ge hz hr hr1 (hb.trans hbk.le) hkw (show 0 < p/4 by positivity)
  have hlim := (tendsto_rpow_atTop (show 0 < 2*(k-b) by linarith)).comp tendsto_natCast_atTop_atTop
  refine ⟨A,hA,?_⟩
  filter_upwards [hhigh,hlim.eventually_gt_atTop (4*K/p),eventually_ge_atTop (1:ℕ)] with N hread hbig hn
  have hpN : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hn
  let I := sectionHeightEnergy N A B
  have hlow := (hread S measurableSet_Icc).trans (hupper N)
  have hsm := mul_le_mul_of_nonneg_right (by linarith only [hmass,hprice] :
    p/2 ≤ (∫ u in S, zeroPoisson ρ u)-(zetaZeroWidth-(ρ.re-1/2))/(zetaZeroWidth-k)-p/4)
    (Real.rpow_nonneg hpN.le (2*k))
  change _ ≤ K*(1+I) at hlow
  change 4*K/p < (N:ℝ)^(2*(k-b)) at hbig
  have hmul := mul_lt_mul_of_pos_right ((div_lt_iff₀ hp).mp hbig) (Real.rpow_pos_of_pos hpN (2*b))
  have hc : (N:ℝ)^(2*(k-b))*p*(N:ℝ)^(2*b) = p*(N:ℝ)^(2*k) := by
    rw [mul_comm _ p,mul_assoc,←Real.rpow_add hpN,show 2*(k-b)+2*b=2*k by ring]
  rw [hc] at hmul
  have hkn := mul_le_mul_of_nonneg_left (Real.one_le_rpow hn1 (by positivity : 0 ≤ 2*b)) hK.le
  have hKI : K*(N:ℝ)^(2*b) < K*I := by linarith only [hkn,hmul,hsm,hlow]
  simpa only [I,A,B,show 1+ρ.im+1=2+ρ.im by ring] using (lt_of_mul_lt_mul_left hKI hK.le)

private theorem section_energy_two_scales {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ T : ℝ, 1 ≤ T →
      1+sectionHeightEnergy N 1 T ≤ C*(N:ℝ)^(2*(zetaZeroWidth+e))*T^(1+2*e) := by
  obtain ⟨D,hD,hb⟩ := hybrid_moebius_section_bound he
  let r := zetaZeroWidth+e
  have hr : 0 ≤ r := add_nonneg zetaZeroWidth_nonneg he.le
  let K := D*2^r*3^e
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨1+K^2,le_add_of_nonneg_right (sq_nonneg _),fun N hN T hT => ?_⟩
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpN := zero_lt_one.trans_le hn
  have hpT := zero_lt_one.trans_le hT
  have hlen := Real.rpow_le_rpow (by positivity : 0 ≤ (N:ℝ)+1) (by linarith : (N:ℝ)+1 ≤ 2*N) hr
  rw [Real.mul_rpow (by norm_num) hpN.le] at hlen
  let F := K*(N:ℝ)^r*T^e
  have hf : 0 ≤ F := by dsimp only [F]; positivity
  have hpt (u : ℝ) (hu : u ∈ Set.Icc 1 T) : ‖moebiusPoly N (linePoint u)‖^2 ≤ F^2 := by
    have hu' : 2+|u| ≤ 3*T := by rw [abs_of_pos (zero_lt_one.trans_le hu.1)]; linarith only [hu.2,hT]
    have hpow := Real.rpow_le_rpow (by positivity) hu' he.le
    rw [Real.mul_rpow (by norm_num) hpT.le] at hpow
    apply pow_le_pow_left₀ (norm_nonneg _)
    refine (hb N u).trans ((mul_le_mul (mul_le_mul_of_nonneg_left hlen hD) hpow (by positivity) (by positivity)).trans_eq ?_)
    dsimp only [K,F];ring
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hT
    ((((differentiable_moebiusPoly N).continuous.comp continuous_linePoint).norm.pow 2).intervalIntegrable _ _)
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const,smul_eq_mul] at hmono
  have hbound : sectionHeightEnergy N 1 T ≤ K^2*((N:ℝ)^(2*r)*T^(1+2*e)) := by
    refine hmono.trans ((mul_le_mul_of_nonneg_right (by linarith : T-1 ≤ T) (sq_nonneg _)).trans_eq ?_)
    dsimp only [F]
    rw [mul_pow,mul_pow,←Real.rpow_natCast ((N:ℝ)^r) 2,←Real.rpow_mul hpN.le,
      ←Real.rpow_natCast (T^e) 2,←Real.rpow_mul hpT.le,Real.rpow_add hpT,Real.rpow_one]
    push_cast
    rw [mul_comm r 2,mul_comm e 2]
    ring
  have h1 := Real.one_le_rpow hn (by positivity : 0 ≤ 2*r)
  have h2 := Real.one_le_rpow hT (by positivity : 0 ≤ 1+2*e)
  have h3 := one_le_mul_of_one_le_of_one_le h1 h2
  change _ ≤ (1+K^2)*(N:ℝ)^(2*r)*T^(1+2*e)
  linarith only [h3,hbound]

/-- Along every schedule with log T = o(log N), the logarithm of one plus
the pure second moment, divided by log N, converges to twice the zero width. -/
theorem superpolynomial_section_energy_order {ι : Type*} {l : Filter ι}
    {N : ι → ℕ} {T : ι → ℝ} (hN : Tendsto N l atTop) (hT : Tendsto T l atTop)
    (hlog : Tendsto (fun i => Real.log (T i)/Real.log (N i)) l (𝓝 0)) :
    Tendsto (fun i => Real.log (1+sectionHeightEnergy (N i) 1 (T i))/Real.log (N i))
      l (𝓝 (2*zetaZeroWidth)) := by
  have hln := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hn := hN.eventually_ge_atTop (2:ℕ)
  have ht := hT.eventually_ge_atTop (1:ℝ)
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro b hb
    by_cases hneg : b < 0
    · filter_upwards [hn,ht] with i hni hti
      have hp : 1 < (N i:ℝ) := by exact_mod_cast (show 1 < N i by omega)
      have hI : 0 ≤ sectionHeightEnergy (N i) 1 (T i) :=
        intervalIntegral.integral_nonneg hti (fun _ _ => sq_nonneg _)
      exact hneg.trans_le (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos hp).le)
    obtain ⟨k,hbk,hkw⟩ := exists_between (show b/2 < zetaZeroWidth by linarith)
    have hk : 0 ≤ k := by linarith only [le_of_not_gt hneg,hbk]
    obtain ⟨A,hA,hlocal⟩ := fixed_window_pays_each_subcritical_length_power hk hkw
    filter_upwards [hn,hN.eventually hlocal,hT.eventually_ge_atTop (A+1)] with i hni hpeak hti
    have hp : 1 < (N i:ℝ) := by exact_mod_cast (show 1 < N i by omega)
    have hcov : sectionHeightEnergy (N i) A (A+1) ≤ sectionHeightEnergy (N i) 1 (T i) :=
      intervalIntegral.integral_mono_interval hA (by linarith) hti
        (.of_forall fun t : ℝ => sq_nonneg ‖moebiusPoly (N i) (linePoint t)‖)
        ((((differentiable_moebiusPoly (N i)).continuous.comp continuous_linePoint).norm.pow 2).intervalIntegrable _ _)
    have hlow := (hpeak.trans_le hcov).trans_le (le_add_of_nonneg_left zero_le_one)
    have h := Real.log_lt_log (Real.rpow_pos_of_pos (zero_lt_one.trans hp) _) hlow
    rw [Real.log_rpow (zero_lt_one.trans hp)] at h
    exact (by linarith : b < 2*k).trans ((lt_div_iff₀ (Real.log_pos hp)).mpr h)
  · intro b hb
    let e := (b-2*zetaZeroWidth)/4
    have he : 0 < e := div_pos (sub_pos.mpr hb) (by norm_num)
    obtain ⟨C,hC,hbound⟩ := section_energy_two_scales he
    have hc := zero_lt_one.trans_le hC
    let k := 2*(zetaZeroWidth+e)
    let d := 1+2*e
    have hlim := ((hln.inv_tendsto_atTop.const_mul (Real.log C)).add
      (tendsto_const_nhds (x := k))).add (hlog.const_mul d)
    simp only [mul_zero,zero_add,add_zero] at hlim
    have hkb : k < b := by dsimp only [e,k]; linarith
    filter_upwards [hn,ht,hlim.eventually (eventually_lt_nhds hkb)] with i hni hti hsmall
    have hp : 1 < (N i:ℝ) := by exact_mod_cast (show 1 < N i by omega)
    have hn₀ := zero_lt_one.trans hp
    have ht₀ := zero_lt_one.trans_le hti
    have hI : 0 ≤ sectionHeightEnergy (N i) 1 (T i) :=
      intervalIntegral.integral_nonneg hti (fun _ _ => sq_nonneg _)
    have h := Real.log_le_log (by linarith only [hI]) (hbound (N i) (by omega) (T i) hti)
    rw [Real.log_mul (mul_pos hc (Real.rpow_pos_of_pos hn₀ _)).ne' (Real.rpow_pos_of_pos ht₀ _).ne',
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hn₀ _).ne',Real.log_rpow hn₀,Real.log_rpow ht₀] at h
    have hh := div_le_div_of_nonneg_right h (Real.log_pos hp).le
    refine hh.trans_lt (lt_of_eq_of_lt ?_ hsmall)
    change (Real.log C+k*Real.log (N i)+d*Real.log (T i))/Real.log (N i) =
      Real.log C*(Real.log (N i))⁻¹+k+d*(Real.log (T i)/Real.log (N i))
    field_simp [(Real.log_pos hp).ne']


end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
