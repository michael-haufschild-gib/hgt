import GaloisForLFunctions.RHTower.XiSimpleCriticalExponentialTypeBound
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityLinearExponent
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCanonicalContourAttachment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularClosedHalfPlane
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceProbeRangeClassification

/-! The three literal angular collisions inject into the actual three-quarter-line zero count. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open Sieve
noncomputable section
set_option autoImplicit false

def fundamentalAngularCollisionMap (j : Fin 3) (z : ℂ) : ℂ :=
  ![2-5*z/2,1-z/2,3*z/2] j

theorem fundamentalAngularCollisionMap_injective (j : Fin 3) :
    Function.Injective (fundamentalAngularCollisionMap j) := by
  fin_cases j
  · intro z u h
    change 2-5*z/2=2-5*u/2 at h
    linear_combination -(2/5:ℂ)*h
  · intro z u h
    change 1-z/2=1-u/2 at h
    linear_combination -(2:ℂ)*h
  · intro z u h
    change 3*z/2=3*u/2 at h
    linear_combination (2/3:ℂ)*h

theorem fundamentalAngularCollisionMap_re (j : Fin 3) {z : ℂ} (hz : z.re=1/2) :
    (fundamentalAngularCollisionMap j z).re=3/4 := by
  fin_cases j <;> norm_num [fundamentalAngularCollisionMap,Complex.mul_re,Complex.div_re,hz]

theorem fundamentalAngularCollisionMap_height (j : Fin 3) {N : ℕ} (hN : 12≤N)
    {z : ℂ} (hz0 : 0<z.im) (hzN : z.im≤(N:ℝ)/3) :
    |(fundamentalAngularCollisionMap j z).im|≤(N:ℝ)-2 := by
  have hNr : (12:ℝ)≤N := by exact_mod_cast hN
  fin_cases j <;>
    norm_num [fundamentalAngularCollisionMap,Complex.mul_im,Complex.div_im,abs_mul,abs_div,
      abs_of_pos hz0] <;> linarith

def fundamentalAngularExceptionFinset (N : ℕ) (j : Fin 3) : Finset ℂ := by
  classical
  exact (xiSimpleCriticalZeroFinset ((N:ℝ)/3)).filter
    (fun z=>xi (fundamentalAngularCollisionMap j z)=0)

/-- The angular exceptional count is bounded by actual residue-unit zero
multiplicities; each affine collision is injective and satisfies the required height bound. -/
theorem fundamentalAngularExceptionFinset_card_le (N : ℕ) (hN : 12≤N) (j : Fin 3) :
    ((fundamentalAngularExceptionFinset N j).card:ℝ)≤
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter (3/4)) 4 ((N:ℝ)-2) (3/4) := by
  classical
  let S := fundamentalAngularExceptionFinset N j
  let Z := (zetaResidueUnitClosedRectangleZeros
    ((inghamUniformGabrielCenter (3/4):ℂ)+(-((N:ℝ)-2):ℝ)*I)
    ((4:ℂ)+(((N:ℝ)-2:ℝ):ℂ)*I)).filter (fun u=>(3/4:ℝ)≤u.re)
  let U := S.image (fundamentalAngularCollisionMap j)
  have hUcard : U.card=S.card :=
    Finset.card_image_iff.mpr (fundamentalAngularCollisionMap_injective j).injOn
  have hU : U⊆Z := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hzset,hzero⟩ := Finset.mem_filter.mp hz
    have hd := mem_xiSimpleCriticalZeroFinset.mp hzset
    have hre := fundamentalAngularCollisionMap_re j hd.2.2.2.2.2.1
    have him := fundamentalAngularCollisionMap_height j hN hd.2.2.1 hd.2.2.2.1
    have hu1 : fundamentalAngularCollisionMap j z≠1 := by
      intro h
      have h' := congrArg Complex.re h
      rw [hre] at h'
      norm_num at h'
    have hzeta := (xi_zero_iff_zeta_zero_of_mem_strip
      (by rw [hre];norm_num) (by rw [hre];norm_num)).mp hzero
    have hunit : zetaResidueUnit (fundamentalAngularCollisionMap j z)=0 := by
      by_contra h
      exact (zetaResidueUnit_ne_zero_iff hu1).mp h hzeta
    have hNr : (12:ℝ)≤N := by exact_mod_cast hN
    have hleft : inghamUniformGabrielCenter (3/4)≤(4:ℝ) := by
      norm_num [inghamUniformGabrielCenter]
    have hheight : -((N:ℝ)-2)≤(N:ℝ)-2 := by linarith
    refine Finset.mem_filter.mpr ⟨mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_,hunit⟩,hre.ge⟩
    apply Complex.mem_reProdIm.mpr
    constructor
    · simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.re_ofNat,
        uIcc_of_le hleft,hre]
      norm_num [inghamUniformGabrielCenter]
    · simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,Complex.im_ofNat,
        uIcc_of_le hheight,Set.mem_Icc] using (abs_le.mp him)
  have hone (u : ℂ) (hu : u∈Z) : (1:ℝ)≤(analyticOrderAt zetaResidueUnit u).toNat := by
    have hz := (mem_zetaResidueUnitClosedRectangleZeros.mp (Finset.mem_filter.mp hu).1).2
    have ho : analyticOrderAt zetaResidueUnit u≠0 := by
      intro h
      exact ((analyticAt_zetaResidueUnit u).analyticOrderAt_eq_zero.mp h) hz
    exact_mod_cast Nat.succ_le_of_lt (ENat.toNat_pos ho (zetaResidueUnit_order_ne_top u))
  change (S.card:ℝ)≤∑ u∈Z,((analyticOrderAt zetaResidueUnit u).toNat:ℝ)
  rw [← hUcard]
  calc
    (U.card:ℝ) = ∑ _u∈U,(1:ℝ) := by simp
    _ ≤ ∑ u∈U,((analyticOrderAt zetaResidueUnit u).toNat:ℝ) :=
      Finset.sum_le_sum (fun u hu=>hone u (hU hu))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _=>by positivity)

/-- At three quarters, the corpus density estimate is eventually smaller
than the height itself, with every fixed polylogarithmic loss absorbed. -/
theorem eventually_threeQuarterZeroCount_le_height :
    ∀ᶠ N : ℕ in atTop,
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter (3/4)) 4 ((N:ℝ)-2) (3/4)≤N := by
  obtain ⟨K,hK,hd⟩ := exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent
  have h0 := (show Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).eventually
    (eventually_const_mul_rpow_polylog_le_rpow (C:=3*K) (α:=0) (β:=1) 14 (by norm_num))
  have h1 := (show Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).eventually
    (eventually_const_mul_rpow_polylog_le_rpow (C:=3*K) (α:=4/5) (β:=1) 16 (by norm_num))
  have h2 := (show Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).eventually
    (eventually_const_mul_rpow_polylog_le_rpow (C:=3*K) (α:=0) (β:=1) 16 (by norm_num))
  filter_upwards [hd,h0,h1,h2,eventually_ge_atTop (1:ℕ)] with N hdN h0N h1N h2N hN
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg hNr
  simp only [Real.rpow_zero,Real.rpow_one,mul_one,abs_of_nonneg hlog] at h0N h1N h2N
  have h := hdN (sigma:=3/4) (by norm_num) (by norm_num)
  norm_num only [show (16/5:ℝ)*(1-3/4)=4/5 by norm_num] at h
  have hp : (1+Real.log (N:ℝ))^14*(1+Real.log (N:ℝ))^2=(1+Real.log (N:ℝ))^16 := by
    rw [← pow_add]
  calc
    _ ≤ K*(1+Real.log (N:ℝ))^14*
        (1+(N:ℝ)^(4/5:ℝ)*(1+Real.log (N:ℝ))^2+(1+Real.log (N:ℝ))^2) := h
    _ = K*(1+Real.log (N:ℝ))^14+
        K*(N:ℝ)^(4/5:ℝ)*(1+Real.log (N:ℝ))^16+K*(1+Real.log (N:ℝ))^16 := by
      generalize 1+Real.log (N:ℝ)=L at hp ⊢
      linear_combination K*((N:ℝ)^(4/5:ℝ)+1)*hp
    _ ≤ N := by
      have divideThree (a : ℝ) (ha : 3*a≤(N:ℝ)) : a≤(N:ℝ)/3 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<3)).mpr
        simpa only [mul_comm] using ha
      have h0' := divideThree (K*(1+Real.log (N:ℝ))^14)
        (by simpa only [mul_assoc] using h0N)
      have h1' := divideThree (K*(N:ℝ)^(4/5:ℝ)*(1+Real.log (N:ℝ))^16)
        (by simpa only [mul_assoc] using h1N)
      have h2' := divideThree (K*(1+Real.log (N:ℝ))^16)
        (by simpa only [mul_assoc] using h2N)
      calc
        _ ≤ (N:ℝ)/3+(N:ℝ)/3+(N:ℝ)/3 := add_le_add (add_le_add h0' h1') h2'
        _ = N := by ring

end
end RHTower.D4BMJointSource

/-! Only linearly many simple critical copies can annihilate the complete canonical action. -/
open Complex Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMJointSource
open Sieve D4BMOriginalCanonicalAction
noncomputable section
set_option autoImplicit false

def fundamentalRadialExceptionFinset (N : ℕ) : Finset ℂ := by
  classical
  exact (xiSimpleCriticalZeroFinset ((N:ℝ)/3)).filter
    (fun z=>fundamentalCanonicalContourNumerator (-1-z/2)=0)

theorem fundamentalRadialExceptionFinset_card_linear :
    ∃ K : ℝ, 0<K ∧ ∀ N : ℕ, 1≤N →
      ((fundamentalRadialExceptionFinset N).card:ℝ)≤K*(1+(N:ℝ)) := by
  classical
  obtain ⟨K,hK,hbound⟩ := fundamentalCanonicalContourNumerator_zeroCount_linear
  refine ⟨K,hK,?_⟩
  intro N hN
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hd : ((fundamentalRadialExceptionFinset N).card:ℤ)≤
      ∑ᶠ u, (MeromorphicOn.divisor fundamentalCanonicalContourNumerator (closedBall (-1:ℂ) (N:ℝ))) u := by
    apply card_le_sum_divisor_of_finite_zeros fundamentalCanonicalContourNumerator_entire
      fundamentalCanonicalContourNumerator_anchor_ne_zero (fundamentalRadialExceptionFinset N)
      (fun z : ℂ=>-1-z/2)
    · intro z _ u _ h
      linear_combination -(2:ℂ)*h
    · intro z hz
      have hh := mem_xiSimpleCriticalZeroFinset.mp (Finset.mem_filter.mp hz).1
      have hn := Complex.norm_le_abs_re_add_abs_im z
      have hzr : |z.re|=1/2 := by rw [hh.2.2.2.2.2.1];norm_num
      rw [hzr,abs_of_pos hh.2.2.1] at hn
      rw [mem_closedBall,dist_eq_norm,show (-1-z/2)-(-1)=-z/2 by ring,norm_div,norm_neg]
      have ht : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
      rw [ht]
      linarith [hh.2.2.2.1]
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hdr : ((fundamentalRadialExceptionFinset N).card:ℝ)≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor fundamentalCanonicalContourNumerator (closedBall (-1:ℂ) (N:ℝ))) u):ℝ) := by
    exact_mod_cast hd
  exact hdr.trans (hbound N hNr)

/-- A zero of the complete canonical action must be one of the exact radial
or angular exceptions; no separately selected contribution is tested. -/
theorem canonicalQNMValue_zero_forces_contour_or_angular (q : XiZeroCopy)
    (hq : (q.1:ℂ).re=1/2) (hv : canonicalQNMValue q true true 1=0) :
    fundamentalCanonicalContourNumerator (-1-(q.1:ℂ)/2)=0 ∨
      ∃ j : Fin 3, xi (fundamentalAngularCollisionMap j (q.1:ℂ))=0 := by
  have hclear := canonicalQNMValue_cleared_eq_fundamentalContour q
  have hi := xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1:ℂ)≠0 := by intro h;apply hi;rw [h];rfl
  have h2 : (q.1:ℂ)-2≠0 := by
    intro h
    apply hi
    have hh := congrArg Complex.im h
    simpa only [Complex.sub_im,Complex.im_ofNat,sub_zero,Complex.zero_im] using hh
  have hmu : physicalAngularParameter q^2-1/4≠0 := by
    have he : physicalAngularParameter q^2-1/4=(q.1:ℂ)*((q.1:ℂ)-2)/4 := by
      rw [physicalAngularParameter_eq]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero h0 h2) (by norm_num)
  dsimp only at hclear
  rw [hv,physicalFundamentalFrequency_eq] at hclear
  simp only [mul_zero,↓reduceIte] at hclear
  by_cases hG : fundamentalCanonicalContourNumerator (-1-(q.1:ℂ)/2)=0
  · exact Or.inl hG
  right
  have hC : physicalSelfSourceCoefficient q=0 := by
    by_contra hC
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hmu) hC) hG) hclear.symm
  rcases (physicalSelfSourceCoefficient_zero_iff_xi_closedHalfPlane q hq.ge).mp hC with hA|hB|hC
  · refine ⟨0,?_⟩
    change xi (2-5*(q.1:ℂ)/2)=0
    rw [show 2-5*(q.1:ℂ)/2=1-(5*(q.1:ℂ)/2-1) by ring,xi_one_sub]
    exact hA
  · refine ⟨1,?_⟩
    change xi (1-(q.1:ℂ)/2)=0
    rw [xi_one_sub]
    exact hB
  · exact ⟨2,hC⟩

/-- Actual simple critical zeros carrying a zero complete canonical action. -/
def fundamentalCanonicalCriticalZeroFinset (N : ℕ) : Finset ℂ := by
  classical
  exact (xiSimpleCriticalZeroFinset ((N:ℝ)/3)).filter
    (fun z=>∃ q : XiZeroCopy, (q.1:ℂ)=z ∧ canonicalQNMValue q true true 1=0)

theorem fundamentalCanonicalCriticalZeroFinset_subset (N : ℕ) :
    fundamentalCanonicalCriticalZeroFinset N ⊆
      fundamentalRadialExceptionFinset N ∪
        (fundamentalAngularExceptionFinset N 0 ∪ fundamentalAngularExceptionFinset N 1 ∪
          fundamentalAngularExceptionFinset N 2) := by
  classical
  intro z hz
  obtain ⟨hzset,q,hq,hv⟩ := Finset.mem_filter.mp hz
  have hline := (mem_xiSimpleCriticalZeroFinset.mp hzset).2.2.2.2.2.1
  have h := canonicalQNMValue_zero_forces_contour_or_angular q (by rw [hq];exact hline) hv
  rw [hq] at h
  rcases h with hG|⟨j,hj⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzset,hG⟩)
  · apply Finset.mem_union_right
    have hm : z∈fundamentalAngularExceptionFinset N j := Finset.mem_filter.mpr ⟨hzset,hj⟩
    fin_cases j
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
    · exact Finset.mem_union_right _ hm

/-- Positive rigidity statement behind the matching obstruction: among the
actual simple critical Xi zeros, zeros of the complete action have a linear
counting envelope. -/
theorem fundamentalCanonicalCriticalZeroFinset_card_linear :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ((fundamentalCanonicalCriticalZeroFinset N).card:ℝ)≤K*(1+(N:ℝ)) := by
  obtain ⟨K,hK,hR⟩ := fundamentalRadialExceptionFinset_card_linear
  refine ⟨K+3,by linarith,?_⟩
  filter_upwards [eventually_threeQuarterZeroCount_le_height,eventually_ge_atTop (12:ℕ)] with N hD hN
  have hR' := hR N (by omega)
  have hA (j : Fin 3) := (fundamentalAngularExceptionFinset_card_le N hN j).trans hD
  have hc : (fundamentalCanonicalCriticalZeroFinset N).card≤
      (fundamentalRadialExceptionFinset N).card+(fundamentalAngularExceptionFinset N 0).card+
        (fundamentalAngularExceptionFinset N 1).card+(fundamentalAngularExceptionFinset N 2).card := by
    have h0 := Finset.card_le_card (fundamentalCanonicalCriticalZeroFinset_subset N)
    have h1 := Finset.card_union_le (fundamentalRadialExceptionFinset N)
      (fundamentalAngularExceptionFinset N 0 ∪ fundamentalAngularExceptionFinset N 1 ∪ fundamentalAngularExceptionFinset N 2)
    have h2 := Finset.card_union_le
      (fundamentalAngularExceptionFinset N 0 ∪ fundamentalAngularExceptionFinset N 1) (fundamentalAngularExceptionFinset N 2)
    have h3 := Finset.card_union_le (fundamentalAngularExceptionFinset N 0) (fundamentalAngularExceptionFinset N 1)
    omega
  have hcr : ((fundamentalCanonicalCriticalZeroFinset N).card:ℝ)≤
      (fundamentalRadialExceptionFinset N).card+(fundamentalAngularExceptionFinset N 0).card+
        (fundamentalAngularExceptionFinset N 1).card+(fundamentalAngularExceptionFinset N 2).card := by
    exact_mod_cast hc
  nlinarith [hA 0,hA 1,hA 2]

/-- Quantitative positive survivor: the proportion of simple critical Xi
zeros annihilated by the complete canonical action tends to zero. -/
theorem fundamentalCanonicalCriticalZeroFinset_relative_density_zero (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop,
      ((fundamentalCanonicalCriticalZeroFinset N).card:ℝ)≤
        eps*(xiSimpleCriticalZeroCount ((N:ℝ)/3):ℝ) := by
  obtain ⟨K,hK,hbound⟩ := fundamentalCanonicalCriticalZeroFinset_card_linear
  have hscale : Tendsto (fun N : ℕ=>(N:ℝ)/3) atTop atTop :=
    (show Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hlower := hscale.eventually eventually_superlinear_xiSimpleCriticalZeroCount
  have hlog := (Real.tendsto_log_atTop.comp hscale).eventually_ge_atTop (216*Real.pi*(2*K/eps))
  filter_upwards [hbound,hlower,hlog,eventually_ge_atTop (12:ℕ)] with N hB hL hlogN hN
  have hNr : (12:ℝ)≤N := by exact_mod_cast hN
  have hlarge : (2*K/eps)*(N:ℝ)≤(xiSimpleCriticalZeroCount ((N:ℝ)/3):ℝ) := by
    calc
      _ = (1/(72*Real.pi))*((N:ℝ)/3)*(216*Real.pi*(2*K/eps)) := by
        field_simp [Real.pi_pos.ne',heps.ne']; ring
      _ ≤ (1/(72*Real.pi))*((N:ℝ)/3)*Real.log ((N:ℝ)/3) := by
        apply mul_le_mul_of_nonneg_left hlogN
        positivity
      _ ≤ _ := hL
  calc
    _ ≤ K*(1+(N:ℝ)) := hB
    _ ≤ 2*K*(N:ℝ) := by nlinarith
    _ = eps*((2*K/eps)*(N:ℝ)) := by field_simp [heps.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hlarge heps.le

end
end RHTower.D4BMJointSource

/-! The original complete temporal/metric/QNM value cannot match the literal unit-source probe. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower
open D4BMJointSource D4BMOriginalCanonicalAction
noncomputable section
set_option autoImplicit false

/-- An actual critical Xi copy has nonzero complete canonical action.
The proof uses the full source cutoff and the actual zero census, without
selecting a numerical zero or importing a nonvanishing hypothesis. -/
theorem exists_critical_canonicalQNMValue_ne_zero :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧ canonicalQNMValue q true true 1≠0 := by
  classical
  by_contra h
  have hall : ∀ q : XiZeroCopy, (q.1:ℂ).re=1/2 → canonicalQNMValue q true true 1=0 := by
    simpa only [not_exists,not_and,not_not] using h
  have hbound := fundamentalCanonicalCriticalZeroFinset_relative_density_zero (1/2) (by norm_num)
  have hscale : Tendsto (fun N : ℕ=>(N:ℝ)/3) atTop atTop :=
    (show Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hlower := hscale.eventually eventually_superlinear_xiSimpleCriticalZeroCount
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hbound,hlower,eventually_ge_atTop (12:ℕ)] with N hB hL hN
    have hNr : (12:ℝ)≤N := by exact_mod_cast hN
    have heq : fundamentalCanonicalCriticalZeroFinset N=xiSimpleCriticalZeroFinset ((N:ℝ)/3) := by
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro z hz
      have hd := mem_xiSimpleCriticalZeroFinset.mp hz
      refine Finset.mem_filter.mpr ⟨hz,?_⟩
      let rho : XiDivisorSupport := ⟨z,mem_xi_divisor_support_of_eq_zero hd.2.2.2.2.1⟩
      have hp := xi_divisor_pos_on_support rho
      let q : XiZeroCopy := ⟨rho,⟨0,by omega⟩⟩
      exact ⟨q,rfl,hall q hd.2.2.2.2.2.1⟩
    rw [heq,card_xiSimpleCriticalZeroFinset] at hB
    have hlogpos : 0<Real.log ((N:ℝ)/3) := Real.log_pos (by linarith)
    have hpos : 0<(1/(72*Real.pi))*((N:ℝ)/3)*Real.log ((N:ℝ)/3) := by positivity
    nlinarith
  obtain ⟨N,hN⟩ := hfalse.exists
  exact hN

/-- Full canonical temporal/metric/QNM matching through the literal complementary
unit source is impossible, even for arbitrary copy-dependent returned vectors. -/
theorem not_exists_hbXiPeierls_fullCanonicalQNM_matching :
    ¬∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, hbXiPeierlsSourceProbeProfile returned q=canonicalQNMValue q true true 1 := by
  rintro ⟨returned,hmatch⟩
  obtain ⟨q,hline,hne⟩ := exists_critical_canonicalQNMValue_ne_zero
  exact hne ((hmatch q).symm.trans (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline))

/-- Even equality of extinction loci fails: the original full action remains
nonzero at an actual critical copy erased by every unit-source measurement. -/
theorem not_exists_hbXiPeierls_fullCanonicalExtinction_matching :
    ¬∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, (canonicalQNMValue q true true 1=0 ↔ hbXiPeierlsSourceProbeProfile returned q=0) := by
  rintro ⟨returned,hmatch⟩
  obtain ⟨q,hline,hne⟩ := exists_critical_canonicalQNMValue_ne_zero
  exact hne ((hmatch q).mpr (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline))

/-- Allowing an arbitrary nonlinear response of the whole carrier still cannot
match the original complete canonical action with this unit testing source. -/
theorem not_exists_hbXiPeierls_arbitraryResponse_fullCanonicalQNM_matching :
    ¬∃ response : HBXiPeierlsCarrier → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, hbXiPeierlsSourceProbeProfile
        (fun r=>response (hbXiPeierlsPlusSource 1 r)) q=canonicalQNMValue q true true 1 := by
  rintro ⟨response,hmatch⟩
  exact not_exists_hbXiPeierls_fullCanonicalQNM_matching
    ⟨fun r=>response (hbXiPeierlsPlusSource 1 r),hmatch⟩

end
end RHTower
