import GaloisForLFunctions.RHTower.QuietCrossingRigidity
import GaloisForLFunctions.RHTower.ThetaSymmetryMellinConverse

/-!
# Continuation from bounds for discrete first means

The triangular mean is affine between consecutive reciprocal integers.
A power bound at those integers therefore controls its Mellin transform
throughout the corresponding open half-plane. The Mellin multiplier
is the reciprocal of `s(s+1)`.
-/

noncomputable section

open Complex Finset Filter Topology Set MeasureTheory Asymptotics

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The triangular mean at inverse cutoff `y`, indexed by positive integers. -/
def triangularPrimeProfile (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, c (n+1)*max (1-((n:ℝ)+1)*y) 0

/-- Beyond the reciprocal cutoff all triangular weights vanish. -/
theorem triangularPrimeProfile_eq_sum (c : ℕ → ℝ) {y : ℝ} (hy : 0 ≤ y) (N : ℕ)
    (hN : 1 ≤ ((N:ℝ)+1)*y) :
    triangularPrimeProfile c y = ∑ n ∈ range N, c (n+1)*max (1-((n:ℝ)+1)*y) 0 := by
  apply tsum_eq_sum
  intro n hn
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast (le_of_not_gt (fun ht => hn (mem_range.mpr ht)))
  have h := mul_le_mul_of_nonneg_right (add_le_add_right hn' 1) hy
  rw [max_eq_right (by linarith only [h,hN]),mul_zero]

private theorem profile_continuous (c : ℕ → ℝ) :
    ContinuousOn (triangularPrimeProfile c) (Ioi 0) := by
  intro y hy
  have hy' : 0<y := hy
  obtain ⟨N,hN⟩ := exists_nat_ge (2/y)
  have hN' : 1 ≤ ((N:ℝ)+1)*(y/2) := by
    have h₂ := (div_le_iff₀ hy').mp hN
    linarith only [h₂,hy']
  have he : triangularPrimeProfile c =ᶠ[𝓝 y]
      fun v => ∑ n ∈ range N, c (n+1)*max (1-((n:ℝ)+1)*v) 0 := by
    filter_upwards [lt_mem_nhds (show y/2<y by linarith)] with v hv
    exact triangularPrimeProfile_eq_sum c (by linarith only [hy',hv]) N
      (hN'.trans (mul_le_mul_of_nonneg_left hv.le (by positivity)))
  have hc : ContinuousAt (fun v : ℝ => ∑ n ∈ range N, c (n+1)*max (1-((n:ℝ)+1)*v) 0) y := by fun_prop
  exact (hc.congr_of_eventuallyEq he).continuousWithinAt

private theorem profile_cell (c : ℕ → ℝ) (N : ℕ) {y : ℝ} (hy : 0≤y)
    (hl : 1 ≤ ((N:ℝ)+1)*y) (hu : (N:ℝ)*y ≤ 1) :
    triangularPrimeProfile c y = (∑ n ∈ range N, c (n+1)) -
      (∑ n ∈ range N, c (n+1)*((n:ℝ)+1))*y := by
  rw [triangularPrimeProfile_eq_sum c hy N hl,sum_mul,← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hN : (n:ℝ)+1 ≤ N := by exact_mod_cast mem_range.mp hn
  rw [max_eq_left (sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hN hy).trans hu))]
  ring

private theorem abs_affine_inside {a d l y u B : ℝ} (hl : l≤y) (hu : y≤u)
    (h₁ : |a-d*l|≤B) (h₂ : |a-d*u|≤B) : |a-d*y|≤B := by
  rw [abs_le] at h₁ h₂ ⊢
  rcases le_total 0 d with hd | hd
  · have hdy := mul_le_mul_of_nonneg_left hl hd
    have hdu := mul_le_mul_of_nonneg_left hu hd
    constructor <;> linarith only [h₁.2,h₂.1,hdy,hdu]
  · have hdy := mul_le_mul_of_nonpos_left hl hd
    have hdu := mul_le_mul_of_nonpos_left hu hd
    constructor <;> linarith only [h₁.1,h₂.2,hdy,hdu]

private theorem profile_bound_between_samples (c : ℕ → ℝ) {C b : ℝ} (hC : 0≤C) (hb : 0≤b)
    (h : ∀ N : ℕ, 1≤N → |triangularPrimeProfile c (N:ℝ)⁻¹| ≤ C*(N:ℝ)^b)
    {y : ℝ} (hy : 0<y) (hy1 : y≤1) :
    |triangularPrimeProfile c y| ≤ (C*2^b)*y^(-b) := by
  let N := ⌊y⁻¹⌋₊
  have hn : 1 ≤ N := (Nat.one_le_floor_iff _).mpr ((one_le_inv₀ hy).mpr hy1)
  have hn0 : 0<(N:ℝ) := by exact_mod_cast hn
  have hs : 0<(N:ℝ)+1 := by positivity
  have hlo : (N:ℝ) ≤ y⁻¹ := Nat.floor_le (inv_nonneg.mpr hy.le)
  have hup : y⁻¹ ≤ (N:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hylo : ((N:ℝ)+1)⁻¹ ≤ y := by
    have := inv_anti₀ (inv_pos.mpr hy) hup
    simpa only [inv_inv] using this
  have hyhi : y ≤ (N:ℝ)⁻¹ := by
    have := inv_anti₀ hn0 hlo
    simpa only [inv_inv] using this
  have he (v : ℝ) (hl : ((N:ℝ)+1)⁻¹ ≤ v) (hu : v ≤ (N:ℝ)⁻¹) :=
    profile_cell c N ((inv_nonneg.mpr hs.le).trans hl)
      (by have hh := mul_le_mul_of_nonneg_left hl hs.le; rwa [mul_inv_cancel₀ hs.ne'] at hh)
      (by have hh := mul_le_mul_of_nonneg_left hu hn0.le; rwa [mul_inv_cancel₀ hn0.ne'] at hh)
  have h₁ := h (N+1) (by omega)
  rw [Nat.cast_add,Nat.cast_one] at h₁
  have h₂ := (h N hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hn0.le (by linarith : (N:ℝ)≤N+1) hb) hC)
  rw [he _ le_rfl (hylo.trans hyhi)] at h₁
  rw [he _ (hylo.trans hyhi) le_rfl] at h₂
  rw [he _ hylo hyhi]
  apply (abs_affine_inside hylo hyhi h₁ h₂).trans
  have hc : (N:ℝ)+1 ≤ 2*y⁻¹ := by linarith only [hlo,(one_le_inv₀ hy).mpr hy1]
  have hpow := Real.rpow_le_rpow hs.le hc hb
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (inv_nonneg.mpr hy.le),
    Real.inv_rpow hy.le,← Real.rpow_neg hy.le] at hpow
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hC

/-- Mellin continuation supplied by first means at integer cutoffs. -/
def triangularDirichletContinuation (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  s*(s+1)*mellin (fun y => (triangularPrimeProfile c y : ℂ)) s

theorem differentiableAt_triangularDirichletContinuation (c : ℕ → ℝ) {C b : ℝ}
    (hC : 0≤C) (hb : 0≤b)
    (h : ∀ N : ℕ, 1≤N → |triangularPrimeProfile c (N:ℝ)⁻¹| ≤ C*(N:ℝ)^b)
    {s : ℂ} (hs : b<s.re) : DifferentiableAt ℂ (triangularDirichletContinuation c) s := by
  have hzero : (fun y => (triangularPrimeProfile c y : ℂ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    rw [triangularPrimeProfile_eq_sum c (by linarith only [hy]) 0 (by simpa using hy),sum_range_zero,ofReal_zero]
  have hbot : (fun y => (triangularPrimeProfile c y : ℂ)) =O[𝓝[>] 0] fun y : ℝ => y^(-b) := by
    apply IsBigO.of_bound (C*2^b)
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
      with y hy hy1
    have hy' : 0<y := hy
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy'.le _)]
      using profile_bound_between_samples c hC hb h hy' hy1.le
  have hd := mellin_differentiableAt_of_isBigO_rpow (a := s.re+1)
    (Complex.continuous_ofReal.comp_continuousOn (profile_continuous c) |>.locallyIntegrableOn measurableSet_Ioi)
    (hzero.isBigO.trans (isBigO_zero _ _)) (lt_add_one _) hbot hs
  exact (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul hd

/-- The continuation agrees with the coefficient series on its half-plane of absolute
convergence provided by the polynomial coefficient bound. -/
theorem triangularDirichletContinuation_eq_series (c : ℕ → ℝ) {C A : ℝ}
    (h : ∀ n : ℕ, |c (n+1)| ≤ C*((n:ℝ)+1)^A) {s : ℂ} (hs : A+1<s.re) (hs0 : 0<s.re) :
    triangularDirichletContinuation c s = ∑' n : ℕ, (c (n+1):ℂ)*(((n:ℂ)+1)^(-s)) := by
  have hkernel : IntegrableOn (fun t : ℝ => (t:ℂ)^((s.re:ℂ)-1) • _root_.RHTower.perronKernelG t) (Ioi 0) :=
    _root_.RHTower.perronKernel_mellinConvergent hs0
  have hk := hkernel.norm
  have hint : IntegrableOn (fun t : ℝ => t^(s.re-1)*‖_root_.RHTower.perronKernelG t‖) (Ioi 0) := by
    apply hk.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0<t := ht
    rw [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht']
    simp
  have hm := _root_.RHTower.mellin_tsum_kernel _root_.RHTower.continuous_perronKernelG.continuousOn hint
    (e := fun n => (c (n+1):ℂ)) (fun n => by simpa only [Complex.norm_real,Real.norm_eq_abs] using h n) hs
  have he (y : ℝ) : (triangularPrimeProfile c y : ℂ) =
      ∑' n : ℕ, (c (n+1):ℂ)*_root_.RHTower.perronKernelG (((n:ℝ)+1)*y) := by
    rw [triangularPrimeProfile,Complex.ofReal_tsum]
    simp only [_root_.RHTower.perronKernelG,ofReal_mul]
  rw [triangularDirichletContinuation,show (fun y => (triangularPrimeProfile c y:ℂ)) = _ from funext he,hm,
    _root_.RHTower.perronKernel_mellin hs0]
  have hn : s ≠ 0 := by intro e; rw [e] at hs0; simp at hs0
  have hn' : s+1 ≠ 0 := by intro e; have := congrArg Complex.re e; simp at this; linarith
  push_cast
  field_simp

#print axioms differentiableAt_triangularDirichletContinuation
#print axioms triangularDirichletContinuation_eq_series

end GaloisForLFunctions.ExceptionalLayerTheory
