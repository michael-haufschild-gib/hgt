import GaloisForLFunctions.RHTower.ChiCubicCoupledKernelDecay
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay

/-!
# All-order frequency decay of the actual reciprocal cubic kernel

The fixed window is attached to the actual Gaussian/logarithmic slice before
estimating its derivatives. Native repeated integration by parts, the proved
actual mass budgets, and exact tangential symmetry give decay in the larger
frequency, uniformly in the full curved defect and shrinking cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private def physicalWindowC (x : ℝ) : ℂ := (bagPhysicalHeightWindow x : ℝ)

private theorem physical_window_smooth : ContDiff ℝ ∞ physicalWindowC :=
  Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff

private theorem physical_window_compact : HasCompactSupport physicalWindowC :=
  bagPhysicalHeightWindow.hasCompactSupport.comp_left (by simp)

private theorem physical_window_derivative_bounds (n : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀x : ℝ, ‖iteratedDeriv n physicalWindowC x‖≤B := by
  have hc := physical_window_smooth.continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))
  have hs := GaloisForLFunctions.HTGeometry.HasCompactSupport.iteratedDeriv_of_hasCompactSupport
    physical_window_compact n
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0+1,by positivity,fun x => ?_⟩
  by_cases hx : x∈tsupport (iteratedDeriv n physicalWindowC)
  · exact (hB x hx).trans (by linarith [le_max_left B 0])
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    positivity

private theorem scaled_window_derivative_bound (n : ℕ) (B : ℝ)
    (hB : ∀x : ℝ, ‖iteratedDeriv n physicalWindowC x‖≤B)
    (k : {r : ℝ // |r|≤2}) (x : ℝ) :
    ‖iteratedDeriv n (fun y : ℝ => physicalWindowC (k.1*y)) x‖≤(2 : ℝ)^n*B := by
  have hw : ContDiff ℝ (n : ℕ) physicalWindowC := physical_window_smooth.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))
  rw [iteratedDeriv_comp_const_smul hw k.1]
  simp only [norm_smul,norm_pow,Real.norm_eq_abs]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) k.2 n) (hB _) (norm_nonneg _) (by positivity)

private theorem window_slice_smooth
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) (k : ℝ) :
    ContDiff ℝ ∞ (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k*x)) :=
  (bagCubicNormalizedSlice_properties δ h).1.mul
    (physical_window_smooth.comp (contDiff_const.mul contDiff_id))

private theorem slice_compact
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    HasCompactSupport (bagCubicNormalizedSlice δ.1 h.1) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (Function.support_subset_iff'.mpr (bagCubicNormalizedSlice_properties δ h).2)

private theorem window_slice_derivative_budgets (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀k : {r : ℝ // |r|≤2},
      Integrable (iteratedDeriv n (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x))) ∧
      (∫x : ℝ, ‖iteratedDeriv n (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)) x‖)≤C/δ.1^(n-1) := by
  choose A hA hAb using bagCubicNormalizedSlice_derivative_budgets
  choose B hB hBb using physical_window_derivative_bounds
  let C := ∑i∈Finset.range (n+1), (n.choose i : ℝ)*A i*((2 : ℝ)^(n-i)*B (n-i))
  have hC : 0≤C := Finset.sum_nonneg (fun i _ => by
    have ha := hA i
    have hb := hB (n-i)
    positivity)
  refine ⟨C+1,by positivity,fun δ h k => ?_⟩
  have hF := (bagCubicNormalizedSlice_properties δ h).1
  have hW : ContDiff ℝ ∞ (fun x => physicalWindowC (k.1*x)) :=
    physical_window_smooth.comp (contDiff_const.mul contDiff_id)
  have hi : Integrable (iteratedDeriv n (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x))) :=
    GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_of_hasCompactSupport
      ((window_slice_smooth δ h k.1).of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤)))
      (slice_compact δ h).mul_right (le_refl n)
  refine ⟨hi,?_⟩
  let M : ℝ→ℝ := fun x => ∑i∈Finset.range (n+1),
    (n.choose i : ℝ)*‖iteratedDeriv i (bagCubicNormalizedSlice δ.1 h.1) x‖*((2 : ℝ)^(n-i)*B (n-i))
  have hMi (i : ℕ) : Integrable (fun x : ℝ =>
      (n.choose i : ℝ)*‖iteratedDeriv i (bagCubicNormalizedSlice δ.1 h.1) x‖*((2 : ℝ)^(n-i)*B (n-i))) :=
    (((hAb i δ h).1).const_mul _).mul_const _
  have hM : Integrable M := integrable_finsetSum _ (fun i _ => hMi i)
  have hpw (x : ℝ) :
      ‖iteratedDeriv n (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)) x‖≤M x := by
    change ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1*(fun x => physicalWindowC (k.1*x))) x‖≤_
    rw [iteratedDeriv_mul (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt
      (hW.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
    simp only [norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (scaled_window_derivative_bound (n-i) (B (n-i)) (hBb (n-i)) k x) (by positivity)
  calc (∫x : ℝ, ‖iteratedDeriv n (fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)) x‖)
      ≤ ∫x : ℝ, M x := integral_mono hi.norm hM hpw
    _ = ∑i∈Finset.range (n+1), (n.choose i : ℝ)*
        (∫x : ℝ, ‖iteratedDeriv i (bagCubicNormalizedSlice δ.1 h.1) x‖)*((2 : ℝ)^(n-i)*B (n-i)) := by
      rw [integral_finsetSum _ (fun i _ => hMi i)]
      simp only [integral_mul_const,integral_const_mul]
    _ ≤ ∑i∈Finset.range (n+1), (n.choose i : ℝ)*(A i/δ.1^(n-1))*((2 : ℝ)^(n-i)*B (n-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hp : δ.1^(n-1)≤δ.1^(i-1) := pow_le_pow_of_le_one δ.2.1.le
        (by linarith only [δ.2.2]) (Nat.sub_le_sub_right hin 1)
      have hb : (∫x : ℝ, ‖iteratedDeriv i (bagCubicNormalizedSlice δ.1 h.1) x‖)≤A i/δ.1^(n-1) :=
        (hAb i δ h).2.trans (div_le_div_of_nonneg_left (hA i).le (pow_pos δ.2.1 _) hp)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)) (mul_nonneg (by positivity) (hB (n-i)).le)
    _ = C/δ.1^(n-1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (C+1)/δ.1^(n-1) := div_le_div_of_nonneg_right (by linarith) (pow_pos δ.2.1 _).le

private theorem window_slice_oscillation (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀k : {r : ℝ // |r|≤2},
      ∀ξ : ℝ, ξ≠0 →
      ‖∫x : ℝ, bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)*bourgainOscillation (-ξ*x)‖≤
        C/δ.1^(n-1)/|ξ|^n := by
  obtain ⟨C,hC,hCb⟩ := window_slice_derivative_budgets n
  refine ⟨C,hC,fun δ h k ξ hξ => ?_⟩
  let f : ℝ→ℂ := fun x => bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)
  have hf : ContDiff ℝ (n : ℕ) f := (window_slice_smooth δ h k.1).of_le
    (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))
  have hs : HasCompactSupport f := (slice_compact δ h).mul_right
  have hh := GaloisForLFunctions.HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv n hf
    (fun i hi => GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_of_hasCompactSupport hf hs hi) hξ
  have he (x : ℝ) : Complex.exp (-((ξ : ℂ)*(x : ℂ))*Complex.I)=bourgainOscillation (-ξ*x) := by
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  simp_rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right (hCb δ h k).2 (pow_nonneg (abs_nonneg _) _))

private def tangentialFiber (δ h q r b : ℝ) : ℂ :=
  ∫p : ℝ, bagCubicNormalizedSlice δ h p*physicalWindowC (p*q/r)*bourgainOscillation (-b*p/r)

private theorem phase_add (x y : ℝ) :
    bourgainOscillation (x+y)=bourgainOscillation x*bourgainOscillation y := by
  unfold bourgainOscillation
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem kernel_fiber_identity (δ h a b c : ℝ) :
    bagCubicReciprocalKernel δ h a b c=
      ∫r : ℝ, (star (bagCubicNormalizedSlice δ h r)/(r : ℂ)^2)*bourgainOscillation (-c/r)*
        (∫q : ℝ, bagCubicNormalizedSlice δ h q*bourgainOscillation (-a*q/r)*tangentialFiber δ h q r b) := by
  unfold bagCubicReciprocalKernel tangentialFiber
  simp_rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with p
  have hp : bourgainOscillation (-(p*b+q*a+c)/r)=
      bourgainOscillation (-c/r)*bourgainOscillation (-a*q/r)*bourgainOscillation (-b*p/r) := by
    rw [←phase_add,←phase_add]
    congr 1
    ring
  rw [hp]
  dsimp only [physicalWindowC]
  ring

private theorem tangential_fiber_bound (n : ℕ) (C : ℝ) (hC : 0<C)
    (hCb : ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀k : {r : ℝ // |r|≤2}, ∀ξ : ℝ, ξ≠0 →
      ‖∫x : ℝ, bagCubicNormalizedSlice δ.1 h.1 x*physicalWindowC (k.1*x)*bourgainOscillation (-ξ*x)‖≤
        C/δ.1^(n-1)/|ξ|^n)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (q r : {x : ℝ // x∈Icc (1 : ℝ) 2}) (b : ℝ) (hb : b≠0) :
    ‖tangentialFiber δ.1 h.1 q.1 r.1 b‖≤C*(2 : ℝ)^n/δ.1^(n-1)/|b|^n := by
  have hr : 0<r.1 := lt_of_lt_of_le zero_lt_one r.2.1
  have hq : 0<q.1 := lt_of_lt_of_le zero_lt_one q.2.1
  have hk : |q.1/r.1|≤2 := by
    rw [abs_of_pos (div_pos hq hr)]
    apply (div_le_iff₀ hr).mpr
    linarith [q.2.2,r.2.1]
  have hh := hCb δ h ⟨q.1/r.1,hk⟩ (b/r.1) (div_ne_zero hb hr.ne')
  have he : tangentialFiber δ.1 h.1 q.1 r.1 b=
      ∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*physicalWindowC ((q.1/r.1)*p)*bourgainOscillation (-(b/r.1)*p) := by
    apply integral_congr_ae
    filter_upwards [] with p
    congr 2 <;> ring
  rw [he]
  refine hh.trans ?_
  calc
    C / δ.1^(n-1) / |b/r.1|^n = C / δ.1^(n-1) * r.1^n / |b|^n := by
      rw [abs_div,abs_of_pos hr,div_pow]
      field_simp
    _ ≤ C/δ.1^(n-1)*(2 : ℝ)^n/|b|^n :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le r.2.2 n)
          (div_nonneg hC.le (pow_nonneg δ.2.1.le _))) (pow_nonneg (abs_nonneg _) _)
    _ = _ := by ring

private theorem kernel_b_decay (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀a b c : ℝ,
      |b|^n*‖bagCubicReciprocalKernel δ.1 h.1 a b c‖≤C/δ.1^(n-1) := by
  obtain ⟨B,hB,hBb⟩ := window_slice_oscillation n
  obtain ⟨A,hA,hAb⟩ := bagCubicNormalizedSlice_derivative_budgets 0
  refine ⟨A^2*B*(2 : ℝ)^n,by positivity,fun δ h a b c => ?_⟩
  have hδ := δ.2.1
  by_cases hb : b=0
  · simp only [hb,abs_zero,zero_pow hn.ne',zero_mul]
    positivity
  let F := bagCubicNormalizedSlice δ.1 h.1
  let S := B*(2 : ℝ)^n/δ.1^(n-1)/|b|^n
  have hS : 0≤S := by dsimp only [S]; positivity
  have hm : Integrable (fun x : ℝ => ‖F x‖) ∧ (∫x : ℝ, ‖F x‖)≤A := by
    simpa only [iteratedDeriv_zero,Nat.zero_sub,pow_zero,div_one] using hAb δ h
  have hf (q r : {x : ℝ // x∈Icc (1 : ℝ) 2}) : ‖tangentialFiber δ.1 h.1 q.1 r.1 b‖≤S :=
    tangential_fiber_bound n B hB hBb δ h q r b hb
  have hq (r : {x : ℝ // x∈Icc (1 : ℝ) 2}) :
      ‖∫q : ℝ, F q*bourgainOscillation (-a*q/r.1)*tangentialFiber δ.1 h.1 q r.1 b‖≤A*S := by
    calc ‖∫q : ℝ, F q*bourgainOscillation (-a*q/r.1)*tangentialFiber δ.1 h.1 q r.1 b‖
        ≤ ∫q : ℝ, ‖F q‖*S := by
          apply norm_integral_le_of_norm_le (hm.1.mul_const S)
          filter_upwards [] with q
          by_cases hqb : q∈Icc (1 : ℝ) 2
          · simp only [norm_mul,norm_bourgainOscillation,mul_one]
            exact mul_le_mul_of_nonneg_left (hf ⟨q,hqb⟩ r) (norm_nonneg _)
          · have hz : F q=0 := (bagCubicNormalizedSlice_properties δ h).2 q hqb
            simp only [hz,zero_mul,norm_zero,le_refl]
      _ = (∫q : ℝ, ‖F q‖)*S := integral_mul_const _ _
      _ ≤ A*S := mul_le_mul_of_nonneg_right hm.2 hS
  have hpw (r : ℝ) :
      ‖(star (F r)/(r : ℂ)^2)*bourgainOscillation (-c/r)*
        (∫q : ℝ, F q*bourgainOscillation (-a*q/r)*tangentialFiber δ.1 h.1 q r b)‖≤‖F r‖*(A*S) := by
    by_cases hrb : r∈Icc (1 : ℝ) 2
    · have hr : 0<r := lt_of_lt_of_le zero_lt_one hrb.1
      have hd : 1≤‖(r : ℂ)‖^2 := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        nlinarith [hrb.1]
      have hfrac : ‖F r‖/‖(r : ℂ)‖^2≤‖F r‖ := by
        apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
        nlinarith [norm_nonneg (F r)]
      simp only [norm_mul,norm_div,norm_star,norm_pow,norm_bourgainOscillation,mul_one]
      exact mul_le_mul hfrac (hq ⟨r,hrb⟩) (norm_nonneg _) (norm_nonneg _)
    · have hz : F r=0 := (bagCubicNormalizedSlice_properties δ h).2 r hrb
      simp only [hz,star_zero,zero_div,zero_mul,norm_zero,le_refl]
  have hh : ‖bagCubicReciprocalKernel δ.1 h.1 a b c‖≤A*(A*S) := by
    rw [kernel_fiber_identity]
    calc ‖∫r : ℝ, (star (F r)/(r : ℂ)^2)*bourgainOscillation (-c/r)*
          (∫q : ℝ, F q*bourgainOscillation (-a*q/r)*tangentialFiber δ.1 h.1 q r b)‖
        ≤ ∫r : ℝ, ‖F r‖*(A*S) := norm_integral_le_of_norm_le (hm.1.mul_const _) (Eventually.of_forall hpw)
      _ = (∫r : ℝ, ‖F r‖)*(A*S) := integral_mul_const _ _
      _ ≤ A*(A*S) := mul_le_mul_of_nonneg_right hm.2 (mul_nonneg hA.le hS)
  have he : A*(A*S)=(A^2*B*(2 : ℝ)^n/δ.1^(n-1))/|b|^n := by dsimp only [S]; ring
  rw [he] at hh
  exact (mul_comm (|b|^n) _).le.trans ((le_div_iff₀ (pow_pos (abs_pos.mpr hb) n)).mp hh)

private theorem kernel_symmetry
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c : ℝ) :
    bagCubicReciprocalKernel δ.1 h.1 a b c=bagCubicReciprocalKernel δ.1 h.1 b a c := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  unfold bagCubicReciprocalKernel
  apply integral_congr_ae
  filter_upwards [] with r
  let T : ℝ×ℝ→ℂ := fun pq => F pq.1*F pq.2*star (F r)/(r : ℂ)^2*
    (bagPhysicalHeightWindow (pq.1*pq.2/r) : ℂ)*bourgainOscillation (-(pq.1*b+pq.2*a+c)/r)
  have hF : Continuous F := (bagCubicNormalizedSlice_properties δ h).1.continuous
  have hW : Continuous (bagPhysicalHeightWindow : ℝ→ℝ) :=
    (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous
  have hc : Continuous T := by
    dsimp only [T]
    unfold bourgainOscillation
    fun_prop
  have hs : HasCompactSupport T := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
    apply Function.support_subset_iff'.mpr
    intro pq hpq
    by_cases hp : pq.1∈Icc (1 : ℝ) 2
    · have hq : pq.2∉Icc (1 : ℝ) 2 := fun hh => hpq ⟨hp,hh⟩
      have hz : F pq.2=0 := (bagCubicNormalizedSlice_properties δ h).2 pq.2 hq
      simp only [T,hz,mul_zero,zero_mul,zero_div]
    · have hz : F pq.1=0 := (bagCubicNormalizedSlice_properties δ h).2 pq.1 hp
      simp only [T,hz,zero_mul,zero_div]
  have hi : Integrable T (volume.prod volume) := hc.integrable_of_hasCompactSupport hs
  calc (∫q : ℝ,∫p : ℝ, T (p,q))=∫p : ℝ,∫q : ℝ, T (p,q) :=
      (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [T,F]
      rw [mul_comm q p,add_comm (q*a) (p*b)]
      ring

/-- Every positive order gives actual full-kernel decay in the larger frequency. -/
theorem bagCubicReciprocalKernel_frequency_decay (n : {k : ℕ // 0<k}) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀a b c : ℝ,
      (max |a| |b|)^n.1*‖bagCubicReciprocalKernel δ.1 h.1 a b c‖≤C/δ.1^(n.1-1) := by
  obtain ⟨C,hC,hCb⟩ := kernel_b_decay n.1 n.2
  refine ⟨C,hC,fun δ h a b c => ?_⟩
  by_cases hab : |a|≤|b|
  · rw [max_eq_right hab]
    exact hCb δ h a b c
  · rw [max_eq_left (le_of_not_ge hab),kernel_symmetry δ h a b c]
    exact hCb δ h b a c

end RHTower.BAGTrace
