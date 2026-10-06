import GaloisForLFunctions.RHTower.ChiCubicCoupledKernelDecay
import GaloisForLFunctions.RHTower.ChiCubicCurvedFrequencyEnergy
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Uniform strip energy of the actual reciprocal cubic kernel

The coupled kernel majorant is squared against the actual compact physical
density. Its uniform mass and the scalar curved-strip energy theorem admit
the joint integral, so weighted Cauchy–Schwarz and Fubini give uniform weighted
L² control through every order below 3/2. All real curvatures are included.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private def densityWeight (δ h x : ℝ) : ℝ :=
  ‖bagCubicNormalizedSlice δ h x‖+‖deriv (bagCubicNormalizedSlice δ h) x‖

private theorem density_weight_properties
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    Continuous (densityWeight δ.1 h.1) ∧
      (∀x : ℝ, x∉Icc (1 : ℝ) 2 → densityWeight δ.1 h.1 x=0) := by
  have hF := (bagCubicNormalizedSlice_properties δ h).1
  refine ⟨hF.continuous.norm.add (hF.continuous_deriv (by simp)).norm,?_⟩
  intro x hx
  have hs : tsupport (bagCubicNormalizedSlice δ.1 h.1)⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr
      (bagCubicNormalizedSlice_properties δ h).2) isClosed_Icc
  have hd := deriv_of_notMem_tsupport (fun hh => hx (hs hh))
  simp only [densityWeight,(bagCubicNormalizedSlice_properties δ h).2 x hx,hd,norm_zero,add_zero]

private def physicalDensity (δ h : ℝ) (pq : ℝ×ℝ) : ℝ :=
  densityWeight δ h pq.1*densityWeight δ h pq.2

private theorem physical_density_properties
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    Continuous (physicalDensity δ.1 h.1) ∧
      HasCompactSupport (physicalDensity δ.1 h.1) ∧
      (∀pq, pq∉Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2 → physicalDensity δ.1 h.1 pq=0) := by
  have hw := density_weight_properties δ h
  have hc : Continuous (physicalDensity δ.1 h.1) :=
    (hw.1.comp continuous_fst).mul (hw.1.comp continuous_snd)
  have hs (pq : ℝ×ℝ) (hpq : pq∉Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2) :
      physicalDensity δ.1 h.1 pq=0 := by
    by_cases hp : pq.1∈Icc (1 : ℝ) 2
    · have hq : pq.2∉Icc (1 : ℝ) 2 := fun hh => hpq ⟨hp,hh⟩
      simp only [physicalDensity,hw.2 pq.2 hq,mul_zero]
    · simp only [physicalDensity,hw.2 pq.1 hp,zero_mul]
  exact ⟨hc,HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
    (Function.support_subset_iff'.mpr hs),hs⟩

private theorem physical_density_nonneg (δ h : ℝ) (pq : ℝ×ℝ) :
    0≤physicalDensity δ h pq := by
  dsimp only [physicalDensity,densityWeight]
  positivity

private theorem physical_density_mass :
    ∃ M : ℝ, 0<M ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1},
      (∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq)≤M := by
  obtain ⟨A,hA,hAb⟩ := bagCubicNormalizedSlice_derivative_budgets 0
  obtain ⟨B,hB,hBb⟩ := bagCubicNormalizedSlice_derivative_budgets 1
  refine ⟨(A+B)^2,by positivity,fun δ h => ?_⟩
  have hmass : Integrable (fun x : ℝ => ‖bagCubicNormalizedSlice δ.1 h.1 x‖) ∧
      (∫x : ℝ, ‖bagCubicNormalizedSlice δ.1 h.1 x‖)≤A := by
    simpa only [iteratedDeriv_zero,Nat.zero_sub,pow_zero,div_one] using hAb δ h
  have hvar : Integrable (fun x : ℝ => ‖deriv (bagCubicNormalizedSlice δ.1 h.1) x‖) ∧
      (∫x : ℝ, ‖deriv (bagCubicNormalizedSlice δ.1 h.1) x‖)≤B := by
    simpa only [iteratedDeriv_one,Nat.sub_self,pow_zero,div_one] using hBb δ h
  have hi : Integrable (densityWeight δ.1 h.1) := hmass.1.add hvar.1
  have hb : (∫x : ℝ, densityWeight δ.1 h.1 x)≤A+B := by
    dsimp only [densityWeight]
    rw [integral_add hmass.1 hvar.1]
    exact add_le_add hmass.2 hvar.2
  have hn : 0≤∫x : ℝ, densityWeight δ.1 h.1 x := integral_nonneg (fun x =>
    add_nonneg (norm_nonneg _) (norm_nonneg _))
  calc (∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq)
      = (∫x : ℝ, densityWeight δ.1 h.1 x)^2 := by
        dsimp only [physicalDensity]
        change (∫pq : ℝ×ℝ, densityWeight δ.1 h.1 pq.1*densityWeight δ.1 h.1 pq.2 ∂volume.prod volume)=_
        rw [integral_prod _ (hi.mul_prod hi)]
        simp_rw [integral_const_mul]
        rw [integral_mul_const,pow_two]
    _ ≤ _ := pow_le_pow_left₀ hn hb 2

private theorem reciprocal_kernel_measurable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (lam : ℝ) :
    Measurable (fun ab : ℝ×ℝ => bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)) := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  let f : (((ℝ×ℝ)×ℝ)×ℝ)×ℝ→ℂ := fun z =>
    F z.2*F z.1.2*star (F z.1.1.2)/(z.1.1.2 : ℂ)^2*
      (bagPhysicalHeightWindow (z.2*z.1.2/z.1.1.2) : ℂ)*
      bourgainOscillation (-(z.2*z.1.1.1.2+z.1.2*z.1.1.1.1+lam*z.1.1.1.1*z.1.1.1.2)/z.1.1.2)
  have hF : Measurable F := (bagCubicNormalizedSlice_properties δ h).1.continuous.measurable
  have hW : Measurable (bagPhysicalHeightWindow : ℝ→ℝ) := (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous.measurable
  have hf : Measurable f := by
    dsimp only [f]
    unfold bourgainOscillation
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right'.integral_prod_right'.integral_prod_right'.measurable

private def inverseKernel (lam : ℝ) (pq ab : ℝ×ℝ) : ℝ :=
  1/((1+|ab.1|)*(1+|ab.2|)*(1+|ab.1*pq.2+ab.2*pq.1+lam*ab.1*ab.2|))

private def energyKernel (s lam : ℝ) (pq ab : ℝ×ℝ) : ℝ :=
  (1+|ab.1|+|ab.2|)^(2*s)/
    ((1+|ab.1|)^2*(1+|ab.2|)^2*(1+|ab.1*pq.2+ab.2*pq.1+lam*ab.1*ab.2|)^2)

private theorem energy_kernel_nonneg (s lam : ℝ) (pq ab : ℝ×ℝ) :
    0≤energyKernel s lam pq ab := by
  dsimp only [energyKernel]
  positivity

private theorem inverse_kernel_continuous (lam : ℝ) :
    Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) => inverseKernel lam z.1 z.2) := by
  apply continuous_const.div
  · fun_prop
  · intro z
    positivity

private theorem energy_kernel_measurable (s lam : ℝ) :
    Measurable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => energyKernel s lam z.1 z.2) := by
  dsimp only [energyKernel]
  fun_prop

private theorem energy_kernel_eq (s lam : ℝ) (pq ab : ℝ×ℝ) :
    energyKernel s lam pq ab=(1+|ab.1|+|ab.2|)^(2*s)*(inverseKernel lam pq ab)^2 := by
  simp only [energyKernel,inverseKernel,div_eq_mul_inv,mul_pow,inv_pow,mul_inv_rev]
  ring

private theorem density_energy_integrable
    (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)})
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (lam : ℝ) (C : ℝ)
    (hCb : ∀u v : {r : ℝ // r∈Icc (1 : ℝ) 2},
      IntegrableOn (energyKernel s.1 lam (u.1,v.1)) {ab : ℝ×ℝ | |lam*ab.1|≤1/4} ∧
      (∫ab : ℝ×ℝ in {ab : ℝ×ℝ | |lam*ab.1|≤1/4}, energyKernel s.1 lam (u.1,v.1) ab)≤C) :
    Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => physicalDensity δ.1 h.1 z.1*energyKernel s.1 lam z.1 z.2)
      (volume.prod (volume.restrict {ab : ℝ×ℝ | |lam*ab.1|≤1/4})) ∧
      (∫pq : ℝ×ℝ,∫ab : ℝ×ℝ in {ab : ℝ×ℝ | |lam*ab.1|≤1/4},
        physicalDensity δ.1 h.1 pq*energyKernel s.1 lam pq ab)≤
          C*(∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq) := by
  let μ := volume.restrict {ab : ℝ×ℝ | |lam*ab.1|≤1/4}
  let f : (ℝ×ℝ)×(ℝ×ℝ)→ℝ := fun z => physicalDensity δ.1 h.1 z.1*energyKernel s.1 lam z.1 z.2
  have hρ := physical_density_properties δ h
  have hρi : Integrable (physicalDensity δ.1 h.1) := hρ.1.integrable_of_hasCompactSupport hρ.2.1
  have hm : Measurable f := (hρ.1.measurable.comp measurable_fst).mul (energy_kernel_measurable s.1 lam)
  have hn (pq ab : ℝ×ℝ) : 0≤f (pq,ab) :=
    mul_nonneg (physical_density_nonneg _ _ _) (energy_kernel_nonneg _ _ _ _)
  have hfib (pq : ℝ×ℝ) : Integrable (fun ab => f (pq,ab)) μ ∧
      (∫ab : ℝ×ℝ, ‖f (pq,ab)‖ ∂μ)≤C*physicalDensity δ.1 h.1 pq := by
    by_cases hpq : pq∈Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2
    · have hh := hCb ⟨pq.1,hpq.1⟩ ⟨pq.2,hpq.2⟩
      refine ⟨hh.1.const_mul (physicalDensity δ.1 h.1 pq),?_⟩
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (hn pq _)]
      dsimp only [f]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hh.2 (physical_density_nonneg _ _ _)).trans_eq (mul_comm _ _)
    · have hz := hρ.2.2 pq hpq
      simp only [f,hz,zero_mul,norm_zero,integral_zero,mul_zero]
      exact ⟨integrable_zero _ _ _ ,le_rfl⟩
  have hi : Integrable f (volume.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun pq => (hfib pq).1),?_⟩
    apply (hρi.const_mul C).mono' hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [] with pq
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun ab => norm_nonneg _))]
    exact (hfib pq).2
  refine ⟨hi,?_⟩
  calc (∫pq : ℝ×ℝ,∫ab : ℝ×ℝ, f (pq,ab) ∂μ)
      = ∫pq : ℝ×ℝ,∫ab : ℝ×ℝ, ‖f (pq,ab)‖ ∂μ := by
        simp_rw [Real.norm_eq_abs,abs_of_nonneg (hn _ _)]
    _ ≤ ∫pq : ℝ×ℝ, C*physicalDensity δ.1 h.1 pq :=
      integral_mono hi.integral_norm_prod_left (hρi.const_mul C) (fun pq => (hfib pq).2)
    _ = _ := integral_const_mul _ _

private theorem weighted_square_majorant
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (lam : ℝ) (ab : ℝ×ℝ) :
    (∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*inverseKernel lam pq ab)^2≤
      (∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq)*
        ∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*(inverseKernel lam pq ab)^2 := by
  have hρ := physical_density_properties δ h
  have hg : Continuous (fun pq : ℝ×ℝ => inverseKernel lam pq ab) :=
    (inverse_kernel_continuous lam).comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (physicalDensity δ.1 h.1) := hρ.1.integrable_of_hasCompactSupport hρ.2.1
  have hi2 : Integrable (fun pq : ℝ×ℝ => physicalDensity δ.1 h.1 pq*(inverseKernel lam pq ab)^2) :=
    (hρ.1.mul (hg.pow 2)).integrable_of_hasCompactSupport hρ.2.1.mul_right
  exact GaloisForLFunctions.HTGeometry.sq_integral_weighted_le
    (physical_density_nonneg _ _) hρ.1.aestronglyMeasurable hg.aestronglyMeasurable hi hi2

private theorem kernel_majorant_eq (δ h lam : ℝ) (ab pq : ℝ×ℝ) :
    ((‖bagCubicNormalizedSlice δ h pq.1‖+‖deriv (bagCubicNormalizedSlice δ h) pq.1‖)*
      (‖bagCubicNormalizedSlice δ h pq.2‖+‖deriv (bagCubicNormalizedSlice δ h) pq.2‖))/
      ((1+|ab.1|)*(1+|ab.2|)*(1+|pq.1*ab.2+pq.2*ab.1+lam*ab.1*ab.2|))=
    physicalDensity δ h pq*inverseKernel lam pq ab := by
  have hd : pq.1*ab.2+pq.2*ab.1+lam*ab.1*ab.2=ab.1*pq.2+ab.2*pq.1+lam*ab.1*ab.2 := by ring
  simp only [physicalDensity,densityWeight,inverseKernel,hd,mul_one_div]

private theorem kernel_weighted_square_bound
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (s lam C : ℝ) (ab : ℝ×ℝ)
    (hK : ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖≤
      C*(∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*inverseKernel lam pq ab)) :
    (1+|ab.1|+|ab.2|)^(2*s)*‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2≤
      C^2*(∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq)*
        ∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*energyKernel s lam pq ab := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) hK 2
  rw [mul_pow] at hs
  have hcs := weighted_square_majorant δ h lam ab
  have hsq := hs.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg C))
  calc (1+|ab.1|+|ab.2|)^(2*s)*‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2
      ≤ (1+|ab.1|+|ab.2|)^(2*s)*(C^2*((∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq)*
          ∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*(inverseKernel lam pq ab)^2)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      simp_rw [energy_kernel_eq]
      have he : (∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*
          ((1+|ab.1|+|ab.2|)^(2*s)*(inverseKernel lam pq ab)^2))=
          (1+|ab.1|+|ab.2|)^(2*s)*∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*(inverseKernel lam pq ab)^2 := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with pq
        ring
      rw [he]
      ring

/-- Uniform weighted strip energy of the full actual reciprocal cubic kernel. -/
theorem bagCubicReciprocalKernel_uniform_strip_energy (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀lam : ℝ,
      IntegrableOn (fun ab : ℝ×ℝ => (1+|ab.1|+|ab.2|)^(2*s.1)*
        ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2)
        {ab : ℝ×ℝ | |lam*ab.1|≤1/4} ∧
      (∫ab : ℝ×ℝ in {ab : ℝ×ℝ | |lam*ab.1|≤1/4},
        (1+|ab.1|+|ab.2|)^(2*s.1)*‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2)≤C := by
  obtain ⟨K,hK,hKb⟩ := bagCubicReciprocalKernel_coupled_decay
  obtain ⟨M,hM,hMb⟩ := physical_density_mass
  obtain ⟨B,hB,hBb⟩ := bagCubicCurvedFrequency_uniform_strip_energy s
  refine ⟨K^2*M^2*B,by positivity,fun δ h lam => ?_⟩
  let μ := volume.restrict {ab : ℝ×ℝ | |lam*ab.1|≤1/4}
  let mass := ∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq
  let G : ℝ×ℝ→ℝ := fun ab => ∫pq : ℝ×ℝ, physicalDensity δ.1 h.1 pq*energyKernel s.1 lam pq ab
  let J : ℝ×ℝ→ℝ := fun ab => (1+|ab.1|+|ab.2|)^(2*s.1)*
    ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2
  have hf := density_energy_integrable s δ h lam B (hBb lam)
  have hGi : Integrable G μ := hf.1.integral_prod_right
  have hGtotal : (∫ab : ℝ×ℝ, G ab ∂μ)≤B*mass := by
    dsimp only [G]
    rw [←integral_integral_swap hf.1]
    exact hf.2
  have hmass : 0 ≤ mass := integral_nonneg (physical_density_nonneg _ _)
  have hmassb : mass≤M := hMb δ h
  have hKm := reciprocal_kernel_measurable δ h lam
  have hJm : Measurable J := by
    dsimp only [J]
    fun_prop
  have hJn (ab : ℝ×ℝ) : 0≤J ab := by dsimp only [J]; positivity
  have hpw (ab : ℝ×ℝ) : J ab≤K^2*mass*G ab := by
    have hh := (hKb δ h ab.1 ab.2 (lam*ab.1*ab.2)).2
    simp_rw [kernel_majorant_eq] at hh
    exact kernel_weighted_square_bound δ h s.1 lam K ab hh
  have hJi : Integrable J μ := by
    apply (hGi.const_mul (K^2*mass)).mono' hJm.aestronglyMeasurable
    filter_upwards [] with ab
    rw [Real.norm_eq_abs,abs_of_nonneg (hJn ab)]
    exact hpw ab
  refine ⟨hJi,?_⟩
  calc (∫ab : ℝ×ℝ, J ab ∂μ)
      ≤ ∫ab : ℝ×ℝ, K^2*mass*G ab ∂μ := integral_mono hJi (hGi.const_mul _) hpw
    _ = K^2*mass*(∫ab : ℝ×ℝ, G ab ∂μ) := integral_const_mul _ _
    _ ≤ K^2*mass*(B*mass) := mul_le_mul_of_nonneg_left hGtotal (by positivity)
    _ = K^2*mass^2*B := by ring
    _ ≤ K^2*M^2*B := by
      gcongr


end RHTower.BAGTrace
