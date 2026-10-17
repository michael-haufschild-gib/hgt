import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-! Compact multiplicative Hankel operators from integrable profiles with a support gap.
Amplitude truncations converge in operator norm by the same row and column mass estimate. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry.MultiplicativeHankel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

local instance intervalVolumeFinite (a : ℝ) :
    IsFiniteMeasure (volume : Measure (Icc (0:ℝ) a)) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet,Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

abbrev Space (a : ℝ) := Lp ℂ 2 (volume : Measure (Icc (0:ℝ) a))

/-- An integrable multiplicative profile whose support starts strictly above one. -/
structure Profile where
  toFun : ℝ → ℂ
  measurable : Measurable toFun
  integrable : Integrable toFun
  zero_below : ∀ x : ℝ, x ≤ 1 → toFun x = 0

namespace Profile

def mass (p : Profile) : ℝ := ∫ u : ℝ, ‖p.toFun u‖

theorem mass_nonneg (p : Profile) : 0 ≤ p.mass :=
  integral_nonneg (fun _ => norm_nonneg _)

def sub (p q : Profile) : Profile where
  toFun u := p.toFun u-q.toFun u
  measurable := p.measurable.sub q.measurable
  integrable := p.integrable.sub q.integrable
  zero_below u hu := by rw [p.zero_below u hu,q.zero_below u hu,sub_self]

def truncate (p : Profile) (N : ℕ) : Profile where
  toFun := {u : ℝ | ‖p.toFun u‖ ≤ (N:ℝ)}.indicator p.toFun
  measurable := p.measurable.indicator (measurableSet_le p.measurable.norm measurable_const)
  integrable := p.integrable.indicator (measurableSet_le p.measurable.norm measurable_const)
  zero_below u hu := by
    simp only [Set.indicator_apply,p.zero_below u hu]
    split_ifs <;> rfl

theorem norm_truncate_le (p : Profile) (N : ℕ) (u : ℝ) :
    ‖(p.truncate N).toFun u‖ ≤ (N:ℝ) := by
  change ‖({u : ℝ | ‖p.toFun u‖ ≤ (N:ℝ)}.indicator p.toFun) u‖ ≤ _
  by_cases hu : ‖p.toFun u‖ ≤ (N:ℝ)
  · simpa only [Set.indicator_apply,Set.mem_setOf_eq,if_pos hu] using hu
  · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hu,norm_zero]
    positivity

theorem norm_sub_truncate_le (p : Profile) (N : ℕ) (u : ℝ) :
    ‖p.toFun u-(p.truncate N).toFun u‖ ≤ ‖p.toFun u‖ := by
  change ‖p.toFun u-({u : ℝ | ‖p.toFun u‖ ≤ (N:ℝ)}.indicator p.toFun) u‖ ≤ _
  by_cases hu : ‖p.toFun u‖ ≤ (N:ℝ)
  · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_pos hu,sub_self,norm_zero]
    exact norm_nonneg _
  · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hu,sub_zero,le_refl]

theorem tendsto_mass_sub_truncate (p : Profile) :
    Tendsto (fun N : ℕ => (p.sub (p.truncate N)).mass) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun N u => ‖p.toFun u-(p.truncate N).toFun u‖) (f := fun _ => (0:ℝ))
    (fun u => ‖p.toFun u‖)
    (fun N => ((p.measurable.sub (p.truncate N).measurable).norm).aestronglyMeasurable)
    p.integrable.norm
    (fun N => Eventually.of_forall (fun u => by
      simpa only [norm_norm] using p.norm_sub_truncate_le N u))
    (Eventually.of_forall (fun u => by
      have hev : ∀ᶠ N : ℕ in atTop, ‖p.toFun u‖ ≤ (N:ℝ) :=
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually
          (eventually_ge_atTop _)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with N hN
      simp only [truncate,Set.indicator_apply,Set.mem_setOf_eq,if_pos hN,sub_self,norm_zero]))
  simpa only [mass,sub,integral_zero] using h

theorem row_integrable (p : Profile) (a : ℝ) (x : Icc (0:ℝ) a) :
    Integrable (fun y : Icc (0:ℝ) a => p.toFun ((x:ℝ)*(y:ℝ))) := by
  by_cases hx : (x:ℝ)=0
  · simp only [hx,zero_mul,p.zero_below 0 zero_le_one]
    exact integrable_zero _ ℂ volume
  · exact (integrableOn_iff_comap_subtypeVal (μ := volume) (s := Icc (0:ℝ) a)
      measurableSet_Icc).mp
      (p.integrable.comp_mul_left' hx).integrableOn

theorem row_mass_le (p : Profile) {a : ℝ} (ha : 1 < a) (x : Icc (0:ℝ) a) :
    (∫ y : Icc (0:ℝ) a, ‖p.toFun ((x:ℝ)*(y:ℝ))‖) ≤ a*p.mass := by
  by_cases hsmall : (x:ℝ)*a ≤ 1
  · have hz (y : Icc (0:ℝ) a) : p.toFun ((x:ℝ)*(y:ℝ))=0 :=
      p.zero_below _ ((mul_le_mul_of_nonneg_left y.property.2 x.property.1).trans hsmall)
    simp only [hz,norm_zero,integral_zero]
    exact mul_nonneg (by linarith) p.mass_nonneg
  · have hx : 0 < (x:ℝ) := by
      have hx0 := x.property.1
      have hxa : 1 < (x:ℝ)*a := lt_of_not_ge hsmall
      nlinarith
    have hinv : (x:ℝ)⁻¹ ≤ a := by
      rw [← one_div]
      exact (div_le_iff₀ hx).mpr (by nlinarith [lt_of_not_ge hsmall])
    calc
      _ = ∫ y in Icc (0:ℝ) a, ‖p.toFun ((x:ℝ)*y)‖ := integral_subtype measurableSet_Icc _
      _ ≤ ∫ y : ℝ, ‖p.toFun ((x:ℝ)*y)‖ :=
        setIntegral_le_integral (p.integrable.norm.comp_mul_left' hx.ne')
          (Eventually.of_forall (fun _ => norm_nonneg _))
      _ = (x:ℝ)⁻¹*p.mass := by
        simpa only [mass,abs_of_pos (inv_pos.mpr hx),smul_eq_mul] using
          (Measure.integral_comp_mul_left (fun u : ℝ => ‖p.toFun u‖) (x:ℝ))
      _ ≤ a*p.mass := mul_le_mul_of_nonneg_right hinv p.mass_nonneg

end Profile

def kernel {a : ℝ} (ha : 1 < a) (p : Profile) :
    SchurKernel (volume : Measure (Icc (0:ℝ) a)) where
  toFun x y := p.toFun ((x:ℝ)*(y:ℝ))
  measurable := p.measurable.comp
    ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))
  bound := ⟨a*p.mass,mul_nonneg (by linarith) p.mass_nonneg⟩
  row x := by
    rw [ENNReal.coe_nnreal_eq,← ofReal_integral_norm_eq_lintegral_enorm (p.row_integrable a x)]
    exact ENNReal.ofReal_le_ofReal (p.row_mass_le ha x)
  col y := by
    rw [ENNReal.coe_nnreal_eq]
    change (∫⁻ x : Icc (0:ℝ) a, ‖p.toFun ((x:ℝ)*(y:ℝ))‖ₑ) ≤
      ENNReal.ofReal (a*p.mass)
    have h := ENNReal.ofReal_le_ofReal (p.row_mass_le ha y)
    rw [ofReal_integral_norm_eq_lintegral_enorm (p.row_integrable a y)] at h
    simpa only [mul_comm] using h

/-- The literal integral operator with kernel `p(xy)` on the original interval space. -/
def operator {a : ℝ} (ha : 1 < a) (p : Profile) : Space a →L[ℂ] Space a :=
  (kernel ha p).op

theorem operator_coeFn {a : ℝ} (ha : 1 < a) (p : Profile) (f : Space a) :
    (operator ha p f : Icc (0:ℝ) a → ℂ) =ᵐ[volume]
      fun x => ∫ y : Icc (0:ℝ) a, p.toFun ((x:ℝ)*(y:ℝ))*f y :=
  (kernel ha p).op_coeFn f

theorem operator_ae_integrable {a : ℝ} (ha : 1 < a) (p : Profile) (f : Space a) :
    ∀ᵐ x : Icc (0:ℝ) a ∂volume,
      Integrable (fun y : Icc (0:ℝ) a => p.toFun ((x:ℝ)*(y:ℝ))*f y) :=
  (kernel ha p).ae_integrable f

theorem norm_operator_le {a : ℝ} (ha : 1 < a) (p : Profile) :
    ‖operator ha p‖ ≤ a*p.mass := (kernel ha p).norm_op_le

private theorem schur_op_congr {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (k₁ k₂ : SchurKernel μ) (h : ∀ x y, k₁.toFun x y=k₂.toFun x y) : k₁.op=k₂.op := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [k₁.op_coeFn f,k₂.op_coeFn f] with x h1 h2
  rw [h1,h2]
  simp only [SchurKernel.apply,h]

theorem operator_sub {a : ℝ} (ha : 1 < a) (p q : Profile) :
    operator ha (p.sub q)=operator ha p-operator ha q := by
  exact (schur_op_congr (kernel ha (p.sub q))
    (SchurKernel.sub (kernel ha p) (kernel ha q)) (fun _ _ => rfl)).trans
      (SchurKernel.sub_op (kernel ha p) (kernel ha q))

theorem norm_operator_sub_le {a : ℝ} (ha : 1 < a) (p q : Profile) :
    ‖operator ha p-operator ha q‖ ≤ a*(p.sub q).mass := by
  rw [← operator_sub]
  exact norm_operator_le ha (p.sub q)

theorem operator_isSelfAdjoint {a : ℝ} (ha : 1 < a) (p : Profile)
    (hp : ∀ u, (starRingEnd ℂ) (p.toFun u)=p.toFun u) :
    IsSelfAdjoint (operator ha p) := by
  apply (kernel ha p).isSelfAdjoint_op
  intro x y
  change (starRingEnd ℂ) (p.toFun ((y:ℝ)*(x:ℝ)))=p.toFun ((x:ℝ)*(y:ℝ))
  rw [hp,mul_comm]

theorem operator_truncate_isHilbertSchmidt {a : ℝ} (ha : 1 < a) (p : Profile) (N : ℕ) :
    (operator ha (p.truncate N)).IsHilbertSchmidt := by
  apply (kernel ha (p.truncate N)).isHilbertSchmidt_op
  have hb (x y : Icc (0:ℝ) a) :
      ‖(p.truncate N).toFun ((x:ℝ)*(y:ℝ))‖ₑ ≤ (N:ℝ≥0∞) := by
    rw [← ofReal_norm]
    exact_mod_cast ENNReal.ofReal_le_ofReal (p.norm_truncate_le N ((x:ℝ)*(y:ℝ)))
  calc
    _ ≤ ∫⁻ _x : Icc (0:ℝ) a, ∫⁻ _y : Icc (0:ℝ) a, (N:ℝ≥0∞)^2 :=
      lintegral_mono (fun x => lintegral_mono (fun y => pow_le_pow_left' (hb x y) 2))
    _ < ∞ := by simp only [lintegral_const]; finiteness

/-- An integrable cusp profile admits a compact operator without square-integrable rows. -/
theorem operator_isCompact {a : ℝ} (ha : 1 < a) (p : Profile) :
    IsCompactOperator (operator ha p) := by
  have hmass : Tendsto (fun N : ℕ => a*(p.sub (p.truncate N)).mass) atTop (𝓝 0) := by
    simpa only [mul_zero] using p.tendsto_mass_sub_truncate.const_mul a
  have hnorm : Tendsto (fun N : ℕ => ‖operator ha (p.truncate N)-operator ha p‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmass
    rw [norm_sub_rev]
    exact norm_operator_sub_le ha p (p.truncate N)
  exact isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm)
    (Eventually.of_forall (fun N => (operator_truncate_isHilbertSchmidt ha p N).isCompactOperator))

end
end GaloisForLFunctions.HTGeometry.MultiplicativeHankel
