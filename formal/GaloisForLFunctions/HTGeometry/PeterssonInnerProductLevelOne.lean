import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import GaloisForLFunctions.HTGeometry.PoincareSeriesPeterssonCoefficient
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Petersson inner product on level-one cusp forms

`⟨f, g⟩ = ∫_𝒟 conj(f) g y^k dμ` is a positive definite Hermitian form on `CuspForm 𝒮ℒ k`:
the integrand is bounded (mathlib) and `𝒟` has finite volume, so it is integrable; symmetry and
sesquilinearity are pointwise; `⟨f, f⟩ = ∫_𝒟 |f|² y^k ≥ 0`, and `⟨f, f⟩ = 0` forces `f = 0` on `𝒟`
by continuity and the positivity of the invariant measure on open sets (`𝒟` is the closure of its
interior), hence `f = 0` everywhere by modularity.  The resulting inner product space
`PeterssonSpace k` is finite dimensional by mathlib's level-one dimension formula.
-/

open UpperHalfPlane hiding I
open MeasureTheory Set ModularForm Complex ModularGroup
open scoped MatrixGroups ModularForm ComplexConjugate Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : ℤ}

theorem measurableSet_fd : MeasurableSet fd := isClosed_fd.measurableSet

theorem continuous_cuspForm (f : CuspForm 𝒮ℒ k) : Continuous f := (CuspFormClass.holo f).continuous

/-! ## Integrability and sesquilinearity -/

theorem integrableOn_fd_petersson (f g : CuspForm 𝒮ℒ k) :
    IntegrableOn (petersson k f g) fd volume := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k 𝒮ℒ f g
  exact Measure.integrableOn_of_bounded volume_fd_ne_top
    (petersson_continuous k (continuous_cuspForm f) (continuous_cuspForm g)).aestronglyMeasurable
    (ae_of_all _ hC)

theorem peterssonInner_add_right (f g₁ g₂ : CuspForm 𝒮ℒ k) :
    peterssonInner k f (g₁ + g₂) = peterssonInner k f g₁ + peterssonInner k f g₂ := by
  unfold peterssonInner
  rw [← integral_add (integrableOn_fd_petersson f g₁) (integrableOn_fd_petersson f g₂)]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  simp only [petersson, Pi.add_apply]
  ring

theorem peterssonInner_smul_right (f g : CuspForm 𝒮ℒ k) (c : ℂ) :
    peterssonInner k f (c • g) = c * peterssonInner k f g := by
  unfold peterssonInner
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  simp only [petersson, Pi.smul_apply, smul_eq_mul]
  ring

theorem peterssonInner_conj_symm (f g : ℍ → ℂ) :
    conj (peterssonInner k g f) = peterssonInner k f g := by
  unfold peterssonInner
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [petersson_symm k f g z, Complex.conj_conj]

theorem peterssonInner_add_left (f₁ f₂ g : CuspForm 𝒮ℒ k) :
    peterssonInner k (⇑f₁ + ⇑f₂) g = peterssonInner k f₁ g + peterssonInner k f₂ g := by
  rw [← peterssonInner_conj_symm (⇑f₁ + ⇑f₂) ⇑g, peterssonInner_add_right, map_add,
    peterssonInner_conj_symm, peterssonInner_conj_symm]

theorem peterssonInner_smul_left (f g : CuspForm 𝒮ℒ k) (c : ℂ) :
    peterssonInner k (c • ⇑f) g = conj c * peterssonInner k f g := by
  rw [← peterssonInner_conj_symm (c • ⇑f) ⇑g, peterssonInner_smul_right, map_mul,
    peterssonInner_conj_symm]

/-! ## Positivity -/

theorem petersson_self_eq (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, Complex.conj_mul']
  push_cast
  ring

theorem peterssonInner_self_eq_ofReal (f : CuspForm 𝒮ℒ k) :
    peterssonInner k f f = ((∫ z in fd, ‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  unfold peterssonInner
  simp_rw [petersson_self_eq]
  exact integral_ofReal

theorem re_peterssonInner_self_nonneg (f : CuspForm 𝒮ℒ k) : 0 ≤ (peterssonInner k f f).re := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun z => by positivity

theorem continuous_normSq_mul_im_zpow (f : CuspForm 𝒮ℒ k) :
    Continuous fun z : ℍ => ‖f z‖ ^ 2 * z.im ^ k :=
  ((continuous_norm.comp (continuous_cuspForm f)).pow 2).mul
    (continuous_im.zpow₀ k fun z => Or.inl z.im_ne_zero)

/-- A cusp form vanishing on `𝒟` vanishes everywhere. -/
theorem cuspForm_eq_zero_of_forall_mem_fd (f : CuspForm 𝒮ℒ k) (h : ∀ z ∈ fd, f z = 0) : f = 0 := by
  apply CuspForm.ext
  intro z
  rw [CuspForm.coe_zero, Pi.zero_apply]
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  have hf : ⇑f ∣[k] g = ⇑f := SlashInvariantFormClass.slash_action_eq f _ ⟨g, rfl⟩
  have := congrFun hf z
  rw [SL_slash_apply, h _ hg, zero_mul] at this
  exact this.symm

/-- **Definiteness**: `⟨f, f⟩ = 0` forces `f = 0`. -/
theorem eq_zero_of_peterssonInner_self_eq_zero (f : CuspForm 𝒮ℒ k)
    (h : peterssonInner k f f = 0) : f = 0 := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_eq_zero] at h
  have hnn : 0 ≤ fun z : ℍ => ‖f z‖ ^ 2 * z.im ^ k := fun z => by positivity
  have hint : Integrable (fun z : ℍ => ‖f z‖ ^ 2 * z.im ^ k) (volume.restrict fd) := by
    have : IntegrableOn (fun z : ℍ => ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ)) fd volume :=
      (integrableOn_fd_petersson f f).congr_fun (fun z _ => petersson_self_eq f z) measurableSet_fd
    exact this.re.congr (ae_of_all _ fun z => by simp only [RCLike.re_to_complex, Complex.ofReal_re])
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_fd, ae_iff] at hae
  have hzero : ∀ z ∈ fd, ‖f z‖ ^ 2 * z.im ^ k = 0 := by
    intro z hz
    by_contra hne
    have hpos : 0 < ‖f z‖ ^ 2 * z.im ^ k := lt_of_le_of_ne (hnn z) (Ne.symm hne)
    set U : Set ℍ := (fun w : ℍ => ‖f w‖ ^ 2 * w.im ^ k) ⁻¹' Ioi 0 with hU
    have hUo : IsOpen U := isOpen_Ioi.preimage (continuous_normSq_mul_im_zpow f)
    have hzU : z ∈ U := hpos
    have hne' : (U ∩ fdo).Nonempty := by
      have hcl : z ∈ closure fdo := fd_eq_closure_fdo ▸ hz
      exact mem_closure_iff.mp hcl U hUo hzU
    have hpos' : 0 < volume (U ∩ fdo) := (hUo.inter isOpen_fdo).measure_pos _ hne'
    have hnull : volume (U ∩ fdo) = 0 := by
      refine measure_mono_null (fun w hw => ?_) hae
      show ¬ (w ∈ fd → ‖f w‖ ^ 2 * w.im ^ k = (0 : ℍ → ℝ) w)
      intro himp
      have hw1 : 0 < ‖f w‖ ^ 2 * w.im ^ k := hw.1
      exact hw1.ne' (himp (fdo_subset_fd hw.2))
    exact hpos'.ne' hnull
  refine cuspForm_eq_zero_of_forall_mem_fd f fun z hz => ?_
  have hy : z.im ^ k ≠ 0 := zpow_ne_zero _ z.im_ne_zero
  rcases mul_eq_zero.mp (hzero z hz) with h0 | h0
  · simpa using h0
  · exact absurd h0 hy

/-! ## The inner product space of level-one cusp forms -/

/-- Level-one cusp forms of weight `k`, carrying the Petersson inner product. -/
def PeterssonSpace (k : ℤ) := CuspForm 𝒮ℒ k

instance : AddCommGroup (PeterssonSpace k) := inferInstanceAs (AddCommGroup (CuspForm 𝒮ℒ k))

instance : Module ℂ (PeterssonSpace k) := inferInstanceAs (Module ℂ (CuspForm 𝒮ℒ k))

/-- The underlying cusp form. -/
def PeterssonSpace.toCuspForm (f : PeterssonSpace k) : CuspForm 𝒮ℒ k := f

/-- The Petersson inner product as an `InnerProductSpace.Core`. -/
abbrev peterssonCore (k : ℤ) : InnerProductSpace.Core ℂ (PeterssonSpace k) where
  inner f g := peterssonInner k f.toCuspForm g.toCuspForm
  conj_inner_symm f g := peterssonInner_conj_symm f.toCuspForm g.toCuspForm
  re_inner_nonneg f := by
    rw [RCLike.re_to_complex]
    exact re_peterssonInner_self_nonneg f.toCuspForm
  add_left f g h := peterssonInner_add_left f.toCuspForm g.toCuspForm h.toCuspForm
  smul_left f g r := peterssonInner_smul_left f.toCuspForm g.toCuspForm r
  definite f h := eq_zero_of_peterssonInner_self_eq_zero f.toCuspForm h

instance : NormedAddCommGroup (PeterssonSpace k) := (peterssonCore k).toNormedAddCommGroup

instance : InnerProductSpace ℂ (PeterssonSpace k) := InnerProductSpace.ofCore (peterssonCore k).toCore

theorem inner_peterssonSpace (f g : PeterssonSpace k) :
    inner ℂ f g = peterssonInner k f.toCuspForm g.toCuspForm := rfl

/-- Level-one cusp forms form a finite-dimensional space (mathlib's dimension formula). -/
instance : FiniteDimensional ℂ (PeterssonSpace k) :=
  FiniteDimensional.of_injective (CuspForm.toModularFormₗ : CuspForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k)
    CuspForm.toModularFormₗ_injective

end

end GaloisForLFunctions.HTGeometry
