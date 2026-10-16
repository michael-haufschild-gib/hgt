import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy

/-!
# Bound-state inertia of the arithmetic resolvent: the lower Birman–Schwinger bound

The bound-state space `P` is the closed span of all eigenvectors of the arithmetic resolvent `R`
with eigenvalue above `1/2`. It is `R`-invariant, the resolvent is at most `1/2` on `Pᗮ`, and RH
holds exactly when `P` is the line spanned by the ground vector.

A graph vector with negative Doob energy has source `w` with `⟪Rw, w⟫ > ½‖w‖²`, so it cannot have
source in `Pᗮ`. For a polar-constrained real test `g` (both Fourier samples at `±i/2` vanish) the
Doob energy of the lift of `g/K` is exactly `Re W(g, g)`: the two polar terms of the Weil form are
the cosh and sinh moments of `g`, which vanish. A complex test splits as `Re W(f,f) =
Re W(Re f) + Re W(Im f)`, and its real and imaginary parts are again polar-constrained. Hence for
a complex subspace `V` of polar-constrained tests on which `Re W` is negative definite, the doubled
source map `V → P × P` (project both lifted parts to `P`) has trivial kernel, and the real dimension
count `2·dim_ℂ V ≤ 2·dim P` gives

`dim_ℂ V ≤ dim P`.

Consequently the finite-level negative index of the Weil form is at most the number of bound
states, and, by the finite-level inertia law, every visible separated set `T` of deep off-line
zeros forces at least `|T| − 2` bound states above `1/2`. Together with the upper bound
`≤ 2·#(off-line zeros)`, the bound states of `R` above the essential threshold are counted from
both sides by off-line zeros.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## The bound-state space -/

/-- The closed span of all bound states of the arithmetic resolvent above `1/2`. -/
def boundStateSpace : Submodule ℝ MassSpace :=
  (Submodule.span ℝ {w : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent w = μ • w}).topologicalClosure

theorem isClosed_boundStateSpace : IsClosed (boundStateSpace : Set MassSpace) :=
  Submodule.isClosed_topologicalClosure _

theorem mem_boundStateSpace_of_eigen {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (heig : resolvent w = μ • w) : w ∈ boundStateSpace :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, hμ, heig⟩)

theorem oneL_mem_boundStateSpace : oneL ∈ boundStateSpace :=
  mem_boundStateSpace_of_eigen (μ := 1) (by norm_num) (by rw [resolvent_oneL, one_smul])

theorem resolventInvariant_boundStateSpace : ResolventInvariant boundStateSpace := by
  intro w hw
  have hspan : Submodule.span ℝ {w : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent w = μ • w} ≤
      boundStateSpace.comap (resolvent : MassSpace →ₗ[ℝ] MassSpace) := by
    rw [Submodule.span_le]
    rintro v ⟨μ, hμ, hv⟩
    show resolvent v ∈ boundStateSpace
    rw [hv]
    exact boundStateSpace.smul_mem μ (mem_boundStateSpace_of_eigen hμ hv)
  have hclosed : IsClosed ((boundStateSpace.comap (resolvent : MassSpace →ₗ[ℝ] MassSpace) :
      Submodule ℝ MassSpace) : Set MassSpace) :=
    isClosed_boundStateSpace.preimage resolvent.continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hw

theorem resolventInvariant_orthogonal {V : Submodule ℝ MassSpace} (hV : ResolventInvariant V) :
    ResolventInvariant Vᗮ := by
  intro w hw
  rw [Submodule.mem_orthogonal'] at hw ⊢
  intro u hu
  rw [resolvent_symm]
  exact hw _ (hV u hu)

/-- The arithmetic resolvent is at most `1/2` on the orthogonal complement of the bound states. -/
theorem half_bound_on_orthogonal_boundStateSpace :
    ∀ w ∈ boundStateSpaceᗮ, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2 := by
  refine half_bound_on_of_no_eigenvector
    (resolventInvariant_orthogonal resolventInvariant_boundStateSpace)
    (Submodule.isClosed_orthogonal _) ?_
  intro μ w hμ hw heig
  have hmem : w ∈ boundStateSpace ⊓ boundStateSpaceᗮ :=
    ⟨mem_boundStateSpace_of_eigen hμ heig, hw⟩
  rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem

/-- **RH ⟺ the bound states above `1/2` are exactly the multiples of the ground vector.** -/
theorem riemannHypothesis_iff_boundStateSpace_eq_span_oneL :
    RiemannHypothesis ↔ boundStateSpace = ℝ ∙ oneL := by
  constructor
  · intro hRH
    obtain ⟨h1, h2⟩ := riemannHypothesis_iff_point_spectrum_above_half.mp hRH
    refine le_antisymm ?_ ?_
    · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.closed_of_finiteDimensional _)
      rw [Submodule.span_le]
      rintro w ⟨μ, hμ, hw⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      by_cases hμ1 : μ = 1
      · subst hμ1
        rw [one_smul] at hw
        exact ⟨2 * ⟪w, oneL⟫_ℝ, (h2 w hw).symm⟩
      · exact ⟨0, by rw [zero_smul, h1 μ w hμ hμ1 hw]⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact oneL_mem_boundStateSpace
  · intro h
    rw [riemannHypothesis_iff_no_primitive_bound_state]
    intro μ w hμ hprim heig
    have hw : w ∈ ℝ ∙ oneL := by
      rw [← h]
      exact mem_boundStateSpace_of_eigen hμ heig
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_oneL_sq] at hprim
    have ha : a = 0 := by linarith
    rw [ha, zero_smul]

/-! ## Negative energy forces the numerical range above `1/2` -/

theorem sourceEnergy_nonneg_of_inner_resolvent_le {p : SourceGraph}
    (h : ⟪resolvent p.val.fst, p.val.fst⟫_ℝ ≤ (1 / 2) * ‖p.val.fst‖ ^ 2) :
    0 ≤ sourceEnergy p := by
  refine energy_nonneg_on_of_half_bound (V := ℝ ∙ p.val.fst) ?_ p
    (Submodule.mem_span_singleton_self _)
  intro w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  have := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  linarith

theorem half_lt_inner_resolvent_of_energy_neg {p : SourceGraph} (hE : sourceEnergy p < 0) :
    (1 / 2) * ‖p.val.fst‖ ^ 2 < ⟪resolvent p.val.fst, p.val.fst⟫_ℝ := by
  by_contra h
  rw [not_lt] at h
  exact absurd hE (not_lt.mpr (sourceEnergy_nonneg_of_inner_resolvent_le h))

/-- A graph vector of negative Doob energy has source outside the complement of the bound
states. -/
theorem fst_notMem_orthogonal_of_energy_neg {p : SourceGraph} (hE : sourceEnergy p < 0) :
    p.val.fst ∉ boundStateSpaceᗮ := fun h =>
  absurd (half_bound_on_orthogonal_boundStateSpace _ h)
    (not_le.mpr (half_lt_inner_resolvent_of_energy_neg hE))

/-! ## Polar-constrained real tests: Doob energy equals the Weil form -/

theorem inner_compactLift_tanhL (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ⟪(compactLift v hv hvc).val.fst, tanhL⟫_ℝ = phiDoobSinhMass v := by
  have h : (fun x => (compactLift v hv hvc).val.fst x * tanhHalf x) =ᵐ[massMeasure]
      fun x => v x * tanhHalf x := by
    filter_upwards [compactLift_source_ae v hv hvc] with x hx
    rw [hx]
  rw [inner_tanhL, integral_congr_ae h, integral_mass]
  unfold phiDoobSinhMass phiDoobTest massDensity tanhHalf
  congr 1
  funext x
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem weilForm_compactLift_eq_sourceEnergy_of_polar (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hc : phiDoobCoshMass v = 0) (hs : phiDoobSinhMass v = 0) :
    weilForm (compactLift v hv hvc) = sourceEnergy (compactLift v hv hvc) := by
  unfold weilForm
  rw [inner_compactLift_oneL, inner_compactLift_tanhL, hc, hs]
  ring

/-- The two polar Fourier samples of a real test vanish iff its cosh and sinh moments vanish. -/
theorem coshHalfMoment_eq_zero_and_sinhHalfMoment_eq_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h₁ : paperFT (fun x => (g x : ℂ)) (Complex.I / 2) = 0)
    (h₂ : paperFT (fun x => (g x : ℂ)) (-(Complex.I / 2)) = 0) :
    coshHalfMoment g = 0 ∧ sinhHalfMoment g = 0 := by
  obtain ⟨hp, hm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hg hgc
  rw [paperFT_ofRealFun_I_div_two, Complex.ofReal_eq_zero] at h₁
  rw [← neg_div, paperFT_ofRealFun_neg_I_div_two, Complex.ofReal_eq_zero] at h₂
  constructor <;> linarith

/-- **Doob energy of a polar-constrained real test is its Weil form.** -/
theorem sourceEnergy_phiDoobInv_eq_re_W {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h₁ : paperFT (fun x => (g x : ℂ)) (Complex.I / 2) = 0)
    (h₂ : paperFT (fun x => (g x : ℂ)) (-(Complex.I / 2)) = 0) :
    sourceEnergy (compactLift (phiDoobInv g) (contDiff_phiDoobInv hg)
      (hasCompactSupport_phiDoobInv hgc)) =
      (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re := by
  obtain ⟨hc, hs⟩ := coshHalfMoment_eq_zero_and_sinhHalfMoment_eq_zero hg.continuous hgc h₁ h₂
  have hc' : phiDoobCoshMass (phiDoobInv g) = 0 := by
    unfold phiDoobCoshMass
    simp only [phiDoobTest_phiDoobInv]
    exact hc
  have hs' : phiDoobSinhMass (phiDoobInv g) = 0 := by
    unfold phiDoobSinhMass
    simp only [phiDoobTest_phiDoobInv]
    exact hs
  rw [← weilForm_compactLift_eq_sourceEnergy_of_polar _ _ _ hc' hs', weilForm_compactLift]
  simp only [phiDoobTest_phiDoobInv]

/-! ## Real and imaginary parts of complex tests -/

/-- Real part of a complex test. -/
def rePart (f : ℝ → ℂ) : ℝ → ℝ := fun x => (f x).re

/-- Imaginary part of a complex test. -/
def imPart (f : ℝ → ℂ) : ℝ → ℝ := fun x => (f x).im

theorem contDiff_rePart {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (rePart f) :=
  Complex.reCLM.contDiff.comp hf

theorem contDiff_imPart {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (imPart f) :=
  Complex.imCLM.contDiff.comp hf

theorem hasCompactSupport_rePart {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (rePart f) :=
  hfc.comp_left (g := fun z : ℂ => z.re) (by simp)

theorem hasCompactSupport_imPart {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (imPart f) :=
  hfc.comp_left (g := fun z : ℂ => z.im) (by simp)

/-- At a point where the Fourier character is real, the transform of the real (imaginary) part
is the real (imaginary) part of the transform. -/
theorem paperFT_rePart_imPart_of_exp_real {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {z : ℂ} {e : ℝ → ℝ} (he : Continuous e)
    (hz : ∀ u : ℝ, Complex.exp (Complex.I * z * u) = (e u : ℂ)) :
    paperFT (fun x => (rePart f x : ℂ)) z = ((paperFT f z).re : ℂ) ∧
    paperFT (fun x => (imPart f x : ℂ)) z = ((paperFT f z).im : ℂ) := by
  unfold paperFT rePart imPart
  simp only [hz]
  have hint : Integrable fun u : ℝ => f u * (e u : ℂ) :=
    (hf.mul (Complex.continuous_ofReal.comp he)).integrable_of_hasCompactSupport hfc.mul_right
  have hre := integral_re hint
  have him := integral_im hint
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre him
  constructor
  · rw [← hre, ← integral_complex_ofReal]
    congr 1
    funext u
    simp [Complex.mul_re]
  · rw [← him, ← integral_complex_ofReal]
    congr 1
    funext u
    simp [Complex.mul_im]

theorem exp_I_mul_I_div_two (u : ℝ) :
    Complex.exp (Complex.I * (Complex.I / 2) * u) = ((Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((u : ℂ) / 2) * Complex.I_mul_I

theorem exp_I_mul_neg_I_div_two (u : ℝ) :
    Complex.exp (Complex.I * (-(Complex.I / 2)) * u) = ((Real.exp (u / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-((u : ℂ) / 2)) * Complex.I_mul_I

theorem paperFT_rePart_imPart_I_div_two {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    paperFT (fun x => (rePart f x : ℂ)) (Complex.I / 2) = ((paperFT f (Complex.I / 2)).re : ℂ) ∧
    paperFT (fun x => (imPart f x : ℂ)) (Complex.I / 2) = ((paperFT f (Complex.I / 2)).im : ℂ) :=
  paperFT_rePart_imPart_of_exp_real hf hfc (e := fun u => Real.exp (-(u / 2))) (by fun_prop)
    exp_I_mul_I_div_two

theorem paperFT_rePart_imPart_neg_I_div_two {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    paperFT (fun x => (rePart f x : ℂ)) (-(Complex.I / 2)) =
      ((paperFT f (-(Complex.I / 2))).re : ℂ) ∧
    paperFT (fun x => (imPart f x : ℂ)) (-(Complex.I / 2)) =
      ((paperFT f (-(Complex.I / 2))).im : ℂ) :=
  paperFT_rePart_imPart_of_exp_real hf hfc (e := fun u => Real.exp (u / 2)) (by fun_prop)
    exp_I_mul_neg_I_div_two

/-! ## The doubled source map -/

open Classical in
/-- The source of the Doob lift of `K⁻¹ g` for a real `C²_c` test `g` (zero otherwise). -/
def testSource (g : ℝ → ℝ) : MassSpace :=
  if h : ContDiff ℝ 2 g ∧ HasCompactSupport g then
    (compactLift (phiDoobInv g) (contDiff_phiDoobInv h.1) (hasCompactSupport_phiDoobInv h.2)).val.fst
  else 0

theorem testSource_eq {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    testSource g = (compactLift (phiDoobInv g) (contDiff_phiDoobInv hg)
      (hasCompactSupport_phiDoobInv hgc)).val.fst := by
  unfold testSource
  rw [dif_pos ⟨hg, hgc⟩]

theorem testSource_ae {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    (testSource g : ℝ → ℝ) =ᵐ[massMeasure] phiDoobInv g := by
  rw [testSource_eq hg hgc]
  exact compactLift_source_ae _ _ _

theorem testSource_add {g g' : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg' : ContDiff ℝ 2 g') (hgc' : HasCompactSupport g') :
    testSource (g + g') = testSource g + testSource g' := by
  rw [Lp.ext_iff]
  have h1 : (testSource (g + g') : ℝ → ℝ) =ᵐ[massMeasure] phiDoobInv (g + g') :=
    testSource_ae (by exact hg.add hg') (hgc.add hgc')
  have h2 := testSource_ae hg hgc
  have h3 := testSource_ae hg' hgc'
  have h4 := Lp.coeFn_add (testSource g) (testSource g')
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  rw [hx1, hx4, Pi.add_apply, hx2, hx3]
  simp only [phiDoobInv, Pi.add_apply, add_div]

theorem testSource_smul (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    testSource (a • g) = a • testSource g := by
  rw [Lp.ext_iff]
  have h1 : (testSource (a • g) : ℝ → ℝ) =ᵐ[massMeasure] phiDoobInv (a • g) :=
    testSource_ae (by exact hg.const_smul a) hgc.smul_left
  have h2 := testSource_ae hg hgc
  have h3 := Lp.coeFn_smul a (testSource g)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx3, Pi.smul_apply, hx2]
  simp only [phiDoobInv, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- The doubled source map on a space of `C²_c` complex tests: the sources of the lifts of the
real and imaginary parts. -/
def doubledSource (V : Submodule ℂ (ℝ → ℂ))
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ HasCompactSupport f) :
    V →ₗ[ℝ] MassSpace × MassSpace where
  toFun f := (testSource (rePart f.1), testSource (imPart f.1))
  map_add' f g := by
    have hf := hV f.1 f.2
    have hg := hV g.1 g.2
    have h1 : rePart ((f + g : V) : ℝ → ℂ) = rePart f.1 + rePart g.1 := by
      funext x
      simp [rePart]
    have h2 : imPart ((f + g : V) : ℝ → ℂ) = imPart f.1 + imPart g.1 := by
      funext x
      simp [imPart]
    show (testSource (rePart ((f + g : V) : ℝ → ℂ)), testSource (imPart ((f + g : V) : ℝ → ℂ))) = _
    rw [h1, h2, testSource_add (contDiff_rePart hf.1) (hasCompactSupport_rePart hf.2)
      (contDiff_rePart hg.1) (hasCompactSupport_rePart hg.2),
      testSource_add (contDiff_imPart hf.1) (hasCompactSupport_imPart hf.2)
      (contDiff_imPart hg.1) (hasCompactSupport_imPart hg.2)]
    rfl
  map_smul' a f := by
    have hf := hV f.1 f.2
    have h1 : rePart ((a • f : V) : ℝ → ℂ) = a • rePart f.1 := by
      funext x
      simp [rePart]
    have h2 : imPart ((a • f : V) : ℝ → ℂ) = a • imPart f.1 := by
      funext x
      simp [imPart]
    show (testSource (rePart ((a • f : V) : ℝ → ℂ)), testSource (imPart ((a • f : V) : ℝ → ℂ))) = _
    rw [h1, h2, testSource_smul a (contDiff_rePart hf.1) (hasCompactSupport_rePart hf.2),
      testSource_smul a (contDiff_imPart hf.1) (hasCompactSupport_imPart hf.2)]
    rfl

theorem doubledSource_apply (V : Submodule ℂ (ℝ → ℂ))
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ HasCompactSupport f) (f : V) :
    doubledSource V hV f = (testSource (rePart f.1), testSource (imPart f.1)) := rfl

/-! ## The lower Birman–Schwinger bound -/

/-- **Negative subspaces of the Weil form inject into the bound states.** For a complex subspace
`V` of polar-constrained `C²_c` tests on which `Re W` is negative definite,
`dim_ℂ V ≤ dim (bound-state space)`. -/
theorem finrank_le_finrank_boundStateSpace_of_negative_subspace
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      paperFT f (Complex.I / 2) = 0 ∧ paperFT f (-(Complex.I / 2)) = 0)
    (hneg : ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < 0)
    [FiniteDimensional ℝ boundStateSpace] :
    Module.finrank ℂ V ≤ Module.finrank ℝ boundStateSpace := by
  by_contra hlt
  rw [not_le] at hlt
  haveI : IsClosed (boundStateSpace : Set MassSpace) := isClosed_boundStateSpace
  haveI : CompleteSpace boundStateSpace := IsClosed.completeSpace_coe
  haveI : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  let Ψ : V →ₗ[ℝ] boundStateSpace × boundStateSpace :=
    ((boundStateSpace.orthogonalProjectionOnto : MassSpace →ₗ[ℝ] boundStateSpace).prodMap
      (boundStateSpace.orthogonalProjectionOnto : MassSpace →ₗ[ℝ] boundStateSpace)).comp
      (doubledSource V fun f hf => ⟨(hV f hf).1, (hV f hf).2.1⟩)
  have hdim : Module.finrank ℝ (boundStateSpace × boundStateSpace) < Module.finrank ℝ V := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]
    omega
  obtain ⟨f, hfker, hf0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := Ψ) hdim)
  rw [LinearMap.mem_ker] at hfker
  have hΨ : Ψ f = (boundStateSpace.orthogonalProjectionOnto (testSource (rePart f.1)),
      boundStateSpace.orthogonalProjectionOnto (testSource (imPart f.1))) := rfl
  rw [hΨ, Prod.mk_eq_zero] at hfker
  obtain ⟨hre, him⟩ := hfker
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff] at hre him
  obtain ⟨hf, hfc, h₁, h₂⟩ := hV f.1 f.2
  have hf1 : (f.1 : ℝ → ℂ) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hreC : ContDiff ℝ 2 (rePart f.1) := contDiff_rePart hf
  have hrec : HasCompactSupport (rePart f.1) := hasCompactSupport_rePart hfc
  have himC : ContDiff ℝ 2 (imPart f.1) := contDiff_imPart hf
  have himc : HasCompactSupport (imPart f.1) := hasCompactSupport_imPart hfc
  have hre1 : paperFT (fun x => (rePart f.1 x : ℂ)) (Complex.I / 2) = 0 := by
    rw [(paperFT_rePart_imPart_I_div_two hf.continuous hfc).1, h₁, Complex.zero_re,
      Complex.ofReal_zero]
  have hre2 : paperFT (fun x => (rePart f.1 x : ℂ)) (-(Complex.I / 2)) = 0 := by
    rw [(paperFT_rePart_imPart_neg_I_div_two hf.continuous hfc).1, h₂, Complex.zero_re,
      Complex.ofReal_zero]
  have him1 : paperFT (fun x => (imPart f.1 x : ℂ)) (Complex.I / 2) = 0 := by
    rw [(paperFT_rePart_imPart_I_div_two hf.continuous hfc).2, h₁, Complex.zero_im,
      Complex.ofReal_zero]
  have him2 : paperFT (fun x => (imPart f.1 x : ℂ)) (-(Complex.I / 2)) = 0 := by
    rw [(paperFT_rePart_imPart_neg_I_div_two hf.continuous hfc).2, h₂, Complex.zero_im,
      Complex.ofReal_zero]
  have hEre : 0 ≤ sourceEnergy (compactLift (phiDoobInv (rePart f.1)) (contDiff_phiDoobInv hreC)
      (hasCompactSupport_phiDoobInv hrec)) := by
    apply sourceEnergy_nonneg_of_inner_resolvent_le
    rw [testSource_eq hreC hrec] at hre
    exact half_bound_on_orthogonal_boundStateSpace _ hre
  have hEim : 0 ≤ sourceEnergy (compactLift (phiDoobInv (imPart f.1)) (contDiff_phiDoobInv himC)
      (hasCompactSupport_phiDoobInv himc)) := by
    apply sourceEnergy_nonneg_of_inner_resolvent_le
    rw [testSource_eq himC himc] at him
    exact half_bound_on_orthogonal_boundStateSpace _ him
  rw [sourceEnergy_phiDoobInv_eq_re_W hreC hrec hre1 hre2] at hEre
  rw [sourceEnergy_phiDoobInv_eq_re_W himC himc him1 him2] at hEim
  have hsplit : (zetaZeroConfig.W f.1 f.1).re =
      (zetaZeroConfig.W (fun x => (rePart f.1 x : ℂ)) (fun x => (rePart f.1 x : ℂ))).re +
      (zetaZeroConfig.W (fun x => (imPart f.1 x : ℂ)) (fun x => (imPart f.1 x : ℂ))).re := by
    have hreCC : ContDiff ℝ 2 (fun x => (rePart f.1 x : ℂ)) := Complex.ofRealCLM.contDiff.comp hreC
    have hrecC : HasCompactSupport (fun x => (rePart f.1 x : ℂ)) :=
      hrec.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have himCC : ContDiff ℝ 2 (fun x => (imPart f.1 x : ℂ)) := Complex.ofRealCLM.contDiff.comp himC
    have himcC : HasCompactSupport (fun x => (imPart f.1 x : ℂ)) :=
      himc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    rw [zeta_W_eq_weilFullFunctional hf hfc, zeta_W_eq_weilFullFunctional hreCC hrecC,
      zeta_W_eq_weilFullFunctional himCC himcC]
    exact re_weilFullFunctional_split _ ⟨f.1, hf, hfc⟩
  have := hneg f.1 f.2 hf1
  linarith

/-- Cardinal form, without finiteness of the bound-state space. -/
theorem finrank_le_rank_boundStateSpace_of_negative_subspace
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      paperFT f (Complex.I / 2) = 0 ∧ paperFT f (-(Complex.I / 2)) = 0)
    (hneg : ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < 0) :
    (Module.finrank ℂ V : Cardinal) ≤ Module.rank ℝ boundStateSpace := by
  by_cases hfin : FiniteDimensional ℝ boundStateSpace
  · rw [← Module.finrank_eq_rank]
    exact_mod_cast finrank_le_finrank_boundStateSpace_of_negative_subspace V hV hneg
  · have h : Cardinal.aleph0 ≤ Module.rank ℝ boundStateSpace := by
      rw [← not_lt]
      exact fun h => hfin (Module.rank_lt_aleph0_iff.mp h)
    exact Cardinal.natCast_lt_aleph0.le.trans h

/-- **The finite-level negative index of the Weil form is at most the number of bound states.** -/
theorem weilNegIndex_le_finrank_boundStateSpace [FiniteDimensional ℝ boundStateSpace]
    {a ε : ℝ} (hε : 0 ≤ ε) :
    weilNegIndex zetaZeroConfig a ε ≤ Module.finrank ℝ boundStateSpace := by
  unfold weilNegIndex
  refine csSup_le ⟨0, ⊥, inferInstance, finrank_bot ℂ (ℝ → ℂ), fun f hf => ?_,
    fun f hf hf0 => absurd ((Submodule.mem_bot ℂ).mp hf) hf0⟩ ?_
  · rw [(Submodule.mem_bot ℂ).mp hf]
    exact ⟨contDiff_const, by simp [tsupport, Function.support], by simp [paperFT_def],
      by simp [paperFT_def]⟩
  · rintro n ⟨V, hVf, rfl, hV, hneg⟩
    exact finrank_le_finrank_boundStateSpace_of_negative_subspace V
      (fun f hf => ⟨(hV f hf).1,
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) (hV f hf).2.1,
        (hV f hf).2.2.1, (hV f hf).2.2.2⟩)
      (fun f hf h0 => lt_of_lt_of_le (hneg f hf h0)
        (neg_nonpos.mpr (mul_nonneg hε (integral_nonneg fun u => by positivity))))

/-- **Visible separated deep off-line zeros force bound states.** Under the hypotheses of the
finite-level inertia law, `|T| ≤ dim (bound-state space) + 2`. -/
theorem card_le_finrank_boundStateSpace_add_two [FiniteDimensional ℝ boundStateSpace] :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (a δ R Hm ε : ℝ) (T : Finset ℂ), 0 < a → 0 < δ → 1 ≤ R → T.Nonempty →
      (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm) →
      (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|) →
      (∀ ρ ∈ T, ∀ σ ∈ zetaZeroConfig.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R →
        σ.re = 1 / 2) →
      0 < visibleMargin A₀ a δ R Hm → 0 < ε → ε ≤ 1 →
      ε ≤ visibleMargin A₀ a δ R Hm / (T.card * ((∫ u, sinhTest a δ u ^ 2) + 1)) →
      T.card ≤ Module.finrank ℝ boundStateSpace + 2 := by
  obtain ⟨A₀, hA₀, -, hlow⟩ := zeta_weil_inertia_law
  refine ⟨A₀, hA₀, fun a δ R Hm ε T ha hδ hR hTne hT hsep hiso hvis hε hε1 hεT => ?_⟩
  exact (hlow a δ R Hm ε T ha hδ hR hTne hT hsep hiso hvis hε hε1 hεT).trans
    (Nat.add_le_add_right (weilNegIndex_le_finrank_boundStateSpace hε.le) 2)

end RHTower.CHMDPolar
