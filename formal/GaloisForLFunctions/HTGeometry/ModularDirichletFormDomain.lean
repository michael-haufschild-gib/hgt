import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import GaloisForLFunctions.HTGeometry.FormEmbeddingCovarianceSpectrum

/-!
# The Dirichlet form domain of the modular surface and its spectral assembly bound

`L²(𝒟)` is `L²` of the hyperbolic measure `dx dy / y²` restricted to the modular fundamental
domain `𝒟`.  The form pre-domain consists of the `C¹` functions on `ℍ` invariant under
`SL(2, ℤ)` whose values and hyperbolic gradient components `y ∂_x f`, `y ∂_y f` are square
integrable on `𝒟`; the form inner product is `⟪f, g⟫ + ∫_𝒟 (y∂_x f · conj(y∂_x g) + y∂_y f ·
conj(y∂_y g)) dμ`, the second summand being the conformally invariant Dirichlet form
`∫_𝒟 ∇f · ∇ḡ dx dy`.  Concretely the pre-domain embeds isometrically into `L²(𝒟)³` by
`f ↦ (f, y∂_x f, y∂_y f)`; the form domain is the closure of the image, and the form embedding
`J` is the first coordinate, a contraction.

The constant function is form-harmonic, so it is fixed by the covariance `C = J J†`, and the
abstract rank-one assembly bound gives, for every real `g ≥ c` continuous on `[0, 1]` and every
`F ∈ L²(𝒟)`,

`g(1)·|∫_𝒟 F|²/vol(𝒟) + c·‖F − P₀F‖² ≤ Re⟪g(C) F, F⟫`,

`P₀` the projection onto constants.  This is the spectral assembly of the modular surface in the
form needed by a kernel bounded below on the spectrum: no eigenfunction expansion, no spectral
measure, no discreteness of the spectrum.
-/

open UpperHalfPlane MeasureTheory ModularGroup
open scoped InnerProductSpace MatrixGroups

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## `L²` of the modular surface -/

/-- The hyperbolic measure restricted to the modular fundamental domain. -/
abbrev modularCellMeasure : Measure ℍ := (volume : Measure ℍ).restrict fd

instance : IsFiniteMeasure modularCellMeasure := isFiniteMeasure_restrict.mpr volume_fd_ne_top

/-- `L²` of the modular surface.  A definition rather than an abbreviation, so that its Hilbert
space structure is the one induced from `InnerProductSpace ℂ` alone. -/
def ModularL2 := Lp ℂ 2 modularCellMeasure

instance : NormedAddCommGroup ModularL2 :=
  inferInstanceAs (NormedAddCommGroup (Lp ℂ 2 modularCellMeasure))

instance : InnerProductSpace ℂ ModularL2 :=
  inferInstanceAs (InnerProductSpace ℂ (Lp ℂ 2 modularCellMeasure))

instance : CompleteSpace ModularL2 :=
  inferInstanceAs (CompleteSpace (Lp ℂ 2 modularCellMeasure))

/-- The `L²` class of a square-integrable function. -/
def toModularL2 (f : ℍ → ℂ) (hf : MemLp f 2 modularCellMeasure) : ModularL2 := MemLp.toLp f hf

/-- The underlying `Lp` element. -/
def modularToLp (F : ModularL2) : Lp ℂ 2 modularCellMeasure := F

theorem toModularL2_add {f g : ℍ → ℂ} (hf : MemLp f 2 modularCellMeasure)
    (hg : MemLp g 2 modularCellMeasure) :
    toModularL2 (f + g) (hf.add hg) = toModularL2 f hf + toModularL2 g hg :=
  MemLp.toLp_add hf hg

theorem toModularL2_smul {f : ℍ → ℂ} (c : ℂ) (hf : MemLp f 2 modularCellMeasure) :
    toModularL2 (c • f) (hf.const_smul c) = c • toModularL2 f hf :=
  MemLp.toLp_const_smul c hf

theorem toModularL2_congr {f g : ℍ → ℂ} (hf : MemLp f 2 modularCellMeasure)
    (hg : MemLp g 2 modularCellMeasure) (h : f =ᵐ[modularCellMeasure] g) :
    toModularL2 f hf = toModularL2 g hg :=
  MemLp.toLp_congr hf hg h

theorem toModularL2_zero (h : MemLp (fun _ : ℍ => (0 : ℂ)) 2 modularCellMeasure) :
    toModularL2 (fun _ => 0) h = 0 :=
  MemLp.toLp_zero h

theorem toModularL2_eq_zero_iff {f : ℍ → ℂ} (hf : MemLp f 2 modularCellMeasure) :
    toModularL2 f hf = 0 ↔ f =ᵐ[modularCellMeasure] 0 := by
  have h1 : (MemLp.toLp f hf : Lp ℂ 2 modularCellMeasure) = 0 ↔
      ⇑(MemLp.toLp f hf : Lp ℂ 2 modularCellMeasure) =ᵐ[modularCellMeasure] 0 :=
    Lp.eq_zero_iff_ae_eq_zero
  refine h1.trans ⟨fun h => (MemLp.coeFn_toLp hf).symm.trans h,
    fun h => (MemLp.coeFn_toLp hf).trans h⟩

/-- The open upper half-plane as a subset of `ℂ`. -/
def upperSet : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperSet : IsOpen upperSet := isOpen_lt continuous_const Complex.continuous_im

theorem coe_mem_upperSet (z : ℍ) : (z : ℂ) ∈ upperSet := z.im_pos

/-- The chart function `ℂ → ℂ` of `f : ℍ → ℂ`. -/
def chartFun (f : ℍ → ℂ) : ℂ → ℂ := f ∘ ofComplex

/-- Directional derivative in the chart. -/
def chartDeriv (f : ℍ → ℂ) (v : ℂ) (z : ℍ) : ℂ := fderiv ℝ (chartFun f) (z : ℂ) v

/-- The hyperbolic gradient component `y ∂_x f`. -/
def hypGradX (f : ℍ → ℂ) (z : ℍ) : ℂ := (z.im : ℂ) * chartDeriv f 1 z

/-- The hyperbolic gradient component `y ∂_y f`. -/
def hypGradY (f : ℍ → ℂ) (z : ℍ) : ℂ := (z.im : ℂ) * chartDeriv f Complex.I z

/-- Continuously differentiable in the chart. -/
def IsChartC1 (f : ℍ → ℂ) : Prop := ContDiffOn ℝ 1 (chartFun f) upperSet

theorem IsChartC1.differentiableAt {f : ℍ → ℂ} (hf : IsChartC1 f) (z : ℍ) :
    DifferentiableAt ℝ (chartFun f) (z : ℂ) :=
  (ContDiffOn.differentiableOn hf one_ne_zero).differentiableAt
    (isOpen_upperSet.mem_nhds (coe_mem_upperSet z))

theorem chartFun_add (f g : ℍ → ℂ) : chartFun (f + g) = chartFun f + chartFun g := rfl

theorem chartFun_smul (c : ℂ) (f : ℍ → ℂ) : chartFun (c • f) = c • chartFun f := rfl

theorem chartFun_const (c : ℂ) : chartFun (fun _ => c) = fun _ => c := rfl

theorem IsChartC1.add {f g : ℍ → ℂ} (hf : IsChartC1 f) (hg : IsChartC1 g) : IsChartC1 (f + g) := by
  unfold IsChartC1
  rw [chartFun_add]
  exact ContDiffOn.add hf hg

theorem IsChartC1.smul {f : ℍ → ℂ} (hf : IsChartC1 f) (c : ℂ) : IsChartC1 (c • f) := by
  unfold IsChartC1
  rw [chartFun_smul]
  exact ContDiffOn.const_smul c hf

theorem isChartC1_const (c : ℂ) : IsChartC1 (fun _ => c) := contDiffOn_const

theorem chartDeriv_add {f g : ℍ → ℂ} (hf : IsChartC1 f) (hg : IsChartC1 g) (v : ℂ) (z : ℍ) :
    chartDeriv (f + g) v z = chartDeriv f v z + chartDeriv g v z := by
  unfold chartDeriv
  rw [chartFun_add, fderiv_add (hf.differentiableAt z) (hg.differentiableAt z)]
  rfl

theorem chartDeriv_smul {f : ℍ → ℂ} (hf : IsChartC1 f) (c v : ℂ) (z : ℍ) :
    chartDeriv (c • f) v z = c * chartDeriv f v z := by
  unfold chartDeriv
  rw [chartFun_smul, fderiv_const_smul (hf.differentiableAt z) c]
  rfl

theorem chartDeriv_const (c v : ℂ) (z : ℍ) : chartDeriv (fun _ => c) v z = 0 := by
  unfold chartDeriv
  rw [chartFun_const, fderiv_const_apply]
  rfl

theorem hypGradX_add {f g : ℍ → ℂ} (hf : IsChartC1 f) (hg : IsChartC1 g) :
    hypGradX (f + g) = hypGradX f + hypGradX g := by
  funext z
  simp only [hypGradX, Pi.add_apply, chartDeriv_add hf hg, mul_add]

theorem hypGradY_add {f g : ℍ → ℂ} (hf : IsChartC1 f) (hg : IsChartC1 g) :
    hypGradY (f + g) = hypGradY f + hypGradY g := by
  funext z
  simp only [hypGradY, Pi.add_apply, chartDeriv_add hf hg, mul_add]

theorem hypGradX_smul {f : ℍ → ℂ} (hf : IsChartC1 f) (c : ℂ) :
    hypGradX (c • f) = c • hypGradX f := by
  funext z
  simp only [hypGradX, Pi.smul_apply, chartDeriv_smul hf, smul_eq_mul]
  ring

theorem hypGradY_smul {f : ℍ → ℂ} (hf : IsChartC1 f) (c : ℂ) :
    hypGradY (c • f) = c • hypGradY f := by
  funext z
  simp only [hypGradY, Pi.smul_apply, chartDeriv_smul hf, smul_eq_mul]
  ring

theorem hypGradX_const (c : ℂ) : hypGradX (fun _ => c) = fun _ => 0 := by
  funext z
  simp [hypGradX, chartDeriv_const]

theorem hypGradY_const (c : ℂ) : hypGradY (fun _ => c) = fun _ => 0 := by
  funext z
  simp [hypGradY, chartDeriv_const]

/-! ## The form pre-domain -/

/-- `C¹` functions on `ℍ`, invariant under `SL(2, ℤ)`, square integrable on `𝒟` together with
their hyperbolic gradient components. -/
def formPreDomain : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | IsChartC1 f ∧ (∀ γ : SL(2, ℤ), ∀ z : ℍ, f (γ • z) = f z) ∧
    MemLp f 2 modularCellMeasure ∧ MemLp (hypGradX f) 2 modularCellMeasure ∧
    MemLp (hypGradY f) 2 modularCellMeasure}
  zero_mem' := by
    refine ⟨isChartC1_const 0, fun _ _ => rfl, memLp_const 0, ?_, ?_⟩
    · show MemLp (hypGradX (fun _ => 0)) 2 modularCellMeasure
      rw [hypGradX_const]; exact memLp_const 0
    · show MemLp (hypGradY (fun _ => 0)) 2 modularCellMeasure
      rw [hypGradY_const]; exact memLp_const 0
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4, hf5⟩ ⟨hg1, hg2, hg3, hg4, hg5⟩
    refine ⟨hf1.add hg1, fun γ z => by simp only [Pi.add_apply, hf2 γ z, hg2 γ z], hf3.add hg3,
      ?_, ?_⟩
    · rw [hypGradX_add hf1 hg1]; exact hf4.add hg4
    · rw [hypGradY_add hf1 hg1]; exact hf5.add hg5
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3, hf4, hf5⟩
    refine ⟨hf1.smul c, fun γ z => by simp only [Pi.smul_apply, hf2 γ z], hf3.const_smul c, ?_, ?_⟩
    · rw [hypGradX_smul hf1]; exact hf4.const_smul c
    · rw [hypGradY_smul hf1]; exact hf5.const_smul c

namespace formPreDomain

theorem c1 (f : formPreDomain) : IsChartC1 (f : ℍ → ℂ) := f.2.1
theorem invariant (f : formPreDomain) (γ : SL(2, ℤ)) (z : ℍ) :
    (f : ℍ → ℂ) (γ • z) = (f : ℍ → ℂ) z := f.2.2.1 γ z
theorem memLp (f : formPreDomain) : MemLp (f : ℍ → ℂ) 2 modularCellMeasure := f.2.2.2.1
theorem memLp_gradX (f : formPreDomain) : MemLp (hypGradX (f : ℍ → ℂ)) 2 modularCellMeasure := f.2.2.2.2.1
theorem memLp_gradY (f : formPreDomain) : MemLp (hypGradY (f : ℍ → ℂ)) 2 modularCellMeasure := f.2.2.2.2.2

end formPreDomain

/-- The three coordinate maps `f ↦ f`, `f ↦ y∂_x f`, `f ↦ y∂_y f` into `L²(𝒟)`. -/
def formCoordinate : Fin 3 → (formPreDomain →ₗ[ℂ] ModularL2)
  | 0 => { toFun := fun f => toModularL2 _ (formPreDomain.memLp f)
           map_add' := fun f g => toModularL2_add (formPreDomain.memLp f) (formPreDomain.memLp g)
           map_smul' := fun c f => toModularL2_smul c (formPreDomain.memLp f) }
  | 1 => { toFun := fun f => toModularL2 _ (formPreDomain.memLp_gradX f)
           map_add' := fun f g => by
             rw [← toModularL2_add (formPreDomain.memLp_gradX f) (formPreDomain.memLp_gradX g)]
             exact toModularL2_congr _ _
               (Filter.EventuallyEq.of_eq (hypGradX_add (formPreDomain.c1 f) (formPreDomain.c1 g)))
           map_smul' := fun c f => by
             rw [RingHom.id_apply, ← toModularL2_smul c (formPreDomain.memLp_gradX f)]
             exact toModularL2_congr _ _
               (Filter.EventuallyEq.of_eq (hypGradX_smul (formPreDomain.c1 f) c)) }
  | 2 => { toFun := fun f => toModularL2 _ (formPreDomain.memLp_gradY f)
           map_add' := fun f g => by
             rw [← toModularL2_add (formPreDomain.memLp_gradY f) (formPreDomain.memLp_gradY g)]
             exact toModularL2_congr _ _
               (Filter.EventuallyEq.of_eq (hypGradY_add (formPreDomain.c1 f) (formPreDomain.c1 g)))
           map_smul' := fun c f => by
             rw [RingHom.id_apply, ← toModularL2_smul c (formPreDomain.memLp_gradY f)]
             exact toModularL2_congr _ _
               (Filter.EventuallyEq.of_eq (hypGradY_smul (formPreDomain.c1 f) c)) }

/-- The Hilbert space `L²(𝒟)³` with the `ℓ²` product structure. -/
abbrev FormTriple := PiLp 2 (fun _ : Fin 3 => ModularL2)

/-- The isometric embedding `f ↦ (f, y∂_x f, y∂_y f)` of the pre-domain into `L²(𝒟)³`. -/
def formEmbeddingMap : formPreDomain →ₗ[ℂ] FormTriple :=
  (WithLp.linearEquiv 2 ℂ (Fin 3 → ModularL2)).symm.toLinearMap ∘ₗ LinearMap.pi formCoordinate

theorem formEmbeddingMap_apply (f : formPreDomain) (i : Fin 3) :
    (formEmbeddingMap f).ofLp i = formCoordinate i f := rfl

/-- The form domain: the closure of the embedded pre-domain in `L²(𝒟)³`. -/
def formDomainClosure : Submodule ℂ FormTriple := (LinearMap.range formEmbeddingMap).topologicalClosure

/-- The form domain of the modular Laplacian, a Hilbert space. -/
abbrev FormDomain := ↥formDomainClosure

instance : CompleteSpace FormDomain :=
  inferInstanceAs (CompleteSpace ↥(LinearMap.range formEmbeddingMap).topologicalClosure)

/-- The form embedding `J : V → L²(𝒟)`, the first coordinate. -/
def formInclusion : FormDomain →L[ℂ] ModularL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => ModularL2) 0).comp formDomainClosure.subtypeL

theorem formInclusion_apply (v : FormDomain) : formInclusion v = (v : FormTriple).ofLp 0 := rfl

/-- The form embedding is a contraction. -/
theorem norm_formInclusion_le : ‖formInclusion‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul, formInclusion_apply]
  exact PiLp.norm_apply_le (v : FormTriple) 0

/-! ## The constant function -/

/-- The constant function `1` as an element of the pre-domain. -/
def constantPre : formPreDomain :=
  ⟨fun _ => 1, isChartC1_const 1, fun _ _ => rfl, memLp_const 1,
    by rw [hypGradX_const]; exact memLp_const 0, by rw [hypGradY_const]; exact memLp_const 0⟩

/-- The constant function as an element of the form domain. -/
def constantVector : FormDomain :=
  ⟨formEmbeddingMap constantPre,
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)⟩

/-- The constant function `1` in `L²(𝒟)`. -/
def modularOne : ModularL2 := formInclusion constantVector

theorem modularOne_eq : modularOne = toModularL2 (fun _ => (1 : ℂ)) (memLp_const 1) := rfl

theorem constantVector_coord_one :
    (constantVector : FormTriple).ofLp 1 = 0 := by
  show toModularL2 (hypGradX fun _ => (1 : ℂ)) (formPreDomain.memLp_gradX constantPre) = 0
  rw [← toModularL2_zero (memLp_const 0)]
  exact toModularL2_congr _ _ (Filter.EventuallyEq.of_eq (hypGradX_const 1))

theorem constantVector_coord_two :
    (constantVector : FormTriple).ofLp 2 = 0 := by
  show toModularL2 (hypGradY fun _ => (1 : ℂ)) (formPreDomain.memLp_gradY constantPre) = 0
  rw [← toModularL2_zero (memLp_const 0)]
  exact toModularL2_congr _ _ (Filter.EventuallyEq.of_eq (hypGradY_const 1))

/-- The constant function is form-harmonic: its form inner product against every element of the
form domain is the `L²` inner product of `1` against the embedded element. -/
theorem constantVector_harmonic (w : FormDomain) :
    ⟪constantVector, w⟫_ℂ = ⟪formInclusion constantVector, formInclusion w⟫_ℂ := by
  rw [Submodule.coe_inner, PiLp.inner_apply, Fin.sum_univ_three, constantVector_coord_one,
    constantVector_coord_two, inner_zero_left, inner_zero_left, add_zero, add_zero]
  rfl

/-- The constant function is a nonzero element of `L²(𝒟)`. -/
theorem modularOne_ne_zero : modularOne ≠ 0 := by
  intro h
  rw [modularOne_eq, toModularL2_eq_zero_iff] at h
  have h2 : modularCellMeasure Set.univ = 0 := by
    have := ae_iff.mp h
    simpa using this
  rw [Measure.restrict_apply_univ] at h2
  have hpos : 0 < (volume : Measure ℍ) fd := by
    refine lt_of_lt_of_le ?_ (measure_mono fdo_subset_fd)
    refine isOpen_fdo.measure_pos volume ⟨⟨2 * Complex.I, by simp⟩, ?_⟩
    show 1 < Complex.normSq (2 * Complex.I) ∧ |(2 * Complex.I).re| < 1 / 2
    norm_num [Complex.normSq_apply]
  exact hpos.ne' h2

/-! ## The covariance and the assembly bound -/

/-- The covariance `C = J J†` of the modular form embedding: the bounded inverse `(1 − Δ)⁻¹` of the
Friedrichs Laplacian of the modular surface. -/
def modularCovariance : ModularL2 →L[ℂ] ModularL2 := formEmbeddingCovariance formInclusion

theorem modularCovariance_isSelfAdjoint : IsSelfAdjoint modularCovariance :=
  formEmbeddingCovariance_isSelfAdjoint formInclusion

theorem spectrum_modularCovariance_subset : spectrum ℝ modularCovariance ⊆ Set.Icc 0 1 :=
  spectrum_formEmbeddingCovariance_subset_Icc formInclusion norm_formInclusion_le

theorem modularCovariance_one : modularCovariance modularOne = modularOne :=
  formEmbeddingCovariance_apply_eq_self formInclusion constantVector_harmonic

/-- **Spectral assembly on the modular surface.**  For a real `g` continuous on `[0, 1]` with
`c ≤ g` there and every `F ∈ L²(𝒟)`,
`g(1)·|⟪1, F⟫|²/‖1‖² + c·‖F − P₀F‖² ≤ Re⟪g(C) F, F⟫`, `P₀` the projection onto constants. -/
theorem modular_spectral_assembly {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) {c : ℝ}
    (hc : ∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ g x) (F : ModularL2) :
    g 1 * (‖⟪modularOne, F⟫_ℂ‖ ^ 2 / ‖modularOne‖ ^ 2) +
        c * ‖F - (ℂ ∙ modularOne).starProjection F‖ ^ 2 ≤
      RCLike.re ⟪cfc g modularCovariance F, F⟫_ℂ :=
  re_inner_cfc_formEmbeddingCovariance_ge formInclusion norm_formInclusion_le
    constantVector_harmonic modularOne_ne_zero hg hc F

/-- The constant function as an indicator element of `Lp`. -/
theorem modularOne_toLp_eq : modularToLp modularOne = indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top modularCellMeasure Set.univ) (1 : ℂ) := by
  apply Lp.ext
  have h1 : ⇑(modularToLp modularOne) =ᵐ[modularCellMeasure] fun _ : ℍ => (1 : ℂ) :=
    MemLp.coeFn_toLp (memLp_const 1)
  refine h1.trans
    ((Filter.EventuallyEq.of_eq (Set.indicator_univ _).symm).trans indicatorConstLp_coeFn.symm)

/-- `⟪1, F⟫ = ∫_𝒟 F`. -/
theorem inner_modularOne (F : ModularL2) :
    ⟪modularOne, F⟫_ℂ = ∫ z in fd, modularToLp F z ∂volume := by
  have h : ⟪modularToLp modularOne, modularToLp F⟫_ℂ = ∫ z in fd, modularToLp F z ∂volume := by
    rw [modularOne_toLp_eq, L2.inner_indicatorConstLp_one, Measure.restrict_univ]
  exact h

/-- `‖1‖² = vol(𝒟)`. -/
theorem norm_modularOne_sq : ‖modularOne‖ ^ 2 = ((volume : Measure ℍ) fd).toReal := by
  have h : ‖modularToLp modularOne‖ ^ 2 = ((volume : Measure ℍ) fd).toReal := by
    rw [modularOne_toLp_eq, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one,
      one_mul, Measure.real_def, Measure.restrict_apply_univ]
    have hnn : 0 ≤ ((volume : Measure ℍ) fd).toReal := ENNReal.toReal_nonneg
    rw [show (1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt hnn]
  exact h

end

end GaloisForLFunctions.HTGeometry
