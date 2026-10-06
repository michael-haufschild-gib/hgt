import GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra

/-!
# The spectral-aperture cone: one generator and spectrum `[0,1]`

For a positive compact injective operator `T` on an infinite-dimensional Hilbert space, the scale
germs `e_c = [ε ↦ cT(ε + cT)⁻¹]` live in the boundary-history corona `Q`, a non-unital C⋆-algebra.
The continuous functional calculus commutes with the quotient map and with evaluation at an
aperture, so `f(e_c)` is the class of the history `ε ↦ f(E_{ε/c}(T))`.

* A function vanishing on `[0,1]` kills every `e_c` (the spectra of `E_η(T)` lie in `[0,1]`);
* along spectral values `λ_n → 0` of `T` the apertures `ε_n = cλ_n(1 − x)/x` read the value `x`
  exactly, so `‖f(e_c)‖ ≥ |f(x)|` for `0 < x < 1` (`le_norm_cfcₙ_scaleGerm`).

Hence (Theorem SAC-A) `σ(e_c) = [0,1]`, also in the unitization of `Q`; the fractional-linear maps
`φ_r(t) = rt/(1 + (r − 1)t)` satisfy `e_d = φ_{d/c}(e_c)` (SAC.3); and
`C*(e_c : c > 0) = C*(e_1) ≅ C(σ(e_1), ℂ)₀ = C_0((0,1])` (SAC.4).
-/

set_option autoImplicit false

open Filter Topology Set ContinuousLinearMap
open scoped BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The structure maps -/

variable (H) in
/-- The quotient map `C_b((0,1], K(H)) → Q`. -/
def coronaMk : ApertureHistory H →⋆ₙₐ[ℂ] BoundaryCorona H where
  toFun F := F
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

theorem continuous_coronaMk : Continuous (coronaMk H) :=
  continuous_quot_mk

/-- Evaluation of a history at the aperture `ε`. -/
def historyEval (ε : Aperture) : ApertureHistory H →⋆ₙₐ[ℂ] CompactOps H where
  toFun F := F ε
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

theorem continuous_historyEval (ε : Aperture) : Continuous (historyEval (H := H) ε) :=
  continuous_eval_const ε

variable (H) in
/-- The inclusion `K(H) → B(H)`. -/
def compactIncl : CompactOps H →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun x := x.op
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' x := by rw [CompactOps.op_star, star_eq_adjoint]

theorem continuous_compactIncl : Continuous (compactIncl H) :=
  continuous_subtype_val

/-- **Functional calculus of a history, evaluated at an aperture**: for `f` continuous on `ℂ`
with `f 0 = 0` and a normal history `F`, `(f(F))(ε) = f(F(ε))` in `B(H)`. -/
theorem compactIncl_historyEval_cfcₙ (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0)
    {F : ApertureHistory H} (hF : IsStarNormal F) (ε : Aperture) :
    compactIncl H (historyEval ε (cfcₙ f F)) = cfc f (compactIncl H (historyEval ε F)) := by
  have hFε : IsStarNormal (historyEval ε F) :=
    ⟨by simpa [map_star] using hF.star_comm_self.map (historyEval ε)⟩
  have hFε' : IsStarNormal (compactIncl H (historyEval ε F)) :=
    ⟨by simpa [map_star] using hFε.star_comm_self.map (compactIncl H)⟩
  rw [(historyEval ε).map_cfcₙ f F hf.continuousOn hf0 (continuous_historyEval ε) hF hFε,
    (compactIncl H).map_cfcₙ f _ hf.continuousOn hf0 continuous_compactIncl hFε hFε',
    cfcₙ_eq_cfc hf.continuousOn hf0]

/-! ## Spectra of the boundary transfer -/

/-- The unit interval `[0,1] ⊆ ℂ`. -/
def unitIntervalC : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1

theorem zero_mem_unitIntervalC : (0 : ℂ) ∈ unitIntervalC :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, Complex.ofReal_zero⟩

theorem isCompact_unitIntervalC : IsCompact unitIntervalC :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem isSelfAdjoint_positiveBoundaryTransfer (T : H →L[ℂ] H) (η : ℝ) :
    IsSelfAdjoint (positiveBoundaryTransfer T η) :=
  cfc_predicate _ T

/-- The complex spectrum of `E_η(T)` lies in `[0,1]`. -/
theorem spectrum_positiveBoundaryTransfer_subset {T : H →L[ℂ] H} (hT : T.IsPositive) {η : ℝ}
    (hη : 0 < η) : spectrum ℂ (positiveBoundaryTransfer T η) ⊆ unitIntervalC := by
  intro z hz
  have hsa := isSelfAdjoint_positiveBoundaryTransfer T η
  have hre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  rw [hre] at hz
  have hzR : z.re ∈ spectrum ℝ (positiveBoundaryTransfer T η) :=
    (spectrum.algebraMap_mem_iff ℂ).mp hz
  have hspec := spectrum_subset_Icc_of_isPositive hT
  rw [positiveBoundaryTransfer, cfc_map_spectrum (fun x : ℝ => x / (η + x)) T hT.isSelfAdjoint
    (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun y hy =>
      (show (0 : ℝ) < η + y by have := (hspec hy).1; linarith).ne')] at hzR
  obtain ⟨x, hx, hxz⟩ := hzR
  have hx0 := (hspec hx).1
  refine ⟨z.re, ⟨?_, ?_⟩, hre.symm⟩
  · rw [← hxz]; exact div_nonneg hx0 (by linarith)
  · rw [← hxz, div_le_one (by linarith)]; linarith

/-- The spectral value `λ/(η + λ)` of `E_η(T)` above a spectral value `λ` of `T`. -/
theorem mem_spectrum_positiveBoundaryTransfer {T : H →L[ℂ] H} (hT : T.IsPositive) {η : ℝ}
    (hη : 0 < η) {x : ℝ} (hx : x ∈ spectrum ℝ T) :
    ((x / (η + x) : ℝ) : ℂ) ∈ spectrum ℂ (positiveBoundaryTransfer T η) := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  show algebraMap ℝ ℂ (x / (η + x)) ∈ spectrum ℂ (positiveBoundaryTransfer T η)
  refine (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := H →L[ℂ] H)).mpr ?_
  rw [positiveBoundaryTransfer, cfc_map_spectrum (fun x : ℝ => x / (η + x)) T hT.isSelfAdjoint
    (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun y hy =>
      (show (0 : ℝ) < η + y by have := (hspec hy).1; linarith).ne')]
  exact ⟨x, hx, rfl⟩

/-! ## The fractional-linear scale change -/

/-- The fractional-linear scale change `φ_r(t) = rt/(1 + (r − 1)t)`. -/
def scaleChange (r : ℝ) (z : ℂ) : ℂ := r * z / (1 + (r - 1) * z)

/-- The retraction of `ℂ` onto `[0,1]`. -/
def clampUnit (z : ℂ) : ℂ := ((max 0 (min 1 z.re) : ℝ) : ℂ)

theorem continuous_clampUnit : Continuous clampUnit :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min Complex.continuous_re))

theorem clampUnit_of_mem {z : ℂ} (hz : z ∈ unitIntervalC) : clampUnit z = z := by
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  simp [clampUnit, min_eq_right ht1, max_eq_right ht0]

theorem clampUnit_re_mem (z : ℂ) : max 0 (min 1 z.re) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem scaleChange_denom_pos {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + (r - 1) * t := by
  rcases ht.2.eq_or_lt with rfl | h1
  · linarith
  · nlinarith [mul_nonneg hr.le ht.1]

theorem scaleChange_ofReal (r t : ℝ) :
    scaleChange r t = ((r * t / (1 + (r - 1) * t) : ℝ) : ℂ) := by
  simp [scaleChange]

/-- The clamped scale change is continuous on `ℂ`. -/
theorem continuous_scaleChange_clamp {r : ℝ} (hr : 0 < r) :
    Continuous fun z => scaleChange r (clampUnit z) := by
  have h : (fun z => scaleChange r (clampUnit z)) = fun z =>
      ((r * max 0 (min 1 z.re) / (1 + (r - 1) * max 0 (min 1 z.re)) : ℝ) : ℂ) := by
    funext z
    exact scaleChange_ofReal r _
  rw [h]
  have hc : Continuous fun z : ℂ => max 0 (min 1 z.re) :=
    continuous_const.max (continuous_const.min Complex.continuous_re)
  exact Complex.continuous_ofReal.comp ((continuous_const.mul hc).div
    (continuous_const.add (continuous_const.mul hc)) fun z =>
      (scaleChange_denom_pos hr (clampUnit_re_mem z)).ne')

theorem scaleChange_clamp_zero (r : ℝ) : scaleChange r (clampUnit 0) = 0 := by
  simp [scaleChange, clampUnit]

/-- The complex form of the boundary transfer: `E_η(T) = cfc (z ↦ re z/(η + re z)) T`. -/
theorem positiveBoundaryTransfer_eq_cfc_complex (T : H →L[ℂ] H) (hT : T.IsPositive) (η : ℝ) :
    positiveBoundaryTransfer T η =
      cfc (fun z : ℂ => ((z.re / (η + z.re) : ℝ) : ℂ)) T := by
  rw [positiveBoundaryTransfer, cfc_real_eq_complex _ hT.isSelfAdjoint]

/-- **(SAC.3) on the operator level**: `φ_r(E_η(T)) = E_{η/r}(T)`. -/
theorem cfc_scaleChange_positiveBoundaryTransfer {T : H →L[ℂ] H} (hT : T.IsPositive) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) :
    cfc (fun z => scaleChange r (clampUnit z)) (positiveBoundaryTransfer T η) =
      positiveBoundaryTransfer T (η / r) := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hsC : ∀ z ∈ spectrum ℂ T, z = (z.re : ℂ) ∧ 0 ≤ z.re := fun z hz => by
    have hre : z = (z.re : ℂ) := hT.isSelfAdjoint.mem_spectrum_eq_re hz
    refine ⟨hre, ?_⟩
    rw [hre] at hz
    exact (hspec ((spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := H →L[ℂ] H)).mp hz)).1
  have hgcont : ContinuousOn (fun z : ℂ => ((z.re / (η + z.re) : ℝ) : ℂ)) (spectrum ℂ T) :=
    (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.continuousOn.div
      (continuousOn_const.add Complex.continuous_re.continuousOn) fun z hz =>
        (show (0 : ℝ) < η + z.re by linarith [(hsC z hz).2]).ne'))
  rw [positiveBoundaryTransfer_eq_cfc_complex T hT, positiveBoundaryTransfer_eq_cfc_complex T hT,
    ← cfc_comp _ _ T hT.isSelfAdjoint.isStarNormal (continuous_scaleChange_clamp hr).continuousOn
      hgcont]
  refine cfc_congr fun z hz => ?_
  obtain ⟨-, hz0⟩ := hsC z hz
  have hmem : z.re / (η + z.re) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hz0 (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
  simp only [Function.comp_apply]
  rw [clampUnit_of_mem ⟨_, hmem, rfl⟩, scaleChange_ofReal]
  congr 1
  have h1 : 0 < η + z.re := by linarith
  have h2 : 0 < η / r + z.re := by positivity
  have h3 : 0 < 1 + (r - 1) * (z.re / (η + z.re)) := scaleChange_denom_pos hr hmem
  rw [div_eq_div_iff h3.ne' h2.ne']
  field_simp
  ring

/-! ## The scale germs -/

section Germ

variable {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T) {c : ℝ} (hc : 0 < c)

/-- The transfer history `ε ↦ E_ε(cT)` representing the scale germ `e_c`. -/
abbrev germHistory : ApertureHistory H :=
  transferHistory (c • T) (isPositive_real_smul hT hc.le) (hcpt.smul c)

include hc in
theorem germHistory_apply (ε : Aperture) :
    compactIncl H (historyEval ε (germHistory hT hcpt hc)) =
      positiveBoundaryTransfer T (ε / c) :=
  positiveBoundaryTransfer_smul hT hc ε.2.1

theorem isSelfAdjoint_germHistory : IsSelfAdjoint (germHistory hT hcpt hc) := by
  refine BoundedContinuousFunction.ext fun ε => CompactOps.op_injective ?_
  change adjoint (positiveBoundaryTransfer (c • T) ε) = positiveBoundaryTransfer (c • T) ε
  rw [← star_eq_adjoint]
  exact (isSelfAdjoint_positiveBoundaryTransfer _ _).star_eq

theorem scaleGerm_eq_coronaMk :
    scaleGerm T hT hcpt hc = coronaMk H (germHistory hT hcpt hc) := rfl

theorem isSelfAdjoint_scaleGerm : IsSelfAdjoint (scaleGerm T hT hcpt hc) := by
  rw [scaleGerm_eq_coronaMk]
  exact (isSelfAdjoint_germHistory hT hcpt hc).map (coronaMk H)

/-- The functional calculus of a scale germ is computed by its history. -/
theorem cfcₙ_scaleGerm (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0) :
    cfcₙ f (scaleGerm T hT hcpt hc) = coronaMk H (cfcₙ f (germHistory hT hcpt hc)) := by
  rw [scaleGerm_eq_coronaMk]
  exact ((coronaMk H).map_cfcₙ f _ hf.continuousOn hf0 continuous_coronaMk
    (isSelfAdjoint_germHistory hT hcpt hc).isStarNormal
    ((isSelfAdjoint_germHistory hT hcpt hc).map (coronaMk H)).isStarNormal).symm

theorem cfcₙ_germHistory_apply (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0) (ε : Aperture) :
    compactIncl H (historyEval ε (cfcₙ f (germHistory hT hcpt hc))) =
      cfc f (positiveBoundaryTransfer T (ε / c)) := by
  rw [compactIncl_historyEval_cfcₙ f hf hf0 (isSelfAdjoint_germHistory hT hcpt hc).isStarNormal,
    germHistory_apply hT hcpt hc]

/-- A function vanishing on `[0,1]` annihilates every scale germ. -/
theorem cfcₙ_scaleGerm_eq_zero (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hfs : ∀ z ∈ unitIntervalC, f z = 0) : cfcₙ f (scaleGerm T hT hcpt hc) = 0 := by
  rw [cfcₙ_scaleGerm hT hcpt hc f hf hf0]
  have : cfcₙ f (germHistory hT hcpt hc) = 0 := by
    refine BoundedContinuousFunction.ext fun ε => CompactOps.op_injective ?_
    change compactIncl H (historyEval ε (cfcₙ f (germHistory hT hcpt hc))) = 0
    rw [cfcₙ_germHistory_apply hT hcpt hc f hf hf0,
      cfc_congr (g := 0) fun z hz => hfs z (spectrum_positiveBoundaryTransfer_subset hT
        (div_pos ε.2.1 hc) hz), cfc_zero]
  rw [this, map_zero]


/-- **Aperture matching.**  For `0 < x < 1` and a functional calculus `f`, `‖f(e_c)‖ ≥ |f(x)|`:
along spectral values `λ_n → 0` of `T` the apertures `ε_n = cλ_n(1 − x)/x` read `E_{ε_n}(cT)` at
the spectral value exactly `x`. -/
theorem le_norm_cfcₙ_scaleGerm (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)
    (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖f x‖ ≤ ‖cfcₙ f (scaleGerm T hT hcpt hc)‖ := by
  rw [cfcₙ_scaleGerm hT hcpt hc f hf hf0]
  change ‖f x‖ ≤ ‖((cfcₙ f (germHistory hT hcpt hc) : ApertureHistory H) : BoundaryCorona H)‖
  rw [BoundaryCorona.norm_mk]
  obtain ⟨y, hy, hy0⟩ := exists_spectrum_seq_tendsto_zero hT hcpt hinj hH
  set κ := c * (1 - x) / x with hκ
  have hκpos : 0 < κ := div_pos (mul_pos hc (by linarith)) hx0
  have hε : Tendsto (fun n => κ * y n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => mul_pos hκpos (hy n).1⟩
    simpa using hy0.const_mul κ
  have hsmall : ∀ᶠ n in atTop, κ * y n ≤ 1 :=
    (hε.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one)
  have hpt : ∀ (ε : Aperture) (n : ℕ), (ε : ℝ) = κ * y n →
      ‖f x‖ ≤ ‖(cfcₙ f (germHistory hT hcpt hc)) ε‖ := by
    intro ε n hεn
    have hyn := (hy n).1
    have hη : 0 < (ε : ℝ) / c := div_pos ε.2.1 hc
    have hmem := mem_spectrum_positiveBoundaryTransfer hT hη (hy n).2
    have hval : y n / ((ε : ℝ) / c + y n) = x := by
      rw [hεn, hκ]
      field_simp
      ring
    rw [hval] at hmem
    change ‖f x‖ ≤ ‖compactIncl H (historyEval ε (cfcₙ f (germHistory hT hcpt hc)))‖
    rw [cfcₙ_germHistory_apply hT hcpt hc f hf hf0]
    exact norm_apply_le_norm_cfc f _ hmem hf.continuousOn
      (isSelfAdjoint_positiveBoundaryTransfer T _).isStarNormal
  refine le_limsup_of_frequently_le ?_ (isBoundedUnder_norm_history _)
  refine frequently_comap.2 (hε.frequently ?_)
  refine (hsmall.mono fun n hn => ?_).frequently
  exact ⟨⟨κ * y n, mul_pos hκpos (hy n).1, hn⟩, rfl, hpt _ n rfl⟩

/-- **Theorem SAC-A (spectrum).**  Every scale germ has quasispectrum `[0,1]`. -/
theorem quasispectrum_scaleGerm (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    quasispectrum ℂ (scaleGerm T hT hcpt hc) = unitIntervalC := by
  set e := scaleGerm T hT hcpt hc
  have hn : IsStarNormal e := (isSelfAdjoint_scaleGerm hT hcpt hc).isStarNormal
  apply le_antisymm
  · intro z hz
    by_contra hzs
    have hpos : 0 < Metric.infDist z unitIntervalC :=
      (isCompact_unitIntervalC.isClosed.notMem_iff_infDist_pos ⟨0, zero_mem_unitIntervalC⟩).mp
        hzs
    set f : ℂ → ℂ := fun w => ((Metric.infDist w unitIntervalC / Metric.infDist z unitIntervalC :
      ℝ) : ℂ)
    have hf : Continuous f :=
      Complex.continuous_ofReal.comp ((Metric.continuous_infDist_pt _).div_const _)
    have hfs : ∀ w ∈ unitIntervalC, f w = 0 := fun w hw => by
      simp [f, Metric.infDist_zero_of_mem hw]
    have hf0 : f 0 = 0 := hfs 0 zero_mem_unitIntervalC
    have h0 := cfcₙ_scaleGerm_eq_zero hT hcpt hc f hf hf0 hfs
    have hmap := cfcₙ_map_quasispectrum f e hf.continuousOn hf0 hn
    rw [h0, CFC.quasispectrum_zero_eq] at hmap
    have hfz : f z ∈ f '' quasispectrum ℂ e := ⟨z, hz, rfl⟩
    rw [← hmap, Set.mem_singleton_iff] at hfz
    simp only [f, Complex.ofReal_eq_zero, div_self hpos.ne'] at hfz
    exact one_ne_zero hfz
  · have hcl : IsClosed (quasispectrum ℂ e) :=
      (NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum e).isClosed
    have hint : ∀ x : ℝ, 0 < x → x < 1 → (x : ℂ) ∈ quasispectrum ℂ e := by
      intro x hx0 hx1
      by_contra hxσ
      have hpos : 0 < Metric.infDist (x : ℂ) (quasispectrum ℂ e) :=
        (hcl.notMem_iff_infDist_pos ⟨0, quasispectrum.zero_mem ℂ e⟩).mp hxσ
      set f : ℂ → ℂ := fun w => ((Metric.infDist w (quasispectrum ℂ e) /
        Metric.infDist (x : ℂ) (quasispectrum ℂ e) : ℝ) : ℂ)
      have hf : Continuous f :=
        Complex.continuous_ofReal.comp ((Metric.continuous_infDist_pt _).div_const _)
      have hf0 : f 0 = 0 := by
        simp [f, Metric.infDist_zero_of_mem (quasispectrum.zero_mem ℂ e)]
      have hzero : cfcₙ f e = 0 := by
        rw [cfcₙ_congr (g := 0) fun w hw => by simp [f, Metric.infDist_zero_of_mem hw],
          cfcₙ_zero]
      have hle := le_norm_cfcₙ_scaleGerm hT hcpt hc hinj hH f hf hf0 hx0 hx1
      rw [hzero, norm_zero] at hle
      have hfx : f x = 1 := by
        simp only [f]; rw [div_self hpos.ne', Complex.ofReal_one]
      rw [hfx, norm_one] at hle
      exact absurd hle (by norm_num)
    rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩
    rcases hx0.eq_or_lt with rfl | hx0
    · rw [Complex.ofReal_zero]; exact quasispectrum.zero_mem ℂ e
    rcases hx1.eq_or_lt with rfl | hx1
    · have hseq : Tendsto (fun n : ℕ => ((1 - 1 / 2 * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
          (𝓝 ((1 : ℝ) : ℂ)) := by
        refine (Complex.continuous_ofReal.tendsto _).comp ?_
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
      refine hcl.mem_of_tendsto hseq (Eventually.of_forall fun n => hint _ ?_ ?_)
      · have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith
      · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    · exact hint x hx0 hx1

/-- **Theorem SAC-A (spectrum in the unitization).** -/
theorem spectrum_scaleGerm (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    spectrum ℂ (scaleGerm T hT hcpt hc : Unitization ℂ (BoundaryCorona H)) = unitIntervalC := by
  rw [← Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ, quasispectrum_scaleGerm hT hcpt hc hinj hH]

/-- **Theorem SAC-A (SAC.3), the one-generator law**: `e_d = φ_{d/c}(e_c)`. -/
theorem scaleGerm_eq_cfcₙ_scaleChange (hinj : Function.Injective T)
    (hH : ¬ FiniteDimensional ℂ H) {d : ℝ} (hd : 0 < d) :
    scaleGerm T hT hcpt hd = cfcₙ (scaleChange (d / c)) (scaleGerm T hT hcpt hc) := by
  have hr : 0 < d / c := div_pos hd hc
  rw [cfcₙ_congr (g := fun z => scaleChange (d / c) (clampUnit z)) fun z hz => by
      rw [quasispectrum_scaleGerm hT hcpt hc hinj hH] at hz
      simp only [clampUnit_of_mem hz],
    cfcₙ_scaleGerm hT hcpt hc _ (continuous_scaleChange_clamp hr) (scaleChange_clamp_zero _),
    scaleGerm_eq_coronaMk]
  congr 1
  refine BoundedContinuousFunction.ext fun ε => CompactOps.op_injective ?_
  change compactIncl H (historyEval ε (germHistory hT hcpt hd)) =
    compactIncl H (historyEval ε (cfcₙ _ (germHistory hT hcpt hc)))
  rw [germHistory_apply hT hcpt hd, cfcₙ_germHistory_apply hT hcpt hc _
      (continuous_scaleChange_clamp hr) (scaleChange_clamp_zero _),
    cfc_scaleChange_positiveBoundaryTransfer hT hr (div_pos ε.2.1 hc)]
  congr 1
  field_simp

end Germ

/-! ## The C⋆-algebra of the scale orbit -/

section Orbit

variable {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)

/-- The closed `*`-algebra `C*(e_c : c > 0)` generated by all scale germs. -/
def scaleOrbitAlgebra : NonUnitalStarSubalgebra ℂ (BoundaryCorona H) :=
  (NonUnitalStarAlgebra.adjoin ℂ
    (Set.range fun c : Set.Ioi (0 : ℝ) => scaleGerm T hT hcpt c.2)).topologicalClosure

/-- **Theorem SAC-A (SAC.4)**: `C*(e_c : c > 0) = C*(e_1)`. -/
theorem scaleOrbitAlgebra_eq_elemental (hinj : Function.Injective T)
    (hH : ¬ FiniteDimensional ℂ H) :
    scaleOrbitAlgebra hT hcpt =
      NonUnitalStarAlgebra.elemental ℂ (scaleGerm T hT hcpt one_pos) := by
  apply le_antisymm
  · refine NonUnitalStarSubalgebra.topologicalClosure_minimal _
      (NonUnitalStarAlgebra.adjoin_le ?_) (NonUnitalStarAlgebra.elemental.isClosed ℂ _)
    rintro _ ⟨c, rfl⟩
    show scaleGerm T hT hcpt c.2 ∈ NonUnitalStarAlgebra.elemental ℂ (scaleGerm T hT hcpt one_pos)
    rw [scaleGerm_eq_cfcₙ_scaleChange hT hcpt one_pos hinj hH c.2]
    exact cfcₙ_mem_elemental _ _
  · refine NonUnitalStarAlgebra.elemental.le_of_mem
      (NonUnitalStarSubalgebra.isClosed_topologicalClosure _) ?_
    exact NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨⟨1, Set.mem_Ioi.mpr one_pos⟩, rfl⟩)

/-- **Theorem SAC-A (SAC.4)**: `C*(e_1) ≅ C_0((0,1])`: the continuous functional calculus of `e_1`
is an isometric `*`-isomorphism of `C(σ(e_1), ℂ)₀` onto `C*(e_1)`, and `σ(e_1) = [0,1]`. -/
theorem scaleGerm_cstar_iso (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    quasispectrum ℂ (scaleGerm T hT hcpt one_pos) = unitIntervalC ∧
      Isometry (cfcₙHom (R := ℂ) (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal) ∧
      NonUnitalStarAlgHom.range
          (cfcₙHom (R := ℂ) (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal) =
        NonUnitalStarAlgebra.elemental ℂ (scaleGerm T hT hcpt one_pos) :=
  ⟨quasispectrum_scaleGerm hT hcpt one_pos hinj hH,
    isometry_cfcₙHom _ (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal,
    range_cfcₙHom ℂ (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal⟩

end Orbit

end GaloisForLFunctions.HTGeometry
