import GaloisForLFunctions.BlackHoleRingdown.TheGravitationalModesOfTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheWeylLowerBound
import GaloisForLFunctions.HTGeometry.PlanarLocalEllipticRegularity
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The cusp forms are gravitational modes at the universal damping

Let `U` be a level-one cusp form, `-y²ΔU = λU`, `λ = ¼ + t²`. Elliptic regularity in the chart makes it
smooth: `Δ_{euc}U = -(λ/y²)U` with a smooth potential (`PlanarElliptic.smooth_of_equation`). So the corpus
reconstructions of the metric apply to it exactly as to the numerator of the Eisenstein series, with
`y²ΔU = -λU = ν² - ¼` for `ν = ±it`:

* vector sector, Neumann branch, `w = -½ + ν`, damping exactly `½`;
* vector sector, Dirichlet branch, `w = -3/2 + ν`, damping exactly `3/2`;
* scalar sector, `s = -3/2 + ν`, damping exactly `3/2`.

Each is an exact vacuum perturbation of the metric of the massless topological black hole with horizon
`PSL₂(ℤ)\ℍ`, and it is not pure gauge in the vector sector: the gradient of `U` does not vanish.

The damping does not depend on the cusp form: Selberg's bound `λ ≥ ¼` puts every cusp mode exactly on the
base rate of its sector. The zeta modes `w = p - ½`, `s = p - 3/2` with `p = (ρ-1)/2` lie strictly deeper,
by `-Re p ∈ (0, ½)`, and exactly `¼` deeper at every zero iff RH. By the Weyl lower bound the cusp modes of
frequency at most `T` number at least `cT²`, while the zeta modes number `O(T log T)`: the gravitational
spectrum is at the universal rate on a set of density one, unconditionally, and RH concerns a density-zero
part of it.
-/

open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction
open GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)

namespace CuspGravity

/-! ### The coordinate chart of the horizon -/

/-- The chart `(x, y) ↦ x + iy`. -/
def chartL : Point →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight I

theorem chartL_apply (z : Point) : chartL z = (z 0 : ℂ) + (z 1 : ℂ) * I := by
  simp [chartL, Complex.real_smul]

theorem chartL_im (z : Point) : (chartL z).im = z 1 := by
  rw [chartL_apply]
  simp

theorem chartL_single_zero : chartL (Pi.single 0 1) = 1 := by
  rw [chartL_apply]
  simp

theorem chartL_single_one : chartL (Pi.single 1 1) = I := by
  rw [chartL_apply]
  simp

theorem coordDeriv_comp {F : ℂ → ℂ} {w : Point} (hF : DifferentiableAt ℝ F (chartL w)) (k : Fin 2) :
    coordDeriv k (fun z => F (chartL z)) w = fderiv ℝ F (chartL w) (chartL (Pi.single k 1)) := by
  have h := (hF.hasFDerivAt.comp w chartL.hasFDerivAt).fderiv
  show fderiv ℝ (F ∘ chartL) w (Pi.single k 1) = _
  rw [h]
  rfl

theorem coordDeriv_two_comp {F : ℂ → ℂ} {z : Point} {k : Fin 2}
    (hF : ∀ᶠ ζ in 𝓝 (chartL z), DifferentiableAt ℝ F ζ)
    (hd : DifferentiableAt ℝ (fun ζ => fderiv ℝ F ζ (chartL (Pi.single k 1))) (chartL z)) :
    coordDeriv k (coordDeriv k (fun z => F (chartL z))) z =
      fderiv ℝ (fun ζ => fderiv ℝ F ζ (chartL (Pi.single k 1))) (chartL z) (chartL (Pi.single k 1)) := by
  have he : coordDeriv k (fun z => F (chartL z)) =ᶠ[𝓝 z]
      fun w => (fun ζ => fderiv ℝ F ζ (chartL (Pi.single k 1))) (chartL w) := by
    filter_upwards [chartL.continuous.continuousAt.tendsto.eventually hF] with w hw
    exact coordDeriv_comp hw k
  show fderiv ℝ (coordDeriv k (fun z => F (chartL z))) z (Pi.single k 1) = _
  rw [he.fderiv_eq]
  exact coordDeriv_comp hd k

/-- A continuous linear map commutes with a second directional derivative of a `C²` germ. -/
theorem fderiv_fderiv_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℂ)
    {G : ℂ → E} {ζ : ℂ} (hG : ContDiffAt ℝ 2 G ζ) (v : ℂ) :
    fderiv ℝ (fun ζ' => fderiv ℝ (fun x => L (G x)) ζ' v) ζ v =
      L (fderiv ℝ (fun ζ' => fderiv ℝ G ζ' v) ζ v) := by
  have hG1 : ∀ᶠ ζ' in 𝓝 ζ, DifferentiableAt ℝ G ζ' :=
    (hG.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have he : (fun ζ' => fderiv ℝ (fun x => L (G x)) ζ' v) =ᶠ[𝓝 ζ] fun ζ' => L (fderiv ℝ G ζ' v) := by
    filter_upwards [hG1] with ζ' h
    rw [show (fun x => L (G x)) = L ∘ G from rfl, (L.hasFDerivAt.comp ζ' h.hasFDerivAt).fderiv]
    rfl
  rw [he.fderiv_eq]
  have hd : DifferentiableAt ℝ (fun ζ' => fderiv ℝ G ζ' v) ζ :=
    (GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy.dir_contDiffAt hG v).differentiableAt (by norm_num)
  rw [show (fun ζ' => L (fderiv ℝ G ζ' v)) = L ∘ fun ζ' => fderiv ℝ G ζ' v from rfl,
    (L.hasFDerivAt.comp ζ hd.hasFDerivAt).fderiv]
  rfl

/-! ### Cusp forms are smooth -/

/-- The upper half plane as an open set of the chart. -/
def upper : TopologicalSpace.Opens ℂ := ⟨{ζ : ℂ | 0 < ζ.im}, isOpen_lt continuous_const Complex.continuous_im⟩

theorem isOpen_upperSet : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im

/-- The scalar component of a level-one field in the chart. -/
def compField (U : UpperHalfPlane → DeckSpace 0) (ζ : ℂ) : ℂ := U (ofComplex ζ) (1 : Deck 0)

/-- The coordinate projection of `DeckSpace 0`. -/
def projL : DeckSpace 0 →L[ℝ] ℂ := (EuclideanSpace.proj (1 : Deck 0) : DeckSpace 0 →L[ℂ] ℂ).restrictScalars ℝ

theorem projL_apply (v : DeckSpace 0) : projL v = v (1 : Deck 0) := rfl

section Eigen

variable {lam : ℝ} {U : UpperHalfPlane → DeckSpace 0} (hU : IsCuspLaplaceEigen 0 lam U)
include hU

theorem contDiffOn_compField : ContDiffOn ℝ 2 (compField U) {ζ : ℂ | 0 < ζ.im} :=
  projL.contDiff.comp_contDiffOn hU.contDiffOn

/-- **The eigenvalue equation in the chart**: `Δ_{euc} U = -(λ/y²) U`. -/
theorem compField_eq {ζ : ℂ} (hζ : 0 < ζ.im) :
    fderiv ℝ (fun ζ' => fderiv ℝ (compField U) ζ' 1) ζ 1 +
        fderiv ℝ (fun ζ' => fderiv ℝ (compField U) ζ' I) ζ I =
      ((-lam / ζ.im ^ 2 : ℝ) : ℂ) * compField U ζ := by
  set G : ℂ → DeckSpace 0 := fun ζ => U (ofComplex ζ) with hGdef
  have hGc : ContDiffAt ℝ 2 G ζ := hU.contDiffOn.contDiffAt (isOpen_upperSet.mem_nhds hζ)
  have h1 := fderiv_fderiv_clm projL hGc 1
  have h2 := fderiv_fderiv_clm projL hGc I
  show fderiv ℝ (fun ζ' => fderiv ℝ (fun x => projL (G x)) ζ' 1) ζ 1 +
      fderiv ℝ (fun ζ' => fderiv ℝ (fun x => projL (G x)) ζ' I) ζ I =
    ((-lam / ζ.im ^ 2 : ℝ) : ℂ) * projL (G ζ)
  rw [h1, h2, ← map_add]
  set X := fderiv ℝ (fun ζ' => fderiv ℝ G ζ' 1) ζ 1 + fderiv ℝ (fun ζ' => fderiv ℝ G ζ' I) ζ I with hX
  have heig := hU.eigen (ofComplex ζ)
  have hw : ((ofComplex ζ : UpperHalfPlane) : ℂ) = ζ := by rw [ofComplex_apply_of_im_pos hζ]
  have him : (ofComplex ζ : UpperHalfPlane).im = ζ.im := by rw [ofComplex_apply_of_im_pos hζ]; rfl
  have hlap : hypLap U (ofComplex ζ) = ((ofComplex ζ : UpperHalfPlane).im ^ 2) • X := by
    unfold hypLap chartLap
    rw [hw]
    rfl
  rw [hlap, him] at heig
  have hP := congrArg (EuclideanSpace.proj (1 : Deck 0) : DeckSpace 0 →L[ℂ] ℂ) heig
  rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul] at hP
  have hP' : ((ζ.im ^ 2 : ℝ) : ℂ) * projL X = ((-lam : ℝ) : ℂ) * projL (G ζ) := by
    rw [← Complex.real_smul]
    exact hP
  have hy : ζ.im ^ 2 ≠ 0 := by positivity
  have hyC : ((ζ.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [show ((-lam / ζ.im ^ 2 : ℝ) : ℂ) = ((-lam : ℝ) : ℂ) / ((ζ.im ^ 2 : ℝ) : ℂ) by push_cast; ring,
    div_mul_eq_mul_div, eq_div_iff hyC]
  linear_combination hP'

/-- **Cusp forms are smooth** (planar elliptic regularity). -/
theorem contDiffOn_compField_top : ContDiffOn ℝ ∞ (compField U) {ζ : ℂ | 0 < ζ.im} := by
  have hV : ContDiffOn ℝ ∞ (fun ζ : ℂ => ((-lam / ζ.im ^ 2 : ℝ) : ℂ)) (upper : Set ℂ) := by
    intro ζ hζ
    have hζ' : 0 < ζ.im := hζ
    have hr : ContDiffAt ℝ ∞ (fun ζ : ℂ => -lam / ζ.im ^ 2) ζ :=
      contDiffAt_const.div (Complex.imCLM.contDiff.contDiffAt.pow 2) (by positivity)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ζ hr).contDiffWithinAt
  exact PlanarElliptic.smooth_of_equation (Ω := upper) (contDiffOn_compField hU) hV
    fun ζ hζ => compField_eq hU hζ

/-! ### The field on the horizon coordinates -/

/-- The cusp form in the horizon coordinates `(x, y)`. -/
def horizonField (U : UpperHalfPlane → DeckSpace 0) : Point → ℂ := fun z => compField U (chartL z)

omit hU in
theorem horizonField_def (z : Point) : horizonField U z = compField U (chartL z) := rfl

theorem contDiffAt_horizonField {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞ (horizonField U) z := by
  have hmem : chartL z ∈ {ζ : ℂ | 0 < ζ.im} := by show 0 < (chartL z).im; rw [chartL_im]; exact hz
  exact ((contDiffOn_compField_top hU).contDiffAt (isOpen_upperSet.mem_nhds hmem)).comp z
    chartL.contDiff.contDiffAt

/-- **The eigenvalue equation in horizon coordinates**: `y²(∂ₓ² + ∂ᵧ²) U = -λ U`. -/
theorem horizonField_eigen {z : Point} (hz : 0 < z 1) :
    (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (horizonField U)) z +
      coordDeriv 1 (coordDeriv 1 (horizonField U)) z) = ((-lam : ℝ) : ℂ) * horizonField U z := by
  have hmem : chartL z ∈ {ζ : ℂ | 0 < ζ.im} := by show 0 < (chartL z).im; rw [chartL_im]; exact hz
  have hF : ContDiffAt ℝ ∞ (compField U) (chartL z) :=
    (contDiffOn_compField_top hU).contDiffAt (isOpen_upperSet.mem_nhds hmem)
  have hF2 : ContDiffAt ℝ 2 (compField U) (chartL z) := contDiffAt_infty.mp hF 2
  have hev : ∀ᶠ ζ in 𝓝 (chartL z), DifferentiableAt ℝ (compField U) ζ :=
    (hF2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hd : ∀ v : ℂ, DifferentiableAt ℝ (fun ζ => fderiv ℝ (compField U) ζ v) (chartL z) := fun v =>
    (GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy.dir_contDiffAt hF2 v).differentiableAt (by norm_num)
  have e0 := coordDeriv_two_comp (k := 0) hev (hd _)
  have e1 := coordDeriv_two_comp (k := 1) hev (hd _)
  rw [chartL_single_zero] at e0
  rw [chartL_single_one] at e1
  have hfun : horizonField U = fun z => compField U (chartL z) := rfl
  rw [hfun, e0, e1, compField_eq hU (by rw [chartL_im]; exact hz), chartL_im]
  have hz1 : ((z 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  push_cast
  field_simp

/-! ### The modes -/

omit hU in
theorem lam_eq_neumann {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) :
    ((-lam : ℝ) : ℂ) = (-1 / 2 + ν) * (-1 / 2 + ν + 1) := by
  push_cast
  linear_combination -hν

omit hU in
theorem lam_eq_dirichlet {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) :
    ((-lam : ℝ) : ℂ) = (-3 / 2 + ν + 1) * (-3 / 2 + ν + 2) := by
  push_cast
  linear_combination -hν

/-- **A cusp form is a vector gravitational mode, Neumann branch** `w = -½ + ν`. -/
theorem vector_mode_neumann {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) (q : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (vectorMetricField (-1 / 2 + ν) (fN (-1 / 2 + ν))
        (gradCovector (horizonField U))) q.val) (-3) i j = 0 := by
  have hr : 1 < q.val 1 := q.property.1
  set w := -1 / 2 + ν with hw
  obtain ⟨h1, h2, h3⟩ := deriv_chain (fun _ h => hasDerivAt_fN h w) (fun _ h => hasDerivAt_fN1 h w)
    (fun _ h => hasDerivAt_fN2 h w) hr
  obtain ⟨hm, hm1⟩ := fN_master hr w
  have hlam : ((-lam : ℝ) : ℂ) = w * (w + 1) := lam_eq_neumann hν
  refine vectorMetricField_vacuum w (lam := ((-lam : ℝ) : ℂ))
    (fun z hz => contDiffAt_infty.mp (contDiffAt_horizonField hU hz) 3)
    (fun z hz => horizonField_eigen hU hz) q
    (by exact_mod_cast contDiffAt_infty.mp (contDiffAt_fN hr w) 3) ?_ ?_ i j
  · rw [h1, h2, hlam]
    exact hm
  · rw [h1, h2, h3, hlam]
    exact hm1

/-- **A cusp form is a vector gravitational mode, Dirichlet branch** `w = -3/2 + ν`. -/
theorem vector_mode_dirichlet {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) (q : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (vectorMetricField (-3 / 2 + ν) (gP (-3 / 2 + ν))
        (gradCovector (horizonField U))) q.val) (-3) i j = 0 := by
  have hr : 1 < q.val 1 := q.property.1
  set w := -3 / 2 + ν with hw
  obtain ⟨h1, h2, h3⟩ := deriv_chain (fun _ h => hasDerivAt_gP h w) (fun _ h => hasDerivAt_gP1 h w)
    (fun _ h => hasDerivAt_gP2 h w) hr
  obtain ⟨hm, hm1⟩ := gP_master hr w
  have hlam : ((-lam : ℝ) : ℂ) = (w + 1) * (w + 2) := lam_eq_dirichlet hν
  refine vectorMetricField_vacuum w (lam := ((-lam : ℝ) : ℂ))
    (fun z hz => contDiffAt_infty.mp (contDiffAt_horizonField hU hz) 3)
    (fun z hz => horizonField_eigen hU hz) q
    (by exact_mod_cast contDiffAt_infty.mp (contDiffAt_gP hr w) 3) ?_ ?_ i j
  · rw [h1, h2, hlam]
    exact hm
  · rw [h1, h2, h3, hlam]
    exact hm1

/-- **A cusp form is a scalar gravitational mode** `s = -3/2 + ν`, through the corpus reconstruction. -/
theorem scalar_mode {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) (a : ℂ) (q : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    D4BMLinearizedEinsteinSource.residual q
      (ofMetricField (D4BMFundamentalScalarMetric.field (-3 / 2 + ν) a (horizonField U)) q.val) i j = 0 := by
  have hz : 0 < angularPoint q.val 1 := q.property.2
  refine D4BMScalarLinearEquation.field_residual_zero _ _ _ q
    (contDiffAt_infty.mp (contDiffAt_horizonField hU hz) 2) ?_ i j
  rw [scalarLaplacian_eq _ _ hz, horizonField_eigen hU hz, lam_eq_dirichlet hν]

/-- **The vector modes of a cusp form are not pure gauge**: the gradient of a nonzero cusp form with
`λ ≠ 0` does not vanish identically. -/
theorem exists_gradCovector_ne_zero (hlam : lam ≠ 0) (hne : ∃ w, U w ≠ 0) :
    ∃ z : Point, 0 < z 1 ∧ ∃ k, gradCovector (horizonField U) k z ≠ 0 := by
  obtain ⟨w, hw⟩ := hne
  have hw1 : U w (1 : Deck 0) ≠ 0 := by
    intro h0
    apply hw
    ext q
    rw [Subsingleton.elim q (1 : Deck 0), h0]
    rfl
  set z : Point := ![w.re, w.im] with hzdef
  have hz : 0 < z 1 := by simp [hzdef, w.im_pos]
  have hcz : chartL z = (w : ℂ) := by
    rw [chartL_apply]
    simp [hzdef]
    exact Complex.re_add_im (w : ℂ)
  have hYz : horizonField U z ≠ 0 := by
    rw [horizonField_def, hcz, compField, UpperHalfPlane.ofComplex_apply]
    exact hw1
  by_contra hcon
  push Not at hcon
  apply hYz
  have h0 : ∀ w : Point, 0 < w 1 → coordDeriv 0 (horizonField U) w = 0 := fun w hw => by
    have := hcon w hw 1
    simpa [gradCovector] using this
  have h1 : ∀ w : Point, 0 < w 1 → coordDeriv 1 (horizonField U) w = 0 := fun w hw => by
    have := hcon w hw 0
    simpa [gradCovector] using this
  have hopen : {w : Point | 0 < w 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have h00 : coordDeriv 0 (coordDeriv 0 (horizonField U)) z = 0 := by
    have he : coordDeriv 0 (horizonField U) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hopen] with w hw using h0 w hw
    change fderiv ℝ _ z _ = 0
    rw [he.fderiv_eq]
    simp
  have h11 : coordDeriv 1 (coordDeriv 1 (horizonField U)) z = 0 := by
    have he : coordDeriv 1 (horizonField U) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hopen] with w hw using h1 w hw
    change fderiv ℝ _ z _ = 0
    rw [he.fderiv_eq]
    simp
  have hE := horizonField_eigen hU hz
  rw [h00, h11, add_zero, mul_zero] at hE
  have hl : ((-lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr hlam
  exact (mul_eq_zero.mp hE.symm).resolve_left hl

end Eigen

/-! ### The spectral parameter and the damping -/

theorem exists_spectralParameter {lam : ℝ} (h : 1 / 4 ≤ lam) : ∃ ν : ℂ, ν ^ 2 = 1 / 4 - lam ∧ ν.re = 0 := by
  refine ⟨(Real.sqrt (lam - 1 / 4) : ℂ) * I, ?_, by simp⟩
  rw [mul_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
  push_cast
  ring

/-- **Selberg's bound puts every cusp exponent on the line**: `ν² = ¼ - λ ≤ 0` forces `Re ν = 0`. -/
theorem re_eq_zero_of_sq {lam : ℝ} (h : 1 / 4 ≤ lam) {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) : ν.re = 0 := by
  have h1 := congrArg Complex.re hν
  have h2 := congrArg Complex.im hν
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im] at h1 h2
  by_contra hne
  have him : ν.im = 0 := by
    have : 2 * ν.re * ν.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact absurd (by linarith : ν.re = 0) hne
    · exact h3
  rw [him] at h1
  have : ν.re * ν.re ≤ 0 := by nlinarith
  exact hne (by nlinarith [mul_self_nonneg ν.re])

/-- The cusp form of the `i`-th basis vector. -/
def cuspFn (i : CuspEigenIndex 0) : UpperHalfPlane → DeckSpace 0 := (cuspEigenBasis_spec i).choose

theorem isCuspLaplaceEigen_cuspFn (i : CuspEigenIndex 0) : IsCuspLaplaceEigen 0 i.1 (cuspFn i) :=
  (cuspEigenBasis_spec i).choose_spec.choose

theorem exists_cuspFn_ne_zero (i : CuspEigenIndex 0) : ∃ w, cuspFn i w ≠ 0 := by
  refine exists_ne_zero_of_toDeckL2_ne (isCuspLaplaceEigen_cuspFn i) ?_
  have h := (cuspEigenBasis_spec i).choose_spec.choose_spec
  intro h0
  apply (cuspEigenBasis 0).orthonormal.ne_zero i
  apply Submodule.coe_eq_zero.mp
  rw [h]
  exact h0

/-- **Every cusp form of the modular horizon is a gravitational quasinormal mode, at the universal
damping.** With `ν = ±it`, `Re ν = 0`, the horizon field `U` of the `i`-th cusp form gives exact vacuum
perturbations in the vector sector with time factors `e^{(-½+ν)t}` and `e^{(-3/2+ν)t}` and in the scalar
sector with `e^{(-3/2+ν)t}`, and the vector modes are not pure gauge. -/
theorem cusp_gravitational_modes (i : CuspEigenIndex 0) :
    ∃ ν : ℂ, ν ^ 2 = 1 / 4 - i.1 ∧ (-1 / 2 + ν).re = -1 / 2 ∧ (-3 / 2 + ν).re = -3 / 2 ∧
      (∀ (q : D4BMBackground.ExteriorPoint) (j k : Fin 4),
        CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
          (ofMetricField (vectorMetricField (-1 / 2 + ν) (fN (-1 / 2 + ν))
            (gradCovector (horizonField (cuspFn i)))) q.val) (-3) j k = 0) ∧
      (∀ (q : D4BMBackground.ExteriorPoint) (j k : Fin 4),
        CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
          (ofMetricField (vectorMetricField (-3 / 2 + ν) (gP (-3 / 2 + ν))
            (gradCovector (horizonField (cuspFn i)))) q.val) (-3) j k = 0) ∧
      (∀ (a : ℂ) (q : D4BMBackground.ExteriorPoint) (j k : Fin 4),
        D4BMLinearizedEinsteinSource.residual q
          (ofMetricField (D4BMFundamentalScalarMetric.field (-3 / 2 + ν) a (horizonField (cuspFn i)))
            q.val) j k = 0) ∧
      ∃ z : Point, 0 < z 1 ∧ ∃ k, gradCovector (horizonField (cuspFn i)) k z ≠ 0 := by
  have hq := one_quarter_le_cuspEigenBasis i
  obtain ⟨ν, hν, -⟩ := exists_spectralParameter hq
  have hre := re_eq_zero_of_sq hq hν
  have hU := isCuspLaplaceEigen_cuspFn i
  refine ⟨ν, hν, by simp [hre], by simp [hre], fun q j k => vector_mode_neumann hU hν q j k,
    fun q j k => vector_mode_dirichlet hU hν q j k, fun a q j k => scalar_mode hU hν a q j k,
    exists_gradCovector_ne_zero hU (by linarith) (exists_cuspFn_ne_zero i)⟩

/-! ### The zeta modes lie deeper -/

/-- **The zeta modes are strictly more damped than every cusp mode of their sector**, by `-Re p ∈ (0, ½)`. -/
theorem zero_modes_lie_deeper {p : ℂ} (hp : xi (1 + 2 * p) = 0) :
    -1 < (p - 1 / 2).re ∧ (p - 1 / 2).re < -1 / 2 ∧ -2 < (p - 3 / 2).re ∧ (p - 3 / 2).re < -3 / 2 := by
  obtain ⟨h1, h2⟩ := zero_re_bounds hp
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  norm_num
  constructor <;> [skip; constructor <;> [skip; constructor]] <;> linarith

/-- **RH is the statement that every zeta mode lies exactly `¼` below the cusp modes.** -/
theorem riemannHypothesis_iff_zero_modes_quarter_deeper :
    RiemannHypothesis ↔ ∀ p : ℂ, xi (1 + 2 * p) = 0 → (p - 1 / 2).re = -1 / 2 - 1 / 4 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h p hp
    have := h _ hp
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re] at this
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    norm_num at this ⊢
    linarith
  · intro h ρ hρ
    have hp : xi (1 + 2 * ((ρ - 1) / 2)) = 0 := by
      rw [show 1 + 2 * ((ρ - 1) / 2) = ρ by ring]
      exact hρ
    have := h _ hp
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at this
    linarith

/-- **The cusp modes have density one.** The zeta modes of frequency at most `T` (zeros with ordinate in
`[0, 2T]`) are a vanishing fraction of the cusp modes of frequency at most `T`. -/
theorem tendsto_zeroModes_div_cuspModes :
    Tendsto (fun T : ℝ => (xiZeroCount (2 * T) : ℝ) / (cuspCount (1 / 4 + T ^ 2) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, Λ₀, hW⟩ := WeylBound.weyl_lower_bound
  obtain ⟨c', hc', hZ⟩ := exists_xiZeroCount_upper_bound
  have hlog : Tendsto (fun T : ℝ => Real.log (2 * T) / (2 * T)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at h
    exact h.comp (tendsto_id.const_mul_atTop two_pos)
  have hup : Tendsto (fun T : ℝ => 4 * c' / c * (Real.log (2 * T) / (2 * T))) atTop (𝓝 0) := by
    simpa using hlog.const_mul (4 * c' / c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun T => div_nonneg (by exact_mod_cast xiZeroCount_nonneg _) (Nat.cast_nonneg _)) ?_
  filter_upwards [eventually_ge_atTop (max 1 Λ₀)] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTΛ : Λ₀ ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hΛ : 1 / 4 + T ^ 2 ≥ Λ₀ := by nlinarith
  have hden : c * (1 / 4 + T ^ 2) ≤ (cuspCount (1 / 4 + T ^ 2) : ℝ) := hW _ hΛ
  have hdpos : 0 < (cuspCount (1 / 4 + T ^ 2) : ℝ) := lt_of_lt_of_le (by positivity) hden
  have hnum : (xiZeroCount (2 * T) : ℝ) ≤ c' * (2 * T) * Real.log (2 * T) := hZ _ (by linarith)
  have hlog0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  rw [div_le_iff₀ hdpos]
  have hfac : 0 ≤ 4 * c' / c * (Real.log (2 * T) / (2 * T)) := by positivity
  calc (xiZeroCount (2 * T) : ℝ) ≤ c' * (2 * T) * Real.log (2 * T) := hnum
    _ ≤ 4 * c' / c * (Real.log (2 * T) / (2 * T)) * (c * (1 / 4 + T ^ 2)) := by
        have e : 4 * c' / c * (Real.log (2 * T) / (2 * T)) * (c * T ^ 2) = c' * (2 * T) * Real.log (2 * T) := by
          field_simp
          ring
        have hle : c * T ^ 2 ≤ c * (1 / 4 + T ^ 2) := by nlinarith
        calc c' * (2 * T) * Real.log (2 * T) = 4 * c' / c * (Real.log (2 * T) / (2 * T)) * (c * T ^ 2) := e.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hle hfac
    _ ≤ 4 * c' / c * (Real.log (2 * T) / (2 * T)) * (cuspCount (1 / 4 + T ^ 2) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hfac

end CuspGravity

end GaloisForLFunctions.BlackHoleRingdown
