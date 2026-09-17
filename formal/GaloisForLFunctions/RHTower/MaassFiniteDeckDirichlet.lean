import GaloisForLFunctions.RHTower.MaassLadderL2

/-!
# Finite-deck equivariant Dirichlet data for exceptional Maass sources

A principal-congruence Maass source is not a scalar modular function. Its
complete finite-deck vector is equivariant for the regular deck action. This
file builds the corresponding vector-valued C¹ Dirichlet pre-domain and proves
that every exceptional Maass source belongs to it. The source's two weighted
chart derivatives have exactly the hyperbolic gradient energy already obtained
from the Maass equation and cusp-flux calculation.

No compactness of this pre-domain, cusp-closed subspace, or finite
multiplicity is asserted here.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open MaassCongruenceL2 SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassCharacterSeamFlux SelbergMaassTraceEnergy SelbergMaassSourceCurrents
  SelbergMaassFullGradient MaassLadderL2 GaloisForLFunctions.HTGeometry
noncomputable section

/-- The finite-deck coefficient space for the principal congruence source. -/
abbrev DeckSpace (N : ℕ) := EuclideanSpace ℂ (Deck N)

/-- The chart representative of a finite-deck vector-valued upper-half-plane function. -/
def chartFun {N : ℕ} (F : ℍ → DeckSpace N) : ℂ → DeckSpace N := F ∘ ofComplex

/-- Its real directional derivative in the upper-half-plane chart. -/
def chartDeriv {N : ℕ} (F : ℍ → DeckSpace N) (v : ℂ) (z : ℍ) : DeckSpace N :=
  fderiv ℝ (chartFun F) (z : ℂ) v

/-- The first hyperbolically weighted chart derivative. -/
def hypGradX {N : ℕ} (F : ℍ → DeckSpace N) (z : ℍ) : DeckSpace N :=
  (z.im : ℂ) • chartDeriv F 1 z

/-- The second hyperbolically weighted chart derivative. -/
def hypGradY {N : ℕ} (F : ℍ → DeckSpace N) (z : ℍ) : DeckSpace N :=
  (z.im : ℂ) • chartDeriv F Complex.I z

/-- `C¹` regularity of a finite-deck function in the physical complex chart. -/
def IsChartC1 {N : ℕ} (F : ℍ → DeckSpace N) : Prop :=
  ContDiffOn ℝ 1 (chartFun F) {z : ℂ | 0 < z.im}

/-- Full integral modular covariance with the literal finite regular deck action. -/
def deckEquivariant (N : ℕ) (F : ℍ → DeckSpace N) : Prop :=
  ∀ A : SL2Z, ∀ z : ℍ,
    F (A • z) = finiteRegularUnitary (QuotientGroup.mk A : Deck N) (F z)

private theorem chartFun_add {N : ℕ} (F G : ℍ → DeckSpace N) :
    chartFun (F + G) = chartFun F + chartFun G := rfl

private theorem chartFun_smul {N : ℕ} (c : ℂ) (F : ℍ → DeckSpace N) :
    chartFun (c • F) = c • chartFun F := rfl

private theorem isChartC1_add {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (hG : IsChartC1 G) : IsChartC1 (F + G) := by
  unfold IsChartC1
  rw [chartFun_add]
  exact hF.add hG

private theorem isChartC1_smul {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (c : ℂ) : IsChartC1 (c • F) := by
  unfold IsChartC1
  rw [chartFun_smul]
  exact ContDiffOn.const_smul c hF

private theorem chartDeriv_add {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (hG : IsChartC1 G) (v : ℂ) (z : ℍ) :
    chartDeriv (F + G) v z = chartDeriv F v z + chartDeriv G v z := by
  unfold IsChartC1 at hF hG
  unfold chartDeriv
  rw [chartFun_add]
  have hF' := (hF.differentiableOn one_ne_zero).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hG' := (hG.differentiableOn one_ne_zero).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  rw [fderiv_add hF' hG']
  rfl

private theorem chartDeriv_smul {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (c v : ℂ) (z : ℍ) :
    chartDeriv (c • F) v z = c • chartDeriv F v z := by
  unfold IsChartC1 at hF
  unfold chartDeriv
  rw [chartFun_smul]
  have hF' := (hF.differentiableOn one_ne_zero).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  rw [fderiv_const_smul hF' c]
  rfl

private theorem hypGradX_add {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (hG : IsChartC1 G) :
    hypGradX (F + G) = hypGradX F + hypGradX G := by
  funext z
  simp only [hypGradX, Pi.add_apply, chartDeriv_add hF hG, smul_add]

private theorem hypGradY_add {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (hG : IsChartC1 G) :
    hypGradY (F + G) = hypGradY F + hypGradY G := by
  funext z
  simp only [hypGradY, Pi.add_apply, chartDeriv_add hF hG, smul_add]

private theorem hypGradX_smul {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (c : ℂ) : hypGradX (c • F) = c • hypGradX F := by
  funext z
  simp only [hypGradX, Pi.smul_apply, chartDeriv_smul hF, smul_smul]
  rw [mul_comm]

private theorem hypGradY_smul {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (c : ℂ) : hypGradY (c • F) = c • hypGradY F := by
  funext z
  simp only [hypGradY, Pi.smul_apply, chartDeriv_smul hF, smul_smul]
  rw [mul_comm]

/-- Vector-valued modular C¹ functions whose values and both hyperbolic chart
components are square integrable on the modular cell. -/
def formPreDomain (N : ℕ) : Submodule ℂ (ℍ → DeckSpace N) where
  carrier := {F | IsChartC1 F ∧ deckEquivariant N F ∧ MemLp F 2 cellMeasure ∧
    MemLp (hypGradX F) 2 cellMeasure ∧ MemLp (hypGradY F) 2 cellMeasure}
  zero_mem' := by
    refine ⟨contDiffOn_const, fun _ _ => by simp, memLp_const 0, ?_, ?_⟩
    · refine (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).mpr
        (memLp_const (μ := cellMeasure) (p := 2) (c := (0 : DeckSpace N)))
      unfold hypGradX chartDeriv chartFun
      simp
    · refine (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).mpr
        (memLp_const (μ := cellMeasure) (p := 2) (c := (0 : DeckSpace N)))
      unfold hypGradY chartDeriv chartFun
      simp
  add_mem' := by
    rintro F G ⟨hF1, hF2, hF3, hF4, hF5⟩ ⟨hG1, hG2, hG3, hG4, hG5⟩
    refine ⟨isChartC1_add hF1 hG1, ?_, hF3.add hG3, ?_, ?_⟩
    · intro A z
      simp only [Pi.add_apply, hF2 A z, hG2 A z, map_add]
    · rw [hypGradX_add hF1 hG1]
      exact hF4.add hG4
    · rw [hypGradY_add hF1 hG1]
      exact hF5.add hG5
  smul_mem' := by
    rintro c F ⟨hF1, hF2, hF3, hF4, hF5⟩
    refine ⟨isChartC1_smul hF1 c, ?_, hF3.const_smul c, ?_, ?_⟩
    · intro A z
      simp only [Pi.smul_apply, hF2 A z, map_smul]
    · rw [hypGradX_smul hF1 c]
      exact hF4.const_smul c
    · rw [hypGradY_smul hF1 c]
      exact hF5.const_smul c

namespace formPreDomain

theorem c1 {N : ℕ} (F : formPreDomain N) : IsChartC1 (F : ℍ → DeckSpace N) := F.2.1

theorem equivariant {N : ℕ} (F : formPreDomain N) (A : SL2Z) (z : ℍ) :
    (F : ℍ → DeckSpace N) (A • z) =
      finiteRegularUnitary (QuotientGroup.mk A : Deck N) ((F : ℍ → DeckSpace N) z) := F.2.2.1 A z

theorem memLp {N : ℕ} (F : formPreDomain N) : MemLp (F : ℍ → DeckSpace N) 2 cellMeasure :=
  F.2.2.2.1

theorem memLp_gradX {N : ℕ} (F : formPreDomain N) :
    MemLp (hypGradX (F : ℍ → DeckSpace N)) 2 cellMeasure := F.2.2.2.2.1

theorem memLp_gradY {N : ℕ} (F : formPreDomain N) :
    MemLp (hypGradY (F : ℍ → DeckSpace N)) 2 cellMeasure := F.2.2.2.2.2

end formPreDomain

/-- Square-integrable finite-deck vectors on the modular cell. -/
abbrev DeckL2 (N : ℕ) := Lp (DeckSpace N) 2 cellMeasure

/-- Passage of a square-integrable finite-deck function to its L² class. -/
def toDeckL2 {N : ℕ} (F : ℍ → DeckSpace N) (hF : MemLp F 2 cellMeasure) : DeckL2 N :=
  hF.toLp F

theorem toDeckL2_add {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : MemLp F 2 cellMeasure) (hG : MemLp G 2 cellMeasure) :
    toDeckL2 (F + G) (hF.add hG) = toDeckL2 F hF + toDeckL2 G hG :=
  MemLp.toLp_add hF hG

theorem toDeckL2_smul {N : ℕ} (c : ℂ) {F : ℍ → DeckSpace N}
    (hF : MemLp F 2 cellMeasure) :
    toDeckL2 (c • F) (hF.const_smul c) = c • toDeckL2 F hF :=
  MemLp.toLp_const_smul c hF

theorem toDeckL2_congr {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : MemLp F 2 cellMeasure) (hG : MemLp G 2 cellMeasure)
    (h : F =ᵐ[cellMeasure] G) : toDeckL2 F hF = toDeckL2 G hG :=
  MemLp.toLp_congr hF hG h

/-- The value and two weighted-gradient coordinates of the finite-deck form. -/
def formCoordinate (N : ℕ) : Fin 3 → (formPreDomain N →ₗ[ℂ] DeckL2 N)
  | 0 => { toFun := fun F => toDeckL2 _ (formPreDomain.memLp F)
           map_add' := fun F G => toDeckL2_add (formPreDomain.memLp F) (formPreDomain.memLp G)
           map_smul' := fun c F => toDeckL2_smul c (formPreDomain.memLp F) }
  | 1 => { toFun := fun F => toDeckL2 _ (formPreDomain.memLp_gradX F)
           map_add' := fun F G => by
             rw [← toDeckL2_add (formPreDomain.memLp_gradX F) (formPreDomain.memLp_gradX G)]
             exact toDeckL2_congr _ _ (Filter.EventuallyEq.of_eq
               (hypGradX_add (formPreDomain.c1 F) (formPreDomain.c1 G)))
           map_smul' := fun c F => by
             rw [RingHom.id_apply, ← toDeckL2_smul c (formPreDomain.memLp_gradX F)]
             exact toDeckL2_congr _ _ (Filter.EventuallyEq.of_eq
               (hypGradX_smul (formPreDomain.c1 F) c)) }
  | 2 => { toFun := fun F => toDeckL2 _ (formPreDomain.memLp_gradY F)
           map_add' := fun F G => by
             rw [← toDeckL2_add (formPreDomain.memLp_gradY F) (formPreDomain.memLp_gradY G)]
             exact toDeckL2_congr _ _ (Filter.EventuallyEq.of_eq
               (hypGradY_add (formPreDomain.c1 F) (formPreDomain.c1 G)))
           map_smul' := fun c F => by
             rw [RingHom.id_apply, ← toDeckL2_smul c (formPreDomain.memLp_gradY F)]
             exact toDeckL2_congr _ _ (Filter.EventuallyEq.of_eq
               (hypGradY_smul (formPreDomain.c1 F) c)) }

/-- The Hilbert triple carrying value and both weighted derivatives. -/
abbrev FormTriple (N : ℕ) := PiLp 2 (fun _ : Fin 3 => DeckL2 N)

/-- Coordinate embedding of the finite-deck form pre-domain. -/
def formEmbeddingMap (N : ℕ) : formPreDomain N →ₗ[ℂ] FormTriple N :=
  (WithLp.linearEquiv 2 ℂ (Fin 3 → DeckL2 N)).symm.toLinearMap ∘ₗ
    LinearMap.pi (formCoordinate N)

theorem formEmbeddingMap_apply (N : ℕ) (F : formPreDomain N) (i : Fin 3) :
    (formEmbeddingMap N F).ofLp i = formCoordinate N i F := rfl

private theorem isChartC1_continuous {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (hF.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [IsChartC1, chartFun, Function.comp_def, ofComplex_apply] using h

/-- A finite-deck equivariant C¹ vector is determined by its form coordinates.
This is pre-domain rigidity only; it does not assert closability after completion. -/
theorem formEmbeddingMap_injective (N : ℕ) : Function.Injective (formEmbeddingMap N) := by
  intro F G hFG
  have h0 : formCoordinate N 0 F = formCoordinate N 0 G := by
    have h := congrArg (fun V : FormTriple N => V.ofLp 0) hFG
    simpa only [formEmbeddingMap_apply] using h
  have hae : (F : ℍ → DeckSpace N) =ᵐ[cellMeasure] (G : ℍ → DeckSpace N) := by
    filter_upwards [MemLp.coeFn_toLp (formPreDomain.memLp F),
      MemLp.coeFn_toLp (formPreDomain.memLp G)] with z hF hG
    rw [← hF, ← hG]
    change (formCoordinate N 0 F) z = (formCoordinate N 0 G) z
    exact congrArg (fun H : DeckL2 N => H z) h0
  have hfd : EqOn (F : ℍ → DeckSpace N) (G : ℍ → DeckSpace N) fd :=
    Measure.eqOn_of_ae_eq (μ := (volume : Measure ℍ)) hae
      (isChartC1_continuous (formPreDomain.c1 F)).continuousOn
      (isChartC1_continuous (formPreDomain.c1 G)).continuousOn
      (by rw [← fdo_eq_interior_fd, ← fd_eq_closure_fdo])
  apply Subtype.ext
  funext z
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  apply (finiteRegularUnitary (QuotientGroup.mk A : Deck N)).injective
  rw [← formPreDomain.equivariant F A z, ← formPreDomain.equivariant G A z]
  exact hfd hA

/-- Completion of the finite-deck equivariant form in its three L² coordinates. -/
def formDomainClosure (N : ℕ) : Submodule ℂ (FormTriple N) :=
  (LinearMap.range (formEmbeddingMap N)).topologicalClosure

/-- Completed finite-deck equivariant Dirichlet form domain. -/
abbrev FormDomain (N : ℕ) := ↥(formDomainClosure N)

instance (N : ℕ) : CompleteSpace (FormDomain N) :=
  inferInstanceAs (CompleteSpace ↥(LinearMap.range (formEmbeddingMap N)).topologicalClosure)

/-- A pre-domain vector as an element of its completed form domain. -/
def toFormDomain (N : ℕ) (F : formPreDomain N) : FormDomain N :=
  ⟨formEmbeddingMap N F, subset_closure ⟨F, rfl⟩⟩

/-- First-coordinate map from completed finite-deck form data to L². -/
def formInclusion (N : ℕ) : FormDomain N →L[ℂ] DeckL2 N :=
  (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 0).comp (formDomainClosure N).subtypeL

theorem formInclusion_toFormDomain (N : ℕ) (F : formPreDomain N) :
    formInclusion N (toFormDomain N F) = toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F) := rfl

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The source's first weighted derivative. -/
def sourceHypGradX (z : ℍ) : DeckSpace N :=
  (z.im : ℂ) • sourceDerivative N f 1 z

/-- The source's second weighted derivative. -/
def sourceHypGradY (z : ℍ) : DeckSpace N :=
  (z.im : ℂ) • sourceDerivative N f Complex.I z

theorem sourceHypGradX_continuous : Continuous (sourceHypGradX N f) :=
  (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
    (sourceDerivative_continuous N f 1)

theorem sourceHypGradY_continuous : Continuous (sourceHypGradY N f) :=
  (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
    (sourceDerivative_continuous N f Complex.I)

/-- The finite-deck weighted derivative energy is the physical hyperbolic
energy density, with no scalar descent. -/
theorem sourceHypGrad_energy (z : ℍ) :
    ‖sourceHypGradX N f z‖ ^ 2 + ‖sourceHypGradY N f z‖ ^ 2 =
      hyperbolicGradient N f z := by
  rw [sourceHypGradX, sourceHypGradY]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_add, sourceDerivative_gradient]
  rfl

theorem hypGradX_sourceVector (z : ℍ) :
    hypGradX (sourceVector N f) z = sourceHypGradX N f z := by
  unfold hypGradX chartDeriv chartFun sourceHypGradX
  exact congrArg ((z.im : ℂ) • ·) (by simpa [dir, Function.comp_def] using (sourceDerivative_eq_dir N f 1 z).symm)

theorem hypGradY_sourceVector (z : ℍ) :
    hypGradY (sourceVector N f) z = sourceHypGradY N f z := by
  unfold hypGradY chartDeriv chartFun sourceHypGradY
  exact congrArg ((z.im : ℂ) • ·) (by simpa [dir, Function.comp_def] using (sourceDerivative_eq_dir N f Complex.I z).symm)

section Exceptional
variable (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

/-- Exceptional source weighted horizontal derivative is square integrable on
its actual finite-deck modular cell. -/
theorem sourceHypGradX_memLp : MemLp (sourceHypGradX N f) 2 cellMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (sourceHypGradX_continuous N f).aestronglyMeasurable).mpr
  apply (cell_gradient_integrable N lam f).mono'
    ((sourceHypGradX_continuous N f).norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sourceHypGrad_energy]
  exact le_add_of_nonneg_right (sq_nonneg ‖sourceHypGradY N f z‖)

/-- Exceptional source weighted vertical derivative is square integrable on
its actual finite-deck modular cell. -/
theorem sourceHypGradY_memLp : MemLp (sourceHypGradY N f) 2 cellMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (sourceHypGradY_continuous N f).aestronglyMeasurable).mpr
  apply (cell_gradient_integrable N lam f).mono'
    ((sourceHypGradY_continuous N f).norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sourceHypGrad_energy]
  exact le_add_of_nonneg_left (sq_nonneg ‖sourceHypGradX N f z‖)

/-- The exceptional source is an element of the finite-deck equivariant
Dirichlet pre-domain. -/
def sourceInFormPreDomain : formPreDomain N :=
  ⟨sourceVector N f, (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).of_le
      (by norm_num), sourceVector_pullback N f, sourceVector_memLp N f,
    (memLp_congr_ae (Filter.Eventually.of_forall
      (hypGradX_sourceVector N f))).mpr (sourceHypGradX_memLp N lam f),
    (memLp_congr_ae (Filter.Eventually.of_forall
      (hypGradY_sourceVector N f))).mpr (sourceHypGradY_memLp N lam f)⟩

theorem sourceInFormPreDomain_coe : (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) =
    sourceVector N f := rfl

/-- The exceptional source in the completed finite-deck form domain. -/
def sourceFormVector : FormDomain N := toFormDomain N (sourceInFormPreDomain N lam f)

/-- The completed form's value coordinate is the existing concrete source L²
vector. -/
theorem formInclusion_sourceFormVector :
    formInclusion N (sourceFormVector N lam f) = sourceLp N f := by
  rw [sourceFormVector, formInclusion_toFormDomain]
  rfl

end Exceptional
end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
