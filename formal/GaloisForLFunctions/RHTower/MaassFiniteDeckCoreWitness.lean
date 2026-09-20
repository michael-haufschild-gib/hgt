import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
import GaloisForLFunctions.HTGeometry.RectangleGridDecomposition
import GaloisForLFunctions.HTGeometry.SmoothHeightRetraction
import GaloisForLFunctions.HTGeometry.WitnessLinePoincare

/-!
# Global witness fields for finite-deck Maass cores

The upper-half-plane chart is only defined smoothly at positive height.  The
smooth height retraction supplies global scalar fields that agree with every
finite-deck coordinate, with its chart germ, on a prescribed positive core.
-/

open UpperHalfPlane Set Filter Topology Complex
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Real-linear readout of one finite-deck coordinate. -/
noncomputable def deckCoordinate (N : ℕ) (q : Deck N) : DeckSpace N →L[ℝ] ℂ :=
  (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Deck N => ℂ) q).restrictScalars ℝ

@[simp]
theorem deckCoordinate_apply (N : ℕ) (q : Deck N) (v : DeckSpace N) :
    deckCoordinate N q v = v q := by
  change (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Deck N => ℂ) q) v = v q
  exact PiLp.proj_apply 2 (𝕜 := ℂ) (fun _ : Deck N => ℂ) q v

/-- Global scalar representative of one deck coordinate through a positive height retraction. -/
noncomputable def retractedDeckComponent {N : ℕ} (ε : ℝ) (F : formPreDomain N) (q : Deck N) :
    ℝ × ℝ → ℂ := fun p =>
  (chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p)) q

/-- Each retracted deck coordinate is globally `C¹`. -/
theorem contDiff_retractedDeckComponent {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (q : Deck N) :
    ContDiff ℝ 1 (retractedDeckComponent ε F q) := by
  have hfield : ContDiffOn ℝ 1
      (fun z => (chartFun (F : ℍ → DeckSpace N) z) q)
      {z : ℂ | 0 < z.im} :=
    by
      change ContDiffOn ℝ 1
        (fun z => deckCoordinate N q (chartFun (F : ℍ → DeckSpace N) z))
        {z : ℂ | 0 < z.im}
      exact (deckCoordinate N q).contDiff.contDiffOn.comp (formPreDomain.c1 F)
        fun _ _ => mem_univ _
  change ContDiff ℝ 1
    (fun p => (chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p)) q)
  exact contDiff_retractedField hε hfield

/-- Horizontal derivative field of a globally retracted deck coordinate. -/
noncomputable def retractedDeckComponentX {N : ℕ} (ε : ℝ) (F : formPreDomain N)
    (q : Deck N) : ℝ × ℝ → ℂ := fun p =>
  fderiv ℝ (retractedDeckComponent ε F q) p (1, 0)

/-- Vertical derivative field of a globally retracted deck coordinate. -/
noncomputable def retractedDeckComponentY {N : ℕ} (ε : ℝ) (F : formPreDomain N)
    (q : Deck N) : ℝ × ℝ → ℂ := fun p =>
  fderiv ℝ (retractedDeckComponent ε F q) p (0, 1)

/-- The horizontal derivative field is continuous. -/
theorem continuous_retractedDeckComponentX {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (q : Deck N) :
    Continuous (retractedDeckComponentX ε F q) := by
  change Continuous fun p : ℝ × ℝ =>
    fderiv ℝ (retractedDeckComponent ε F q) p (1, 0)
  exact (contDiff_retractedDeckComponent hε F q).continuous_fderiv_apply one_ne_zero |>.comp
    (continuous_id.prodMk continuous_const)

/-- The vertical derivative field is continuous. -/
theorem continuous_retractedDeckComponentY {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (q : Deck N) :
    Continuous (retractedDeckComponentY ε F q) := by
  change Continuous fun p : ℝ × ℝ =>
    fderiv ℝ (retractedDeckComponent ε F q) p (0, 1)
  exact (contDiff_retractedDeckComponent hε F q).continuous_fderiv_apply one_ne_zero |>.comp
    (continuous_id.prodMk continuous_const)

/-- The declared horizontal derivative is the derivative on every horizontal line. -/
theorem hasDerivAt_retractedDeckComponentX {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (q : Deck N) (x y : ℝ) :
    HasDerivAt (fun t => retractedDeckComponent ε F q (t, y))
      (retractedDeckComponentX ε F q (x, y)) x := by
  have hline : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x := by
    simpa using
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := ℝ) (F := ℝ) x y).hasDerivAt
  have h := ((contDiff_retractedDeckComponent hε F q).differentiable one_ne_zero (x, y)).hasFDerivAt
    |>.comp_hasDerivAt x hline
  change HasDerivAt (retractedDeckComponent ε F q ∘ fun t => (t, y))
    (fderiv ℝ (retractedDeckComponent ε F q) (x, y) (1, 0)) x
  exact h

/-- The declared vertical derivative is the derivative on every vertical line. -/
theorem hasDerivAt_retractedDeckComponentY {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (q : Deck N) (x y : ℝ) :
    HasDerivAt (fun t => retractedDeckComponent ε F q (x, t))
      (retractedDeckComponentY ε F q (x, y)) y := by
  have hline : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y := by
    simpa using
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := ℝ) x y).hasDerivAt
  have h := ((contDiff_retractedDeckComponent hε F q).differentiable one_ne_zero (x, y)).hasFDerivAt
    |>.comp_hasDerivAt y hline
  change HasDerivAt (retractedDeckComponent ε F q ∘ fun t => (x, t))
    (fderiv ℝ (retractedDeckComponent ε F q) (x, y) (0, 1)) y
  exact h

/-- A whole finite deck shares one witness line and one cell-constant approximation. -/
theorem exists_retractedDeck_witness_line {N : ℕ} {ε a b c d : ℝ} (hε : 0 < ε)
    (hab : a < b) (hcd : c ≤ d) (F : formPreDomain N) :
    ∃ x0 ∈ Set.Ioc a b,
      (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq
          (retractedDeckComponent ε F q (x, y) -
            verticalCellAverage c d (retractedDeckComponent ε F q) x0)) ≤
        8 * (b - a) ^ 2 * (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
          Complex.normSq (retractedDeckComponentX ε F q (x, y))) +
        2 * (d - c) ^ 2 * (∑ q, ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
          Complex.normSq (retractedDeckComponentY ε F q (x, y))) := by
  exact exists_rectangle_witness_line_finset hab hcd
    (fun q => (contDiff_retractedDeckComponent hε F q).continuous)
    (fun q => continuous_retractedDeckComponentX hε F q)
    (fun q => continuous_retractedDeckComponentY hε F q)
    (fun q x y => hasDerivAt_retractedDeckComponentX hε F q x y)
    (fun q x y => hasDerivAt_retractedDeckComponentY hε F q x y)

/-- The unretracted coordinate formula on a positive-height rectangle. -/
noncomputable def standardDeckComponent {N : ℕ} (F : formPreDomain N) (q : Deck N) :
    ℝ × ℝ → ℂ := fun p =>
  (chartFun (F : ℍ → DeckSpace N) ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) q

/-- Strictly above the cutoff, retracted and unretracted coordinates have the same germ. -/
theorem retractedDeckComponent_eventuallyEq_standard {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) (q : Deck N) :
    retractedDeckComponent ε F q =ᶠ[𝓝 (x, y)] standardDeckComponent F q := by
  filter_upwards [retractedPoint_eventuallyEq_standard hε hy] with p hp
  simp only [retractedDeckComponent, standardDeckComponent, hp]

/-- Strictly above the cutoff, the full real derivative is the original coordinate derivative. -/
theorem retractedDeckComponent_fderiv_eq_standard {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) (q : Deck N) :
    fderiv ℝ (retractedDeckComponent ε F q) (x, y) =
      fderiv ℝ (standardDeckComponent F q) (x, y) :=
  (retractedDeckComponent_eventuallyEq_standard hε hy F q).fderiv_eq

/-- On a positive horizontal line, the standard coordinate derivative is `chartDeriv 1`. -/
theorem hasDerivAt_standardDeckComponentX {N : ℕ} (F : formPreDomain N) (q : Deck N)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => standardDeckComponent F q (t, y))
      ((chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q) x := by
  change HasDerivAt (fun t : ℝ => deckCoordinate N q
      (chartFun (F : ℍ → DeckSpace N) ((t : ℂ) + (y : ℂ) * Complex.I)))
      (deckCoordinate N q (chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))) x
  have hpoint : HasDerivAt (fun t : ℝ =>
      (t : ℂ) + (y : ℂ) * Complex.I) 1 x := by
    simpa using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
  have hpos : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa using hy
  have hchart :=
    (((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hpos)).hasFDerivAt.comp_hasDerivAt x hpoint
  have hcoordinate := (deckCoordinate N q).hasFDerivAt.comp_hasDerivAt x hchart
  simp only [chartDeriv, ofComplex_apply_of_im_pos hpos]
  convert hcoordinate using 1 <;> rfl

/-- On a positive vertical line, the standard coordinate derivative is `chartDeriv I`. -/
theorem hasDerivAt_standardDeckComponentY {N : ℕ} (F : formPreDomain N) (q : Deck N)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => standardDeckComponent F q (x, t))
      ((chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q) y := by
  change HasDerivAt (fun t : ℝ => deckCoordinate N q
      (chartFun (F : ℍ → DeckSpace N) ((x : ℂ) + (t : ℂ) * Complex.I)))
      (deckCoordinate N q (chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))) y
  have hpoint : HasDerivAt (fun t : ℝ =>
      (x : ℂ) + (t : ℂ) * Complex.I) Complex.I y := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)
  have hpos : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa using hy
  have hchart :=
    (((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hpos)).hasFDerivAt.comp_hasDerivAt y hpoint
  have hcoordinate := (deckCoordinate N q).hasFDerivAt.comp_hasDerivAt y hchart
  simp only [chartDeriv, ofComplex_apply_of_im_pos hpos]
  convert hcoordinate using 1 <;> rfl

/-- Above the cutoff, the global horizontal derivative is exactly the chart derivative. -/
theorem retractedDeckComponentX_eq_chartDeriv {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) (q : Deck N) :
    retractedDeckComponentX ε F q (x, y) =
      (chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q := by
  have hline : (fun t => retractedDeckComponent ε F q (t, y)) =ᶠ[𝓝 x]
      fun t => standardDeckComponent F q (t, y) :=
    Filter.Eventually.of_forall fun t => by
      simp only [retractedDeckComponent, standardDeckComponent,
        retractedPoint_eq_of_le hε hy.le]
  exact (hasDerivAt_retractedDeckComponentX hε F q x y).unique
    ((hasDerivAt_standardDeckComponentX F q x (hε.trans hy)).congr_of_eventuallyEq hline)

/-- Above the cutoff, the global vertical derivative is exactly the chart derivative. -/
theorem retractedDeckComponentY_eq_chartDeriv {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) (q : Deck N) :
    retractedDeckComponentY ε F q (x, y) =
      (chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q := by
  have hline : (fun t => retractedDeckComponent ε F q (x, t)) =ᶠ[𝓝 y]
      fun t => standardDeckComponent F q (x, t) :=
    (retractedDeckComponent_eventuallyEq_standard hε hy F q).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto y)
  exact (hasDerivAt_retractedDeckComponentY hε F q x y).unique
    ((hasDerivAt_standardDeckComponentY F q x (hε.trans hy)).congr_of_eventuallyEq hline)

/-- The finite-deck Hilbert norm is the sum of the coordinate norm squares. -/
theorem sum_normSq_deckCoordinate {N : ℕ} (v : DeckSpace N) :
    (∑ q, Complex.normSq (deckCoordinate N q v)) = ‖v‖ ^ 2 := by
  change (∑ q, Complex.normSq (v q)) = ‖v‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Complex.normSq_eq_norm_sq]

/-- On the core, coordinate horizontal energies reconstruct the vector chart energy exactly. -/
theorem sum_retractedDeckComponentX_normSq_eq {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) :
    (∑ q, Complex.normSq (retractedDeckComponentX ε F q (x, y))) =
      ‖chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 := by
  calc
    (∑ q, Complex.normSq (retractedDeckComponentX ε F q (x, y))) =
        ∑ q, Complex.normSq
          ((chartDeriv (F : ℍ → DeckSpace N) 1
            (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [retractedDeckComponentX_eq_chartDeriv hε hy F q]
    _ = ‖chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 :=
      sum_normSq_deckCoordinate _

/-- On the core, coordinate vertical energies reconstruct the vector chart energy exactly. -/
theorem sum_retractedDeckComponentY_normSq_eq {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) :
    (∑ q, Complex.normSq (retractedDeckComponentY ε F q (x, y))) =
      ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 := by
  calc
    (∑ q, Complex.normSq (retractedDeckComponentY ε F q (x, y))) =
        ∑ q, Complex.normSq
          ((chartDeriv (F : ℍ → DeckSpace N) Complex.I
            (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) q) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [retractedDeckComponentY_eq_chartDeriv hε hy F q]
    _ = ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 :=
      sum_normSq_deckCoordinate _

/-- The global deck-valued field whose coordinates feed the witness construction. -/
noncomputable def retractedDeckField {N : ℕ} (ε : ℝ) (F : formPreDomain N) :
    ℝ × ℝ → DeckSpace N := fun p =>
  chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p)

@[simp]
theorem retractedDeckField_apply {N : ℕ} (ε : ℝ) (F : formPreDomain N)
    (q : Deck N) (p : ℝ × ℝ) :
    retractedDeckField ε F p q = retractedDeckComponent ε F q p :=
  rfl

/-- The finite-deck vector formed by all coordinate vertical cell means. -/
noncomputable def retractedDeckCellAverage {N : ℕ} (ε c d : ℝ)
    (F : formPreDomain N) (x0 : ℝ) : DeckSpace N :=
  WithLp.toLp 2 (fun q => verticalCellAverage c d (retractedDeckComponent ε F q) x0)

@[simp]
theorem retractedDeckCellAverage_apply {N : ℕ} (ε c d : ℝ)
    (F : formPreDomain N) (x0 : ℝ) (q : Deck N) :
    retractedDeckCellAverage ε c d F x0 q =
      verticalCellAverage c d (retractedDeckComponent ε F q) x0 :=
  by
    change (WithLp.toLp 2
      (fun q => verticalCellAverage c d (retractedDeckComponent ε F q) x0)).ofLp q = _
    rfl

/-- Coordinatewise witness error is exactly the Hilbert error to its assembled deck constant. -/
theorem sum_retractedDeckCell_error_normSq {N : ℕ} (ε c d : ℝ)
    (F : formPreDomain N) (x0 : ℝ) (p : ℝ × ℝ) :
    (∑ q, Complex.normSq
      (retractedDeckComponent ε F q p -
        verticalCellAverage c d (retractedDeckComponent ε F q) x0)) =
      ‖retractedDeckField ε F p - retractedDeckCellAverage ε c d F x0‖ ^ 2 := by
  rw [← sum_normSq_deckCoordinate]
  apply Finset.sum_congr rfl
  intro q _
  change Complex.normSq
      (retractedDeckComponent ε F q p -
        verticalCellAverage c d (retractedDeckComponent ε F q) x0) =
    Complex.normSq
      ((chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p)) q -
        (WithLp.toLp 2
          (fun q => verticalCellAverage c d (retractedDeckComponent ε F q) x0)).ofLp q)
  rfl

/-- A finite deck sum commutes with both integrals of a continuous rectangle energy. -/
theorem sum_rectangle_integral_normSq_eq_integral_sum {N : ℕ}
    {G : Deck N → ℝ × ℝ → ℂ} (hG : ∀ q, Continuous (G q))
    (a b c d : ℝ) :
    (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (G q (x, y))) =
      ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        ∑ q, Complex.normSq (G q (x, y)) := by
  let E : Deck N → ℝ × ℝ → ℝ := fun q p => Complex.normSq (G q p)
  have hE (q : Deck N) : Continuous (E q) :=
    Complex.continuous_normSq.comp (hG q)
  have hEouter (q : Deck N) : Continuous fun y =>
      ∫ x in Set.Ioc a b, E q (x, y) := by
    let H : ℝ → ℝ → ℝ := fun y x => E q (x, y)
    have hH : Continuous (Function.uncurry H) := by
      change Continuous fun p : ℝ × ℝ => E q (p.2, p.1)
      exact (hE q).comp (continuous_snd.prodMk continuous_fst)
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, H y x) :=
      continuous_parametric_integral_of_continuous hH isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, H y x) := by
      simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [H] using hIoc
  calc
    (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (G q (x, y))) =
        ∫ y in Set.Ioc c d, ∑ q, ∫ x in Set.Ioc a b, E q (x, y) := by
          exact (MeasureTheory.integral_finsetSum Finset.univ
            (fun q _ => (hEouter q).integrableOn_Ioc)).symm
    _ = ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        ∑ q, Complex.normSq (G q (x, y)) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          intro y _
          exact (MeasureTheory.integral_finsetSum Finset.univ
            (fun q _ => ((hE q).comp
              (continuous_id.prodMk continuous_const)).integrableOn_Ioc)).symm

/-- Sum of the global retracted horizontal coordinate energies. -/
noncomputable def retractedDeckEnergyX {N : ℕ} (ε : ℝ) (F : formPreDomain N) :
    ℝ × ℝ → ℝ := fun p =>
  ∑ q, Complex.normSq (retractedDeckComponentX ε F q p)

/-- Sum of the global retracted vertical coordinate energies. -/
noncomputable def retractedDeckEnergyY {N : ℕ} (ε : ℝ) (F : formPreDomain N) :
    ℝ × ℝ → ℝ := fun p =>
  ∑ q, Complex.normSq (retractedDeckComponentY ε F q p)

theorem continuous_retractedDeckEnergyX {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) : Continuous (retractedDeckEnergyX ε F) := by
  unfold retractedDeckEnergyX
  exact continuous_finsetSum Finset.univ fun q _ =>
    Complex.continuous_normSq.comp (continuous_retractedDeckComponentX hε F q)

theorem continuous_retractedDeckEnergyY {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) : Continuous (retractedDeckEnergyY ε F) := by
  unfold retractedDeckEnergyY
  exact continuous_finsetSum Finset.univ fun q _ =>
    Complex.continuous_normSq.comp (continuous_retractedDeckComponentY hε F q)

/-- Horizontal coordinate energies are exactly the integral of their global deck sum. -/
theorem sum_retractedDeckComponentX_rectangle_eq_energy {N : ℕ} {ε : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) (a b c d : ℝ) :
    (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (retractedDeckComponentX ε F q (x, y))) =
      ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        retractedDeckEnergyX ε F (x, y) := by
  exact sum_rectangle_integral_normSq_eq_integral_sum
    (fun q => continuous_retractedDeckComponentX hε F q) a b c d

/-- Vertical coordinate energies are exactly the integral of their global deck sum. -/
theorem sum_retractedDeckComponentY_rectangle_eq_energy {N : ℕ} {ε : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) (a b c d : ℝ) :
    (∑ q, ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
      Complex.normSq (retractedDeckComponentY ε F q (x, y))) =
      ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
        retractedDeckEnergyY ε F (x, y) := by
  simpa only [retractedDeckEnergyY] using
    (sum_rectangle_integral_normSq_eq_integral_sum
      (G := fun q p => retractedDeckComponentY ε F q (p.2, p.1))
      (fun q => (continuous_retractedDeckComponentY hε F q).comp
        (continuous_snd.prodMk continuous_fst)) c d a b)

/-- The shared coordinate witness is an actual deck-valued rectangle approximation. -/
theorem exists_retractedDeck_witness_line_vectorized {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (hab : a < b) (hcd : c ≤ d) (F : formPreDomain N) :
    ∃ x0 ∈ Set.Ioc a b,
      (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        ‖retractedDeckField ε F (x, y) - retractedDeckCellAverage ε c d F x0‖ ^ 2) ≤
        8 * (b - a) ^ 2 * (∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
          Complex.normSq (retractedDeckComponentX ε F q (x, y))) +
        2 * (d - c) ^ 2 * (∑ q, ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
          Complex.normSq (retractedDeckComponentY ε F q (x, y))) := by
  obtain ⟨x0, hx0, hbound⟩ :=
    exists_retractedDeck_witness_line hε hab hcd F
  refine ⟨x0, hx0, ?_⟩
  let E : Deck N → ℝ × ℝ → ℝ := fun q p =>
    Complex.normSq (retractedDeckComponent ε F q p -
      verticalCellAverage c d (retractedDeckComponent ε F q) x0)
  have hE (q : Deck N) : Continuous (E q) := by
    exact Complex.continuous_normSq.comp
      ((contDiff_retractedDeckComponent hε F q).continuous.sub continuous_const)
  have hEouter (q : Deck N) : Continuous fun y =>
      ∫ x in Set.Ioc a b, E q (x, y) := by
    let G : ℝ → ℝ → ℝ := fun y x => E q (x, y)
    have hG : Continuous (Function.uncurry G) := by
      change Continuous fun p : ℝ × ℝ => E q (p.2, p.1)
      exact (hE q).comp (continuous_snd.prodMk continuous_fst)
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, G y x) :=
      continuous_parametric_integral_of_continuous hG isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, G y x) := by
      simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [G] using hIoc
  have hEinner (y : ℝ) :
      (∫ x in Set.Ioc a b, ∑ q, E q (x, y)) =
        ∑ q, ∫ x in Set.Ioc a b, E q (x, y) := by
    rw [MeasureTheory.integral_finsetSum]
    intro q _
    exact ((hE q).comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  calc
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      ‖retractedDeckField ε F (x, y) - retractedDeckCellAverage ε c d F x0‖ ^ 2) =
        ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, ∑ q, E q (x, y) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          intro y _
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          intro x _
          exact (sum_retractedDeckCell_error_normSq ε c d F x0 (x, y)).symm
    _ = ∫ y in Set.Ioc c d, ∑ q, ∫ x in Set.Ioc a b, E q (x, y) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          intro y _
          exact hEinner y
    _ = ∑ q, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, E q (x, y) := by
          rw [MeasureTheory.integral_finsetSum]
          intro q _
          exact (hEouter q).integrableOn_Ioc
    _ ≤ _ := hbound

/-- Uniformly summing the shared witness on every cell gives one finite deck-valued
piecewise-constant approximation budget on a product grid. -/
theorem exists_retractedDeck_product_grid_witness {N : ℕ} {ε a c hx hy : ℝ}
    (hε : 0 < ε) (hhx : 0 < hx) (hhy : 0 ≤ hy) (F : formPreDomain N)
    (M K : ℕ) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
        ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
          ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
            ‖retractedDeckField ε F (x, y) - C k j‖ ^ 2) ≤
        8 * hx ^ 2 *
          (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
            ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              retractedDeckEnergyX ε F (x, y)) +
        2 * hy ^ 2 *
          (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
            ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              retractedDeckEnergyY ε F (x, y)) := by
  classical
  have hcellX (j : ℕ) :
      a + (j : ℝ) * hx < a + ((j + 1 : ℕ) : ℝ) * hx := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hcellY (k : ℕ) :
      c + (k : ℝ) * hy ≤ c + ((k + 1 : ℕ) : ℝ) * hy := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hwidthX (j : ℕ) :
      (a + ((j + 1 : ℕ) : ℝ) * hx) - (a + (j : ℝ) * hx) = hx := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hwidthY (k : ℕ) :
      (c + ((k + 1 : ℕ) : ℝ) * hy) - (c + (k : ℝ) * hy) = hy := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hcell (k j : ℕ) : ∃ v : DeckSpace N,
      (∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
        ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
          ‖retractedDeckField ε F (x, y) - v‖ ^ 2) ≤
        8 * hx ^ 2 *
          (∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
            ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
              retractedDeckEnergyX ε F (x, y)) +
        2 * hy ^ 2 *
          (∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
            ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              retractedDeckEnergyY ε F (x, y)) := by
    obtain ⟨x0, hx0, hx0bound⟩ := exists_retractedDeck_witness_line_vectorized hε
      (hcellX j) (hcellY k) F
    refine ⟨retractedDeckCellAverage ε
      (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy) F x0, ?_⟩
    calc
      (∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
        ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
          ‖retractedDeckField ε F (x, y) -
            retractedDeckCellAverage ε
              (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy) F x0‖ ^ 2) ≤
          8 * ((a + ((j + 1 : ℕ) : ℝ) * hx) - (a + (j : ℝ) * hx)) ^ 2 *
            (∑ q, ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                Complex.normSq (retractedDeckComponentX ε F q (x, y))) +
          2 * ((c + ((k + 1 : ℕ) : ℝ) * hy) - (c + (k : ℝ) * hy)) ^ 2 *
            (∑ q, ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
              ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
                Complex.normSq (retractedDeckComponentY ε F q (x, y))) := hx0bound
      _ = 8 * hx ^ 2 *
            (∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ 2 *
            (∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
              ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y)) := by
          rw [hwidthX, hwidthY,
            sum_retractedDeckComponentX_rectangle_eq_energy hε F,
            sum_retractedDeckComponentY_rectangle_eq_energy hε F]
  choose C hC using hcell
  refine ⟨C, ?_⟩
  have hsplit (X Y : ℕ → ℕ → ℝ) :
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
        ((8 * hx ^ 2) * X k j + (2 * hy ^ 2) * Y k j)) =
        (8 * hx ^ 2) * (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M, X k j) +
          (2 * hy ^ 2) * (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M, Y k j) := by
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hXgrid := setIntegral_rectangle_grid_sum
    (continuous_retractedDeckEnergyX hε F) (a := a) (c := c) (hx := hx) (hy := hy)
      (le_of_lt hhx) hhy M K
  have hYgrid :
      (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
        ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
          retractedDeckEnergyY ε F (x, y)) =
        ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range K,
          ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
            ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              retractedDeckEnergyY ε F (x, y) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using
      (setIntegral_rectangle_grid_sum
        ((continuous_retractedDeckEnergyY hε F).comp
          (continuous_snd.prodMk continuous_fst)) (a := c) (c := a) (hx := hy) (hy := hx)
        hhy (le_of_lt hhx) K M)
  calc
    (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
      ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
        ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
          ‖retractedDeckField ε F (x, y) - C k j‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
          ((8 * hx ^ 2) *
            (∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          (2 * hy ^ 2) *
            (∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
              ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro j _
          exact hC k j
    _ = 8 * hx ^ 2 *
          (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
            ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
        2 * hy ^ 2 *
          (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
            ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
              ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y)) := by
          exact hsplit _ _
    _ = 8 * hx ^ 2 *
          (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
            ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              retractedDeckEnergyX ε F (x, y)) +
        2 * hy ^ 2 *
          (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
            ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              retractedDeckEnergyY ε F (x, y)) := by
          rw [← hXgrid]
          rw [Finset.sum_comm]
          rw [← hYgrid]

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
