import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreWitness
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart
import GaloisForLFunctions.RHTower.MaassFiniteDeckRellichCore

/-!
# Hyperbolic error bounds on finite-deck core cells

The core grid witness is Euclidean.  This file supplies its missing conversion
to the hyperbolic invariant measure on cells bounded away from height zero.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The full finite-deck field remains `C¹` after the positive-height
retraction, so squared grid errors are integrable on compact rectangles. -/
theorem contDiff_retractedDeckField {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) : ContDiff ℝ 1 (retractedDeckField ε F) := by
  change ContDiff ℝ 1 (fun p => chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p))
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  exact ((formPreDomain.c1 F).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds (retractedPoint_im_pos hε p))).comp p
      ((contDiff_retractedPoint ε).of_le (by simp)).contDiffAt

/-- Continuity of the retracted deck field. -/
theorem continuous_retractedDeckField {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) : Continuous (retractedDeckField ε F) :=
  (contDiff_retractedDeckField hε F).continuous

/-- Above the retraction cutoff, the retracted deck field is the original
upper-half-plane field in its literal coordinates. -/
theorem retractedDeckField_eq_of_height {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : formPreDomain N) (z : ℍ) (hz : ε ≤ z.im) :
    retractedDeckField ε F (z.re, z.im) = (F : ℍ → DeckSpace N) z := by
  unfold retractedDeckField
  rw [retractedPoint_eq_of_le hε hz]
  rw [show (z.re : ℂ) + (z.im : ℂ) * Complex.I = (z : ℂ) by
    simpa using (Complex.re_add_im (z : ℂ))]
  simp only [chartFun, Function.comp_apply, ofComplex_apply]

/-- On every grid cell above a retraction cutoff, the original field is its
retracted coordinate representative. -/
theorem form_eq_retractedDeckField_on_upperChartGridCell {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) (hhy : 0 ≤ hy)
    (F : formPreDomain N) (i : Fin K × Fin M) {z : ℍ}
    (hz : z ∈ upperChartGridCell a c hx hy i) :
    (F : ℍ → DeckSpace N) z = retractedDeckField ε F (z.re, z.im) := by
  change z.re ∈ Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx) ∧
    z.im ∈ Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy) at hz
  have hk : 0 ≤ (i.1 : ℝ) * hy := mul_nonneg (Nat.cast_nonneg _) hhy
  have hcy : c ≤ z.im := by
    linarith [hz.2.1]
  exact (retractedDeckField_eq_of_height hε F z (hεc.trans hcy)).symm

/-- On a grid cell, the finite `Lp` step has the assigned value almost
everywhere, hence its squared retracted error is the literal cell error. -/
theorem ae_retractedDeckField_sub_deckGridStep_eq_cell {N M K : ℕ}
    {ε a c hx hy : ℝ} (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) (i : Fin K × Fin M) :
    ∀ᵐ z ∂cellMeasure, z ∈ upperChartGridCell a c hx hy i →
      ‖retractedDeckField ε F (z.re, z.im) -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2 =
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by
  filter_upwards [deckGridStep_ae_eq_cell_value hhx hhy C i] with z hstep
  intro hz
  rw [hstep hz]

/-- On a positive core cell, the original field's error against the finite
grid step is the Euclidean witness error almost everywhere. -/
theorem ae_form_sub_deckGridStep_eq_cell {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) (i : Fin K × Fin M) :
    ∀ᵐ z ∂cellMeasure, z ∈ upperChartGridCell a c hx hy i →
      ‖(F : ℍ → DeckSpace N) z -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2 =
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by
  filter_upwards [ae_retractedDeckField_sub_deckGridStep_eq_cell hhx hhy F C i] with z hstep
  intro hz
  rw [form_eq_retractedDeckField_on_upperChartGridCell hε hεc hhy.le F i hz]
  exact hstep hz

/-- Union of the finitely many upper-chart grid cells. -/
def upperChartGridCore {M K : ℕ} (a c hx hy : ℝ) : Set ℍ :=
  ⋃ i : Fin K × Fin M, upperChartGridCell a c hx hy i

/-- The fundamental domain expressed in literal real chart coordinates.

Keeping this region in the coordinate plane is essential: the grid witness is
Euclidean, while the `DeckL2` representative is only defined modulo the
measure restricted to the fundamental domain. -/
def fundamentalChartRegion : Set (ℝ × ℝ) :=
  {p | 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ |p.1| ≤ (1 : ℝ) / 2}

/-- The fundamental chart region is measurable. -/
theorem measurableSet_fundamentalChartRegion : MeasurableSet fundamentalChartRegion := by
  change MeasurableSet {p : ℝ × ℝ | 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧
    |p.1| ≤ (1 : ℝ) / 2}
  exact
    (measurableSet_le measurable_const
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable).inter
    (measurableSet_le continuous_fst.abs.measurable measurable_const)

/-- Membership in the modular fundamental domain is exactly membership in its
real-chart description. -/
theorem mem_fd_iff_mem_fundamentalChartRegion (z : ℍ) :
    z ∈ ModularGroup.fd ↔ (z.re, z.im) ∈ fundamentalChartRegion := by
  change (1 ≤ Complex.normSq (z : ℂ) ∧ |z.re| ≤ (1 : ℝ) / 2) ↔
    (1 ≤ z.re ^ 2 + z.im ^ 2 ∧ |z.re| ≤ (1 : ℝ) / 2)
  rw [Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two]

/-- The literal rectangle in real coordinates underlying an upper-chart grid
cell. -/
def upperChartGridRect {M K : ℕ} (a c hx hy : ℝ) (i : Fin K × Fin M) :
    Set (ℝ × ℝ) :=
  Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx) ×ˢ
    Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy)

/-- A grid cell is precisely the upper-half-plane preimage of its coordinate
rectangle. -/
theorem upperChartGridCell_eq_setOf_mem_rect {M K : ℕ} (a c hx hy : ℝ)
    (i : Fin K × Fin M) :
    upperChartGridCell a c hx hy i =
      {z : ℍ | (z.re, z.im) ∈ upperChartGridRect a c hx hy i} := rfl

/-- The cell-value identity for the `DeckL2` grid representative, transported
from `volume.restrict fd` to ambient volume on the only set where it is used. -/
theorem ae_form_sub_deckGridStep_eq_cell_on_fd_inter {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) (i : Fin K × Fin M) :
    ∀ᵐ z ∂volume, z ∈ ModularGroup.fd ∩ upperChartGridCell a c hx hy i →
      ‖(F : ℍ → DeckSpace N) z -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2 =
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by
  have h := ae_form_sub_deckGridStep_eq_cell
    (a := a) (c := c) (hx := hx) (hy := hy) hε hεc hhx hhy F C i
  change ∀ᵐ z ∂volume.restrict ModularGroup.fd,
    z ∈ upperChartGridCell a c hx hy i → _ at h
  rw [ae_restrict_iff' ModularGroup.isClosed_fd.measurableSet] at h
  filter_upwards [h] with z hz
  intro hzfd
  exact hz hzfd.1 hzfd.2

/-- A squared error against any fixed deck vector is integrable on every
finite retracted coordinate rectangle. -/
theorem integrableOn_retractedDeckField_error {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) (v : DeckSpace N) :
    IntegrableOn (fun p => ‖retractedDeckField ε F p - v‖ ^ 2)
      (Set.Ioc a b ×ˢ Set.Ioc c d) := by
  have hcont : Continuous (fun p => ‖retractedDeckField ε F p - v‖ ^ 2) :=
    ((continuous_retractedDeckField hε F).sub continuous_const).norm.pow 2
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  apply (hcont.continuousOn.integrableOn_compact hcompact).mono_set
  rintro p ⟨hp1, hp2⟩
  exact ⟨⟨hp1.1.le, hp1.2⟩, ⟨hp2.1.le, hp2.2⟩⟩

/-- The same squared error is integrable after hyperbolic coordinate
weighting on every rectangle whose lower height is positive. -/
theorem integrableOn_retractedDeckField_error_div_sq {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (F : formPreDomain N) (v : DeckSpace N) :
    IntegrableOn (fun p => ‖retractedDeckField ε F p - v‖ ^ 2 / p.2 ^ 2)
      (Set.Ioc a b ×ˢ Set.Ioc c d) := by
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  let A : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.Ioc c d
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hA : MeasurableSet A := measurableSet_Ioc.prod measurableSet_Ioc
  have hAK : A ⊆ K := by
    rintro p ⟨hp1, hp2⟩
    exact ⟨⟨hp1.1.le, hp1.2⟩, ⟨hp2.1.le, hp2.2⟩⟩
  have hweight : ContinuousOn (fun p : ℝ × ℝ => (p.2 ^ 2)⁻¹) K := by
    apply (continuous_snd.pow 2).continuousOn.inv₀
    rintro p ⟨_, hp2⟩
    exact pow_ne_zero 2 (ne_of_gt (hc.trans_le hp2.1))
  have herror : IntegrableOn (fun p => ‖retractedDeckField ε F p - v‖ ^ 2) A :=
    integrableOn_retractedDeckField_error hε F v
  simpa only [A, div_eq_mul_inv, mul_comm] using
    herror.continuousOn_mul_of_subset hweight hK hA hAK

/-- Fubini in the ordering used by the finite product-grid witness. -/
theorem setIntegral_prod_eq_iterated {a b c d : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioc a b ×ˢ Set.Ioc c d)) :
    (∫ p in Set.Ioc a b ×ˢ Set.Ioc c d, f p) =
      ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, f (x, y) := by
  rw [Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hf
  simp only [← Measure.prod_restrict, IntegrableOn] at hf ⊢
  exact integral_prod_symm f hf

/-- On a measurable coordinate set at height at least `c > 0`, the hyperbolic
weight `y⁻²` costs at most `c⁻²` in a nonnegative integrable error integral. -/
theorem setIntegral_div_sq_le_of_height {A : Set (ℝ × ℝ)} {c : ℝ}
    {f : ℝ × ℝ → ℝ} (hA : MeasurableSet A) (hc : 0 < c)
    (hheight : ∀ p ∈ A, c ≤ p.2) (hf0 : ∀ p ∈ A, 0 ≤ f p)
    (hf : IntegrableOn f A) (hweighted : IntegrableOn (fun p => f p / p.2 ^ 2) A) :
    ∫ p in A, f p / p.2 ^ 2 ≤ (c ^ 2)⁻¹ * ∫ p in A, f p := by
  have hconst : IntegrableOn (fun p => (c ^ 2)⁻¹ * f p) A := by
    change Integrable (fun p => (c ^ 2)⁻¹ * f p) (volume.restrict A)
    exact hf.const_mul ((c ^ 2)⁻¹)
  calc
    ∫ p in A, f p / p.2 ^ 2 ≤ ∫ p in A, (c ^ 2)⁻¹ * f p := by
      apply setIntegral_mono_on hweighted hconst hA
      intro p hp
      have hypos : 0 < p.2 := hc.trans_le (hheight p hp)
      have hsquares : c ^ 2 ≤ p.2 ^ 2 := by
        exact pow_le_pow_left₀ hc.le (hheight p hp) 2
      have hinv : (p.2 ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ :=
        (inv_le_inv₀ (sq_pos_of_pos hypos) (sq_pos_of_pos hc)).2 hsquares
      calc
        f p / p.2 ^ 2 = (p.2 ^ 2)⁻¹ * f p := by
          rw [div_eq_mul_inv, mul_comm]
        _ ≤ (c ^ 2)⁻¹ * f p := mul_le_mul_of_nonneg_right hinv (hf0 p hp)
    _ = (c ^ 2)⁻¹ * ∫ p in A, f p := by
      rw [integral_const_mul]

/-- Coordinate transport followed by the bounded-height estimate.  This is the
hyperbolic-to-Euclidean error conversion used on every compact core cell. -/
theorem setIntegral_coord_le_of_height {A : Set (ℝ × ℝ)} {c : ℝ}
    {f : ℝ × ℝ → ℝ} (hA : MeasurableSet A) (hc : 0 < c)
    (hheight : ∀ p ∈ A, c ≤ p.2) (hf0 : ∀ p ∈ A, 0 ≤ f p)
    (hf : IntegrableOn f A) (hweighted : IntegrableOn (fun p => f p / p.2 ^ 2) A) :
    ∫ z in {z : ℍ | (z.re, z.im) ∈ A}, f (z.re, z.im) ≤
      (c ^ 2)⁻¹ * ∫ p in A, f p := by
  rw [RHTower.setIntegral_coord_eq_real hA (fun p hp => hc.trans_le (hheight p hp)) f]
  exact setIntegral_div_sq_le_of_height hA hc hheight hf0 hf hweighted

/-- Hyperbolic squared error of the retracted finite-deck field on one
positive coordinate rectangle is controlled by its Euclidean squared error. -/
theorem setIntegral_retractedDeckField_error_le_of_rect {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (F : formPreDomain N) (v : DeckSpace N) :
    ∫ z in {z : ℍ | (z.re, z.im) ∈ Set.Ioc a b ×ˢ Set.Ioc c d},
        ‖retractedDeckField ε F (z.re, z.im) - v‖ ^ 2 ≤
      (c ^ 2)⁻¹ * ∫ p in Set.Ioc a b ×ˢ Set.Ioc c d,
        ‖retractedDeckField ε F p - v‖ ^ 2 := by
  refine setIntegral_coord_le_of_height
    (A := Set.Ioc a b ×ˢ Set.Ioc c d) (c := c)
    (f := fun p => ‖retractedDeckField ε F p - v‖ ^ 2)
    (measurableSet_Ioc.prod measurableSet_Ioc) hc ?_ ?_ ?_ ?_
  · rintro p ⟨_, hp2⟩
    exact hp2.1.le
  · intro p _
    exact sq_nonneg _
  · exact integrableOn_retractedDeckField_error hε F v
  · exact integrableOn_retractedDeckField_error_div_sq hε hc F v

/-- One positive upper-chart grid cell has hyperbolic squared error at most
`c⁻²` times its Euclidean iterated error. -/
theorem upperChartGridCell_retractedDeckField_error_le {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hc : 0 < c) (hhy : 0 ≤ hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) (i : Fin K × Fin M) :
    ∫ z in upperChartGridCell a c hx hy i,
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 ≤
      (c ^ 2)⁻¹ *
        ∫ y in Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy),
          ∫ x in Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx),
            ‖retractedDeckField ε F (x, y) - C i.1 i.2‖ ^ 2 := by
  let x0 : ℝ := a + (i.2 : ℝ) * hx
  let x1 : ℝ := a + ((i.2 : ℕ) + 1 : ℝ) * hx
  let y0 : ℝ := c + (i.1 : ℝ) * hy
  let y1 : ℝ := c + ((i.1 : ℕ) + 1 : ℝ) * hy
  let A : Set (ℝ × ℝ) := Set.Ioc x0 x1 ×ˢ Set.Ioc y0 y1
  have hcy0 : 0 < y0 := by
    dsimp only [y0]
    have hk : 0 ≤ (i.1 : ℝ) * hy := mul_nonneg (Nat.cast_nonneg _) hhy
    linarith
  have hheight (p : ℝ × ℝ) (hp : p ∈ A) : c ≤ p.2 := by
    have hk : 0 ≤ (i.1 : ℝ) * hy := mul_nonneg (Nat.cast_nonneg _) hhy
    have hp2 : y0 < p.2 := hp.2.1
    dsimp only [y0] at hp2
    linarith
  have herror : IntegrableOn (fun p => ‖retractedDeckField ε F p - C i.1 i.2‖ ^ 2) A := by
    simpa only [A] using
      (integrableOn_retractedDeckField_error (a := x0) (b := x1) (c := y0) (d := y1)
        hε F (C i.1 i.2))
  have hweighted : IntegrableOn
      (fun p => ‖retractedDeckField ε F p - C i.1 i.2‖ ^ 2 / p.2 ^ 2) A := by
    simpa only [A] using
      (integrableOn_retractedDeckField_error_div_sq (a := x0) (b := x1) (c := y0) (d := y1)
        hε hcy0 F (C i.1 i.2))
  have hcell := setIntegral_coord_le_of_height (A := A) (c := c)
    (f := fun p => ‖retractedDeckField ε F p - C i.1 i.2‖ ^ 2)
    (by simpa only [A] using (measurableSet_Ioc.prod measurableSet_Ioc)) hc hheight
    (fun _ _ => sq_nonneg _) herror hweighted
  rw [setIntegral_prod_eq_iterated herror] at hcell
  change
    ∫ z in {z : ℍ | (z.re, z.im) ∈
      Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx) ×ˢ
        Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy)},
      ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 ≤ _
  simpa only [A, x0, x1, y0, y1] using hcell

/-- On the fundamental-domain portion of a positive grid cell, the actual
`DeckL2` grid error is bounded by the retracted error on the whole chart cell.
This is the measure-correct bridge from a finite `Lp` approximant to the
Euclidean grid witness. -/
theorem setIntegral_fd_inter_upperChartGridCell_form_sub_deckGridStep_le {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c)
    (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) (i : Fin K × Fin M) :
    ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
      ‖(F : ℍ → DeckSpace N) z -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2 ≤
      ∫ z in upperChartGridCell a c hx hy i,
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by
  let R : Set (ℝ × ℝ) := upperChartGridRect a c hx hy i
  let A : Set (ℝ × ℝ) := fundamentalChartRegion ∩ R
  let E : ℝ × ℝ → ℝ := fun p => ‖retractedDeckField ε F p - C i.1 i.2‖ ^ 2
  have hR : MeasurableSet R := by
    dsimp only [R, upperChartGridRect]
    exact measurableSet_Ioc.prod measurableSet_Ioc
  have hA : MeasurableSet A := measurableSet_fundamentalChartRegion.inter hR
  have hheightR (p : ℝ × ℝ) (hp : p ∈ R) : c ≤ p.2 := by
    change p.1 ∈ Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx) ∧
      p.2 ∈ Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy) at hp
    have hk : 0 ≤ (i.1 : ℝ) * hy := mul_nonneg (Nat.cast_nonneg _) hhy.le
    linarith [hp.2.1]
  have hheightA (p : ℝ × ℝ) (hp : p ∈ A) : c ≤ p.2 :=
    hheightR p hp.2
  have hcy0 : 0 < c + (i.1 : ℝ) * hy := by
    have hk : 0 ≤ (i.1 : ℝ) * hy := mul_nonneg (Nat.cast_nonneg _) hhy.le
    linarith
  have hweighted : IntegrableOn (fun p => E p / p.2 ^ 2) R := by
    dsimp only [E, R, upperChartGridRect]
    exact integrableOn_retractedDeckField_error_div_sq
      (a := a + (i.2 : ℝ) * hx) (b := a + ((i.2 : ℕ) + 1 : ℝ) * hx)
      (c := c + (i.1 : ℝ) * hy) (d := c + ((i.1 : ℕ) + 1 : ℝ) * hy)
      hε hcy0 F (C i.1 i.2)
  have hmono : (∫ p in A, E p / p.2 ^ 2) ≤ ∫ p in R, E p / p.2 ^ 2 := by
    apply setIntegral_mono_set hweighted
    · exact Eventually.of_forall fun p => div_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact Eventually.of_forall fun _ hp => hp.2
  have hset : ModularGroup.fd ∩ upperChartGridCell a c hx hy i =
      {z : ℍ | (z.re, z.im) ∈ A} := by
    rw [upperChartGridCell_eq_setOf_mem_rect]
    ext z
    simp only [mem_inter_iff, mem_setOf_eq, mem_fd_iff_mem_fundamentalChartRegion]
    rfl
  have hfdcell : MeasurableSet (ModularGroup.fd ∩ upperChartGridCell a c hx hy i) :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (measurableSet_upperChartGridCell a c hx hy i)
  calc
    ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
        ‖(F : ℍ → DeckSpace N) z -
            ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
              ℍ → DeckSpace N) z‖ ^ 2 =
        ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i, E (z.re, z.im) := by
          apply setIntegral_congr_ae hfdcell
          simpa only [E] using
            ae_form_sub_deckGridStep_eq_cell_on_fd_inter hε hεc hhx hhy F C i
    _ = ∫ z in {z : ℍ | (z.re, z.im) ∈ A}, E (z.re, z.im) := by rw [hset]
    _ = ∫ p in A, E p / p.2 ^ 2 :=
      RHTower.setIntegral_coord_eq_real hA (fun p hp => hc.trans_le (hheightA p hp)) E
    _ ≤ ∫ p in R, E p / p.2 ^ 2 := hmono
    _ = ∫ z in {z : ℍ | (z.re, z.im) ∈ R}, E (z.re, z.im) :=
      (RHTower.setIntegral_coord_eq_real hR
        (fun p hp => hc.trans_le (hheightR p hp)) E).symm
    _ = ∫ z in upperChartGridCell a c hx hy i, E (z.re, z.im) := by
      rw [upperChartGridCell_eq_setOf_mem_rect]
    _ = ∫ z in upperChartGridCell a c hx hy i,
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by rfl

/-- Summing the one-cell transport bound over a finite product grid gives the
hyperbolic core error budget before the Euclidean Poincaré estimate is used. -/
theorem sum_upperChartGridCell_retractedDeckField_error_le {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hc : 0 < c) (hhy : 0 ≤ hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) :
    (∑ i : Fin K × Fin M,
      ∫ z in upperChartGridCell a c hx hy i,
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2) ≤
      ∑ i : Fin K × Fin M,
        (c ^ 2)⁻¹ *
          ∫ y in Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy),
            ∫ x in Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx),
              ‖retractedDeckField ε F (x, y) - C i.1 i.2‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  exact upperChartGridCell_retractedDeckField_error_le hε hc hhy F C i

/-- The finite `DeckL2` grid approximation has no larger error on the
fundamental-domain pieces than the whole-cell retracted witness. -/
theorem sum_fd_inter_upperChartGridCell_form_sub_deckGridStep_le {N M K : ℕ}
    {ε a c hx hy : ℝ} (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c)
    (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) :
    (∑ i : Fin K × Fin M,
      ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
        ‖(F : ℍ → DeckSpace N) z -
            ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
              ℍ → DeckSpace N) z‖ ^ 2) ≤
      ∑ i : Fin K × Fin M,
        ∫ z in upperChartGridCell a c hx hy i,
          ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  exact setIntegral_fd_inter_upperChartGridCell_form_sub_deckGridStep_le
    hε hc hεc hhx hhy F C i

/-- Reindex a finite product sum into the range form used by the grid witness. -/
theorem sum_fin_product_mul_eq {K M : ℕ} (r : ℝ) (E : ℕ → ℕ → ℝ) :
    (∑ i : Fin K × Fin M, r * E i.1 i.2) =
      r * (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M, E k j) := by
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ j : Fin M, r * E k j) K]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_eq_sum_range (fun j => r * E k j) M]
  rw [Finset.mul_sum]

/-- The finite Euclidean grid witness gives a hyperbolic bounded-core error
budget, before chart derivative energy is transferred to the modular strip. -/
theorem exists_grid_hyperbolic_error_le {N : ℕ} {ε a c hx hy : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hhx : 0 < hx) (hhy : 0 ≤ hy)
    (F : formPreDomain N) (M K : ℕ) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      (∑ i : Fin K × Fin M,
        ∫ z in upperChartGridCell a c hx hy i,
          ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2) ≤
        (c ^ 2)⁻¹ *
          (8 * hx ^ 2 *
            (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ 2 *
            (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) := by
  obtain ⟨C, hC⟩ := exists_retractedDeck_product_grid_witness hε hhx hhy F M K
  refine ⟨C, ?_⟩
  calc
    (∑ i : Fin K × Fin M,
      ∫ z in upperChartGridCell a c hx hy i,
        ‖retractedDeckField ε F (z.re, z.im) - C i.1 i.2‖ ^ 2) ≤
        ∑ i : Fin K × Fin M,
          (c ^ 2)⁻¹ *
            ∫ y in Set.Ioc (c + (i.1 : ℝ) * hy) (c + ((i.1 : ℕ) + 1 : ℝ) * hy),
              ∫ x in Set.Ioc (a + (i.2 : ℝ) * hx) (a + ((i.2 : ℕ) + 1 : ℝ) * hx),
                ‖retractedDeckField ε F (x, y) - C i.1 i.2‖ ^ 2 :=
      sum_upperChartGridCell_retractedDeckField_error_le hε hc hhy F C
    _ = (c ^ 2)⁻¹ *
          (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
            ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
              ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                ‖retractedDeckField ε F (x, y) - C k j‖ ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (sum_fin_product_mul_eq (K := K) (M := M) (c ^ 2)⁻¹ (fun k j =>
              ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
                ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx),
                  ‖retractedDeckField ε F (x, y) - C k j‖ ^ 2))
    _ ≤ (c ^ 2)⁻¹ *
          (8 * hx ^ 2 *
            (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ 2 *
            (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) :=
      mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr (sq_nonneg c))

/-- The Euclidean grid witness yields a finite-dimensional `DeckL2`
approximation on the actual fundamental-domain core. -/
theorem exists_grid_fd_hyperbolic_error_le {N : ℕ} {ε a c hx hy : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c) (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (M K : ℕ) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      (∑ i : Fin K × Fin M,
        ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
          ‖(F : ℍ → DeckSpace N) z -
              ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
                ℍ → DeckSpace N) z‖ ^ 2) ≤
        (c ^ 2)⁻¹ *
          (8 * hx ^ 2 *
            (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ 2 *
            (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) := by
  obtain ⟨C, hC⟩ := exists_grid_hyperbolic_error_le hε hc hhx hhy.le F M K
  refine ⟨C, ?_⟩
  exact (sum_fd_inter_upperChartGridCell_form_sub_deckGridStep_le
    hε hc hεc hhx hhy F C).trans hC

/-- The actual finite-deck grid core: each Euclidean chart cell is intersected
with the fundamental domain before taking the finite union. -/
def fdUpperChartGridCore {M K : ℕ} (a c hx hy : ℝ) : Set ℍ :=
  ⋃ i : Fin K × Fin M, ModularGroup.fd ∩ upperChartGridCell a c hx hy i

/-- Intersecting the grid union with the fundamental domain is the same as
intersecting every finite grid cell first. -/
theorem fdUpperChartGridCore_eq_fd_inter_upperChartGridCore {M K : ℕ}
    (a c hx hy : ℝ) :
    fdUpperChartGridCore (M := M) (K := K) a c hx hy =
      ModularGroup.fd ∩ upperChartGridCore (M := M) (K := K) a c hx hy := by
  ext z
  simp only [fdUpperChartGridCore, upperChartGridCore, mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, hzfd, hzcell⟩
    exact ⟨hzfd, i, hzcell⟩
  · rintro ⟨hzfd, i, hzcell⟩
    exact ⟨i, hzfd, hzcell⟩

/-- The error integral on the actual finite-deck grid core is exactly its
finite cell sum. -/
theorem setIntegral_fdUpperChartGridCore_form_sub_deckGridStep_eq {N M K : ℕ}
    {a c hx hy : ℝ} (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (C : ℕ → ℕ → DeckSpace N) :
    ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy,
      ‖(F : ℍ → DeckSpace N) z -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2 =
      ∑ i : Fin K × Fin M,
        ∫ z in ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
          ‖(F : ℍ → DeckSpace N) z -
              ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
                ℍ → DeckSpace N) z‖ ^ 2 := by
  have hmem : MemLp (fun z => (F : ℍ → DeckSpace N) z -
      ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
        ℍ → DeckSpace N) z) 2 cellMeasure :=
    (formPreDomain.memLp F).sub (Lp.memLp _)
  have hsq : Integrable (fun z => ‖(F : ℍ → DeckSpace N) z -
      ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
        ℍ → DeckSpace N) z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hsqfd : IntegrableOn (fun z => ‖(F : ℍ → DeckSpace N) z -
      ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
        ℍ → DeckSpace N) z‖ ^ 2) ModularGroup.fd := by
    exact hsq
  change (∫ z in ⋃ i : Fin K × Fin M,
      ModularGroup.fd ∩ upperChartGridCell a c hx hy i,
      ‖(F : ℍ → DeckSpace N) z -
          ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
            ℍ → DeckSpace N) z‖ ^ 2) = _
  exact integral_iUnion_fintype
    (fun i => ModularGroup.isClosed_fd.measurableSet.inter
      (measurableSet_upperChartGridCell a c hx hy i))
    (fun i j hij => by
      change Disjoint (ModularGroup.fd ∩ upperChartGridCell a c hx hy i)
        (ModularGroup.fd ∩ upperChartGridCell a c hx hy j)
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact (Set.disjoint_left.mp (disjoint_upperChartGridCell hhx hhy hij)) hzi.2 hzj.2)
    (fun _ => hsqfd.mono_set Set.inter_subset_left)

/-- A finite-dimensional grid step approximates the full fundamental-domain
grid core with the Euclidean Poincaré error budget. -/
theorem exists_grid_fdUpperChartGridCore_hyperbolic_error_le {N : ℕ} {ε a c hx hy : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c) (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (M K : ℕ) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy,
        ‖(F : ℍ → DeckSpace N) z -
            ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
              ℍ → DeckSpace N) z‖ ^ 2 ≤
        (c ^ 2)⁻¹ *
          (8 * hx ^ 2 *
            (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ 2 *
            (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) := by
  obtain ⟨C, hC⟩ := exists_grid_fd_hyperbolic_error_le hε hc hεc hhx hhy F M K
  refine ⟨C, ?_⟩
  rw [setIntegral_fdUpperChartGridCore_form_sub_deckGridStep_eq hhx hhy F C]
  exact hC

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
