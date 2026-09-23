import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreEnergyBridge
import GaloisForLFunctions.RHTower.EisensteinFundamentalDomainIntegrability

/-!
# Finite-deck core energy controlled by the modular strip

A finite rectangular chart core above the retraction cutoff has its combined
Euclidean coordinate energy bounded by twice the invariant Dirichlet energy
on the modular fundamental domain.  Combining the two coordinate directions
before applying the strip cover preserves the sharp `8 hx²` Poincaré factor
when `hy ≤ 2 hx`.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Complex chart point associated to a real coordinate pair. -/
def coreChartPoint (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- Real rectangular chart region, with `x` first and `y` second. -/
def coreChartRect (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioc a b ×ˢ Set.Ioc c d

theorem measurableSet_coreChartRect (a b c d : ℝ) :
    MeasurableSet (coreChartRect a b c d) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem coreChartRect_pos {a b c d : ℝ} (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ coreChartRect a b c d) : 0 < p.2 := by
  change p.1 ∈ Set.Ioc a b ∧ p.2 ∈ Set.Ioc c d at hp
  exact hc.trans hp.2.1

/-- The literal upper-half-plane point of a positive coordinate pair has the
expected imaginary part. -/
theorem ofComplex_coreChartPoint_im {p : ℝ × ℝ} (hp : 0 < p.2) :
    (ofComplex (coreChartPoint p)).im = p.2 := by
  change ((ofComplex (coreChartPoint p) : ℂ).im) = p.2
  rw [ofComplex_apply_of_im_pos (by simpa [coreChartPoint] using hp)]
  simp [coreChartPoint]

/-- Reconstructing an upper-half-plane point from its real chart coordinates. -/
theorem ofComplex_coreChartPoint_re_im (z : ℍ) :
    ofComplex (coreChartPoint (z.re, z.im)) = z := by
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa [coreChartPoint] using z.im_pos)]
  apply Complex.ext <;> simp [coreChartPoint]

/-- Coordinate rectangle transported into the literal two-cell strip. -/
theorem setOf_coreChartRect_subset_strip {a b c d : ℝ}
    (hx : ∀ x ∈ Set.Ioc a b, |x| ≤ (1 : ℝ) / 2)
    (hy : ∀ y ∈ Set.Ioc c d, 3 ≤ 4 * y ^ (2 : ℕ)) :
    {z : ℍ | (z.re, z.im) ∈ coreChartRect a b c d} ⊆
      SelbergModularStripComparison.strip := by
  intro z hz
  change z.re ∈ Set.Ioc a b ∧ z.im ∈ Set.Ioc c d at hz
  exact ⟨hx z.re hz.1, hy z.im hz.2⟩

/-- Exact coordinate transport for the full literal chart-gradient energy. -/
theorem setIntegral_coreChartRect_chartGradientNormSq_eq {N : ℕ}
    (F : ℍ → DeckSpace N) {a b c d : ℝ} (hc : 0 < c) :
    (∫ p in coreChartRect a b c d,
      chartGradientNormSq F (ofComplex (coreChartPoint p))) =
      ∫ z in {z : ℍ | (z.re, z.im) ∈ coreChartRect a b c d},
        hyperbolicChartGradientDensity F z := by
  calc
    (∫ p in coreChartRect a b c d,
        chartGradientNormSq F (ofComplex (coreChartPoint p))) =
        ∫ p in coreChartRect a b c d,
          hyperbolicChartGradientDensity F (ofComplex (coreChartPoint p)) / p.2 ^ (2 : ℕ) := by
      symm
      apply setIntegral_congr_fun (measurableSet_coreChartRect a b c d)
      intro p hp
      have hp0 : p.2 ≠ 0 := (coreChartRect_pos hc hp).ne'
      change ((ofComplex (coreChartPoint p)).im ^ (2 : ℕ) *
        chartGradientNormSq F (ofComplex (coreChartPoint p))) / p.2 ^ (2 : ℕ) = _
      rw [ofComplex_coreChartPoint_im (coreChartRect_pos hc hp)]
      field_simp
    _ = ∫ z in {z : ℍ | (z.re, z.im) ∈ coreChartRect a b c d},
        hyperbolicChartGradientDensity F
          (ofComplex (coreChartPoint (z.re, z.im))) := by
      exact (RHTower.setIntegral_coord_eq_real (measurableSet_coreChartRect a b c d)
        (fun p hp => coreChartRect_pos hc hp)
        (fun p => hyperbolicChartGradientDensity F (ofComplex (coreChartPoint p)))).symm
    _ = ∫ z in {z : ℍ | (z.re, z.im) ∈ coreChartRect a b c d},
        hyperbolicChartGradientDensity F z := by
      apply setIntegral_congr_fun
        ((measurableSet_coreChartRect a b c d).preimage RHTower.measurable_coordMap)
      intro z _
      change hyperbolicChartGradientDensity F
        (ofComplex (coreChartPoint (z.re, z.im))) = _
      rw [ofComplex_coreChartPoint_re_im]

/-- Both retracted energy densities are integrable on each bounded chart rectangle. -/
theorem integrableOn_retractedDeckEnergyX_coreChartRect {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) :
    IntegrableOn (retractedDeckEnergyX ε F) (coreChartRect a b c d) volume := by
  exact ((continuous_retractedDeckEnergyX hε F).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem integrableOn_retractedDeckEnergyY_coreChartRect {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) :
    IntegrableOn (retractedDeckEnergyY ε F) (coreChartRect a b c d) volume := by
  exact ((continuous_retractedDeckEnergyY hε F).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- Horizontal iterated energy is the real product integral on the core rectangle. -/
theorem setIntegral_coreChartRect_energyX_eq_iterated {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) :
    (∫ p in coreChartRect a b c d, retractedDeckEnergyX ε F p) =
      ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y) := by
  have hprod : Integrable (retractedDeckEnergyX ε F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_retractedDeckEnergyX_coreChartRect hε F
  have h := integral_prod_symm (retractedDeckEnergyX ε F) hprod
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

/-- Vertical iterated energy is the same product integral, in the other Fubini order. -/
theorem setIntegral_coreChartRect_energyY_eq_iterated {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (F : formPreDomain N) :
    (∫ p in coreChartRect a b c d, retractedDeckEnergyY ε F p) =
      ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y) := by
  have hprod : Integrable (retractedDeckEnergyY ε F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_retractedDeckEnergyY_coreChartRect hε F
  have h := integral_prod (retractedDeckEnergyY ε F) hprod
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

/-- Above the retraction cutoff, the two iterated grid energies combine into
one literal chart-gradient integral. -/
theorem coreChartRect_energy_sum_eq_chartGradient {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c) (F : formPreDomain N) :
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
      (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) =
        ∫ p in coreChartRect a b c d,
          chartGradientNormSq (F : ℍ → DeckSpace N) (ofComplex (coreChartPoint p)) := by
  rw [← setIntegral_coreChartRect_energyX_eq_iterated hε F,
    ← setIntegral_coreChartRect_energyY_eq_iterated hε F,
    ← integral_add (integrableOn_retractedDeckEnergyX_coreChartRect hε F)
      (integrableOn_retractedDeckEnergyY_coreChartRect hε F)]
  apply setIntegral_congr_fun (measurableSet_coreChartRect a b c d)
  intro p hp
  have hpc : c < p.2 := by
    change p.1 ∈ Set.Ioc a b ∧ p.2 ∈ Set.Ioc c d at hp
    exact hp.2.1
  have hpε : ε < p.2 := hεc.trans_lt hpc
  simpa only [coreChartPoint] using
    retractedDeckEnergy_sum_eq_chartGradientNormSq hε hpε F

/-- The combined coordinate energy of a bounded core is controlled by the
invariant Dirichlet energy on two modular cells. -/
theorem coreChartRect_energy_sum_le_twice_fd {N : ℕ} {ε a b c d : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c)
    (hx : ∀ x ∈ Set.Ioc a b, |x| ≤ (1 : ℝ) / 2)
    (hy : ∀ y ∈ Set.Ioc c d, 3 ≤ 4 * y ^ (2 : ℕ))
    (F : formPreDomain N) :
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
      (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) ≤
        2 * ∫ z in ModularGroup.fd,
          hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by
  calc
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
        (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) =
        ∫ p in coreChartRect a b c d,
          chartGradientNormSq (F : ℍ → DeckSpace N) (ofComplex (coreChartPoint p)) :=
      coreChartRect_energy_sum_eq_chartGradient hε hc hεc F
    _ = ∫ z in {z : ℍ | (z.re, z.im) ∈ coreChartRect a b c d},
        hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z :=
      setIntegral_coreChartRect_chartGradientNormSq_eq (F : ℍ → DeckSpace N) hc
    _ ≤ ∫ z in SelbergModularStripComparison.strip,
        hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by
      apply setIntegral_mono_set
        (SelbergModularStripComparison.integrable_strip
          (hyperbolicChartGradientDensity_integrable_fd F)
          (fun z => hyperbolicChartGradientDensity_modular F ModularGroup.S z))
      · exact Filter.Eventually.of_forall fun z => by
          rw [hyperbolicChartGradientDensity_eq_hypGradNormSq]
          exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      · exact Filter.Eventually.of_forall (setOf_coreChartRect_subset_strip hx hy)
    _ ≤ 2 * ∫ z in ModularGroup.fd,
        hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z :=
      hyperbolicChartGradientDensity_strip_le_twice F

/-- The anisotropic grid budget collapses to the combined energy when its
vertical mesh is at most twice its horizontal mesh. -/
theorem coreChartRect_grid_energy_budget_le {N : ℕ} {ε a b c d hx hy : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c) (hhx : 0 < hx) (hhy : 0 < hy)
    (hhyx : hy ≤ 2 * hx)
    (hstripx : ∀ x ∈ Set.Ioc a b, |x| ≤ (1 : ℝ) / 2)
    (hstripy : ∀ y ∈ Set.Ioc c d, 3 ≤ 4 * y ^ (2 : ℕ))
    (F : formPreDomain N) :
    8 * hx ^ (2 : ℕ) *
        (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
      2 * hy ^ (2 : ℕ) *
        (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) ≤
      16 * hx ^ (2 : ℕ) * ∫ z in ModularGroup.fd,
        hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by
  have hcoeff : 2 * hy ^ (2 : ℕ) ≤ 8 * hx ^ (2 : ℕ) := by
    have h1 : 0 ≤ 2 * hx - hy := by linarith
    have h2 : 0 ≤ 2 * hx + hy := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hEy0 (p : ℝ × ℝ) : 0 ≤ retractedDeckEnergyY ε F p := by
    unfold retractedDeckEnergyY
    exact Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
  have hIy0 : 0 ≤ ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
      retractedDeckEnergyY ε F (x, y) := by
    apply integral_nonneg
    intro x
    apply integral_nonneg
    intro y
    exact hEy0 (x, y)
  calc
    8 * hx ^ (2 : ℕ) *
          (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
        2 * hy ^ (2 : ℕ) *
          (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) ≤
        8 * hx ^ (2 : ℕ) *
          (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
        8 * hx ^ (2 : ℕ) *
          (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y)) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hIy0) _
    _ = 8 * hx ^ (2 : ℕ) *
          ((∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, retractedDeckEnergyX ε F (x, y)) +
          (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, retractedDeckEnergyY ε F (x, y))) := by
      ring
    _ ≤ 8 * hx ^ (2 : ℕ) *
          (2 * ∫ z in ModularGroup.fd,
            hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z) := by
      exact mul_le_mul_of_nonneg_left
        (coreChartRect_energy_sum_le_twice_fd hε hc hεc hstripx hstripy F)
        (mul_nonneg (by norm_num) (sq_nonneg hx))
    _ = 16 * hx ^ (2 : ℕ) * ∫ z in ModularGroup.fd,
        hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by ring

/-- The finite grid step has a modular-energy error budget on every strip-contained core. -/
theorem exists_grid_fdUpperChartGridCore_hyperbolic_error_le_fd_energy {N : ℕ}
    (M K : ℕ) {ε a c hx hy : ℝ} (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c)
    (hhx : 0 < hx) (hhy : 0 < hy) (hhyx : hy ≤ 2 * hx)
    (hstripx : ∀ x ∈ Set.Ioc a (a + (M : ℝ) * hx), |x| ≤ (1 : ℝ) / 2)
    (hstripy : ∀ y ∈ Set.Ioc c (c + (K : ℝ) * hy), 3 ≤ 4 * y ^ (2 : ℕ))
    (F : formPreDomain N) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy,
        ‖(F : ℍ → DeckSpace N) z -
            ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
              ℍ → DeckSpace N) z‖ ^ (2 : ℕ) ≤
        (c ^ (2 : ℕ))⁻¹ *
          (16 * hx ^ (2 : ℕ) * ∫ z in ModularGroup.fd,
            hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z) := by
  obtain ⟨C, hC⟩ := exists_grid_fdUpperChartGridCore_hyperbolic_error_le
    hε hc hεc hhx hhy F M K
  refine ⟨C, hC.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (coreChartRect_grid_energy_budget_le hε hc hεc hhx hhy hhyx hstripx hstripy F)
    (inv_nonneg.mpr (sq_nonneg c))

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
