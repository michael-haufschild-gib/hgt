import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionProjectionHasACanonicalLimit
import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The source kernel pays the Schur cost on the actual cells

The complete mixed source functional is represented by a continuous kernel.
Restricting its square energy to the old logarithmic cells bounds every finite
section projection and its canonical completion. Prime, Gamma and pole terms
are combined before this square is taken. Gaps in the old support remain visible.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- The actual support cells of the independent arithmetic profiles. -/
def arithmeticSectionSupport (N : ℕ) (w : ℝ) : Set ℝ :=
  ⋃ n ∈ Finset.Icc 1 N, Set.Icc (Real.log n) (Real.log n + w)

theorem isCompact_arithmeticSectionSupport (N : ℕ) (w : ℝ) :
    IsCompact (arithmeticSectionSupport N w) :=
  (Finset.Icc 1 N).isCompact_biUnion fun _ _ => isCompact_Icc

/-- Arithmetic sections vanish outside their cells, including all intervening gaps. -/
theorem arithmeticSectionTest_eq_zero_off_support {N : ℕ} {w : ℝ}
    (p : arithmeticSectionTests N w) {u : ℝ}
    (hu : u ∉ arithmeticSectionSupport N w) : p.1.1 u = 0 := by
  obtain ⟨G, _, hs, he⟩ := p.2
  rw [he]
  apply Finset.sum_eq_zero
  intro n hn
  apply hs n
  intro hm
  apply hu
  simp only [arithmeticSectionSupport, Set.mem_iUnion]
  exact ⟨n, hn, ⟨by linarith only [hm.1], by linarith only [hm.2]⟩⟩

/-- Square energy of the combined source kernel on a specified support set. -/
def sourceKernelEnergy (s : Set ℝ) (g : realTests) : ℝ :=
  ∫ u in s, ‖weilSourceKernel g u‖ ^ 2

theorem sourceKernelEnergy_nonneg (s : Set ℝ) (g : realTests) :
    0 ≤ sourceKernelEnergy s g := integral_nonneg fun _ => sq_nonneg _

theorem integrableOn_sourceKernel_sq {s : Set ℝ} (hs : IsCompact s) (g : realTests) :
    IntegrableOn (fun u => ‖weilSourceKernel g u‖ ^ 2) s :=
  ContinuousOn.integrableOn_compact hs ((continuous_weilSourceKernel g).norm.pow 2).continuousOn

/-- Compact support turns the exact mixed source representation into a square-mass bound. -/
theorem realWeilForm_sq_le_mass_mul_sourceKernelEnergy {s : Set ℝ} (hs : IsCompact s)
    (p g : realTests) (hp : ∀ u, u ∉ s → p.1 u = 0) :
    realWeilForm p g ^ 2 ≤ (∫ u, p.1 u ^ 2) * sourceKernelEnergy s g := by
  have hpc : Continuous (fun u => (p.1 u : ℂ)) :=
    (cx_contDiff p.2.1).continuous
  have hkc : Continuous (fun u => (starRingEnd ℂ) (weilSourceKernel g u)) :=
    Complex.continuous_conj.comp (continuous_weilSourceKernel g)
  have hpi : IntegrableOn (fun u => ‖(p.1 u : ℂ)‖ ^ 2) s :=
    ContinuousOn.integrableOn_compact hs (hpc.norm.pow 2).continuousOn
  have hki : IntegrableOn (fun u => ‖(starRingEnd ℂ) (weilSourceKernel g u)‖ ^ 2) s :=
    ContinuousOn.integrableOn_compact hs (hkc.norm.pow 2).continuousOn
  have hcs := HTGeometry.norm_integral_mul_conj_sq_le
    (ν := volume.restrict s) hpc.norm.aestronglyMeasurable hkc.norm.aestronglyMeasurable hpi hki
  simp only [Complex.conj_conj, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at hcs
  have hmix : (∫ u in s, (p.1 u : ℂ) * weilSourceKernel g u) =
      ∫ u, (p.1 u : ℂ) * weilSourceKernel g u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      simp only [hp u hu, Complex.ofReal_zero, zero_mul]
  have hmass : (∫ u in s, p.1 u ^ 2) = ∫ u, p.1 u ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      simp only [hp u hu, zero_pow (by decide : 2 ≠ 0)]
  rw [hmix, hmass] at hcs
  rw [realWeilForm_eq_sourceKernel]
  calc
    _ = |(∫ u, (p.1 u : ℂ) * weilSourceKernel g u).re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖∫ u, (p.1 u : ℂ) * weilSourceKernel g u‖ ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    _ ≤ _ := hcs

/-- Every finite section projection is paid by kernel energy on the exact old cells. -/
theorem arithmeticSectionProjection_energy_le_sourceKernelEnergy
    {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (g : realTests) :
    realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
      (arithmeticSectionProjection hN hw0 hw f g) ≤
      sourceKernelEnergy (arithmeticSectionSupport N w) g := by
  let p := arithmeticSectionProjection hN hw0 hw f g
  have hp : p ∈ arithmeticSectionTests N w := arithmeticSectionProjection_mem hN hw0 hw f g
  have hfloor : (∫ u, p.1 u ^ 2) ≤ realWeilForm p p :=
    integral_sq_le_weilPair_arithmeticSection hN hw0 hw ⟨p, hp⟩
  have hE : 0 ≤ realWeilForm p p := arithmeticSectionProjection_energy_nonneg hN hw0 hw f g
  have hD := sourceKernelEnergy_nonneg (arithmeticSectionSupport N w) g
  have hpair : realWeilForm p g = realWeilForm p p := by
    obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
    have horth := arithmeticSectionProjection_orthogonal hN hw0 hw f c g
    rw [← hc, map_sub] at horth
    exact sub_eq_zero.mp horth
  have hcs := realWeilForm_sq_le_mass_mul_sourceKernelEnergy
    (isCompact_arithmeticSectionSupport N w) p g
    (fun _ hu => arithmeticSectionTest_eq_zero_off_support ⟨p, hp⟩ hu)
  rw [hpair] at hcs
  have hbudget := hcs.trans (mul_le_mul_of_nonneg_right hfloor hD)
  by_cases hz : realWeilForm p p = 0
  · change realWeilForm p p ≤ _
    rw [hz]
    exact hD
  · have hpos := lt_of_le_of_ne hE (Ne.symm hz)
    change realWeilForm p p ≤ _
    by_contra h
    have hbad := mul_pos
      (sub_pos.mpr (lt_of_not_ge h)) hpos
    nlinarith only [hbudget, hbad]

/-- The same explicit source upper bound survives completion of the entire old profile space. -/
theorem sectionCompletionEnergy_le_sourceKernelEnergy
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) (g : realTests) :
    sectionCompletionEnergy hN hw0 hw g ≤
      sourceKernelEnergy (arithmeticSectionSupport N w) g := by
  apply ciSup_le
  intro S
  exact arithmeticSectionProjection_energy_le_sourceKernelEnergy hN hw0 hw (fun p : S => p.1) g

/-- A source-derived lower bound on the signed completed residual, retaining its full diagonal. -/
theorem completedSectionResidualForm_ge_sourceKernelEnergy
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) (g : realTests) :
    realWeilForm g g - sourceKernelEnergy (arithmeticSectionSupport N w) g ≤
      completedSectionResidualForm hN hw0 hw g g := by
  change realWeilForm g g - _ ≤ realWeilForm g g - sectionCompletionPair hN hw0 hw g g
  rw [sectionCompletionPair_self]
  exact sub_le_sub_left (sectionCompletionEnergy_le_sourceKernelEnergy hN hw0 hw g) _

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_energy_le_sourceKernelEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionCompletionEnergy_le_sourceKernelEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionResidualForm_ge_sourceKernelEnergy
