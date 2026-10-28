import GaloisForLFunctions.ArithmeticIndexDescent.TheProjectionCostIsBoundedOnEachWindow
import GaloisForLFunctions.RHTower.CHMDPolarTransfer
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization

/-!
# Arithmetic section energy controls the actual complete source graph

The inverse Doob lift sends compact real C² tests into the complete arithmetic
source graph and preserves their full Weil diagonal. On a fixed source window,
its weighted mass is bounded by ordinary square mass. The global polar rows
then control graph norm by Weil energy plus square mass. The positive arithmetic
section floor absorbs this last term, including for all section differences.
-/

open MeasureTheory Set
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- The literal inverse Doob lift of a compact real C² test. -/
def realTestGraphLift (f : realTests) : SourceGraph := testLift f.1 f.2.1 f.2.2

theorem realTestGraphLift_add (f g : realTests) :
    realTestGraphLift (f + g) = realTestGraphLift f + realTestGraphLift g :=
  testLift_add f.1 g.1 f.2.1 g.2.1 f.2.2 g.2.2

theorem realTestGraphLift_sub (f g : realTests) :
    realTestGraphLift (f - g) = realTestGraphLift f - realTestGraphLift g :=
  testLift_sub f.1 g.1 f.2.1 g.2.1 f.2.2 g.2.2

/-- The graph retains the literal complete Weil pairing, including both poles. -/
theorem weilForm_realTestGraphLift (f : realTests) :
    weilForm (realTestGraphLift f) = realWeilForm f f := by
  rw [realTestGraphLift, testLift, weilForm_compactLift]
  simp only [phiDoobTest_phiDoobInv]
  change (zetaZeroConfig.W (cx f.1) (cx f.1)).re = realWeilForm f f
  rw [zeta_W_eq_weilFullFunctional (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)]
  rfl

private def sourceMassWeight (u : ℝ) : ℝ := Real.cosh (u / 2) / riemannKernelReal u

private theorem sourceMassWeight_pos (u : ℝ) : 0 < sourceMassWeight u :=
  div_pos (Real.cosh_pos _) (riemannKernelReal_pos _)

private theorem continuous_sourceMassWeight : Continuous sourceMassWeight :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).div
    continuous_riemannKernelReal (fun u => (riemannKernelReal_pos u).ne')

private theorem norm_realTestGraphLift_source_sq (f : realTests) :
    ‖(realTestGraphLift f).val.fst‖ ^ 2 =
      ∫ u, f.1 u ^ 2 * sourceMassWeight u := by
  rw [_root_.RHTower.CHMDPolar.norm_sq_eq_integral]
  have he : (∫ u, ((realTestGraphLift f).val.fst u) ^ 2 ∂massMeasure) =
      ∫ u, phiDoobInv f.1 u ^ 2 ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [testLift_source f.1 f.2.1 f.2.2] with u hu
    change ((testLift f.1 f.2.1 f.2.2).val.fst u) ^ 2 = _
    rw [hu]
  rw [he, _root_.RHTower.CHMDPolar.integral_mass]
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp [massDensity, phiDoobInv, sourceMassWeight]
  field_simp [(riemannKernelReal_pos u).ne']

private theorem exists_graphSourceMass_window_bound {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : realTests,
      (∀ u, R < |u| → f.1 u = 0) →
      ‖(realTestGraphLift f).val.fst‖ ^ 2 ≤ K * sectionMass f.1 := by
  obtain ⟨x, _, hx⟩ := (isCompact_Icc (a := -R) (b := R)).exists_isMaxOn
    ⟨0, by constructor <;> linarith only [hR]⟩ continuous_sourceMassWeight.continuousOn
  refine ⟨sourceMassWeight x, sourceMassWeight_pos x, ?_⟩
  intro f hs
  have hcs : HasCompactSupport (fun u => f.1 u ^ 2) :=
    HasCompactSupport.comp_left (f := f.1) (g := fun t : ℝ => t ^ 2) f.2.2 (by simp)
  have hc : Continuous (fun u => f.1 u ^ 2) := f.2.1.continuous.pow 2
  have hi : Integrable (fun u => f.1 u ^ 2) := hc.integrable_of_hasCompactSupport hcs
  have hwcs : HasCompactSupport (fun u => f.1 u ^ 2 * sourceMassWeight u) := hcs.mul_right
  have hwi : Integrable (fun u => f.1 u ^ 2 * sourceMassWeight u) :=
    (hc.mul continuous_sourceMassWeight).integrable_of_hasCompactSupport hwcs
  rw [norm_realTestGraphLift_source_sq]
  calc
    _ ≤ ∫ u, f.1 u ^ 2 * sourceMassWeight x := by
      apply integral_mono hwi (hi.mul_const _)
      intro u
      by_cases hu : u ∈ Icc (-R) R
      · exact mul_le_mul_of_nonneg_left (hx hu) (sq_nonneg _)
      · have hz : f.1 u = 0 := hs u (lt_of_not_ge fun hh => hu (abs_le.mp hh))
        simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, le_refl]
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

/-- On a fixed window, the full source graph norm costs only Weil energy and
a bounded square-mass remainder. No sign of the test's Weil diagonal is assumed. -/
theorem exists_realTestGraphLift_window_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : realTests,
      (∀ u, R < |u| → f.1 u = 0) →
      ‖realTestGraphLift f‖ ^ 2 ≤ realWeilForm f f + C * sectionMass f.1 := by
  obtain ⟨K, hK, hmass⟩ := exists_graphSourceMass_window_bound hR
  let B := 2 * (1 + ‖tanhL‖ ^ 2)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * K, mul_pos hB hK, ?_⟩
  intro f hs
  let p := realTestGraphLift f
  have hn := sourceEnergy_add_two_mass p
  have hw := weilForm_realTestGraphLift f
  change weilForm p = realWeilForm f f at hw
  have ht : ⟪p.val.fst, tanhL⟫_ℝ ^ 2 ≤ ‖p.val.fst‖ ^ 2 * ‖tanhL‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hgraph : ‖p‖ ^ 2 ≤ realWeilForm f f + B * ‖p.val.fst‖ ^ 2 := by
    unfold weilForm at hw
    change ‖p‖ ^ 2 ≤ realWeilForm f f +
      2 * (1 + ‖tanhL‖ ^ 2) * ‖p.val.fst‖ ^ 2
    nlinarith only [hn, hw, ht, sq_nonneg ⟪p.val.fst, oneL⟫_ℝ]
  calc
    _ ≤ realWeilForm f f + B * ‖p.val.fst‖ ^ 2 := hgraph
    _ ≤ realWeilForm f f + B * (K * sectionMass f.1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmass f hs) hB.le)
    _ = _ := by ring

/-- The independently proved arithmetic floor absorbs the graph's mass remainder,
uniformly over the entire old section space and every presentation. -/
theorem exists_arithmeticSection_graphNorm_bound
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : arithmeticSectionTests N w,
      ‖realTestGraphLift p.1‖ ^ 2 ≤ C * realWeilForm p.1 p.1 := by
  have hR : 0 < Real.log N + w := add_pos_of_nonneg_of_pos
    (Real.log_nonneg (by exact_mod_cast hN)) hw0
  obtain ⟨C, hC, hbound⟩ := exists_realTestGraphLift_window_bound hR
  refine ⟨1 + C, by linarith only [hC], ?_⟩
  intro p
  have hg := hbound p.1 (fun u hu => arithmeticSectionTest_eq_zero_of_abs_gt p hu)
  have hm := integral_sq_le_weilPair_arithmeticSection hN hw0 hw p
  change sectionMass p.1.1 ≤ realWeilForm p.1 p.1 at hm
  have hp := mul_le_mul_of_nonneg_left hm hC.le
  nlinarith only [hg, hp]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_realTestGraphLift_window_bound
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_arithmeticSection_graphNorm_bound
