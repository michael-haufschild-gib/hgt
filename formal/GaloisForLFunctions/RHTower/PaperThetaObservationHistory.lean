import GaloisForLFunctions.RHTower.PaperThetaObservationContrast
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Bounded information along predeclared theta observation histories

The first `n` observations form a literal finite history. Its reflected KL
information increases with refinement and converges to a source-bounded limit.
That one limit controls every finite-history reflection gap.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The first `n` outcomes of a predeclared sequence of finite observations. -/
def paperThetaHistoryObservation (f : ℕ → SimpleFunc ℝ α) (n : ℕ) :
    SimpleFunc ℝ (Fin n → α) where
  toFun x i := f i.val x
  measurableSet_fiber' w := by
    have hs : (fun x : ℝ => fun i : Fin n => f i.val x) ⁻¹' {w} =
        ⋂ i : Fin n, (f i.val) ⁻¹' {w i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, funext_iff]
    rw [hs]
    exact MeasurableSet.iInter fun i => (f i.val).measurableSet_fiber (w i)
  finite_range' := Set.toFinite _

/-- Forget the final recorded observation. -/
def paperThetaHistoryPrefix (n : ℕ) (w : Fin (n + 1) → α) : Fin n → α :=
  fun i => w i.castSucc

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem paperThetaHistoryObservation_prefix (f : ℕ → SimpleFunc ℝ α) (n : ℕ) :
    (paperThetaHistoryObservation f (n + 1)).map (paperThetaHistoryPrefix n) =
      paperThetaHistoryObservation f n := by
  apply SimpleFunc.ext
  intro x
  rfl

def paperThetaHistoryInformation (a : PaperThetaTilt) (f : ℕ → SimpleFunc ℝ α) (n : ℕ) : ℝ :=
  (paperThetaObservationLaw a (paperThetaHistoryObservation f n)).kl
    (paperThetaObservationLaw (paperThetaTiltReflection a) (paperThetaHistoryObservation f n))

theorem paperThetaHistoryInformation_nonneg (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) (n : ℕ) : 0 ≤ paperThetaHistoryInformation a f n :=
  Law.kl_nonneg (paperThetaObservationLaw_dominated a (paperThetaHistoryObservation f n))

theorem paperThetaHistoryInformation_le_source (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) (n : ℕ) :
    paperThetaHistoryInformation a f n ≤ 2 * (a : ℝ) * thetaTiltMean a :=
  paperThetaObservation_kl_budget a (paperThetaHistoryObservation f n)

/-- Each additional observation contributes exactly its conditional relative entropy. -/
theorem paperThetaHistoryInformation_step (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) (n : ℕ) :
    paperThetaHistoryInformation a f (n + 1) = paperThetaHistoryInformation a f n +
      (paperThetaObservationLaw a (paperThetaHistoryObservation f n)).Ex (fun w =>
        ((paperThetaObservationLaw a (paperThetaHistoryObservation f (n + 1))).after
          (paperThetaHistoryPrefix n) w).kl
        ((paperThetaObservationLaw (paperThetaTiltReflection a)
          (paperThetaHistoryObservation f (n + 1))).after (paperThetaHistoryPrefix n) w)) := by
  simpa only [paperThetaHistoryInformation, paperThetaHistoryObservation_prefix] using
    paperThetaObservation_coarsen_kl_decomposition a (paperThetaHistoryObservation f (n + 1))
      (paperThetaHistoryPrefix n)

theorem paperThetaHistoryInformation_monotone (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) : Monotone (paperThetaHistoryInformation a f) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [paperThetaHistoryInformation, paperThetaHistoryObservation_prefix] using
    paperThetaObservation_coarsen_kl_le a (paperThetaHistoryObservation f (n + 1))
      (paperThetaHistoryPrefix n)

/-- Information visible to the whole prescribed observation history. -/
def paperThetaHistoryInformationLimit (a : PaperThetaTilt) (f : ℕ → SimpleFunc ℝ α) : ℝ :=
  ⨆ n, paperThetaHistoryInformation a f n

private theorem history_information_bdd (a : PaperThetaTilt) (f : ℕ → SimpleFunc ℝ α) :
    BddAbove (Set.range (paperThetaHistoryInformation a f)) :=
  ⟨2 * (a : ℝ) * thetaTiltMean a, by
    rintro _ ⟨n, rfl⟩
    exact paperThetaHistoryInformation_le_source a f n⟩

theorem paperThetaHistoryInformation_le_limit (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) (n : ℕ) :
    paperThetaHistoryInformation a f n ≤ paperThetaHistoryInformationLimit a f :=
  le_ciSup (history_information_bdd a f) n

/-- The full history converges in information, with no subsequence or extra source estimate. -/
theorem paperThetaHistoryInformation_tendsto (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) :
    Tendsto (paperThetaHistoryInformation a f) atTop (𝓝 (paperThetaHistoryInformationLimit a f)) :=
  tendsto_atTop_ciSup (paperThetaHistoryInformation_monotone a f) (history_information_bdd a f)

theorem paperThetaHistoryInformationLimit_bounds (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) :
    0 ≤ paperThetaHistoryInformationLimit a f ∧
      paperThetaHistoryInformationLimit a f ≤ 2 * (a : ℝ) * thetaTiltMean a :=
  ⟨(paperThetaHistoryInformation_nonneg a f 0).trans (paperThetaHistoryInformation_le_limit a f 0),
    ciSup_le (paperThetaHistoryInformation_le_source a f)⟩

/-- The history's own information limit controls every finite-history reflected statistic. -/
theorem paperThetaHistory_reflectionGap_budget (a : PaperThetaTilt)
    (f : ℕ → SimpleFunc ℝ α) (n : ℕ) (g : (Fin n → α) → ℝ) :
    |thetaTiltStatisticReflectionGap (fun x => g (paperThetaHistoryObservation f n x)) a| ≤
      2 * ‖g‖ * Real.sqrt (paperThetaHistoryInformationLimit a f) := by
  apply (paperThetaObservation_reflectionGap_tv a (paperThetaHistoryObservation f n) g).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Law.tv_le_sqrt_kl
    (paperThetaObservationLaw_dominated a (paperThetaHistoryObservation f n))).trans
      (Real.sqrt_le_sqrt (paperThetaHistoryInformation_le_limit a f n))

end
end RHTower
