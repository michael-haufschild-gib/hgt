import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionMoment
import GaloisForLFunctions.RHTower.WeilLogShiftMixtureLogTransport

/-! Squared local-correction error on the moving part of an actual optimal transport plan. -/

noncomputable section
namespace RHTower

def finiteWeilLogCorrectionDispersionCost (r k : ℕ) (u v : Fin (r + 2)) : ℝ :=
  if u = v then 0 else
    ((((k + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) *
      (1 - ((k + 2 : ℕ) : ℝ) * |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) -
        1 / 2) ^ 2

theorem finiteWeilLogCorrectionDispersionCost_self (r k : ℕ) (u : Fin (r + 2)) :
    finiteWeilLogCorrectionDispersionCost r k u u = 0 := by
  rw [finiteWeilLogCorrectionDispersionCost, if_pos rfl]

theorem finiteWeilLogCorrectionDispersionCost_symm (r k : ℕ) (u v : Fin (r + 2)) :
    finiteWeilLogCorrectionDispersionCost r k u v = finiteWeilLogCorrectionDispersionCost r k v u := by
  by_cases h : u = v
  · subst v
    rfl
  · simp only [finiteWeilLogCorrectionDispersionCost, if_neg h, if_neg (Ne.symm h), abs_sub_comm]

theorem finiteWeilLogCorrectionDispersionCost_nonneg (r k : ℕ) (u v : Fin (r + 2)) :
    0 ≤ finiteWeilLogCorrectionDispersionCost r k u v := by
  unfold finiteWeilLogCorrectionDispersionCost
  split_ifs <;> positivity

theorem finiteWeilLogCorrectionDispersionCost_edge (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilLogCorrectionDispersionCost r k (finiteWeilCanonicalEdgeSource r i)
      (finiteWeilCanonicalEdgeTarget r i) = (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) ^ 2 := by
  rw [finiteWeilLogCorrectionDispersionCost, if_neg (finiteWeilCanonicalEdge_ne r i)]
  have hp : 0 ≤ finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc :=
    (sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
      (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))).le
  rw [finiteWeilCanonicalEdge_difference r i (finiteWeilClusterLogNodes r k), abs_mul,
    finiteWeilBinomialParity_abs, one_mul, abs_sub_comm, abs_of_nonneg hp]
  rfl

theorem finiteWeilCanonicalCoupling_log_correction_dispersion (r k : ℕ) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (finiteWeilLogCorrectionDispersionCost r k) =
      finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k := by
  rw [finiteWeilCanonicalCoupling_cost_eq]
  simp only [finiteWeilLogCorrectionDispersionCost_edge, finiteWeilCanonicalEdgeLogCorrectionSecondMoment]

theorem finiteWeilMixtureCoupling_log_correction_dispersion (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionDispersionCost r k) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k := by
  rw [finiteWeilMixtureCoupling_cost_eq r k a b _ (finiteWeilLogCorrectionDispersionCost_self r k)
    (finiteWeilLogCorrectionDispersionCost_symm r k), finiteWeilCanonicalCoupling_log_correction_dispersion]

end RHTower
