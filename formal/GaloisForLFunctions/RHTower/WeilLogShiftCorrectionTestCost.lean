import GaloisForLFunctions.RHTower.WeilLogShiftEdgeLogCorrection
import GaloisForLFunctions.RHTower.WeilLogShiftMixtureLogTransport

/-! Arbitrary correction observables identify the moving-part law of every optimal mixture coupling. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilLogCorrectionTestCost (r k : ℕ) (φ : ℝ → ℝ) (u v : Fin (r + 2)) : ℝ :=
  if u = v then 0 else φ ((((k + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) *
    (1 - ((k + 2 : ℕ) : ℝ) * |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|))

theorem finiteWeilLogCorrectionTestCost_self (r k : ℕ) (φ : ℝ → ℝ) (u : Fin (r + 2)) :
    finiteWeilLogCorrectionTestCost r k φ u u = 0 := by
  rw [finiteWeilLogCorrectionTestCost, if_pos rfl]

theorem finiteWeilLogCorrectionTestCost_symm (r k : ℕ) (φ : ℝ → ℝ) (u v : Fin (r + 2)) :
    finiteWeilLogCorrectionTestCost r k φ u v = finiteWeilLogCorrectionTestCost r k φ v u := by
  by_cases h : u = v
  · subst v
    rfl
  · simp only [finiteWeilLogCorrectionTestCost, if_neg h, if_neg (Ne.symm h), abs_sub_comm]

theorem finiteWeilLogCorrectionTestCost_edge (r k : ℕ) (φ : ℝ → ℝ) (i : Fin (r + 1)) :
    finiteWeilLogCorrectionTestCost r k φ (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) =
      φ (finiteWeilCanonicalEdgeLogCorrection r k i) := by
  rw [finiteWeilLogCorrectionTestCost, if_neg (finiteWeilCanonicalEdge_ne r i)]
  have hp : 0 ≤ finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc :=
    (sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
      (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))).le
  rw [finiteWeilCanonicalEdge_difference r i (finiteWeilClusterLogNodes r k), abs_mul,
    finiteWeilBinomialParity_abs, one_mul, abs_sub_comm, abs_of_nonneg hp]
  rfl

theorem finiteWeilCanonicalCoupling_log_correction_test (r k : ℕ) (φ : ℝ → ℝ) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (finiteWeilLogCorrectionTestCost r k φ) =
      ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * φ (finiteWeilCanonicalEdgeLogCorrection r k i) := by
  rw [finiteWeilCanonicalCoupling_cost_eq]
  simp only [finiteWeilLogCorrectionTestCost_edge]

theorem finiteWeilMixtureCoupling_log_correction_test (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) (φ : ℝ → ℝ) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionTestCost r k φ) =
      |(a : ℝ) - (b : ℝ)| *
        ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * φ (finiteWeilCanonicalEdgeLogCorrection r k i) := by
  rw [finiteWeilMixtureCoupling_cost_eq r k a b _ (finiteWeilLogCorrectionTestCost_self r k φ)
    (finiteWeilLogCorrectionTestCost_symm r k φ), finiteWeilCanonicalCoupling_log_correction_test]

theorem finiteWeilMixtureCoupling_log_correction_moving_mass (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionTestCost r k (fun _ => 1)) =
      |(a : ℝ) - (b : ℝ)| := by
  rw [finiteWeilMixtureCoupling_log_correction_test]
  simp only [mul_one, finiteWeilCanonicalEdgeMass_sum]

theorem finiteWeilMixtureCoupling_log_correction_mean (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionTestCost r k (fun x => x)) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalLogTransportCorrection r k := by
  rw [finiteWeilMixtureCoupling_log_correction_test, finiteWeilCanonicalEdgeLogCorrection_mean]

end RHTower
