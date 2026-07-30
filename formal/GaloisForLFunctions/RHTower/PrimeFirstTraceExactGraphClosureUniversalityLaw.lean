import GaloisForLFunctions.RHTower.ArithmeticLogClockBoundedCompletionSaturation

/-!
# Exact graph closure of the actual-prime first-trace clock

The order-one finite logarithmic clock becomes the first-trace clock after the canonical isometric
zero-prepending shift.  Bounded-completion saturation therefore determines its graph closure
exactly: source and response decouple completely subject only to vanishing of the response vacuum
coordinate.
-/

open Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Zero-prepending is an isometry of the prime Hardy pivot. -/
theorem norm_hardyPrependZeroVec (x : PrimeHardy) :
    ‖hardyPrependZeroVec x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  norm_num only [ENNReal.toReal_ofNat]
  have hs : Summable
      (fun n : ℕ => ‖hardyPrependZeroVec x n‖ ^ (2 : ℝ)) :=
    (hardyPrependZeroVec x).2.summable (by norm_num)
  calc
    (∑' n : ℕ, ‖hardyPrependZeroVec x n‖ ^ (2 : ℝ)) =
        (∑ n ∈ Finset.range 1, ‖hardyPrependZeroVec x n‖ ^ (2 : ℝ)) +
          ∑' n : ℕ, ‖hardyPrependZeroVec x (n + 1)‖ ^ (2 : ℝ) :=
      (hs.sum_add_tsum_nat_add 1).symm
    _ = ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by simp

/-- Continuous isometric form of the canonical zero-prepending shift. -/
def hardyPrependZeroCLM : PrimeHardy →L[ℝ] PrimeHardy :=
  LinearMap.mkContinuous hardyPrependZero 1 (fun x => by
    change ‖hardyPrependZeroVec x‖ ≤ 1 * ‖x‖
    rw [norm_hardyPrependZeroVec]
    simp)

@[simp] theorem hardyPrependZeroCLM_apply (x : PrimeHardy) :
    hardyPrependZeroCLM x = hardyPrependZero x := rfl

/-- Dropping then prepending reconstructs exactly the codimension-one zero-vacuum sector. -/
theorem hardyPrependZeroCLM_hardyDrop_of_head_zero
    (y : PrimeHardy) (hy : y 0 = 0) :
    hardyPrependZeroCLM (hardyDrop y) = y := by
  apply lp.ext
  funext n
  cases n with
  | zero => simpa using hy.symm
  | succ n => simp [hardyPrependZeroCLM, hardyPrependZero]

/-- **Exact first-trace graph-closure law.**  A source-response pair lies in the closed graph of
the actual-prime first-trace clock exactly when the response has zero vacuum coordinate. -/
theorem primeFirstTraceClock_graphClosure_mem_iff
    (w : WithLp 2 (PrimeHardy × PrimeHardy)) :
    w ∈ (realLinearGraphSubmodule primeHardyKernelMap
        primeFirstTraceClock).topologicalClosure ↔
      w.ofLp.2 0 = 0 := by
  constructor
  · intro hw
    have hsubset :
        (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
            Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆
          {z | z.ofLp.2 0 = 0} := by
      rintro z ⟨d, rfl⟩
      have happ := LinearMap.congr_fun
        hardyPrependZero_comp_primeFiniteTraceClock_one d
      change primeFirstTraceClock d 0 = 0
      rw [← happ]
      rfl
    have hclosed : IsClosed {z : WithLp 2 (PrimeHardy × PrimeHardy) |
        z.ofLp.2 0 = 0} := by
      apply isClosed_eq
      · change Continuous (fun z =>
          ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0).comp
            (WithLp.sndL 2 ℝ PrimeHardy PrimeHardy)) z)
        exact ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0).comp
          (WithLp.sndL 2 ℝ PrimeHardy PrimeHardy)).continuous
      · fun_prop
    have hw' : w ∈ closure
        (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
          Set (WithLp 2 (PrimeHardy × PrimeHardy))) := by
      simpa only [Submodule.topologicalClosure_coe] using! hw
    exact closure_minimal hsubset hclosed hw'
  · intro hw
    let C : PrimeHardy →L[ℝ] PrimeHardy := hardyPrependZeroCLM
    have hpair := primeBoundedPostprocessedTraceClock_pair_mem_graphClosure
      1 C w.ofLp.1 (hardyDrop w.ofLp.2)
    have hCy : C (hardyDrop w.ofLp.2) = w.ofLp.2 := by
      exact hardyPrependZeroCLM_hardyDrop_of_head_zero w.ofLp.2 hw
    have hclock : primeBoundedPostprocessedTraceClock 1 C = primeFirstTraceClock := by
      apply LinearMap.ext
      intro d
      change hardyPrependZero (primeFiniteTraceClock 1 d) = primeFirstTraceClock d
      exact LinearMap.congr_fun hardyPrependZero_comp_primeFiniteTraceClock_one d
    rw [hCy, hclock] at hpair
    simpa only [WithLp.toLp_ofLp] using hpair

/-- Every source vector pairs with every zero-vacuum response in the first-trace graph closure. -/
theorem primeFirstTraceClock_pair_mem_graphClosure_iff
    (x y : PrimeHardy) :
    WithLp.toLp 2 (x, y) ∈
        (realLinearGraphSubmodule primeHardyKernelMap
          primeFirstTraceClock).topologicalClosure ↔
      y 0 = 0 := by
  simpa only [WithLp.ofLp_toLp, Prod.snd] using
    primeFirstTraceClock_graphClosure_mem_iff (WithLp.toLp 2 (x, y))

end

end RHTower
