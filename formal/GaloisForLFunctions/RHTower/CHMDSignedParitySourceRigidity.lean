import GaloisForLFunctions.RHTower.CHMDSignedEulerPoissonRigidity
import GaloisForLFunctions.BiScaleUncertainty.EulerPoissonChiralDriftAndPrimeShiftRigidity

/-!
# Complete signed Euler–Poisson arithmetic rigidity

The even and odd harmonic readouts together determine every arithmetic weight.
This removes the coefficientwise-order hypothesis from the existing perturbation
obstruction: even compensating signed changes cannot preserve both identities.
Agreement on any unbounded integer sample set suffices.

The positive content is constructive: subtracting the two readouts gives twice
the forward source, whose coefficients have the quantitative recovery and
lexicographic cusp-order laws proved in the preceding modules.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace RHTower.CHMDArithmeticTheta
open CHMDPolar GaloisForLFunctions.BiScaleUncertainty

/-- Convergence of the symmetric signed series controls both directed series,
because the two theta factors in each summand are positive. -/
theorem summable_directed_of_symmetric (w : ℕ → ℝ) (x : ℝ)
    (hs : Summable fun n => w n *
      (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :
    (Summable fun n => w n * riemannKernelReal (x + Real.log n)) ∧
      Summable (fun n => w n * riemannKernelReal (x - Real.log n)) := by
  constructor
  · apply Summable.of_norm_bounded hs.norm
    intro n
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _),
      abs_of_pos (add_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (riemannKernelReal_pos _).le) (abs_nonneg _)
  · apply Summable.of_norm_bounded hs.norm
    intro n
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _),
      abs_of_pos (add_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (riemannKernelReal_pos _).le) (abs_nonneg _)

/-- Both parity readouts recover the directed source without any positivity
assumption on the arithmetic weights. -/
theorem weightedSym_sub_odd_eq_two_forward (w : ℕ → ℝ) (x : ℝ)
    (hs : Summable fun n => w n *
      (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :
    weightedSymKernelSum w x - weightedOddKernelSum w x =
      2 * ∑' n, w n * riemannKernelReal (x + Real.log n) := by
  obtain ⟨hf, hb⟩ := summable_directed_of_symmetric w x hs
  simp_rw [weightedSymKernelSum, weightedOddKernelSum, mul_add, mul_sub]
  rw [hf.tsum_add hb, hb.tsum_sub hf]
  ring

theorem forward_eq_shifted_of_arithmetic_support (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0) (x : ℝ)
    (hf : Summable fun n => w n * riemannKernelReal (x + Real.log n)) :
    (∑' n, w (n + 2) * riemannKernelReal (x + Real.log (site n))) =
      ∑' n, w n * riemannKernelReal (x + Real.log n) := by
  have h := hf.sum_add_tsum_nat_add 2
  simpa [Finset.sum_range_succ, hw0, hw1, site, Nat.cast_add] using h

/-- No compensating signed arithmetic repair can preserve both complete
Euler–Poisson identities, even on an arbitrary unbounded set of integer samples. -/
theorem signed_parity_source_rigidity (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (hs : ∀ N : ℕ, Summable fun n => w n *
      (riemannKernelReal ((N : ℝ) + Real.log n) +
        riemannKernelReal ((N : ℝ) - Real.log n)))
    (hmatch : ∃ᶠ N : ℕ in atTop,
      weightedSymKernelSum w N = primeKernelSum N ∧
        weightedOddKernelSum w N = oddPrimeKernelSum N) :
    w = vonMangoldtAtom := by
  have hf (N : ℕ) := (summable_directed_of_symmetric w N (hs N)).1
  have hc : Summable fun n => w (n + 2) * riemannKernelReal (Real.log (site n)) := by
    simpa only [Nat.cast_zero, zero_add, site, Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := fun n => w n *
        riemannKernelReal ((0 : ℕ) + Real.log n)) 2).mpr (hf 0)
  have hcoeff := signed_arithmetic_source_rigidity (fun n => w (n + 2)) hc
    (hmatch.mono fun N hN => by
      have h1 := weightedSym_sub_odd_eq_two_forward w N (hs N)
      have h2 := weightedSym_sub_odd_eq_two_forward vonMangoldtAtom N
        (summable_primeKernelSum N)
      rw [hN.1, hN.2] at h1
      change primeKernelSum N - oddPrimeKernelSum N = _ at h2
      have hr : (∑' n, w n * riemannKernelReal ((N : ℝ) + Real.log n)) =
          ∑' n, vonMangoldtAtom n * riemannKernelReal ((N : ℝ) + Real.log n) := by
        linarith
      rw [forward_eq_shifted_of_arithmetic_support w hw0 hw1 N (hf N), hr]
      exact (wave_mangoldtData N).symm.trans (wave_mangoldtData_eq_sourceReadout N))
  funext n
  cases n with
  | zero => simpa [vonMangoldtAtom] using hw0
  | succ n =>
    cases n with
    | zero => simpa [vonMangoldtAtom] using hw1
    | succ n => exact congrFun hcoeff n

/-- The original arithmetic coefficients are the unique signed realization of
both complete parity readouts. All convergence obligations for existence are
discharged by the actual von Mangoldt source. -/
theorem unique_signed_parity_source :
    ∃! w : ℕ → ℝ, w 0 = 0 ∧ w 1 = 0 ∧
      (∀ N : ℕ, Summable fun n => w n *
        (riemannKernelReal ((N : ℝ) + Real.log n) +
          riemannKernelReal ((N : ℝ) - Real.log n))) ∧
      (∃ᶠ N : ℕ in atTop, weightedSymKernelSum w N = primeKernelSum N ∧
        weightedOddKernelSum w N = oddPrimeKernelSum N) := by
  refine ⟨vonMangoldtAtom, ⟨by simp [vonMangoldtAtom], by simp [vonMangoldtAtom],
    fun N => summable_primeKernelSum N, ?_⟩, ?_⟩
  · exact (Eventually.of_forall fun _ => And.intro rfl rfl).frequently
  · intro w hw
    exact signed_parity_source_rigidity w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2

end RHTower.CHMDArithmeticTheta
