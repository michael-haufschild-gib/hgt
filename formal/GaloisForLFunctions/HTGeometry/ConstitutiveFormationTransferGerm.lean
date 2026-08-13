import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cofinal formation-transfer germs

This module formalizes the exact algebraic core of ULF-FTGM-1.

* observer work defines a scale-transfer cell;
* transfer cells obey a strict multiplicative cocycle;
* hidden history satisfies the matching conservation law;
* a functional-equation leg exchange preserves symmetric transfer and reverses orientation;
* the exact exponential model underlying boundary-germ tomography recovers its decay rate and
  amplitude from scale data.

The concrete Poisson--Bernoulli relative-entropy asymptotics remain a separate analytic module.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Information moved out of an observer when `n` depth-`m` blocks are formed into one
depth-`m*n` observer. -/
def formationInformationTransfer (observerWork : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (n : ℝ) * observerWork m - observerWork (m * n)

/-- **Scale-transfer cocycle.**  Direct formation by `n*k` equals transfer through `n`, repeated
`k` times, plus transfer from depth `m*n` through `k`. -/
theorem formationInformationTransfer_cocycle
    (observerWork : ℕ → ℝ) (m n k : ℕ) :
    formationInformationTransfer observerWork m (n * k) =
      (k : ℝ) * formationInformationTransfer observerWork m n +
        formationInformationTransfer observerWork (m * n) k := by
  simp only [formationInformationTransfer, Nat.cast_mul]
  ring_nf

/-- Data-processing subadditivity is exactly positivity of the transfer cell. -/
theorem formationInformationTransfer_nonneg
    (observerWork : ℕ → ℝ) (m n : ℕ)
    (hprocess : observerWork (m * n) ≤ (n : ℝ) * observerWork m) :
    0 ≤ formationInformationTransfer observerWork m n := by
  simpa [formationInformationTransfer] using sub_nonneg.mpr hprocess

/-- Hidden history is total extensive source work minus visible observer work. -/
def formationHiddenHistory (sourceDensity : ℝ) (observerWork : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * sourceDensity - observerWork m

/-- **Formation conservation.**  Hidden history after formation equals repeated old history plus
the information newly transferred out of the observer. -/
theorem formationHiddenHistory_mul
    (sourceDensity : ℝ) (observerWork : ℕ → ℝ) (m n : ℕ) :
    formationHiddenHistory sourceDensity observerWork (m * n) =
      (n : ℝ) * formationHiddenHistory sourceDensity observerWork m +
        formationInformationTransfer observerWork m n := by
  simp only [formationHiddenHistory, formationInformationTransfer, Nat.cast_mul]
  ring

/-- Directed observer works and their symmetric sum. -/
def symmetricObserverWork (forward backward : ℕ → ℝ) (m : ℕ) : ℝ :=
  forward m + backward m

/-- Symmetric transfer is the sum of both directed transfer cells. -/
theorem formationInformationTransfer_symmetric
    (forward backward : ℕ → ℝ) (m n : ℕ) :
    formationInformationTransfer (symmetricObserverWork forward backward) m n =
      formationInformationTransfer forward m n +
        formationInformationTransfer backward m n := by
  simp only [formationInformationTransfer, symmetricObserverWork]
  ring

/-- Functional-equation label exchange reverses the ordered transfer pair. -/
theorem directedFormationTransfer_swap
    (forward backward : ℕ → ℝ) (m n : ℕ) :
    (formationInformationTransfer backward m n,
        formationInformationTransfer forward m n) =
      Prod.swap
        (formationInformationTransfer forward m n,
          formationInformationTransfer backward m n) := by
  rfl

/-- Functional-equation label exchange preserves total symmetric transfer. -/
theorem symmetricFormationTransfer_swap
    (forward backward : ℕ → ℝ) (m n : ℕ) :
    formationInformationTransfer (symmetricObserverWork backward forward) m n =
      formationInformationTransfer (symmetricObserverWork forward backward) m n := by
  rw [formationInformationTransfer_symmetric, formationInformationTransfer_symmetric]
  ring

/-- Exact exponential transfer model appearing as the leading boundary germ in ULF-FTGM-1. -/
def exponentialFormationTransferGerm (amplitude decay : ℝ) (m : ℕ) : ℝ :=
  amplitude * Real.exp (-decay * (m : ℝ))

/-- The exact exponential germ is positive for positive amplitude. -/
theorem exponentialFormationTransferGerm_pos
    {amplitude : ℝ} (hamplitude : 0 < amplitude) (decay : ℝ) (m : ℕ) :
    0 < exponentialFormationTransferGerm amplitude decay m := by
  exact mul_pos hamplitude (Real.exp_pos _)

/-- Logarithmic decay of the exact germ separates into decay rate and a vanishing amplitude term. -/
theorem exponentialFormationTransferGerm_log_slope
    {amplitude : ℝ} (hamplitude : 0 < amplitude) (decay : ℝ) {m : ℕ} (hm : m ≠ 0) :
    -Real.log (exponentialFormationTransferGerm amplitude decay m) / (m : ℝ) =
      decay - Real.log amplitude / (m : ℝ) := by
  rw [exponentialFormationTransferGerm,
    Real.log_mul (ne_of_gt hamplitude) (Real.exp_ne_zero _), Real.log_exp]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

/-- **Decay tomography.**  The logarithmic boundary-germ slope recovers the exponential rate. -/
theorem exponentialFormationTransferGerm_decay_tendsto
    {amplitude : ℝ} (hamplitude : 0 < amplitude) (decay : ℝ) :
    Tendsto
      (fun m : ℕ =>
        -Real.log (exponentialFormationTransferGerm amplitude decay m) / (m : ℝ))
      atTop (𝓝 decay) := by
  have hvanish : Tendsto (fun m : ℕ => Real.log amplitude / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hmodel : Tendsto (fun m : ℕ => decay - Real.log amplitude / (m : ℝ))
      atTop (𝓝 decay) := by
    simpa using tendsto_const_nhds.sub hvanish
  apply hmodel.congr'
  filter_upwards [eventually_ne_atTop 0] with m hm
  exact (exponentialFormationTransferGerm_log_slope hamplitude decay hm).symm

/-- Exact multiplicative-scale relation of the exponential germ.  It is the algebraic source of
the amplitude reconstruction ratio in ULF-FTGM-1. -/
theorem exponentialFormationTransferGerm_scale_identity
    (amplitude decay : ℝ) (m : ℕ) {d : ℕ} (hdpos : 0 < d) :
    exponentialFormationTransferGerm amplitude decay (d * m) * amplitude ^ (d - 1) =
      exponentialFormationTransferGerm amplitude decay m ^ d := by
  rw [exponentialFormationTransferGerm, exponentialFormationTransferGerm]
  rw [show (d * m : ℕ) = m * d by exact Nat.mul_comm d m, Nat.cast_mul]
  rw [show -decay * ((m : ℝ) * (d : ℝ)) = (d : ℕ) * (-decay * (m : ℝ)) by ring]
  rw [Real.exp_nat_mul]
  rw [mul_pow]
  have hpow : amplitude ^ d = amplitude * amplitude ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hdpos]
  rw [hpow]
  ring

/-- The exact exponential model is invariant under label exchange at the symmetric level and
carries no orientation until two directed germs are marked. -/
theorem exponentialFormationTransferGerm_pair_swap_sum
    (a b decayA decayB : ℝ) (m : ℕ) :
    exponentialFormationTransferGerm a decayA m +
        exponentialFormationTransferGerm b decayB m =
      exponentialFormationTransferGerm b decayB m +
        exponentialFormationTransferGerm a decayA m := by
  ring

/-- Positive exponential germ parametrized by its logarithmic amplitude.  This parameterization
removes every side condition from the tomography law. -/
def positiveExponentialFormationTransferGerm
    (logAmplitude decay : ℝ) (m : ℕ) : ℝ :=
  exponentialFormationTransferGerm (Real.exp logAmplitude) decay (m + 1)

/-- **Unconditional decay tomography.**  Every log-amplitude and decay parameter is recovered by
the logarithmic slope of its positive cofinal germ. -/
theorem positiveExponentialFormationTransferGerm_decay_tendsto
    (logAmplitude decay : ℝ) :
    Tendsto
      (fun m : ℕ =>
        -Real.log (positiveExponentialFormationTransferGerm logAmplitude decay m) /
          ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 decay) := by
  have hbase := exponentialFormationTransferGerm_decay_tendsto
    (Real.exp_pos logAmplitude) decay
  exact hbase.comp (tendsto_add_atTop_nat 1)

/-- **Unconditional amplitude cocycle.**  For every positive multiplicative scale `d+1`, the
cofinal exponential germ satisfies the exact power law from which amplitude is reconstructed. -/
theorem positiveExponentialFormationTransferGerm_scale_identity
    (logAmplitude decay : ℝ) (m d : ℕ) :
    exponentialFormationTransferGerm (Real.exp logAmplitude) decay ((d + 1) * (m + 1)) *
        Real.exp logAmplitude ^ d =
      positiveExponentialFormationTransferGerm logAmplitude decay m ^ (d + 1) := by
  simpa [positiveExponentialFormationTransferGerm] using
    exponentialFormationTransferGerm_scale_identity
      (Real.exp logAmplitude) decay (m + 1) (Nat.succ_pos d)

/-- **Formation-transfer germ capstone.**  Scale coherence, hidden-history conservation,
functional-equation neutrality, decay tomography, and amplitude scaling hold simultaneously with
no unproved premise. -/
theorem formationTransferGerm_mechanism
    (sourceDensity logAmplitude decay : ℝ)
    (observerWork forward backward : ℕ → ℝ) (m n k d : ℕ) :
    formationInformationTransfer observerWork m (n * k) =
        (k : ℝ) * formationInformationTransfer observerWork m n +
          formationInformationTransfer observerWork (m * n) k ∧
      formationHiddenHistory sourceDensity observerWork (m * n) =
        (n : ℝ) * formationHiddenHistory sourceDensity observerWork m +
          formationInformationTransfer observerWork m n ∧
      formationInformationTransfer (symmetricObserverWork backward forward) m n =
        formationInformationTransfer (symmetricObserverWork forward backward) m n ∧
      Tendsto
        (fun j : ℕ =>
          -Real.log (positiveExponentialFormationTransferGerm logAmplitude decay j) /
            ((j + 1 : ℕ) : ℝ))
        atTop (𝓝 decay) ∧
      exponentialFormationTransferGerm (Real.exp logAmplitude) decay ((d + 1) * (m + 1)) *
          Real.exp logAmplitude ^ d =
        positiveExponentialFormationTransferGerm logAmplitude decay m ^ (d + 1) := by
  exact ⟨formationInformationTransfer_cocycle observerWork m n k,
    formationHiddenHistory_mul sourceDensity observerWork m n,
    symmetricFormationTransfer_swap forward backward m n,
    positiveExponentialFormationTransferGerm_decay_tendsto logAmplitude decay,
    positiveExponentialFormationTransferGerm_scale_identity logAmplitude decay m d⟩

end

end GaloisForLFunctions.HTGeometry
