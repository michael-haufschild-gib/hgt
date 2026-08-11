import Mathlib

/-!
# Marked variation dynamics

Finite source histories carry two executions: coherent complex addition and a positive variation
envelope.  Positive observers transport their difference by an exact chain rule, while conservative
history refinement creates a separately transported positive increment.  The resulting interchange
identity is a route-independent fusion law.

The module contains no RH premise and uses no computational proof.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- A finite positive observer kernel. Positivity is part of the object, not a theorem premise. -/
structure FinitePositiveKernel (X Y : Type*) where
  weight : Y → X → ℝ
  nonneg : ∀ y x, 0 ≤ weight y x

namespace FinitePositiveKernel

variable {X Y Z : Type*}

/-- Action of a positive kernel on a real profile. -/
def applyReal [Fintype X] (T : FinitePositiveKernel X Y) (f : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, T.weight y x * f x

/-- Action of a positive kernel on a coherent complex profile. -/
def applyComplex [Fintype X] (T : FinitePositiveKernel X Y) (f : X → ℂ) : Y → ℂ :=
  fun y => ∑ x, (T.weight y x : ℂ) * f x

/-- Serial composition of positive kernels. -/
def comp [Fintype Y] (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y) :
    FinitePositiveKernel X Z where
  weight z x := ∑ y, S.weight z y * T.weight y x
  nonneg z x := Finset.sum_nonneg fun y _ =>
    mul_nonneg (S.nonneg z y) (T.nonneg y x)

/-- Positive kernels preserve pointwise order on real profiles. -/
theorem applyReal_mono [Fintype X] (T : FinitePositiveKernel X Y)
    {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) (y : Y) :
    T.applyReal f y ≤ T.applyReal g y := by
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hfg x) (T.nonneg y x)

/-- A positive kernel sends nonnegative profiles to nonnegative profiles. -/
theorem applyReal_nonneg [Fintype X] (T : FinitePositiveKernel X Y)
    {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (y : Y) :
    0 ≤ T.applyReal f y := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (T.nonneg y x) (hf x)

/-- Positive-kernel execution preserves addition. -/
theorem applyReal_add [Fintype X] (T : FinitePositiveKernel X Y) (f g : X → ℝ) :
    T.applyReal (fun x => f x + g x) =
      fun y => T.applyReal f y + T.applyReal g y := by
  funext y
  simp [applyReal, mul_add, Finset.sum_add_distrib]

/-- Positive-kernel execution preserves subtraction. -/
theorem applyReal_sub [Fintype X] (T : FinitePositiveKernel X Y) (f g : X → ℝ) :
    T.applyReal (fun x => f x - g x) =
      fun y => T.applyReal f y - T.applyReal g y := by
  funext y
  simp [applyReal, mul_sub, Finset.sum_sub_distrib]

/-- Positive-kernel modulus inequality. -/
theorem norm_applyComplex_le [Fintype X] (T : FinitePositiveKernel X Y)
    (f : X → ℂ) (y : Y) :
    ‖T.applyComplex f y‖ ≤ T.applyReal (fun x => ‖f x‖) y := by
  calc
    ‖T.applyComplex f y‖ =
        ‖∑ x, (T.weight y x : ℂ) * f x‖ := rfl
    _ ≤ ∑ x, ‖(T.weight y x : ℂ) * f x‖ := norm_sum_le _ _
    _ = ∑ x, T.weight y x * ‖f x‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (T.nonneg y x)]
    _ = T.applyReal (fun x => ‖f x‖) y := rfl

/-- Serial real execution agrees with execution by the composite kernel. -/
theorem applyReal_comp [Fintype X] [Fintype Y]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y) (f : X → ℝ) :
    (S.comp T).applyReal f = S.applyReal (T.applyReal f) := by
  funext z
  simp only [applyReal, comp]
  calc
    (∑ x, (∑ y, S.weight z y * T.weight y x) * f x) =
        ∑ x, ∑ y, (S.weight z y * T.weight y x) * f x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
    _ = ∑ y, ∑ x, (S.weight z y * T.weight y x) * f x := by
          rw [Finset.sum_comm]
    _ = ∑ y, S.weight z y * ∑ x, T.weight y x * f x := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring

/-- Serial coherent execution agrees with execution by the composite kernel. -/
theorem applyComplex_comp [Fintype X] [Fintype Y]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y) (f : X → ℂ) :
    (S.comp T).applyComplex f = S.applyComplex (T.applyComplex f) := by
  funext z
  simp only [applyComplex, comp, Complex.ofReal_sum, Complex.ofReal_mul]
  calc
    (∑ x, (∑ y, (S.weight z y : ℂ) * (T.weight y x : ℂ)) * f x) =
        ∑ x, ∑ y, ((S.weight z y : ℂ) * (T.weight y x : ℂ)) * f x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
    _ = ∑ y, ∑ x, ((S.weight z y : ℂ) * (T.weight y x : ℂ)) * f x := by
          rw [Finset.sum_comm]
    _ = ∑ y, (S.weight z y : ℂ) * ∑ x, (T.weight y x : ℂ) * f x := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring

end FinitePositiveKernel

/-- A positive kernel that preserves total mass of every nonnegative source profile. -/
structure FiniteMarkovKernel (X Y : Type*) [Fintype Y]
    extends FinitePositiveKernel X Y where
  column_sum : ∀ x, ∑ y, weight y x = 1

namespace FiniteMarkovKernel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A finite Markov kernel preserves total real mass. -/
theorem sum_applyReal (K : FiniteMarkovKernel X Y) (f : X → ℝ) :
    ∑ y, K.toFinitePositiveKernel.applyReal f y = ∑ x, f x := by
  simp only [FinitePositiveKernel.applyReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_mul, K.column_sum]
  simp

/-- A finite Markov kernel preserves the coherent total sum. -/
theorem sum_applyComplex (K : FiniteMarkovKernel X Y) (f : X → ℂ) :
    ∑ y, K.toFinitePositiveKernel.applyComplex f y = ∑ x, f x := by
  simp only [FinitePositiveKernel.applyComplex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_mul]
  have hcolumn : (∑ y, (K.weight y x : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, K.column_sum]
    simp
  rw [hcolumn, one_mul]

end FiniteMarkovKernel

section MarkedPackets

variable {X Y Z I J : Type*}

/-- Coherent source execution of a marked packet. -/
def markedCoherent [Fintype I] (a : I → X → ℂ) : X → ℂ :=
  fun x => ∑ i, a i x

/-- Positive source envelope of a marked packet. -/
def markedEnvelope [Fintype I] (a : I → X → ℂ) : X → ℝ :=
  fun x => ∑ i, ‖a i x‖

/-- Coherent output of a marked packet after a positive observer. -/
def markedCoherentOutput [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) : Y → ℂ :=
  T.applyComplex (markedCoherent a)

/-- Positive envelope output after a positive observer. -/
def markedEnvelopeOutput [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) : Y → ℝ :=
  T.applyReal (markedEnvelope a)

/-- Positive variation retained after coherent cancellation. -/
def markedVariationDefect [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) : Y → ℝ :=
  fun y => markedEnvelopeOutput T a y - ‖markedCoherentOutput T a y‖

/-- A marked packet's coherent source modulus is bounded by its positive source envelope. -/
theorem norm_markedCoherent_le_envelope [Fintype I] (a : I → X → ℂ) (x : X) :
    ‖markedCoherent a x‖ ≤ markedEnvelope a x := by
  exact norm_sum_le _ _

/-- The marked-variation defect is pointwise nonnegative. -/
theorem markedVariationDefect_nonneg [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y) :
    0 ≤ markedVariationDefect T a y := by
  have hkernel := T.norm_applyComplex_le (markedCoherent a) y
  have henvelope := T.applyReal_mono (fun x => norm_markedCoherent_le_envelope a x) y
  dsimp [markedVariationDefect, markedCoherentOutput, markedEnvelopeOutput]
  linarith

/-- Coherent output and defect reconstruct the pushed positive envelope exactly. -/
theorem markedEnvelope_reconstruction [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) :
    markedEnvelopeOutput T a =
      fun y => ‖markedCoherentOutput T a y‖ + markedVariationDefect T a y := by
  funext y
  simp [markedVariationDefect]

/-- Phase loss introduced by one positive observer. -/
def positiveObserverLoss [Fintype Y]
    (S : FinitePositiveKernel Y Z) (u : Y → ℂ) : Z → ℝ :=
  fun z => S.applyReal (fun y => ‖u y‖) z - ‖S.applyComplex u z‖

/-- Observer phase loss is pointwise nonnegative. -/
theorem positiveObserverLoss_nonneg [Fintype Y]
    (S : FinitePositiveKernel Y Z) (u : Y → ℂ) (z : Z) :
    0 ≤ positiveObserverLoss S u z := by
  exact sub_nonneg.mpr (S.norm_applyComplex_le u z)

/-- Exact observer-chain transport law for marked variation. -/
theorem markedVariationDefect_observerChain [Fintype X] [Fintype Y] [Fintype I]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (a : I → X → ℂ) :
    markedVariationDefect (S.comp T) a =
      fun z => S.applyReal (markedVariationDefect T a) z +
        positiveObserverLoss S (markedCoherentOutput T a) z := by
  rw [show markedVariationDefect (S.comp T) a =
      fun z => S.applyReal (markedEnvelopeOutput T a) z -
        ‖S.applyComplex (markedCoherentOutput T a) z‖ by
    funext z
    simp [markedVariationDefect, markedEnvelopeOutput, markedCoherentOutput,
      S.applyReal_comp T, S.applyComplex_comp T]]
  rw [show markedVariationDefect T a =
      fun y => markedEnvelopeOutput T a y - ‖markedCoherentOutput T a y‖ from rfl]
  rw [S.applyReal_sub]
  funext z
  simp [positiveObserverLoss]

/-- Defect of fusing two independently marked packets before the final modulus. -/
def markedFusionDefect [Fintype X] [Fintype I] [Fintype J]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (b : J → X → ℂ) : Y → ℝ :=
  fun y => markedEnvelopeOutput T a y + markedEnvelopeOutput T b y -
    ‖markedCoherentOutput T a y + markedCoherentOutput T b y‖

/-- Exact marked-fusion law: within-packet debts plus between-packet interference. -/
theorem markedVariationDefect_fusion [Fintype X] [Fintype I] [Fintype J]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (b : J → X → ℂ) :
    markedFusionDefect T a b =
      fun y => markedVariationDefect T a y + markedVariationDefect T b y +
        (‖markedCoherentOutput T a y‖ + ‖markedCoherentOutput T b y‖ -
          ‖markedCoherentOutput T a y + markedCoherentOutput T b y‖) := by
  funext y
  simp [markedFusionDefect, markedVariationDefect]
  ring

/-- Between-packet interference is nonnegative. -/
theorem markedFusionInterference_nonneg [Fintype X] [Fintype I] [Fintype J]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (b : J → X → ℂ) (y : Y) :
    0 ≤ ‖markedCoherentOutput T a y‖ + ‖markedCoherentOutput T b y‖ -
      ‖markedCoherentOutput T a y + markedCoherentOutput T b y‖ := by
  exact sub_nonneg.mpr (norm_add_le _ _)

/-- Conservative refinement: same coherent source profile, larger positive envelope. -/
structure MarkedRefinement [Fintype I] [Fintype J] (X : Type*) where
  coarse : I → X → ℂ
  fine : J → X → ℂ
  coherent_eq : markedCoherent fine = markedCoherent coarse
  envelope_le : ∀ x, markedEnvelope coarse x ≤ markedEnvelope fine x

/-- Positive envelope born in a conservative refinement. -/
def refinementExcess [Fintype I] [Fintype J]
    (R : MarkedRefinement (I := I) (J := J) X) : X → ℝ :=
  fun x => markedEnvelope R.fine x - markedEnvelope R.coarse x

/-- Refinement excess is pointwise nonnegative. -/
theorem refinementExcess_nonneg [Fintype I] [Fintype J]
    (R : MarkedRefinement (I := I) (J := J) X) (x : X) :
    0 ≤ refinementExcess R x := by
  exact sub_nonneg.mpr (R.envelope_le x)

/-- Exact refinement increment after one observer. -/
theorem markedVariationDefect_refinement [Fintype X] [Fintype I] [Fintype J]
    (T : FinitePositiveKernel X Y) (R : MarkedRefinement (I := I) (J := J) X) :
    markedVariationDefect T R.fine =
      fun y => markedVariationDefect T R.coarse y + T.applyReal (refinementExcess R) y := by
  have hcoherent :
      markedCoherentOutput T R.fine = markedCoherentOutput T R.coarse := by
    unfold markedCoherentOutput
    rw [R.coherent_eq]
  rw [show refinementExcess R =
      fun x => markedEnvelope R.fine x - markedEnvelope R.coarse x from rfl]
  rw [T.applyReal_sub]
  funext y
  rw [markedVariationDefect, markedVariationDefect, hcoherent]
  simp only [markedEnvelopeOutput]
  ring

/-- Generation-observation interchange: inherited variation, newborn variation, and observer
phase loss form one exact positive decomposition. -/
theorem markedVariationDefect_interchange [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (R : MarkedRefinement (I := I) (J := J) X) :
    markedVariationDefect (S.comp T) R.fine =
      fun z => S.applyReal (markedVariationDefect T R.coarse) z +
        (S.comp T).applyReal (refinementExcess R) z +
        positiveObserverLoss S (markedCoherentOutput T R.coarse) z := by
  rw [markedVariationDefect_observerChain S T R.fine]
  rw [markedVariationDefect_refinement T R]
  rw [S.applyReal_add]
  rw [← S.applyReal_comp T]
  have hcoherent :
      markedCoherentOutput T R.fine = markedCoherentOutput T R.coarse := by
    unfold markedCoherentOutput
    rw [R.coherent_eq]
  rw [hcoherent]

/-- The refinement increment commutes exactly with a serial observer chain. -/
theorem markedVariationDefect_interchange_increment [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (R : MarkedRefinement (I := I) (J := J) X) :
    (fun z => markedVariationDefect (S.comp T) R.fine z -
        markedVariationDefect (S.comp T) R.coarse z) =
      (S.comp T).applyReal (refinementExcess R) := by
  rw [markedVariationDefect_refinement (S.comp T) R]
  funext z
  ring

/-- Three-sector conservation for genuine, splice, and between-sector interference. -/
theorem genuineSpliceInterference_conservation
    (genuine splice : ℂ) (genuineEnvelope spliceEnvelope : ℝ) :
    genuineEnvelope + spliceEnvelope - ‖genuine + splice‖ =
      (genuineEnvelope - ‖genuine‖) + (spliceEnvelope - ‖splice‖) +
        (‖genuine‖ + ‖splice‖ - ‖genuine + splice‖) := by
  ring

/-- If both sector envelopes dominate their coherent executions, all three terms in the
source/splice conservation law are nonnegative. -/
theorem genuineSpliceInterference_nonneg
    (genuine splice : ℂ) (genuineEnvelope spliceEnvelope : ℝ)
    (hgenuine : ‖genuine‖ ≤ genuineEnvelope)
    (hsplice : ‖splice‖ ≤ spliceEnvelope) :
    0 ≤ genuineEnvelope - ‖genuine‖ ∧
      0 ≤ spliceEnvelope - ‖splice‖ ∧
      0 ≤ ‖genuine‖ + ‖splice‖ - ‖genuine + splice‖ := by
  exact ⟨sub_nonneg.mpr hgenuine, sub_nonneg.mpr hsplice,
    sub_nonneg.mpr (norm_add_le _ _)⟩

/-- Global marked-variation conservation for a mass-preserving positive observer. -/
theorem markedVariationDefect_totalBudget [Fintype X] [Fintype Y] [Fintype I]
    (K : FiniteMarkovKernel X Y) (a : I → X → ℂ) :
    ∑ y, markedVariationDefect K.toFinitePositiveKernel a y =
      (∑ x, markedEnvelope a x) -
        ∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖ := by
  change
    (∑ y, (markedEnvelopeOutput K.toFinitePositiveKernel a y -
      ‖markedCoherentOutput K.toFinitePositiveKernel a y‖)) =
      (∑ x, markedEnvelope a x) -
        ∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖
  rw [Finset.sum_sub_distrib]
  change
    (∑ y, K.toFinitePositiveKernel.applyReal (markedEnvelope a) y) -
        ∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖ =
      (∑ x, markedEnvelope a x) -
        ∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖
  rw [K.sum_applyReal]

/-- Selection consequence: a source-admitted mass-preserving marked realization cannot exhibit
strict coherent amplification beyond its source variation mass. -/
theorem markedCoherentOutput_l1_le_envelopeMass [Fintype X] [Fintype Y] [Fintype I]
    (K : FiniteMarkovKernel X Y) (a : I → X → ℂ) :
    (∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖) ≤
      ∑ x, markedEnvelope a x := by
  have hsum : 0 ≤ ∑ y, markedVariationDefect K.toFinitePositiveKernel a y :=
    Finset.sum_nonneg fun y _ =>
      markedVariationDefect_nonneg K.toFinitePositiveKernel a y
  rw [markedVariationDefect_totalBudget K a] at hsum
  linarith

/-- Exact realizability exclusion: strict output amplification refutes the existence of the given
positive mass-preserving marked realization. -/
theorem markedRealization_strictAmplification_impossible [Fintype X] [Fintype Y] [Fintype I]
    (K : FiniteMarkovKernel X Y) (a : I → X → ℂ) :
    ¬((∑ x, markedEnvelope a x) <
      ∑ y, ‖markedCoherentOutput K.toFinitePositiveKernel a y‖) := by
  exact not_lt_of_ge (markedCoherentOutput_l1_le_envelopeMass K a)

/-- Unconditional fusion capstone: every conservative refinement observed through two positive
kernels obeys reconstruction, nonnegativity, observer transport, and the exact interchange law. -/
theorem markedVariationDynamics_fusion_capstone [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (R : MarkedRefinement (I := I) (J := J) X) :
    (∀ z, 0 ≤ markedVariationDefect (S.comp T) R.fine z) ∧
      markedEnvelopeOutput (S.comp T) R.fine =
        (fun z => ‖markedCoherentOutput (S.comp T) R.fine z‖ +
          markedVariationDefect (S.comp T) R.fine z) ∧
      markedVariationDefect (S.comp T) R.fine =
        fun z => S.applyReal (markedVariationDefect T R.coarse) z +
          (S.comp T).applyReal (refinementExcess R) z +
          positiveObserverLoss S (markedCoherentOutput T R.coarse) z := by
  exact ⟨markedVariationDefect_nonneg (S.comp T) R.fine,
    markedEnvelope_reconstruction (S.comp T) R.fine,
    markedVariationDefect_interchange S T R⟩

end MarkedPackets

section SerialLossBudget

/-- Every scalar observer-loss ledger telescopes exactly. -/
theorem finiteObserverLoss_telescope (mass : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (mass k - mass (k + 1))) = mass 0 - mass n := by
  exact Finset.sum_range_sub' mass n

/-- A decreasing observer mass with an exact later return has accumulated no loss before that
return. -/
theorem observerLoss_zero_before_exactReturn (mass : ℕ → ℝ) (hmono : Antitone mass)
    {n k : ℕ} (hk : k < n) (hreturn : mass n = mass 0) :
    mass k - mass (k + 1) = 0 := by
  have hk0 : mass k ≤ mass 0 := hmono (Nat.zero_le k)
  have hnext : mass n ≤ mass (k + 1) := hmono (Nat.succ_le_iff.mpr hk)
  have hstep : mass (k + 1) ≤ mass k := hmono (Nat.le_succ k)
  rw [hreturn] at hnext
  linarith

/-- Macroscopic observer-loss events have a finite exact budget. -/
theorem macroscopicObserverLoss_count (mass : ℕ → ℝ) (hmono : Antitone mass)
    (ε : ℝ) (n : ℕ) :
    ε * (((Finset.range n).filter
      (fun k => ε ≤ mass k - mass (k + 1))).card : ℝ) ≤ mass 0 - mass n := by
  let large := (Finset.range n).filter (fun k => ε ≤ mass k - mass (k + 1))
  have hlarge :
      ε * (large.card : ℝ) ≤ ∑ k ∈ large, (mass k - mass (k + 1)) := by
    calc
      ε * (large.card : ℝ) = ∑ k ∈ large, ε := by simp [mul_comm]
      _ ≤ ∑ k ∈ large, (mass k - mass (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.mem_filter.mp hk |>.2
  have hsubset : large ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_filter.mp hk |>.1
  have hnonneg : ∀ k ∈ Finset.range n, k ∉ large →
      0 ≤ mass k - mass (k + 1) := by
    intro k hk hkl
    exact sub_nonneg.mpr (hmono (Nat.le_succ k))
  have hsum :
      (∑ k ∈ large, (mass k - mass (k + 1))) ≤
        ∑ k ∈ Finset.range n, (mass k - mass (k + 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  rw [finiteObserverLoss_telescope] at hsum
  exact hlarge.trans hsum

end SerialLossBudget

section GenuineCarrierDistance

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Finite positive probability carrier. -/
structure FiniteHistoryProbability (H : Type*) [Fintype H] where
  mass : H → ℝ
  nonneg : ∀ h, 0 ≤ mass h
  total : ∑ h, mass h = 1

/-- Total-variation distance of two finite history carriers. -/
def finiteHistoryTV (π ν : FiniteHistoryProbability H) : ℝ :=
  (∑ h, |π.mass h - ν.mass h|) / 2

/-- Normalized mass carried by observer-manufactured histories. -/
def finiteSpliceMass (π : FiniteHistoryProbability H) (genuine : Finset H) : ℝ :=
  ∑ h ∈ genuineᶜ, π.mass h

/-- A history carrier supported on the declared genuine sector. -/
def IsGenuineSupported (ν : FiniteHistoryProbability H) (genuine : Finset H) : Prop :=
  ∀ h ∉ genuine, ν.mass h = 0

/-- Splice mass is nonnegative. -/
theorem finiteSpliceMass_nonneg (π : FiniteHistoryProbability H) (genuine : Finset H) :
    0 ≤ finiteSpliceMass π genuine := by
  exact Finset.sum_nonneg fun h hh => π.nonneg h

/-- Every genuine-supported carrier is at least the splice mass away in total variation. -/
theorem finiteSpliceMass_le_tv (π ν : FiniteHistoryProbability H) (genuine : Finset H)
    (hν : IsGenuineSupported ν genuine) :
    finiteSpliceMass π genuine ≤ finiteHistoryTV π ν := by
  have hν_out : ∑ h ∈ genuineᶜ, ν.mass h = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    exact hν h (Finset.mem_compl.mp hh)
  have hν_in : ∑ h ∈ genuine, ν.mass h = 1 := by
    have hsplit := Finset.sum_add_sum_compl genuine ν.mass
    rw [ν.total, hν_out] at hsplit
    linarith
  have hπ_split := Finset.sum_add_sum_compl genuine π.mass
  have hπ_in :
      ∑ h ∈ genuine, π.mass h = 1 - finiteSpliceMass π genuine := by
    rw [π.total] at hπ_split
    dsimp [finiteSpliceMass]
    linarith
  have hout :
      (∑ h ∈ genuineᶜ, |π.mass h - ν.mass h|) =
        finiteSpliceMass π genuine := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hν h (Finset.mem_compl.mp hh), sub_zero, abs_of_nonneg (π.nonneg h)]
  have hinsum :
      (∑ h ∈ genuine, (π.mass h - ν.mass h)) =
        -finiteSpliceMass π genuine := by
    rw [Finset.sum_sub_distrib, hπ_in, hν_in]
    ring
  have hin :
      finiteSpliceMass π genuine ≤
        ∑ h ∈ genuine, |π.mass h - ν.mass h| := by
    have habs := Finset.abs_sum_le_sum_abs (fun h => π.mass h - ν.mass h) genuine
    rw [hinsum, abs_neg, abs_of_nonneg (finiteSpliceMass_nonneg π genuine)] at habs
    exact habs
  have htotal := Finset.sum_compl_add_sum genuine
    (fun h => |π.mass h - ν.mass h|)
  rw [hout] at htotal
  dsimp [finiteHistoryTV]
  linarith

/-- Move every splice-history mass to one marked genuine history. -/
def moveSpliceToGenuine (π : FiniteHistoryProbability H) (genuine : Finset H)
    (g₀ : H) (hg₀ : g₀ ∈ genuine) : FiniteHistoryProbability H where
  mass h :=
    if h ∈ genuine then
      π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0
    else 0
  nonneg h := by
    by_cases hg : h ∈ genuine
    · simp only [hg, if_true]
      by_cases heq : h = g₀
      · subst h
        simpa using add_nonneg (π.nonneg g₀) (finiteSpliceMass_nonneg π genuine)
      · simp [heq, π.nonneg h]
    · simp [hg]
  total := by
    calc
      (∑ h, if h ∈ genuine then
          π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0 else 0) =
          ∑ h ∈ genuine,
            (π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0) := by
              rw [Finset.sum_ite]
              simp
      _ = (∑ h ∈ genuine, π.mass h) + finiteSpliceMass π genuine := by
            rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_eq_single g₀]
            · simp
            · intro h hh hne
              simp [hne]
            · exact fun hnot => (hnot hg₀).elim
      _ = 1 := by
            have hsplit := Finset.sum_add_sum_compl genuine π.mass
            rw [π.total] at hsplit
            exact hsplit

/-- The moved-splice carrier is genuinely supported. -/
theorem moveSpliceToGenuine_supported (π : FiniteHistoryProbability H) (genuine : Finset H)
    (g₀ : H) (hg₀ : g₀ ∈ genuine) :
    IsGenuineSupported (moveSpliceToGenuine π genuine g₀ hg₀) genuine := by
  intro h hh
  change (if h ∈ genuine then
    π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0 else 0) = 0
  simp [hh]

/-- Moving all splice mass to one genuine atom attains exactly the splice-mass TV bound. -/
theorem finiteHistoryTV_moveSplice_eq (π : FiniteHistoryProbability H) (genuine : Finset H)
    (g₀ : H) (hg₀ : g₀ ∈ genuine) :
    finiteHistoryTV π (moveSpliceToGenuine π genuine g₀ hg₀) =
      finiteSpliceMass π genuine := by
  have hout :
      (∑ h ∈ genuineᶜ,
          |π.mass h - (moveSpliceToGenuine π genuine g₀ hg₀).mass h|) =
        finiteSpliceMass π genuine := by
    apply Finset.sum_congr rfl
    intro h hh
    have hnot : h ∉ genuine := Finset.mem_compl.mp hh
    have hmove : (moveSpliceToGenuine π genuine g₀ hg₀).mass h = 0 := by
      change (if h ∈ genuine then
        π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0 else 0) = 0
      simp [hnot]
    rw [hmove]
    rw [sub_zero, abs_of_nonneg (π.nonneg h)]
  have hin :
      (∑ h ∈ genuine,
          |π.mass h - (moveSpliceToGenuine π genuine g₀ hg₀).mass h|) =
        finiteSpliceMass π genuine := by
    rw [Finset.sum_eq_single g₀]
    · have hmove :
          (moveSpliceToGenuine π genuine g₀ hg₀).mass g₀ =
            π.mass g₀ + finiteSpliceMass π genuine := by
        change (if g₀ ∈ genuine then
          π.mass g₀ + if g₀ = g₀ then finiteSpliceMass π genuine else 0 else 0) =
            π.mass g₀ + finiteSpliceMass π genuine
        simp [hg₀]
      rw [hmove]
      rw [show π.mass g₀ - (π.mass g₀ + finiteSpliceMass π genuine) =
        -finiteSpliceMass π genuine by ring]
      rw [abs_neg, abs_of_nonneg (finiteSpliceMass_nonneg π genuine)]
    · intro h hh hne
      have hmove : (moveSpliceToGenuine π genuine g₀ hg₀).mass h = π.mass h := by
        change (if h ∈ genuine then
          π.mass h + if h = g₀ then finiteSpliceMass π genuine else 0 else 0) =
            π.mass h
        simp [hh, hne]
      rw [hmove, sub_self, abs_zero]
    · exact fun hnot => (hnot hg₀).elim
  have htotal := Finset.sum_compl_add_sum genuine
    (fun h => |π.mass h - (moveSpliceToGenuine π genuine g₀ hg₀).mass h|)
  rw [hout, hin] at htotal
  dsimp [finiteHistoryTV]
  linarith

/-- Exact nearest-carrier theorem without an infimum formalism: every genuine carrier is at least
the splice mass away, and a canonical marked transfer witness attains that value. -/
theorem finiteGenuineCarrier_exactDistance (π : FiniteHistoryProbability H)
    (genuine : Finset H) (g₀ : H) (hg₀ : g₀ ∈ genuine) :
    (∀ ν : FiniteHistoryProbability H,
        IsGenuineSupported ν genuine →
          finiteSpliceMass π genuine ≤ finiteHistoryTV π ν) ∧
      IsGenuineSupported (moveSpliceToGenuine π genuine g₀ hg₀) genuine ∧
      finiteHistoryTV π (moveSpliceToGenuine π genuine g₀ hg₀) =
        finiteSpliceMass π genuine := by
  exact ⟨fun ν hν => finiteSpliceMass_le_tv π ν genuine hν,
    moveSpliceToGenuine_supported π genuine g₀ hg₀,
    finiteHistoryTV_moveSplice_eq π genuine g₀ hg₀⟩

end GenuineCarrierDistance

end

end GaloisForLFunctions.HTGeometry
