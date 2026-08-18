import GaloisForLFunctions.RHTower.Sieve.LadderHarmonicSplit
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# One step of the ladder, in mean square

A step of the ladder contributes the product of a prime polynomial over a thin range and a Möbius
polynomial over the step's cofactor block.  Once the prime polynomial is bounded pointwise — which
is what cancellation in `∑_{p ∈ P_j} p^{iy}` provides — the step's mean square is that bound squared
times the mean value theorem for the cofactor polynomial, whose support is an interval.

Both inputs are separated here so that the analytic one (the twisted prime sum) enters exactly
once, as a hypothesis of the shape the corpus's Route-T layer produces.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The cofactor block of a step misses zero and lies below `B₀/Q_j`. -/
theorem geomCofactorBlockAt_bounds {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (j : ℕ) :
    (0 : ℕ) ∉ geomCofactorBlockAt A₀ B₀ Q η j
      ∧ ∀ n ∈ geomCofactorBlockAt A₀ B₀ Q η j, n ≤ ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ := by
  constructor
  · intro hc
    exact absurd (ladderGapSetAt_pos hA hQ hη j hc) (lt_irrefl 0)
  · intro n hn
    rw [geomCofactorBlockAt, Finset.mem_Icc] at hn
    exact hn.2

/-- **One step of the ladder, in mean square.**  A pointwise bound on the prime polynomial and the
mean value theorem for the cofactor polynomial. -/
theorem integral_normSq_ladderStep_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q η W V : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (hV : 0 ≤ V) (j : ℕ)
    (hbound : ∀ w ∈ Set.Icc (-W) W, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
          * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2)
      ≤ V ^ 2 * ((5 * Real.pi / 2 * W
            + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
          * ((geomCofactorBlockAt A₀ B₀ Q η j).card : ℝ)) := by
  classical
  set D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q η j with hD
  set N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ with hN
  have hcontR : Continuous fun w : ℝ => ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 :=
    ((continuous_primeBlockPoly _).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly moebiusCoeff D w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ =>
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2)
      (Set.Icc (-W) W) volume := (hcontR.mul hcontS).integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ => V ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2)
      (Set.Icc (-W) W) volume := (hcontS.const_mul _).integrableOn_Icc
  have hpt : ∀ w ∈ Set.Icc (-W) W,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2
        ≤ V ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2 := by
    intro w hw
    have hb := hbound w hw
    have h0 : (0 : ℝ) ≤ ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ := norm_nonneg _
    have hsq : ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 ≤ V ^ 2 := by nlinarith [hb, h0]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  refine hmono.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨h0, hle⟩ := geomCofactorBlockAt_bounds (A₀ := A₀) (B₀ := B₀) hA hQ hη j
  exact integral_Icc_normSq_logPoly_le_support moebiusCoeff h0 hle norm_moebiusCoeff_le_one hW

/-- The cofactor block of a step is an interval, so its size is explicit. -/
theorem card_geomCofactorBlockAt_le {A₀ B₀ : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    ((geomCofactorBlockAt A₀ B₀ Q η j).card : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) + 1 := by
  classical
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hcast : geomCofactorBlockAt A₀ B₀ Q η j
      = Finset.Icc ⌈(A₀ : ℝ) / (Qj * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Qj⌋₊ := by
    rw [geomCofactorBlockAt, hQj]
  rw [hcast]
  have hlo : (0 : ℝ) ≤ ((⌈(A₀ : ℝ) / (Qj * (1 + η))⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhi : ((⌊(B₀ : ℝ) / Qj⌋₊ : ℕ) : ℝ) ≤ (B₀ : ℝ) / Qj := Nat.floor_le (by positivity)
  rcases Nat.lt_or_ge ⌊(B₀ : ℝ) / Qj⌋₊ ⌈(A₀ : ℝ) / (Qj * (1 + η))⌉₊ with hlt | hge
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ (B₀ : ℝ) / Qj := by positivity
    linarith
  · have hval : ((Finset.Icc ⌈(A₀ : ℝ) / (Qj * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Qj⌋₊).card : ℝ)
        = ((⌊(B₀ : ℝ) / Qj⌋₊ : ℕ) : ℝ) + 1 - ((⌈(A₀ : ℝ) / (Qj * (1 + η))⌉₊ : ℕ) : ℝ) := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hval]
    linarith

end

end RHTower.Sieve
