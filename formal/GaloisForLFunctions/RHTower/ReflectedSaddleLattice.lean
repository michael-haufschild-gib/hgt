/-
The saddle lattice of the reflected AFE block.

For the negative Fourier mode `-(k+1)` at height `T > 0`, the reflected-block phase is

  `g_k(x) = -2π(k+1)x + T log x`.

Its stationary point is the exact lattice point `x*_k = T / (2π(k+1))`, and its second
derivative is `-T/x²`, independent of the mode.  This names the constraint geometry behind the
uniform-in-mode reflected-block estimate and gives a finite saddle-mode count whose parity feeds
the existing `LedgerFluxPaired` interface.
-/
import GaloisForLFunctions.RHTower.EdgeEventLedger

open Complex Real
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The reflected-block saddle for negative Fourier mode `-(k+1)` at height `T`. -/
def reflectedSaddle (T : ℝ) (k : ℕ) : ℝ :=
  T / (2 * Real.pi * ((k + 1 : ℕ) : ℝ))

/-- The reflected-block phase for negative Fourier mode `-(k+1)`: `-2π(k+1)x + T log x`. -/
def reflectedPhase (T : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) * x + T * Real.log x

/-- The first derivative of the reflected-block phase. -/
def reflectedPhaseDeriv (T : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) + T * x⁻¹

/-- The second derivative of the reflected-block phase; the mode index does not occur. -/
def reflectedPhaseSecond (T : ℝ) (_k : ℕ) (x : ℝ) : ℝ :=
  -T * (x ^ (2 : ℕ))⁻¹

/-- The reflected phase has the stated first derivative away from `0`. -/
theorem reflectedPhase_hasDerivAt {T : ℝ} {k : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (reflectedPhase T k) (reflectedPhaseDeriv T k x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) * y)
      (-(2 * Real.pi * ((k + 1 : ℕ) : ℝ))) x := by
    simpa using (hasDerivAt_id x).const_mul (-(2 * Real.pi * ((k + 1 : ℕ) : ℝ)))
  have hlog : HasDerivAt (fun y : ℝ => T * Real.log y) (T * x⁻¹) x :=
    (Real.hasDerivAt_log hx).const_mul T
  change HasDerivAt
    (fun y : ℝ => -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) * y + T * Real.log y)
    (-(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) + T * x⁻¹) x
  exact hlin.add hlog

/-- The reflected phase derivative has second derivative `-T/x²`, independent of the mode. -/
theorem reflectedPhaseDeriv_hasDerivAt {T : ℝ} {k : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (reflectedPhaseDeriv T k) (reflectedPhaseSecond T k x) x := by
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ (2 : ℕ))⁻¹) x := hasDerivAt_inv hx
  have hT : HasDerivAt (fun y : ℝ => T * y⁻¹) (T * (-(x ^ (2 : ℕ))⁻¹)) x := hinv.const_mul T
  have hconst : HasDerivAt (fun _y : ℝ => -(2 * Real.pi * ((k + 1 : ℕ) : ℝ))) 0 x :=
    hasDerivAt_const x _
  convert! hconst.add hT using 1
  simp [reflectedPhaseSecond, mul_neg]

/-- The reflected-block curvature is independent of the Fourier mode. -/
theorem reflectedPhaseSecond_independent (T : ℝ) (k l : ℕ) (x : ℝ) :
    reflectedPhaseSecond T k x = reflectedPhaseSecond T l x := rfl

/-- At positive height the reflected saddle lies on the positive real axis. -/
theorem reflected_saddle_pos {T : ℝ} {k : ℕ} (hT : 0 < T) :
    0 < reflectedSaddle T k := by
  unfold reflectedSaddle
  positivity

/-- The reflected phase derivative vanishes at its saddle. -/
theorem reflectedPhaseDeriv_saddle_eq_zero {T : ℝ} (hT : 0 < T) (k : ℕ) :
    reflectedPhaseDeriv T k (reflectedSaddle T k) = 0 := by
  unfold reflectedPhaseDeriv reflectedSaddle
  have hden : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hTne : T ≠ 0 := hT.ne'
  field_simp [hden, hTne]
  ring

/-- The stationary point of the reflected phase is exactly the saddle lattice point. -/
theorem reflectedPhaseDeriv_eq_zero_iff {T : ℝ} {k : ℕ} {x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    reflectedPhaseDeriv T k x = 0 ↔ x = reflectedSaddle T k := by
  unfold reflectedPhaseDeriv reflectedSaddle
  have hApos : 0 < 2 * Real.pi * ((k + 1 : ℕ) : ℝ) := by positivity
  have hA : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) ≠ 0 := hApos.ne'
  constructor
  · intro h
    have hxne : x ≠ 0 := hx.ne'
    field_simp [hxne, hA] at h ⊢
    linarith
  · intro h
    rw [h]
    exact reflectedPhaseDeriv_saddle_eq_zero hT k

/-- The finite set of reflected saddle modes, cut off at `K`, whose saddles lie in `[a,b]`. -/
def reflectedSaddleModes (K : ℕ) (T a b : ℝ) : Finset ℕ :=
  (Finset.range K).filter fun k => a ≤ reflectedSaddle T k ∧ reflectedSaddle T k ≤ b

/-- The unit event list carried by a finite reflected saddle-mode set. -/
def reflectedSaddleFluxList (K : ℕ) (T a b : ℝ) : List ℤ :=
  List.replicate (reflectedSaddleModes K T a b).card 1

/-- The saddle-flux list has sum equal to the saddle-mode count. -/
theorem reflectedSaddleFluxList_sum (K : ℕ) (T a b : ℝ) :
    (reflectedSaddleFluxList K T a b).sum = (reflectedSaddleModes K T a b).card := by
  simp [reflectedSaddleFluxList]

/-- Even reflected saddle-mode count supplies the paired-flux interface. -/
theorem reflectedSaddleFluxPaired_of_even {K : ℕ} {T a b : ℝ}
    (hEven : Even (reflectedSaddleModes K T a b).card) :
    LedgerFluxPaired (reflectedSaddleFluxList K T a b) := by
  rw [reflectedSaddleFluxList]
  exact ledgerFluxPaired_replicate_one
    (nonempty_bandEdgePairing_of_even hEven.two_dvd)

/-- Even reflected saddle-mode count gives an even total unit flux. -/
theorem reflectedSaddleFluxList_two_dvd_sum_of_even {K : ℕ} {T a b : ℝ}
    (hEven : Even (reflectedSaddleModes K T a b).card) :
    (2 : ℤ) ∣ (reflectedSaddleFluxList K T a b).sum := by
  exact ledgerFluxPaired_two_dvd_sum (reflectedSaddleFluxPaired_of_even hEven)

end RHTower
