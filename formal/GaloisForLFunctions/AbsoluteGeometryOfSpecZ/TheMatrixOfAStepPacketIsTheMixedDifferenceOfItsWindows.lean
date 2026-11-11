import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets

/-!
# The matrix of a step packet is the mixed difference of its windows

Weil's form `𝔚_Q` of the step packet with the values `σ_j` on the blocks `(R + j, R + j + 1]` is a
quadratic form in `σ`. Its matrix is read off the values of `𝔚_Q` on single windows: with

  `w(j, l) = 𝔚_Q(flat packet of the window between R + j and R + l)`  (`windowValue`),

symmetric and zero for `j = l`, the entry of the blocks `j` and `l` is half the mixed second
difference

  `m(j, l) = ½ (w(j, l + 1) + w(j + 1, l) − w(j, l) − w(j + 1, l + 1))`  (`blockEntry`),

and `𝔚_Q(step packet) = Σ_{j, l < J} σ_j σ_l m(j, l)` (`packetForm_stepPacket_eq_sum_blockEntry`).
On the diagonal `m(j, j) = w(j, j + 1)`. The proof is summation by parts in both variables.

The window values are elementary (`windowValue_eq`): for `a = R + j < b = R + l`,

  `w = 2(b − a) log(b/a) − [(b − a)(γ + log 2π) + (b + a) log 2 + 2a log a
        − (b + a) log(b + a) + (b − a) log(b − a)] − 2 Σ_{k ≤ Q} Λ(k)(b/k − a)⁺`:

the pole term, the jets, and the contacts of the window with itself.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Summation by parts in both variables -/

/-- A quadratic form in the nested coefficients of a step function is the form of the mixed
second differences in its values. -/
theorem sum_sum_nestedCoeff_eq (J : ℕ) (σ : ℕ → ℝ) (E : ℕ → ℕ → ℝ) :
    ∑ j ∈ range (J + 1), ∑ l ∈ range (J + 1), nestedCoeff J σ j * nestedCoeff J σ l * E j l =
      ∑ j ∈ range J, ∑ l ∈ range J,
        σ j * σ l * (E (j + 1) (l + 1) - E (j + 1) l - E j (l + 1) + E j l) := by
  have hrow : ∀ j, ∑ l ∈ range (J + 1), nestedCoeff J σ j * nestedCoeff J σ l * E j l =
      nestedCoeff J σ j * ∑ l ∈ range J, σ l * (E j (l + 1) - E j l) := fun j => by
    rw [sum_mul_sub_eq_nested J σ fun l => E j l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun j _ => hrow j,
    ← sum_mul_sub_eq_nested J σ fun j => ∑ l ∈ range J, σ l * (E j (l + 1) - E j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ### Window values and the entries -/

/-- Weil's form `𝔚_Q` of the flat packet of the window between the block ends `R + j` and
`R + l`. -/
def windowValue (Q R j l : ℕ) : ℝ :=
  packetForm Q (flatPacket ((min (R + j) (R + l) : ℕ) : ℝ) ((max (R + j) (R + l) : ℕ) : ℝ))

theorem windowValue_comm (Q R j l : ℕ) : windowValue Q R j l = windowValue Q R l j := by
  rw [windowValue, windowValue, min_comm, max_comm]

theorem windowValue_self (Q R j : ℕ) : windowValue Q R j j = 0 := by
  rw [windowValue, min_self, max_self, flatPacket_self, packetForm_zero]

theorem windowValue_zero_left (Q R j : ℕ) :
    windowValue Q R 0 j = packetForm Q (flatPacket (R : ℝ) ((R + j : ℕ) : ℝ)) := by
  rw [windowValue, Nat.add_zero, min_eq_left (Nat.le_add_right R j),
    max_eq_right (Nat.le_add_right R j)]

/-- The entry of the blocks `j` and `l` in the matrix of `𝔚_Q` on step packets: half the mixed
second difference of the window values. -/
def blockEntry (Q R j l : ℕ) : ℝ :=
  (windowValue Q R j (l + 1) + windowValue Q R (j + 1) l - windowValue Q R j l -
    windowValue Q R (j + 1) (l + 1)) / 2

theorem blockEntry_comm (Q R j l : ℕ) : blockEntry Q R j l = blockEntry Q R l j := by
  rw [blockEntry, blockEntry, windowValue_comm Q R j (l + 1), windowValue_comm Q R (j + 1) l,
    windowValue_comm Q R j l, windowValue_comm Q R (j + 1) (l + 1)]
  ring

/-- On the diagonal the entry is the form of the flat packet of one block. -/
theorem blockEntry_self (Q R j : ℕ) : blockEntry Q R j j = windowValue Q R j (j + 1) := by
  rw [blockEntry, windowValue_comm Q R (j + 1) j, windowValue_self, windowValue_self]
  ring

/-- **The matrix of a step packet.** Weil's form of the step packet with the values `σ_j` on
the `J` blocks above `R` is the quadratic form with the entries `blockEntry`. -/
theorem packetForm_stepPacket_eq_sum_blockEntry {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ) (σ : ℕ → ℝ) :
    packetForm Q (stepPacket R J σ) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockEntry Q R j l := by
  have hE : ∀ j l, stepEntry Q R (fun j => R + j) j l =
      windowValue Q R 0 j + windowValue Q R 0 l - windowValue Q R j l := fun j l => by
    rw [windowValue_zero_left, windowValue_zero_left, windowValue, Nat.cast_min, Nat.cast_max]
    rfl
  rw [stepPacket_eq_nested hR J σ,
    packetForm_nested_eq (x := fun j => R + j) hR (nested_bounds R J) (nestedCoeff J σ)]
  simp only [hE]
  rw [sum_sum_nestedCoeff_eq J σ fun j l =>
    windowValue Q R 0 j + windowValue Q R 0 l - windowValue Q R j l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [blockEntry]
  ring

/-! ### The window values are elementary -/

/-- The finite part of the jets inside the window `(a, b]`, per degree point of the scale. -/
theorem flatPairing_window {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    flatPairing b b - 2 * flatPairing a b + flatPairing a a =
      ((b : ℝ) - a) * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) +
        ((b : ℝ) + a) * Real.log 2 + 2 * a * Real.log a -
        ((b : ℝ) + a) * Real.log ((b : ℝ) + a) + ((b : ℝ) - a) * Real.log ((b : ℝ) - a) := by
  have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 2 * Real.pi) (by norm_num) (by positivity)]
  rw [flatPairing_self (ha.trans hab.le), flatPairing_self ha, flatPairing, h4]
  ring

/-- **The value of a window**: pole term, jets and contacts in closed form. -/
theorem windowValue_eq {R j l : ℕ} (hR : 1 ≤ R) (hjl : j < l) (Q : ℕ) :
    windowValue Q R j l =
      2 * ((Real.log ((R + l : ℕ) : ℝ) - Real.log ((R + j : ℕ) : ℝ)) *
          (((R + l : ℕ) : ℝ) - ((R + j : ℕ) : ℝ))) -
        ((((R + l : ℕ) : ℝ) - ((R + j : ℕ) : ℝ)) *
            (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) +
          (((R + l : ℕ) : ℝ) + ((R + j : ℕ) : ℝ)) * Real.log 2 +
          2 * ((R + j : ℕ) : ℝ) * Real.log ((R + j : ℕ) : ℝ) -
          (((R + l : ℕ) : ℝ) + ((R + j : ℕ) : ℝ)) *
            Real.log (((R + l : ℕ) : ℝ) + ((R + j : ℕ) : ℝ)) +
          (((R + l : ℕ) : ℝ) - ((R + j : ℕ) : ℝ)) *
            Real.log (((R + l : ℕ) : ℝ) - ((R + j : ℕ) : ℝ))) -
        2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((((R + l : ℕ) : ℝ)) / k - ((R + j : ℕ) : ℝ)) 0 := by
  have hlt : R + j < R + l := by omega
  rw [windowValue, min_eq_left hlt.le, max_eq_right hlt.le,
    packetForm_flatPacket_eq (by omega) hlt Q, flatPairing_window (by omega) hlt]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
