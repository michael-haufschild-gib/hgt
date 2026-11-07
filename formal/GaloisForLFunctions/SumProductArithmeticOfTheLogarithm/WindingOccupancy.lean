import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.LogarithmicCollisionCells

/-!
# The winding occupation of consecutive phase level sets

If `n` and `n+1` lie in prescribed phase arcs, two pair sums of their
integer windings encode an unordered pair at sufficiently fine resolution.
Thus a set of `M` such integers needs at least `M²/2` winding signatures.
This retains the information discarded by circle-valued moments.
-/

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset

/-- Nearest integer lift of the phase relative to an arc centre. -/
def logWinding (t θ : ℝ) (n : ℕ) : ℤ :=
  ⌊(t * Real.log n - θ) / (2 * Real.pi) + 1 / 2⌋

/-- Signed distance to the chosen real lift of an arc centre. -/
def phaseRemainder (t θ : ℝ) (n : ℕ) : ℝ :=
  t * Real.log n - θ - 2 * Real.pi * logWinding t θ n

/-- Integers whose phases and successor phases lie in two specified arcs. -/
def consecutiveArcSet (N : ℕ) (t ε θ η : ℝ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter fun n =>
    |phaseRemainder t θ n| ≤ ε ∧ |phaseRemainder t η (n + 1)| ≤ ε

/-- Two pair sums of integer windings, before and after translation. -/
def windingSignature (t θ η : ℝ) (p : ℕ × ℕ) : ℤ × ℤ :=
  (logWinding t θ p.1 + logWinding t θ p.2,
    logWinding t η (p.1 + 1) + logWinding t η (p.2 + 1))

private theorem product_cell_bound {a b : ℕ} {t ε θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (har : |phaseRemainder t θ a| ≤ ε) (hbr : |phaseRemainder t θ b| ≤ ε) :
    |t * Real.log (a * b : ℕ) -
      (2 * θ + 2 * Real.pi * ((logWinding t θ a + logWinding t θ b : ℤ) : ℝ))| ≤
      2 * ε := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : t * Real.log (a * b : ℕ) -
      (2 * θ + 2 * Real.pi * ((logWinding t θ a + logWinding t θ b : ℤ) : ℝ)) =
      phaseRemainder t θ a + phaseRemainder t θ b := by
    rw [Nat.cast_mul, Real.log_mul ha' hb']
    simp only [phaseRemainder, Int.cast_add]
    ring
  rw [he]
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp har).1, (abs_le.mp hbr).1],
    by linarith only [(abs_le.mp har).2, (abs_le.mp hbr).2]⟩

/-- A winding signature specifies a real cell of radius `2ε`. -/
theorem arc_pair_mem_logPairCell {N a b : ℕ} {t ε θ η : ℝ}
    (ha : a ∈ consecutiveArcSet N t ε θ η)
    (hb : b ∈ consecutiveArcSet N t ε θ η) :
    (a, b) ∈ logPairCell N t (2 * ε)
      (2 * θ + 2 * Real.pi * (windingSignature t θ η (a, b)).1)
      (2 * η + 2 * Real.pi * (windingSignature t θ η (a, b)).2) := by
  classical
  obtain ⟨haN, haθ, haη⟩ := mem_filter.mp ha
  obtain ⟨hbN, hbθ, hbη⟩ := mem_filter.mp hb
  refine mem_filter.mpr ⟨mem_product.mpr ⟨haN, hbN⟩, ?_⟩
  constructor
  · exact product_cell_bound (mem_Icc.mp haN).1 (mem_Icc.mp hbN).1 haθ hbθ
  · exact product_cell_bound (Nat.succ_pos a) (Nat.succ_pos b) haη hbη

/-- No winding signature contains more than two ordered pairs at this resolution. -/
theorem card_winding_fibre_le_two (N : ℕ) (t ε θ η : ℝ) (w : ℤ × ℤ)
    (hres : 4 * ε * ((N + 1 : ℕ) : ℝ) ^ 2 < |t|) :
    (((consecutiveArcSet N t ε θ η) ×ˢ (consecutiveArcSet N t ε θ η)).filter
      fun p => windingSignature t θ η p = w).card ≤ 2 := by
  classical
  have hsub :
      (((consecutiveArcSet N t ε θ η) ×ˢ (consecutiveArcSet N t ε θ η)).filter
        fun p => windingSignature t θ η p = w) ⊆
      logPairCell N t (2 * ε) (2 * θ + 2 * Real.pi * w.1)
        (2 * η + 2 * Real.pi * w.2) := by
    rintro ⟨a, b⟩ hp
    obtain ⟨hpA, hpw⟩ := mem_filter.mp hp
    obtain ⟨ha, hb⟩ := mem_product.mp hpA
    have h := arc_pair_mem_logPairCell ha hb
    rwa [hpw] at h
  refine (card_le_card hsub).trans (card_logPairCell_le_two _ _ _ _ _ ?_)
  nlinarith only [hres]

/-- Fine simultaneous arcs force quadratically many distinct winding signatures. -/
theorem card_sq_le_two_mul_windingSignatures (N : ℕ) (t ε θ η : ℝ)
    (hres : 4 * ε * ((N + 1 : ℕ) : ℝ) ^ 2 < |t|) :
    (consecutiveArcSet N t ε θ η).card ^ 2 ≤
      2 * (((consecutiveArcSet N t ε θ η) ×ˢ (consecutiveArcSet N t ε θ η)).image
        (windingSignature t θ η)).card := by
  classical
  have h := card_le_mul_card_image
    ((consecutiveArcSet N t ε θ η) ×ˢ (consecutiveArcSet N t ε θ η)) 2
    (fun w _ => card_winding_fibre_le_two N t ε θ η w hres)
  simpa only [card_product, pow_two] using h

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
