import GaloisForLFunctions.RHTower.ZetaCriticalInteriorRows

/-!
# The critical-scale anti-crystal law

**Theorem** (`false_of_critical_facts`). Let `T` be large, `L = log T`, and assume the zeros of
`ζ` are `10⁶⁰/L`-rigid on `[T^{1/2}, T³]`. Also assume four inputs at this height:
* Montgomery's averaged pair form `P = ∫Λ₁(β) F(T^{1/8 + β/16}, T) dβ` has `Re P ≥ TL/(32π)`;
* the explicit-formula bound for the narrow mass holds on `[3T^{1/2} − 1, T + 1]`;
* the low pairs and the edge rows are each `≤ TL/1000`;
* `#{0 < γ ≤ T} ≤ TL/5`.

These are contradictory. Rigidity puts every zero on the line in the window and splits
`P = Σ_low + Σ_{n ∈ I} Ψ_n`. The interior rows sum to
`≤ 10⁻⁴ #I + TL/20000` (`sum_norm_critRow_interior_le`). Hence
`TL/(32π) ≤ Re P ≤ TL (2/1000 + 1/50000 + 1/20000)`, which is false.
-/

noncomputable section

open Complex Finset

namespace RHTower

/-- The edge indices: `I` minus the interior indices. -/
def edgeIndices (T : ℝ) : Finset ℕ := bulkIndices (3 * T ^ (1 / 2 : ℝ)) T \ interiorIndices T

/-- The low copies `0 < γ < 3T^{1/2}`. -/
def lowCopies (T : ℝ) : Finset XiZeroCopy :=
  (zeroWindow T).filter (fun q : XiZeroCopy => ¬ 3 * T ^ (1 / 2 : ℝ) ≤ (q.1 : ℂ).im)

/-- Strict increase on the rigid window puts the window zeros on the critical line. -/
theorem re_eq_half_of_rigidWindow {h T : ℝ} (hrig : RigidWindow h T) {q : XiZeroCopy}
    (h1 : T ^ (1 / 2 : ℝ) ≤ (q.1 : ℂ).im) (h2 : (q.1 : ℂ).im ≤ T ^ 3) (h0 : 0 < (q.1 : ℂ).im) :
    (q.1 : ℂ).re = 1 / 2 :=
  re_eq_half_of_strict_window (fun k hk1 hk2 => (hrig k hk1 hk2).1)
    (xi_xiZeroCopy_eq_zero q) h1 h2 h0

/-- The bulk indices inject into the zero window. -/
theorem card_bulkIndices_le (Y T : ℝ) :
    (bulkIndices Y T).card ≤ (zeroWindow T).card := by
  have h := filter_zeroWindow_eq_map_bulkIndices Y T
  have h2 := congrArg Finset.card h
  rw [Finset.card_map] at h2
  rw [← h2]
  exact Finset.card_filter_le _ _

/-- **The edge rows.** -/
theorem norm_sum_edge_le (T : ℝ) :
    ‖∑ n ∈ edgeIndices T,
        critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      (edgeIndices T).card * (4 * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ fun n hn => ?_).trans (by rw [nsmul_eq_mul])
  refine (norm_critRow_le_lorentzMass _ _ _ n).trans ?_
  gcongr
  refine (lorentzMass_le_log _).trans ?_
  have hn' := (Finset.mem_sdiff.mp hn).1
  rw [mem_bulkIndices] at hn'
  have hpos := xiOrderedPositiveOrdinate_pos n
  rw [abs_of_pos hpos]
  gcongr
  exact hn'.2

/-- **The deterministic contradiction**, from the bounds on the pieces of `P`. -/
theorem false_of_critical_bounds {T E₀ : ℝ} (hT1 : 1 ≤ T) (hL : 10 ^ 25 ≤ Real.log T)
    (hM : (1 - 1 / 2) * ((T / (2 * Real.pi)) * (1 / 8 * Real.log T)) ≤
      (averagedMontgomeryForm (1 / 8) 16 T).re)
    (hlow : 2 * ((lowCopies T).card : ℝ) *
      (8 * T ^ (1 / 8 : ℝ) * Real.exp (Real.log T / 16) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000)
    (hedge : ((edgeIndices T).card : ℝ) *
      (4 * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000)
    (hcount : ((zeroWindow T).card : ℝ) ≤ T * Real.log T / 5)
    (hRH : ∀ n ∈ bulkIndices (3 * T ^ (1 / 2 : ℝ)) T,
      ((xiOrderedPositiveZeroCopy n).1 : ℂ).re = 1 / 2)
    (hE₀ : E₀ ≤ T * Real.log T / 200)
    (hint : ∑ n ∈ interiorIndices T,
        ‖critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      1 / 10000 * (interiorIndices T).card + T * Real.log T / 20000 + E₀) : False := by
  classical
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hT0 : 0 < T := by linarith
  set Y := 3 * T ^ (1 / 2 : ℝ) with hY
  set I := bulkIndices Y T with hI
  set Ψ := fun n => critRow (L / 8) (L / 16) I n with hΨ
  -- `P` minus the bulk
  have hP := averagedMontgomeryForm_eq_sum_pairTerm (α₀ := 1 / 8) (R := 16) hT0
  have hbulk := sum_bulk_pairTerm_eq (α₀ := 1 / 8) (R := 16) (Y := Y) hT0 hRH
  have hθ : (1 / 8 : ℝ) * Real.log T = L / 8 := by rw [hLdef]; ring
  rw [hθ] at hbulk
  have hlowP := norm_sum_sub_bulk_le (α₀ := 1 / 8) (R := 16) (Y := Y) hT1 (by norm_num)
    (by norm_num)
  rw [hbulk, ← hP] at hlowP
  -- the split of the bulk sum
  have hsplit : ∑ n ∈ I, Ψ n = ∑ n ∈ interiorIndices T, Ψ n + ∑ n ∈ edgeIndices T, Ψ n := by
    rw [edgeIndices, ← hY, ← hI, add_comm]
    exact (Finset.sum_sdiff (Finset.filter_subset _ _)).symm
  have hedge' := norm_sum_edge_le T
  have hcardI : ((interiorIndices T).card : ℝ) ≤ T * L / 5 := by
    have h1 : (interiorIndices T).card ≤ I.card := Finset.card_filter_le _ _
    have h2 := card_bulkIndices_le Y T
    have : ((interiorIndices T).card : ℝ) ≤ (zeroWindow T).card := by exact_mod_cast h1.trans h2
    linarith
  have hnormP : ‖averagedMontgomeryForm (1 / 8) 16 T‖ ≤
      T * L / 1000 + T * L / 1000 + (1 / 10000 * (T * L / 5) + T * L / 20000 + T * L / 200) := by
    have e : averagedMontgomeryForm (1 / 8) 16 T =
        (averagedMontgomeryForm (1 / 8) 16 T - ∑ n ∈ I, Ψ n) +
          ∑ n ∈ edgeIndices T, Ψ n + ∑ n ∈ interiorIndices T, Ψ n := by
      rw [hsplit]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have hA : ‖averagedMontgomeryForm (1 / 8) 16 T - ∑ n ∈ I, Ψ n +
        ∑ n ∈ edgeIndices T, Ψ n‖ ≤ T * L / 1000 + T * L / 1000 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine hlowP.trans ?_
        unfold lowCopies at hlow
        rw [← hY] at hlow
        exact hlow
      · exact hedge'.trans hedge
    have hB : ‖∑ n ∈ interiorIndices T, Ψ n‖ ≤
        1 / 10000 * (T * L / 5) + T * L / 20000 + T * L / 200 := by
      refine (norm_sum_le _ _).trans (hint.trans ?_)
      have : 1 / 10000 * ((interiorIndices T).card : ℝ) ≤ 1 / 10000 * (T * L / 5) := by gcongr
      linarith
    linarith
  have hre := (Complex.re_le_norm _).trans hnormP
  have hπ := Real.pi_lt_d2
  have hTL : 0 < T * L := by positivity
  have h1 : (1 - 1 / 2) * (T / (2 * Real.pi) * (1 / 8 * L)) = T * L / (32 * Real.pi) := by
    field_simp; ring
  rw [h1] at hM
  have h2 : T * L / (32 * (315 / 100)) ≤ T * L / (32 * Real.pi) := by
    gcongr
    linarith
  have h3 := h2.trans (hM.trans hre)
  set a := T * L with ha
  have : a / (32 * (315 / 100)) -
      (a / 1000 + a / 1000 + (1 / 10000 * (a / 5) + a / 20000 + a / 200)) =
      a * (1 / (32 * (315 / 100)) - 707 / 100000) := by ring
  have h5 : 0 < a * (1 / (32 * (315 / 100)) - 707 / 100000) :=
    mul_pos hTL (by norm_num)
  linarith

/-- **The deterministic contradiction.** -/
theorem false_of_critical_facts {T x : ℝ} (hT1 : 1 ≤ T) (hL : 10 ^ 25 ≤ Real.log T)
    (hx1 : 1 < x) (hlx : Real.log x = Real.log T / 20)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (hlen : (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) ≤ 2 * T)
    (hM : (1 - 1 / 2) * ((T / (2 * Real.pi)) * (1 / 8 * Real.log T)) ≤
      (averagedMontgomeryForm (1 / 8) 16 T).re)
    (hlow : 2 * ((lowCopies T).card : ℝ) *
      (8 * T ^ (1 / 8 : ℝ) * Real.exp (Real.log T / 16) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000)
    (hedge : ((edgeIndices T).card : ℝ) *
      (4 * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000)
    (hcount : ((zeroWindow T).card : ℝ) ≤ T * Real.log T / 5)
    (hrig : RigidWindow (10 ^ 60 / Real.log T) T) : False := by
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (by norm_num) hL
  have hs := crit_rpow_half_ge hT1 hL
  have hsT : T ^ (1 / 2 : ℝ) ≤ T := by
    calc T ^ (1 / 2 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  have hT3 : T ≤ T ^ 3 := by
    have : 1 ≤ T * T := by nlinarith
    nlinarith
  have hRH : ∀ n ∈ bulkIndices (3 * T ^ (1 / 2 : ℝ)) T,
      ((xiOrderedPositiveZeroCopy n).1 : ℂ).re = 1 / 2 := by
    intro n hn
    rw [mem_bulkIndices] at hn
    have him := xiOrderedPositiveZeroCopy_im_eq n
    exact re_eq_half_of_rigidWindow hrig (by rw [him]; nlinarith) (by rw [him]; linarith)
      (by rw [him]; exact xiOrderedPositiveOrdinate_pos n)
  exact false_of_critical_bounds (E₀ := 0) hT1 hL hM hlow hedge hcount hRH (by positivity)
    (by simpa using sum_norm_critRow_interior_le hT1 hL hx1 hlx hV hW hrig hlen)

end RHTower
