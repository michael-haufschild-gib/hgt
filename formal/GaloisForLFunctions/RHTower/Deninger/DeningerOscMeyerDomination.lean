import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerOscDomination

/-!
# Each two-sided oscillator seminorm is dominated by a finite supremum of Meyer seminorms

The converse comparison.  A single oscillator seminorm is bounded by finitely many Schwartz
seminorms of the weighted cochain, and each of those is bounded by Meyer seminorms at exponent
`K+1`.

* `deningerFinsetSup_apply_le` : a pointwise bound for a finite supremum of seminorms.
* `deningerTwoSidedOsc_le_meyerSup` : **`Q_m(w_K \cdot) \le C\,\sup_{s} q`.**
-/

namespace RHTower

open SchwartzMap GaloisForLFunctions

noncomputable section

/-- A finite supremum of seminorms is bounded at a point by any common bound. -/
theorem deningerFinsetSup_apply_le {𝕜 E ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i ∈ s, p i x ≤ C) : (s.sup p) x ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sup_insert, Seminorm.sup_apply]
    refine max_le (hb a (Finset.mem_insert_self a s)) ?_
    exact ih fun i hi => hb i (Finset.mem_insert_of_mem hi)

/-- **Each two-sided oscillator seminorm is dominated by a finite supremum of Meyer seminorms.** -/
theorem deningerTwoSidedOsc_le_meyerSup (K m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ h : DeningerExpSchwartz,
      deningerTwoSidedOscFamily (K, m) h
        ≤ C * (s.sup (fun i : ℕ × ℕ => deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2)) h := by
  classical
  obtain ⟨s₀, C₀, hC₀ne, hC₀⟩ := shiftedSeminorm_le_schwartzSup m
  set B : ℕ := s₀.sup (fun i : ℕ × ℕ => i.2) with hB
  set s : Finset (ℕ × ℕ) := (Finset.range (B + 1)).image (fun i => (K + 1, i)) with hs
  set E : ℝ := ∑ i ∈ s₀, 2 * (Nat.factorial i.1 : ℝ)
      * ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) * (K : ℝ) ^ j with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨s, (C₀ : ℝ) * (E * ((B : ℝ) + 1)), by positivity, fun h => ?_⟩
  set w : 𝓢(ℝ, ℂ) := ((deningerTwoSidedMul (K : ℝ) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hw
  set Q : ℝ := (s.sup (fun i : ℕ × ℕ => deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2)) h with hQ
  have hQnn : 0 ≤ Q := apply_nonneg _ _
  -- every Meyer seminorm at exponent `K+1` and order at most `B` is below the supremum
  have hone : ∀ i' : ℕ, i' ≤ B → deningerMeyerSeminormFun ((K : ℝ) + 1) i' h ≤ Q := by
    intro i' hi'
    have hmem : ((K + 1 : ℕ), i') ∈ s :=
      Finset.mem_image.2 ⟨i', Finset.mem_range.2 (Nat.lt_succ_of_le hi'), rfl⟩
    have hsup := Finset.le_sup
      (f := fun i : ℕ × ℕ => deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2) hmem
    have hval := hsup h
    have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hval
    exact hval
  have hsch : ∀ i ∈ s₀, (schwartzSeminormFamily ℂ ℝ ℂ) i w ≤ (E * ((B : ℝ) + 1)) * Q := by
    intro i hi
    have hiB : i.2 ≤ B := Finset.le_sup (f := fun j : ℕ × ℕ => j.2) hi
    have hbound := deningerTwoSidedWeighted_schwartzSeminorm_bound K i.1 i.2 h
    have hterm : (2 * (Nat.factorial i.1 : ℝ)
        * ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) * (K : ℝ) ^ j) ≤ E :=
      Finset.single_le_sum
        (f := fun i : ℕ × ℕ => 2 * (Nat.factorial i.1 : ℝ)
          * ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) * (K : ℝ) ^ j)
        (fun i _ => by positivity) hi
    have hmey : ∑ i' ∈ Finset.range (i.2 + 1),
        deningerMeyerSeminormFun ((K : ℝ) + 1) i' h ≤ ((B : ℝ) + 1) * Q := by
      have hstep : ∀ i' ∈ Finset.range (i.2 + 1),
          deningerMeyerSeminormFun ((K : ℝ) + 1) i' h ≤ Q := by
        intro i' hi'
        exact hone i' (le_trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi')) hiB)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hQnn
      have : (i.2 : ℝ) + 1 ≤ (B : ℝ) + 1 := by
        have : (i.2 : ℝ) ≤ (B : ℝ) := Nat.cast_le.2 hiB
        linarith
      push_cast
      linarith
    calc (schwartzSeminormFamily ℂ ℝ ℂ) i w
        ≤ (2 * (Nat.factorial i.1 : ℝ)
            * ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) * (K : ℝ) ^ j)
          * ∑ i' ∈ Finset.range (i.2 + 1), deningerMeyerSeminormFun ((K : ℝ) + 1) i' h :=
          hbound
      _ ≤ E * (((B : ℝ) + 1) * Q) := by
          refine mul_le_mul hterm hmey (Finset.sum_nonneg fun i' _ =>
            deningerMeyerSeminormFun_nonneg _ i' h) hEnn
      _ = (E * ((B : ℝ) + 1)) * Q := by ring
  have hsupw : (s₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w ≤ (E * ((B : ℝ) + 1)) * Q :=
    deningerFinsetSup_apply_le _ s₀ w (by positivity) hsch
  have hshift : shiftedSeminorm m w ≤ (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w := by
    have := hC₀ w
    simpa [NNReal.smul_def] using this
  have hfinal : deningerTwoSidedOscFamily (K, m) h = shiftedSeminorm m w := rfl
  rw [hfinal]
  calc shiftedSeminorm m w
      ≤ (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w := hshift
    _ ≤ (C₀ : ℝ) * ((E * ((B : ℝ) + 1)) * Q) :=
        mul_le_mul_of_nonneg_left hsupw (by positivity)
    _ = (C₀ : ℝ) * (E * ((B : ℝ) + 1)) * Q := by ring

end

end RHTower
