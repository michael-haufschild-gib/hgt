import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFromTwoSided

/-!
# Each Meyer seminorm is dominated by a two-sided oscillator seminorm

The pointwise estimate of the previous step becomes a seminorm estimate once the derivatives of
`w_K h` are read off finitely many Schwartz seminorms and those are collapsed into a single
oscillator seminorm.

* `deningerMeyerSeminorm_le_twoSidedShifted` : **`q_{K,n} ≤ C\,Q_m(w_K \cdot)`.**
-/

namespace RHTower

open SchwartzMap GaloisForLFunctions

noncomputable section

/-- **Each Meyer seminorm is bounded by one oscillator seminorm of the weighted cochain.** -/
theorem deningerMeyerSeminorm_le_twoSidedShifted {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ h : DeningerExpSchwartz,
      deningerMeyerSeminormFun K n h
        ≤ C * shiftedSeminorm m ((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := by
  classical
  obtain ⟨C₀, hC₀, hbd⟩ := deningerMeyerWeight_le_twoSidedDeriv hK n
  set s : Finset (ℕ × ℕ) := (Finset.range (n + 1)).image (fun m => ((0 : ℕ), m)) with hs
  obtain ⟨m, C₁, hC₁, hb⟩ := schwartzSup_le_shiftedSeminorm s
  refine ⟨m, C₀ * ((n : ℝ) + 1) * C₁, by positivity, fun h => ?_⟩
  set w : 𝓢(ℝ, ℂ) := ((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hw
  refine deningerMeyerSeminormFun_le fun t => ?_
  rw [deningerMeyerWeight]
  refine le_trans (hbd h t) ?_
  -- every derivative of the weighted cochain is read off the Schwartz sup
  have hterm : ∀ m' ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ m' (w : ℝ → ℂ) t‖
        ≤ (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w := by
    intro m' hm'
    have hle : ‖iteratedFDeriv ℝ m' (w : ℝ → ℂ) t‖
        ≤ SchwartzMap.seminorm ℂ 0 m' w := by
      have := SchwartzMap.le_seminorm ℂ 0 m' w t
      simpa using this
    refine le_trans hle ?_
    have hmem : ((0 : ℕ), m') ∈ s := Finset.mem_image.2 ⟨m', hm', rfl⟩
    have hsup := Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) hmem
    exact hsup w
  have hsum : ∑ m' ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ m' (w : ℝ → ℂ) t‖
      ≤ ((n : ℝ) + 1) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w := by
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc C₀ * ∑ m' ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ m' (w : ℝ → ℂ) t‖
      ≤ C₀ * (((n : ℝ) + 1) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w) :=
        mul_le_mul_of_nonneg_left hsum hC₀
    _ ≤ C₀ * (((n : ℝ) + 1) * (C₁ * shiftedSeminorm m w)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb w) (by positivity)) hC₀
    _ = C₀ * ((n : ℝ) + 1) * C₁ * shiftedSeminorm m w := by ring

/-- **The Meyer seminorms are monotone in the exponent.** -/
theorem deningerMeyerSeminormFun_mono {A A' : ℝ} (hAA : A ≤ A') (n : ℕ)
    (h : DeningerExpSchwartz) :
    deningerMeyerSeminormFun A n h ≤ deningerMeyerSeminormFun A' n h := by
  refine deningerMeyerSeminormFun_le fun t => ?_
  rw [deningerMeyerWeight]
  have hexp : Real.exp (A * |t|) ≤ Real.exp (A' * |t|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hAA (abs_nonneg t))
  refine le_trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) ?_
  have hw := deningerMeyerWeight_le A' n h t
  rwa [deningerMeyerWeight] at hw

/-- **A finite supremum of Meyer seminorms is dominated by one two-sided oscillator seminorm.** -/
theorem deningerMeyerSup_le_twoSidedShifted (s : Finset (ℕ × ℕ)) :
    ∃ (A m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ h : DeningerExpSchwartz,
      (s.sup (fun i : ℕ × ℕ => deningerMeyerSeminorm (i.1 : ℝ) i.2)) h
        ≤ C * shiftedSeminorm m
            ((deningerTwoSidedMul (A : ℝ) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := by
  classical
  set A : ℕ := s.sup (fun i : ℕ × ℕ => i.1) with hA
  set N : ℕ := s.sup (fun i : ℕ × ℕ => i.2) with hN
  choose mm CC hCC0 hCC using fun n : ℕ =>
    deningerMeyerSeminorm_le_twoSidedShifted (K := (A : ℝ)) (Nat.cast_nonneg A) n
  set M : ℕ := (Finset.range (N + 1)).sup mm with hM
  have hraise : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ f : 𝓢(ℝ, ℂ), n ≤ N →
      shiftedSeminorm (mm n) f ≤ D * shiftedSeminorm M f := by
    intro n
    by_cases hn : n ≤ N
    · have hle : mm n ≤ M :=
        Finset.le_sup (f := mm) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
      obtain ⟨D, hD0, hD⟩ := shiftedSeminorm_le_of_le hle
      exact ⟨D, hD0, fun f _ => hD f⟩
    · exact ⟨0, le_refl 0, fun _ hcon => absurd hcon hn⟩
  choose DD hDD0 hDD using hraise
  have hC0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), CC n * DD n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (hCC0 n) (hDD0 n)
  refine ⟨A, M, ∑ n ∈ Finset.range (N + 1), CC n * DD n, hC0, fun h => ?_⟩
  have hpt : ∀ i ∈ s, ∀ x : DeningerExpSchwartz,
      deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2 x
        ≤ (∑ n ∈ Finset.range (N + 1), CC n * DD n)
          * deningerTwoSidedOscFamily (A, M) x := by
    intro i hi x
    have hiA : (i.1 : ℝ) ≤ (A : ℝ) := by
      exact_mod_cast Finset.le_sup (f := fun j : ℕ × ℕ => j.1) hi
    have hiN : i.2 ≤ N := Finset.le_sup (f := fun j : ℕ × ℕ => j.2) hi
    have hmono : deningerMeyerSeminormFun ((i.1 : ℕ) : ℝ) i.2 x
        ≤ deningerMeyerSeminormFun ((A : ℕ) : ℝ) i.2 x :=
      deningerMeyerSeminormFun_mono hiA i.2 x
    have hstep := hCC i.2 x
    have hraise' := hDD i.2
      ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) hiN
    have hterm : CC i.2 * DD i.2 ≤ ∑ n ∈ Finset.range (N + 1), CC n * DD n :=
      Finset.single_le_sum (f := fun n => CC n * DD n)
        (fun n _ => mul_nonneg (hCC0 n) (hDD0 n))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hiN))
    have hosc : (0 : ℝ) ≤ shiftedSeminorm M
        ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) :=
      apply_nonneg _ _
    calc deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2 x
        = deningerMeyerSeminormFun ((i.1 : ℕ) : ℝ) i.2 x := rfl
      _ ≤ deningerMeyerSeminormFun ((A : ℕ) : ℝ) i.2 x := hmono
      _ ≤ CC i.2 * shiftedSeminorm (mm i.2)
            ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := hstep
      _ ≤ CC i.2 * (DD i.2 * shiftedSeminorm M
            ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) :=
          mul_le_mul_of_nonneg_left hraise' (hCC0 i.2)
      _ = (CC i.2 * DD i.2) * shiftedSeminorm M
            ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := by ring
      _ ≤ (∑ n ∈ Finset.range (N + 1), CC n * DD n) * shiftedSeminorm M
            ((deningerTwoSidedMul (A : ℝ) x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) :=
          mul_le_mul_of_nonneg_right hterm hosc
  have hcoe : ((Real.toNNReal (∑ n ∈ Finset.range (N + 1), CC n * DD n) : NNReal) : ℝ)
      = ∑ n ∈ Finset.range (N + 1), CC n * DD n := Real.coe_toNNReal _ hC0
  have hsem : (s.sup (fun i : ℕ × ℕ => deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2))
      ≤ (Real.toNNReal (∑ n ∈ Finset.range (N + 1), CC n * DD n))
        • deningerTwoSidedOscFamily (A, M) := by
    refine Finset.sup_le fun i hi => fun x => ?_
    have hb := hpt i hi x
    simpa [NNReal.smul_def, hcoe] using hb
  have hfin := hsem h
  simpa [NNReal.smul_def, hcoe, deningerTwoSidedOscFamily, deningerSourceOscSeminorm,
    deningerRestrictSeminorm_apply] using hfin

end

end RHTower
