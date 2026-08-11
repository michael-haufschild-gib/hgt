import GaloisForLFunctions.RHTower.DeningerPeriodizationBounded

/-!
# The splitting is bounded by the circle seminorms

The lift `s_χ F = χ·F` is supported where `χ` is, so every exponential Meyer weight is bounded there
by a fixed constant, and the Leibniz rule bounds each derivative of the lift by the corresponding
derivatives of `F`.  Hence `s_χ` carries the `C^∞` seminorms of the circle to the Meyer seminorms.

* `deningerPeriodicSup` : the `C^r` sup-seminorm of a smooth periodic function.
* `deningerSplit_meyerSeminorm_bound` : **`q_{A,r}(s_χ F) ≤ K · \|F\|_{C^r}`.**
-/

namespace RHTower

open SchwartzMap Metric

noncomputable section

/-! ## Bounds for compactly supported smooth functions -/

theorem deningerCompactSupport_iteratedFDeriv_bound {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcs : HasCompactSupport g) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i g t‖ ≤ D := by
  have hbd : ∀ i : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i g t‖ ≤ D := by
    intro i
    obtain ⟨D, hD⟩ := (hcs.iteratedFDeriv i).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    exact ⟨max D 0, le_max_right _ _, fun t => le_trans (hD t) (le_max_left _ _)⟩
  choose D hDnn hDle using hbd
  refine ⟨∑ i ∈ Finset.range (k + 1), D i, Finset.sum_nonneg fun i _ => hDnn i, ?_⟩
  intro i hi t
  refine le_trans (hDle i t) ?_
  exact Finset.single_le_sum (f := D) (fun j _ => hDnn j) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-! ## The partition of unity vanishes off a fixed interval -/

theorem deningerPartitionUnity_support_subset (L : ℝ) :
    Function.support (fun s : ℝ => (deningerPartitionUnity L s : ℂ))
      ⊆ closedBall (0 : ℝ) (|L| + 2) := by
  intro s hs
  by_contra hout
  have hdist : (deningerPartitionBump L).rOut ≤ dist s (0 : ℝ) := by
    have : |L| + 2 < |s| := by
      simpa [Real.dist_eq] using not_le.1 (by simpa [mem_closedBall, Real.dist_eq] using hout)
    simpa [Real.dist_eq] using le_of_lt this
  have hzero : (deningerPartitionBump L : ℝ → ℝ) s = 0 :=
    (deningerPartitionBump L).zero_of_le_dist hdist
  apply hs
  simp [deningerPartitionUnity, hzero]

theorem deningerPartitionUnity_iteratedFDeriv_eq_zero {L t : ℝ} (ht : |L| + 2 < |t|) (i : ℕ) :
    iteratedFDeriv ℝ i (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) t = 0 := by
  have hts : tsupport (fun s : ℝ => (deningerPartitionUnity L s : ℂ))
      ⊆ closedBall (0 : ℝ) (|L| + 2) :=
    closure_minimal (deningerPartitionUnity_support_subset L) isClosed_closedBall
  have hnot : t ∉ tsupport (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) := by
    intro hmem
    have := hts hmem
    rw [mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  by_contra hne
  exact hnot (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i (subset_tsupport _ hne))

theorem deningerPartitionUnityC_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (deningerPartitionUnity_contDiff hL)

theorem deningerPartitionUnityC_hasCompactSupport (L : ℝ) :
    HasCompactSupport (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) :=
  (deningerPartitionUnity_hasCompactSupport L).comp_left
    (g := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) (by simp)

/-! ## The `C^r` seminorm of a smooth periodic function -/

/-- The derivatives of a periodic function are periodic. -/
theorem deningerSmoothPeriodic_iteratedFDeriv_periodic {L : ℝ} (F : DeningerSmoothPeriodic L)
    (r : ℕ) (t : ℝ) :
    iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) (t + L)
      = iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t := by
  have hfun : (fun s : ℝ => ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) (s + L))
      = ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) :=
    funext fun s => deningerSmoothPeriodic_periodic F s
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := ((F : DeningerSmoothPeriodic L) : ℝ → ℂ)) r L t
  rw [hfun] at h
  exact h.symm

/-- **Every derivative of a smooth periodic function is bounded.** -/
theorem deningerSmoothPeriodic_iteratedFDeriv_bounded {L : ℝ} (hL : 0 < L)
    (F : DeningerSmoothPeriodic L) (r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖ ≤ M := by
  have hcont : Continuous (fun x : ℝ =>
      ‖iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) x‖) :=
    ((deningerSmoothPeriodic_contDiff F).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  set n : ℤ := -⌊t / L⌋ with hn
  have hfr : t + (n : ℝ) * L = L * Int.fract (t / L) := by
    rw [hn, Int.fract]
    push_cast
    field_simp
    ring
  have hmem : t + (n : ℝ) * L ∈ Set.Icc (0 : ℝ) L := by
    have h0 : 0 ≤ Int.fract (t / L) := Int.fract_nonneg _
    have h1 : Int.fract (t / L) < 1 := Int.fract_lt_one _
    have hlt : L * Int.fract (t / L) < L := mul_lt_of_lt_one_right hL h1
    rw [hfr]
    exact ⟨by positivity, le_of_lt hlt⟩
  have hshift := (Function.Periodic.int_mul
    (fun s => deningerSmoothPeriodic_iteratedFDeriv_periodic F r s) n) t
  rw [← hshift]
  have hb := hM _ hmem
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
  exact le_trans hb (le_max_left _ _)

/-- The `C^r` sup-seminorm of a smooth periodic function. -/
def deningerPeriodicSup {L : ℝ} (r : ℕ) (F : DeningerSmoothPeriodic L) : ℝ :=
  ⨆ t : ℝ, ‖iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖

theorem deningerPeriodicSup_le {L : ℝ} (hL : 0 < L) (r : ℕ) (F : DeningerSmoothPeriodic L)
    (t : ℝ) :
    ‖iteratedFDeriv ℝ r ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖
      ≤ deningerPeriodicSup r F := by
  obtain ⟨M, _, hM⟩ := deningerSmoothPeriodic_iteratedFDeriv_bounded hL F r
  exact le_ciSup ⟨M, fun _ ⟨s, hs⟩ => hs ▸ hM s⟩ t

theorem deningerPeriodicSup_nonneg {L : ℝ} (hL : 0 < L) (r : ℕ) (F : DeningerSmoothPeriodic L) :
    0 ≤ deningerPeriodicSup r F :=
  le_trans (norm_nonneg _) (deningerPeriodicSup_le hL r F 0)

/-- The full `C^r` seminorm: all derivative orders up to `r`. -/
def deningerPeriodicSupLe {L : ℝ} (r : ℕ) (F : DeningerSmoothPeriodic L) : ℝ :=
  ∑ m ∈ Finset.range (r + 1), deningerPeriodicSup m F

theorem deningerPeriodicSupLe_nonneg {L : ℝ} (hL : 0 < L) (r : ℕ)
    (F : DeningerSmoothPeriodic L) : 0 ≤ deningerPeriodicSupLe r F :=
  Finset.sum_nonneg fun m _ => deningerPeriodicSup_nonneg hL m F

theorem deningerPeriodicSup_le_supLe {L : ℝ} (hL : 0 < L) {m r : ℕ} (hm : m ≤ r)
    (F : DeningerSmoothPeriodic L) : deningerPeriodicSup m F ≤ deningerPeriodicSupLe r F :=
  Finset.single_le_sum (f := fun k => deningerPeriodicSup k F)
    (fun k _ => deningerPeriodicSup_nonneg hL k F) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

/-! ## The splitting is bounded -/

/-- **The lift is bounded by the circle seminorms.**  Every Meyer weight of `s_χ F` is dominated by
a fixed multiple of the `C^r` seminorm of `F`, because `s_χ F` is supported where `χ` is. -/
theorem deningerSplit_meyerSeminorm_bound {L : ℝ} (hL : 0 < L) (A : ℝ) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : DeningerSmoothPeriodic L,
      deningerMeyerSeminormFun A r (deningerPeriodizationSplit hL F)
        ≤ K * deningerPeriodicSupLe r F := by
  obtain ⟨D, hDnn, hD⟩ := deningerCompactSupport_iteratedFDeriv_bound
    (deningerPartitionUnityC_contDiff hL) (deningerPartitionUnityC_hasCompactSupport L) r
  refine ⟨2 ^ r * D * Real.exp (|A| * (|L| + 2)), by positivity, fun F => ?_⟩
  set S : ℝ := deningerPeriodicSupLe r F with hS
  have hSnn : 0 ≤ S := deningerPeriodicSupLe_nonneg hL r F
  refine deningerMeyerSeminormFun_le fun t => ?_
  rw [deningerMeyerWeight]
  have hcoe : (((deningerPeriodizationSplit hL F : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun s : ℝ => (deningerPartitionUnity L s : ℂ)
          * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) s := rfl
  rw [hcoe]
  have hleib : ‖iteratedFDeriv ℝ r (fun s : ℝ => (deningerPartitionUnity L s : ℂ)
        * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) s) t‖
      ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) t‖
          * ‖iteratedFDeriv ℝ (r - i) ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖ :=
    norm_iteratedFDeriv_mul_le (deningerPartitionUnityC_contDiff hL)
      (deningerSmoothPeriodic_contDiff F) t (by exact_mod_cast le_top)
  by_cases hin : |t| ≤ |L| + 2
  · have hexp : Real.exp (A * |t|) ≤ Real.exp (|A| * (|L| + 2)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : A * |t| ≤ |A| * |t| :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (abs_nonneg t)
      have h2 : |A| * |t| ≤ |A| * (|L| + 2) := mul_le_mul_of_nonneg_left hin (abs_nonneg A)
      linarith
    have hchoose : (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)) = 2 ^ r := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    have hsum : (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) t‖
          * ‖iteratedFDeriv ℝ (r - i) ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖)
        ≤ 2 ^ r * D * S := by
      have hstep : (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (fun s : ℝ => (deningerPartitionUnity L s : ℂ)) t‖
            * ‖iteratedFDeriv ℝ (r - i) ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖)
          ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * D * S := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hF : ‖iteratedFDeriv ℝ (r - i) ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t‖ ≤ S :=
          le_trans (deningerPeriodicSup_le hL (r - i) F t)
            (deningerPeriodicSup_le_supLe hL (Nat.sub_le _ _) F)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hD i hik t) (by positivity)) hF
          (norm_nonneg _) (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    have hprod : Real.exp (A * |t|)
        * ‖iteratedFDeriv ℝ r (fun s : ℝ => (deningerPartitionUnity L s : ℂ)
            * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) s) t‖
        ≤ Real.exp (|A| * (|L| + 2)) * (2 ^ r * D * S) :=
      mul_le_mul hexp (le_trans hleib hsum) (norm_nonneg _) (Real.exp_pos _).le
    refine le_trans hprod (le_of_eq ?_)
    ring
  · have hzero : iteratedFDeriv ℝ r (fun s : ℝ => (deningerPartitionUnity L s : ℂ)
        * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) s) t = 0 := by
      refine norm_eq_zero.1 (le_antisymm (le_trans hleib (le_of_eq ?_)) (norm_nonneg _))
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [deningerPartitionUnity_iteratedFDeriv_eq_zero (not_le.1 hin) i]
      simp
    rw [hzero, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hSnn

end

end RHTower
