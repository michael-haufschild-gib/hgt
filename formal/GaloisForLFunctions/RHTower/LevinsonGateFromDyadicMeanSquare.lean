import GaloisForLFunctions.RHTower.LevinsonReciprocalLogMeanSquareGate
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorAdmissibleContour
import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget
import GaloisForLFunctions.RHTower.LevinsonRightEdge
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor

/-!
# The Levinson mean-square gate from a dyadic mean-square law

Item 7 of the mollified mean-square programme is bookkeeping: the analytic lane produces bounds on
dyadic blocks `[a, v]`, `a ≤ v ≤ 2a`, for the actual mollified detector on the Levinson abscissa,
while the gate `LevinsonReciprocalLogMeanSquareGate` asks for one window `[T₁, T₂] ⊆ [20, U]` with
`T₂ > U − 1`, zero-free horizontal edges, and the mean square at most `(c + ε)(T₂ − T₁)`.

`DyadicDetectorMeanSquareLaw R c` is the exact interface: for every `ε > 0` and all large `U`,
a mollifier of the gate's class and, for every abscissa `σ₀ = ½ − R/log T` with `T ∈ [U−1, U]`,
every dyadic block `[a, v] ⊆ [20, U]` satisfies

  `∫_a^v ‖(ζ + λζ')Ψ(σ₀ + it)‖² dt ≤ (c + ε)(v − a) + ε (a + U/log U)`,   `λ = 1/log U`.

The theorem selects `T₁ ∈ (20, 21)`, `T₂ ∈ (U−1, U)` avoiding the zeros of the entire detector
times the mollifier on the horizontal edges (`exists_horizontal_slices_avoiding_entire_zeros`),
splits `[T₁, T₂]` into the dyadic blocks `[T₁2^k, T₁2^{k+1}]` and a partial last block, and sums:
the additive slack costs `ε(2U + 3U)` because `Σ_k T₁2^k ≤ 2T₂` and there are at most `3 log U`
blocks, and `U ≤ 2(T₂ − T₁)` absorbs it into `(c + ε')(T₂ − T₁)`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **The dyadic mean-square law** for the reciprocal-log Levinson detector. -/
def DyadicDetectorMeanSquareLaw (R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log (U - 1) ∧
    ∀ σ₀ : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 →
      R ≤ (1 / 2 - σ₀) * Real.log U → (1 / 2 - σ₀) * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ t in a..v,
          ‖levinsonMollifiedDetector ((((1 : ℝ) / Real.log U : ℝ)) : ℂ)
            b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * (a + U / Real.log U)

/-- **Item 7.** A dyadic mean-square law yields the reciprocal-log Levinson gate. -/
theorem levinsonReciprocalLogMeanSquareGate_of_dyadicLaw {R c : ℝ} (hR : 0 < R)
    (hlaw : DyadicDetectorMeanSquareLaw R c) : LevinsonReciprocalLogMeanSquareGate R c := by
  classical
  intro ε hε
  have hε' : 0 < ε / 13 := by positivity
  filter_upwards [hlaw (ε / 13) hε', eventually_ge_atTop (max 100 (Real.exp (4 * R) + 1))]
    with U hU hUbig
  obtain ⟨Mb, b, N, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb, hdy⟩ := hU
  have hU100 : (100 : ℝ) ≤ U := le_trans (le_max_left _ _) hUbig
  have hUexp : Real.exp (4 * R) + 1 ≤ U := le_trans (le_max_right _ _) hUbig
  have hU0 : (0 : ℝ) < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlogU1 : 1 ≤ Real.log U := by
    have he : Real.exp 1 ≤ U := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  set lam : ℝ := (1 : ℝ) / Real.log U with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hlamC : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlampos, hlam, div_le_one hlogU]
    exact hlogU1
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  set Ψ : ℂ → ℂ := edPoly b (Finset.Icc 1 N) with hΨdef
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  set F : ℂ → ℂ := fun z => levinsonGEntire ((lam : ℝ) : ℂ) z * Ψ z with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz =>
    ((analyticOnNhd_levinsonGEntire _) z hz).mul (hΨan z hz)
  have hΨright : Ψ (((15 / 2 : ℝ) : ℂ)) ≠ 0 := by
    intro h0
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    rw [← hΨdef, h0] at h
    norm_num at h
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero
      (levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)) hΨright⟩
  -- zero-free horizontal edges
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) (by norm_num : (20 : ℝ) < 21) (by linarith : (21 : ℝ) < U - 1)
      (by linarith : U - 1 < U)
  have hT₁20 : 20 < T₁ := hT₁.1
  have hT₁21 : T₁ < 21 := hT₁.2
  have hT₂U : T₂ < U := hT₂.2
  have hT₂lo : U - 1 < T₂ := hT₂.1
  have hT12 : T₁ < T₂ := by linarith
  have hT₂pos : 0 < T₂ := by linarith
  have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
  have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log hT₂pos hT₂U.le
  have hlogU1T₂ : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂lo.le
  have hlogT₂4R : 4 * R ≤ Real.log T₂ := by
    have := Real.log_le_log (Real.exp_pos (4 * R)) (by linarith : Real.exp (4 * R) ≤ T₂)
    rwa [Real.log_exp] at this
  -- the abscissa
  set σ₀ : ℝ := 1 / 2 - R / Real.log T₂ with hσ₀
  have hσ₀R : (1 / 2 - σ₀) * Real.log T₂ = R := by
    rw [hσ₀]
    field_simp
    try ring
  have hσ₀a : 1 / 4 ≤ σ₀ := by
    rw [hσ₀]
    have : R / Real.log T₂ ≤ 1 / 4 := by
      rw [div_le_iff₀ hlogT₂]
      linarith
    linarith
  have hσ₀b : σ₀ < 1 / 2 := by
    rw [hσ₀]
    have : 0 < R / Real.log T₂ := by positivity
    linarith
  have hσ₀lawU : R ≤ (1 / 2 - σ₀) * Real.log U := by
    have hw : 1 / 2 - σ₀ = R / Real.log T₂ := by rw [hσ₀]; ring
    rw [hw, div_mul_eq_mul_div, le_div_iff₀ hlogT₂]
    nlinarith [hlogT₂U, hR]
  have hσ₀lawU1 : (1 / 2 - σ₀) * Real.log (U - 1) ≤ R := by
    have hw : 1 / 2 - σ₀ = R / Real.log T₂ := by rw [hσ₀]; ring
    rw [hw, div_mul_eq_mul_div, div_le_iff₀ hlogT₂]
    nlinarith [hlogU1T₂, hR]
  -- edge nonvanishing from `F`
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
        levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), Ψ ((x : ℂ) + (T : ℂ) * I) ≠ 0) := by
    intro T hT hF
    have hmem : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      intro x hx
      rw [uIcc_of_le (by norm_num)]
      exact ⟨le_trans hσ₀a hx.1, hx.2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · intro h0
      apply hF x (hmem x hx)
      have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      simp only [hFdef]
      rw [levinsonGEntire_eq _ hne1, h0]
      ring
    · intro h0
      apply hF x (hmem x hx)
      simp only [hFdef]
      rw [h0, mul_zero]
  obtain ⟨hG1, hP1⟩ := hedge T₁ hT₁20.le hF1
  obtain ⟨hG2, hP2⟩ := hedge T₂ (by linarith) hF2
  -- the mean square via dyadic blocks
  set f : ℝ → ℝ := fun t =>
    ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
      ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hfdef
  have hcont : ∀ t : ℝ, 20 ≤ t → ContinuousAt f t := by
    intro t ht
    have hz : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hA := (analyticAt_levinsonMollifiedDetector ((lam : ℝ) : ℂ) b hs hz).continuousAt
    have hmap : ContinuousAt (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact (ContinuousAt.comp (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) hA hmap).norm.pow 2
  have hint : ∀ a v : ℝ, 20 ≤ a → a ≤ v → IntervalIntegrable f volume a v := by
    intro a v ha hav
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hav] at ht
    exact (hcont t (le_trans ha ht.1)).continuousWithinAt
  have hblock : ∀ a v : ℝ, 20 ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
      (∫ t in a..v, f t) ≤ (c + ε / 13) * (v - a) + ε / 13 * (a + U / Real.log U) :=
    fun a v ha hav hv2 hvU => hdy σ₀ hσ₀a hσ₀b hσ₀lawU hσ₀lawU1 a v ha hav hv2 hvU
  -- dyadic scale
  set A : ℕ → ℝ := fun k => T₁ * (2 : ℝ) ^ k with hAdef
  have hA0 : A 0 = T₁ := by simp [hAdef]
  have hAsucc : ∀ k, A (k + 1) = 2 * A k := by intro k; simp [hAdef]; ring
  have hApos : ∀ k, 20 ≤ A k := by
    intro k
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h2 : T₁ ≤ T₁ * 2 ^ k := le_mul_of_one_le_right (by linarith) h1
    simp only [hAdef]
    linarith
  have hAmono : ∀ k, A k ≤ A (k + 1) := by
    intro k; rw [hAsucc]; linarith [hApos k]
  have hexK : ∃ k : ℕ, T₂ < A (k + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T₂ / T₁) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [hAsucc]
    have h1 : T₂ < T₁ * 2 ^ n := by
      rw [div_lt_iff₀ (by linarith)] at hn
      linarith
    have h2 : A n = T₁ * 2 ^ n := rfl
    linarith [hApos n]
  set K : ℕ := Nat.find hexK with hKdef
  have hKspec : T₂ < A (K + 1) := Nat.find_spec hexK
  have hKle : A K ≤ T₂ := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, hA0]; exact hT12.le
    · obtain ⟨K', hK'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
      have hmin : ¬ (T₂ < A (K' + 1)) := Nat.find_min hexK (by omega)
      rw [hK']
      exact le_of_not_gt hmin
  -- K is at most 2 log U
  have hKlog : (K : ℝ) ≤ 2 * Real.log U := by
    have h2K : T₁ * (2 : ℝ) ^ K ≤ U := le_trans hKle hT₂U.le
    have hpow : (2 : ℝ) ^ K ≤ U := by
      have : (2 : ℝ) ^ K ≤ T₁ * 2 ^ K :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      linarith
    have hlogpow : (K : ℝ) * Real.log 2 ≤ Real.log U := by
      have := Real.log_le_log (by positivity) hpow
      rwa [Real.log_pow] at this
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have := mul_le_mul_of_nonneg_left hlog2 hK0
    linarith
  -- split the integral
  have hsplit : (∫ t in T₁..T₂, f t)
      = (∑ k ∈ Finset.range K, ∫ t in A k..A (k + 1), f t) + ∫ t in A K..T₂, f t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hint _ _ (hApos k) (hAmono k))]
    rw [hA0]
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by linarith) (by
      have : T₁ = A 0 := hA0.symm
      rw [this]
      exact monotone_nat_of_le_succ hAmono (Nat.zero_le K))) (hint _ _ (hApos K) hKle)]
  have hterm : ∀ k ∈ Finset.range K,
      (∫ t in A k..A (k + 1), f t)
        ≤ (c + ε / 13) * (A (k + 1) - A k) + ε / 13 * (A k + U / Real.log U) := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    refine hblock (A k) (A (k + 1)) (hApos k) (hAmono k) (by rw [hAsucc]) ?_
    have : A (k + 1) ≤ A K := monotone_nat_of_le_succ hAmono (by omega)
    linarith
  have hlast : (∫ t in A K..T₂, f t)
      ≤ (c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U) := by
    refine hblock (A K) T₂ (hApos K) hKle ?_ hT₂U.le
    rw [hAsucc] at hKspec
    exact hKspec.le
  have hsumA : ∑ k ∈ Finset.range K, A k = T₁ * ((2 : ℝ) ^ K - 1) := by
    simp only [hAdef]
    rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    ring
  have htele : ∑ k ∈ Finset.range K, (A (k + 1) - A k) = A K - A 0 :=
    Finset.sum_range_sub (fun k => A k) K
  have hsum_le := Finset.sum_le_sum hterm
  have hRHS : (∑ k ∈ Finset.range K,
      ((c + ε / 13) * (A (k + 1) - A k) + ε / 13 * (A k + U / Real.log U)))
      = (c + ε / 13) * (A K - A 0)
        + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htele, ← Finset.mul_sum,
      Finset.sum_add_distrib, hsumA, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hRHS] at hsum_le
  -- assemble the numeric bound
  have hAK : A K = T₁ * 2 ^ K := rfl
  have hAKle : T₁ * (2 : ℝ) ^ K ≤ T₂ := hKle
  have hUlog : U / Real.log U ≤ U := by
    rw [div_le_iff₀ hlogU]
    exact le_mul_of_one_le_right hU0.le hlogU1
  have hK1 : (K : ℝ) + 1 ≤ 3 * Real.log U := by linarith
  have hslack : ε / 13 * ((T₁ * ((2 : ℝ) ^ K - 1) + A K) + ((K : ℝ) + 1) * (U / Real.log U))
      ≤ ε / 13 * (5 * U) := by
    apply mul_le_mul_of_nonneg_left _ hε'.le
    have h1 : T₁ * ((2 : ℝ) ^ K - 1) + A K ≤ 2 * U := by
      rw [hAK]
      have hexp : T₁ * ((2 : ℝ) ^ K - 1) + T₁ * 2 ^ K = 2 * (T₁ * 2 ^ K) - T₁ := by ring
      rw [hexp]
      linarith
    have h2 : ((K : ℝ) + 1) * (U / Real.log U) ≤ 3 * U := by
      calc ((K : ℝ) + 1) * (U / Real.log U) ≤ (3 * Real.log U) * (U / Real.log U) :=
            mul_le_mul_of_nonneg_right hK1 (by positivity)
        _ = 3 * U := by field_simp
    linarith
  have hU2 : U ≤ 2 * (T₂ - T₁) := by linarith
  refine ⟨T₁, T₂, σ₀, Mb, b, N, ⟨hT₁20.le, hT₁21.le⟩, ⟨hT₂lo, hT₂U.le⟩, hN, hb1, hbn, hbreal,
    hMb1, hmass, ?_, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, ?_⟩
  · calc Real.log Mb ≤ 5 * Real.log (U - 1) := hlogMb
      _ ≤ 5 * Real.log T₂ := by linarith
  · show (∫ t in T₁..T₂, f t) ≤ (c + ε) * (T₂ - T₁)
    rw [hsplit]
    have hεU : ε / 13 * (5 * U) ≤ 10 * (ε / 13) * (T₂ - T₁) := by
      have := mul_le_mul_of_nonneg_left hU2 hε'.le
      linarith
    have hεT : 0 ≤ ε * (T₂ - T₁) := mul_nonneg hε.le (by linarith)
    have hfin : (c + ε / 13) * (A K - A 0) + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U))
        + ((c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U))
        ≤ (c + ε) * (T₂ - T₁) := by
      have hexp : (c + ε / 13) * (A K - A 0) + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U))
          + ((c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U))
          = (c + ε / 13) * (T₂ - A 0)
            + ε / 13 * ((T₁ * ((2 : ℝ) ^ K - 1) + A K) + ((K : ℝ) + 1) * (U / Real.log U)) := by
        ring
      rw [hexp, hA0]
      linarith [hslack, hεU, hεT]
    linarith [hsum_le, hlast, hfin]

end

end RHTower
