import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectionBound

/-!
# Guth–Maynard Lemma 6.2 for `ζ`: all nonzero Poisson modes

Guth–Maynard's Lemma 6.2 bounds `Σ_{m ≠ 0} ĥ_t(mN)`.  This module splits the punctured
frequency sum (on the Chen–Gupta–Li carrier `{m : ℤ // m ≠ 0}`) as

`Σ_{m ≠ 0} f(m) = Σ_{m=1}^{M} (f(m) + f(−m)) + Σ_{k ≥ 0} (f(k+M+1) + f(−(k+M+1)))`,

bounds the tail `|m| > M` by the all-order decay of Lemma 4.3,
`‖ĥ_t(ξ)‖ ≤ A_j (1+|t|)^j/|ξ|^j`, as `2 A_j (1+|t|)^j N^{−j} M^{2−j} Σ_k (k+1)^{−2}`, and combines
it with the two one-sided bounds of `ChenGuptaLiLemma62PrincipalReflectionBound` into the explicit
form of Lemma 6.2: for `N ≥ 1`, `M ≥ 1`, `2 ≤ |t|`, `0 < U ≤ |t|/2`, `n`, `j ≥ 2`,

`‖Σ_{m ≠ 0} ĥ_t(mN)‖ ≤ (c₁/π) ∫_{−U}^{U} ‖Σ_{m ≤ M} m^{−i(t+u)}‖ du + c₂ + tail`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- **Punctured split.** For summable `f : ℤ → ℂ` and every `M`,
`Σ_{m ≠ 0} f(m) = Σ_{m=1}^{M} (f(m) + f(−m)) + Σ_k (f(k+M+1) + f(−(k+M+1)))`. -/
theorem tsum_puncturedFrequency_eq_sum_add_tail (f : ℤ → ℂ) (hf : Summable f) (M : ℕ) :
    ∑' m : CGLProposition51PuncturedFrequency, f m =
      ∑ m ∈ Finset.Icc 1 M, (f m + f (-(m : ℤ))) +
        ∑' k : ℕ, (f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ))) := by
  set g : ℤ → ℂ := {m : ℤ | m ≠ 0}.indicator f with hg
  have hgs : Summable g := hf.indicator _
  have hpos : Summable fun n : ℕ => f ((n : ℤ) + 1) :=
    hf.comp_injective (fun a b h => by simpa using h)
  have hneg : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hf.comp_injective (fun a b h => by simpa using h)
  have hg0 : g 0 = 0 := by simp [hg]
  have hgpos : ∀ n : ℕ, g ((n : ℤ) + 1) = f ((n : ℤ) + 1) := fun n => by
    rw [hg, indicator_of_mem]; simp only [mem_setOf_eq]; omega
  have hgneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = f (-((n : ℤ) + 1)) := fun n => by
    rw [hg, indicator_of_mem]; simp only [mem_setOf_eq]; omega
  have hsub : ∑' m : CGLProposition51PuncturedFrequency, f m = ∑' m : ℤ, g m :=
    tsum_subtype {m : ℤ | m ≠ 0} f
  have hnat : Summable fun n : ℕ => g n :=
    hgs.comp_injective (fun a b h => by simpa using h)
  have hnegg : Summable fun n : ℕ => g (-((n : ℤ) + 1)) :=
    hgs.comp_injective (fun a b h => by simpa using h)
  rw [hsub, tsum_of_nat_of_neg_add_one hnat hnegg, hnat.tsum_eq_zero_add]
  simp only [Nat.cast_zero, hg0, zero_add, Nat.cast_add, Nat.cast_one, hgpos, hgneg]
  rw [← hpos.tsum_add hneg]
  set F : ℕ → ℂ := fun n => f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)) with hF
  have hFs : Summable F := hpos.add hneg
  rw [← hFs.sum_add_tsum_nat_add M]
  congr 1
  · rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF]
    push_cast
    ring_nf

/-- The Poisson modes `m ↦ ĥ_t(mN)` are summable over `ℤ` for `N > 0`. -/
theorem summable_fourier_cglSmoothBumpHt_int (w : CGLSmoothBump) (t N : ℝ) (hN : 0 < N) :
    Summable fun m : ℤ => 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((m : ℝ) * N) := by
  set A : ℝ := cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 / N ^ 2
  have hbase : Summable fun n : ℕ => A * (1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact (by simpa using h : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2).mul_left A
  have hbound : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ n : ℕ,
      ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) (s * ((n : ℝ) + 1) * N)‖ ≤
        A * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro s hs n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have habs : |s * ((n : ℝ) + 1) * N| = ((n : ℝ) + 1) * N := by
      rcases hs with rfl | rfl
      · rw [one_mul, abs_of_pos (by positivity)]
      · rw [abs_mul, abs_mul, abs_neg, abs_one, one_mul, abs_of_pos hn, abs_of_pos hN]
    have h := norm_fourier_cglSmoothBumpHt_le_div w 2 t (ξ := s * ((n : ℝ) + 1) * N)
      (by rw [← abs_pos, habs]; positivity)
    rw [habs, mul_pow] at h
    refine h.trans (le_of_eq ?_)
    simp only [A]
    field_simp
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_nat_add_iff 1).mp ?_
    refine Summable.of_norm_bounded hbase fun n => ?_
    have := hbound 1 (Or.inl rfl) n
    simpa using this
  · refine Summable.of_norm_bounded hbase fun n => ?_
    have := hbound (-1) (Or.inr rfl) n
    simpa [neg_mul, Int.cast_add] using this

/-- The inverse-square mass `Z = Σ_{k ≥ 0} (k+1)^{−2}`. -/
def cglGMInverseSquareMass : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2

theorem summable_inverseSquare_succ : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simpa using h

theorem cglGMInverseSquareMass_nonneg : 0 ≤ cglGMInverseSquareMass :=
  tsum_nonneg fun k => by positivity

/-- `(k+M+1)^j ≥ (k+1)² M^{j−2}` for `j ≥ 2`. -/
theorem succ_add_pow_ge (k M j : ℕ) (hj : 2 ≤ j) :
    ((k : ℝ) + 1) ^ 2 * (M : ℝ) ^ (j - 2) ≤ ((k : ℝ) + M + 1) ^ j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left, pow_add]
  gcongr <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

/-- The tail weight `2 A_j (1+|t|)^j / (N^j M^{j−2}) · Z`. -/
def cglGMFrequencyTailWeight (w : CGLSmoothBump) (j : ℕ) (t N : ℝ) (M : ℕ) : ℝ :=
  2 * (cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j * (1 + |t|) ^ j /
    (N ^ j * (M : ℝ) ^ (j - 2))) * cglGMInverseSquareMass

/-- **Frequency tail.** `‖Σ_k (ĥ_t((k+M+1)N) + ĥ_t(−(k+M+1)N))‖ ≤ 2 A_j (1+|t|)^j N^{−j} M^{2−j} Z`. -/
theorem norm_frequencyTail_le (w : CGLSmoothBump) (t N : ℝ) (hN : 0 < N) {M : ℕ} (hM : 1 ≤ M)
    {j : ℕ} (hj : 2 ≤ j) :
    ‖∑' k : ℕ, (𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((((k + M + 1 : ℕ) : ℤ) : ℝ) * N) +
        𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((((-((k + M + 1 : ℕ) : ℤ)) : ℤ) : ℝ) * N))‖ ≤
      cglGMFrequencyTailWeight w j t N M := by
  set f : ℤ → ℂ := fun m => 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((m : ℝ) * N) with hf
  have hfs := summable_fourier_cglSmoothBumpHt_int w t N hN
  set c : ℝ := cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j * (1 + |t|) ^ j /
    (N ^ j * (M : ℝ) ^ (j - 2)) with hc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hA : 0 ≤ cglSmoothBumpHtAllOrderBudget w j := cglSmoothBumpHtAllOrderBudget_nonneg w j
  have hpt : ∀ k : ℕ, ∀ s : ℝ, |s| = 1 →
      ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) (s * ((k : ℝ) + M + 1) * N)‖ ≤
        c * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k s hs
    have hk : (0 : ℝ) < (k : ℝ) + M + 1 := by positivity
    have habs : |s * ((k : ℝ) + M + 1) * N| = ((k : ℝ) + M + 1) * N := by
      rw [abs_mul, abs_mul, hs, one_mul, abs_of_pos hk, abs_of_pos hN]
    have h := norm_fourier_cglSmoothBumpHt_le_div w j t (ξ := s * ((k : ℝ) + M + 1) * N)
      (by rw [← abs_pos, habs]; positivity)
    rw [habs] at h
    set X : ℝ := cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j * (1 + |t|) ^ j
      with hX
    have hX0 : 0 ≤ X := by positivity
    have hge := succ_add_pow_ge k M j hj
    have hle : N ^ j * (M : ℝ) ^ (j - 2) * ((k : ℝ) + 1) ^ 2 ≤ (((k : ℝ) + M + 1) * N) ^ j := by
      calc N ^ j * (M : ℝ) ^ (j - 2) * ((k : ℝ) + 1) ^ 2
          = N ^ j * (((k : ℝ) + 1) ^ 2 * (M : ℝ) ^ (j - 2)) := by ring
        _ ≤ N ^ j * ((k : ℝ) + M + 1) ^ j := by gcongr
        _ = (((k : ℝ) + M + 1) * N) ^ j := by rw [mul_pow, mul_comm]
    calc _ ≤ X / (((k : ℝ) + M + 1) * N) ^ j := h
      _ ≤ X / (N ^ j * (M : ℝ) ^ (j - 2) * ((k : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_left hX0 (by positivity) hle
      _ = c * (1 / ((k : ℝ) + 1) ^ 2) := by
          rw [hc]; field_simp
  have hterm : ∀ k : ℕ, ‖f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ))‖ ≤
      2 * c * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have h1 := hpt k 1 (by simp)
    have h2 := hpt k (-1) (by simp)
    simp only [one_mul, neg_mul] at h1 h2
    refine (norm_add_le _ _).trans ?_
    simp only [hf]
    push_cast
    rw [neg_add, neg_add, show (-(k : ℝ) + -(M : ℝ) + -1) = -((k : ℝ) + M + 1) by ring,
      neg_mul]
    linarith
  have hsumR : Summable fun k : ℕ => 2 * c * (1 / ((k : ℝ) + 1) ^ 2) :=
    summable_inverseSquare_succ.mul_left _
  have hnorm : Summable fun k : ℕ => ‖f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumR
  calc _ = ‖∑' k : ℕ, (f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ)))‖ := rfl
    _ ≤ ∑' k : ℕ, ‖f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, 2 * c * (1 / ((k : ℝ) + 1) ^ 2) := hnorm.tsum_le_tsum hterm hsumR
    _ = cglGMFrequencyTailWeight w j t N M := by
        rw [tsum_mul_left, cglGMFrequencyTailWeight, cglGMInverseSquareMass, hc]

/-- The nonzero-mode sum `Σ_{m ≠ 0} ĥ_t(mN)` of Guth–Maynard's Lemma 6.2. -/
def cglGMNonzeroModeSum (w : CGLSmoothBump) (N t : ℝ) : ℂ :=
  ∑' m : CGLProposition51PuncturedFrequency, 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((m : ℝ) * N)

/-- **Lemma 6.2 for `ζ`, explicit form.** For `N ≥ 1`, `M ≥ 1`, `2 ≤ |t|`, `0 < U ≤ |t|/2`,
every `n` and every `j ≥ 2`:
`‖Σ_{m ≠ 0} ĥ_t(mN)‖ ≤ (c₁/π) ∫_{−U}^{U} ‖Σ_{m ≤ M} m^{−i(t+u)}‖ du + c₂ + tail_j`. -/
theorem norm_cglGMNonzeroModeSum_le (w : CGLRealSmoothBump) {t N U : ℝ} (hN : 1 ≤ N)
    {M : ℕ} (hM : 1 ≤ M) (hU : 0 < U) (hUt : U ≤ |t| / 2) (ht : 2 ≤ |t|) (n : ℕ) {j : ℕ}
    (hj : 2 ≤ j) :
    ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤
      cglGMWindowWeight w t / Real.pi * (∫ u in (-U)..U, ‖cglGMHeadPoly M (t + u)‖) +
        cglGMTailWeight w n U M + cglGMFrequencyTailWeight w.toCGLSmoothBump j t N M := by
  have hN0 : 0 < N := by linarith
  set f : ℤ → ℂ := fun m => 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N)
    with hf
  have hsplit := tsum_puncturedFrequency_eq_sum_add_tail f
    (summable_fourier_cglSmoothBumpHt_int w.toCGLSmoothBump t N hN0) M
  have hpos := cglGM_norm_sum_fourier_pos_le w hN hM hU hUt ht n
  have hneg := cglGM_norm_sum_fourier_neg_le w hN hM hU hUt ht n
  have htail := norm_frequencyTail_le w.toCGLSmoothBump t N hN0 hM hj
  have hposeq : ∑ m ∈ Finset.Icc 1 M, f m =
      ∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N) := by
    simp [hf]
  have hnegeq : ∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ)) =
      ∑ m ∈ Finset.Icc 1 M,
        𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) (-((m : ℝ) * N)) := by
    simp [hf, neg_mul]
  unfold cglGMNonzeroModeSum
  change ‖∑' m : CGLProposition51PuncturedFrequency, f m‖ ≤ _
  rw [hsplit, Finset.sum_add_distrib, hposeq, hnegeq]
  calc _ ≤ ‖∑ m ∈ Finset.Icc 1 M,
          𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M,
          𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) (-((m : ℝ) * N))‖ +
        ‖∑' k : ℕ, (f ((k + M + 1 : ℕ) : ℤ) + f (-((k + M + 1 : ℕ) : ℤ)))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
        have hpi : 0 < Real.pi := Real.pi_pos
        have hw : cglGMWindowWeight w t / Real.pi =
            2 * (cglGMWindowWeight w t / (2 * Real.pi)) := by
          field_simp
        rw [hw]
        linarith [htail]

end RHTower
