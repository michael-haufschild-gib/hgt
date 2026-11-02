import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalClassOfAWindow

/-!
# The stages of a window and the first-prime fold

A window of length `A` is at **stage** `n` when `⌊e^A⌋ = n`, i.e. `log n ≤ A < log(n + 1)`
(`windowLevel_eq_iff`); a new prime power enters at each `A = log n`.

* **The arithmetic is bounded by the canonical class** (`abs_weilQuad_sub_arch_le`): on every window
  `|Q(H) − (Ω(0)‖H‖² + J_∞(H) + pole)| ≤ ∫ k_A H²`. Each fold moves Weil's form by
  `−2(Λ(n)/√n)∫H(u)H(u + log n)` (`foldEnergy_sub_count_eq`), between `∓(Λ(n)/√n)∫ m_n H²`.
* **Prime-free stage** (`weilQuad_eq_arch_of_primeFree`): for `A < log 2` the window form is purely
  archimedean, `Q(H) = Ω(0)‖H‖² + J_∞(H) + pole`.
* **First-prime stage** (`weilQuad_eq_firstPrimeFold`): for `log 2 ≤ A < log 3` exactly one fold
  acts, the graph of `T₂` from `[−A, −log 2]` onto `[log 2 − A, 0]`; the two ends are disjoint
  (`ends_disjoint_of_lt_two_log_two`), and
  `Q(H) = Ω(0)‖H‖² + J_∞(H) + (log 2/√2)(fold energy − ∫_{ends} H²) + pole`.
* **Half-folded tests see no prime** (`foldEnergy_sub_count_eq_zero_of_vanish_left`): a test that
  vanishes on one end of a fold is not acted on by it.
* **Extremal tests** (`foldEnergy_eq_zero_of_symmetric`, `foldEnergy_eq_of_antisymmetric`):
  fold-symmetric tests pay the full end mass, fold-antisymmetric tests gain it.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A ℓ : ℝ} {H : ℝ → ℝ}

/-! ### Stages -/

/-- A window is at stage `n ≥ 1` iff `log n ≤ A < log(n + 1)`. -/
theorem windowLevel_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    windowLevel A = n ↔ Real.log n ≤ A ∧ A < Real.log (n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le, Real.log_le_iff_le_exp hn0,
    Real.lt_log_iff_exp_lt (by positivity)]

theorem windowLevel_eq_one (h0 : 0 ≤ A) (h : A < Real.log 2) : windowLevel A = 1 :=
  (windowLevel_eq_iff le_rfl).mpr ⟨by simpa using h0, by norm_num; exact h⟩

theorem windowLevel_eq_two (h2 : Real.log 2 ≤ A) (h3 : A < Real.log 3) : windowLevel A = 2 :=
  (windowLevel_eq_iff (by norm_num)).mpr ⟨by simpa using h2, by norm_num; exact h3⟩

/-! ### Each fold is an autocorrelation -/

/-- The fold of the jump by `ℓ` moves the form by `−2∫H(u)H(u+ℓ)`. -/
theorem foldEnergy_sub_count_eq (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (ℓ : ℝ) :
    foldEnergy A ℓ H - ∫ u, inWindowCount A ℓ u * H u ^ 2 = -2 * ∫ u, H u * H (u + ℓ) := by
  rw [← jump_sub_creation_eq_fold hc hcs hv]
  have iH := integrable_sq hc hcs
  have iHs : Integrable fun u => H (u + ℓ) ^ 2 :=
    integrable_sq (hc.comp (continuous_add_const ℓ)) (hasCompactSupport_comp_add hcs ℓ)
  have iP := integrable_mul_shift hc hcs ℓ
  have hexp : ∀ u, (H u - H (u + ℓ)) ^ 2 = H u ^ 2 + H (u + ℓ) ^ 2 - 2 * (H u * H (u + ℓ)) :=
    fun u => by ring
  simp_rw [hexp]
  rw [integral_add_sub_two_mul iH iHs iP, integral_add_right_eq_self (fun u => H u ^ 2) ℓ]
  ring

/-- The fold energy is at most twice the end mass. -/
theorem foldEnergy_le_two_mul_count (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (ℓ : ℝ) :
    foldEnergy A ℓ H ≤ 2 * ∫ u, inWindowCount A ℓ u * H u ^ 2 := by
  have h := foldEnergy_sub_count_eq hc hcs hv ℓ
  have hP : |2 * ∫ u, H u * H (u + ℓ)| ≤ ∫ u, inWindowCount A ℓ u * H u ^ 2 := by
    have h1 := jump_sub_creation_eq_fold hc hcs hv (ℓ := ℓ)
    have h2 := foldEnergy_nonneg A ℓ H
    have h3 : 0 ≤ ∫ u, (H u - H (u + ℓ)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    -- `(a + b)² ≥ 0` gives the other side: `∫(H + H(·+ℓ))² = 2∫H² + 2∫P`
    have h4 : 0 ≤ ∫ u, (H u + H (u + ℓ)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have iH := integrable_sq hc hcs
    have iHs : Integrable fun u => H (u + ℓ) ^ 2 :=
      integrable_sq (hc.comp (continuous_add_const ℓ)) (hasCompactSupport_comp_add hcs ℓ)
    have iP := integrable_mul_shift hc hcs ℓ
    have hsum : ∫ u, (H u + H (u + ℓ)) ^ 2 = 2 * (∫ u, H u ^ 2) + 2 * ∫ u, H u * H (u + ℓ) := by
      have hexp : ∀ u, (H u + H (u + ℓ)) ^ 2 =
          H u ^ 2 + H (u + ℓ) ^ 2 - 2 * (-(H u * H (u + ℓ))) := fun u => by ring
      simp_rw [hexp]
      rw [integral_add_sub_two_mul iH iHs iP.neg, integral_neg,
        integral_add_right_eq_self (fun u => H u ^ 2) ℓ]
      ring
    have hdiff : ∫ u, (H u - H (u + ℓ)) ^ 2 = 2 * (∫ u, H u ^ 2) - 2 * ∫ u, H u * H (u + ℓ) := by
      have hexp : ∀ u, (H u - H (u + ℓ)) ^ 2 =
          H u ^ 2 + H (u + ℓ) ^ 2 - 2 * (H u * H (u + ℓ)) := fun u => by ring
      simp_rw [hexp]
      rw [integral_add_sub_two_mul iH iHs iP, integral_add_right_eq_self (fun u => H u ^ 2) ℓ]
      ring
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_le] at hP
  linarith [hP.1, hP.2]

/-- **The arithmetic of a window is bounded by its canonical class**:
`|Q(H) − (Ω(0)‖H‖² + J_∞(H) + pole)| ≤ ∫ k_A H²`. -/
theorem abs_weilQuad_sub_arch_le (hH : IsWindowTest A H) :
    |weilQuad H - (EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2))| ≤
      ∫ u, canonicalDensity A u * H u ^ 2 := by
  rw [weilQuad_eq_fold_sub_canonical hH, integral_canonicalDensity_mul hH.continuous
    hH.hasCompactSupport]
  have hle : ∀ n ∈ Finset.Icc 2 (windowLevel A),
      |primeJumpWeight n * foldEnergy A (Real.log n) H -
          primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2| ≤
        primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2 := fun n _ => by
    have h1 := foldEnergy_nonneg A (Real.log n) H
    have h2 := foldEnergy_le_two_mul_count hH.continuous hH.hasCompactSupport hH.vanish
      (Real.log n) (A := A)
    have hw := primeJumpWeight_nonneg n
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    refine mul_le_mul_of_nonneg_left ?_ hw
    rw [abs_le]; constructor <;> linarith
  have := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hle)
  rw [Finset.sum_sub_distrib] at this
  have e : EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
      (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * foldEnergy A (Real.log n) H) -
        (∑ n ∈ Finset.Icc 2 (windowLevel A),
          primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2) +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) -
      (EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2)) =
      (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * foldEnergy A (Real.log n) H) -
        ∑ n ∈ Finset.Icc 2 (windowLevel A),
          primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2 := by ring
  rw [e]
  exact this

/-! ### The prime-free stage -/

/-- **Prime-free windows**: for `0 ≤ A < log 2` the canonical density vanishes. -/
theorem canonicalDensity_eq_zero_of_primeFree (h0 : 0 ≤ A) (h : A < Real.log 2) (u : ℝ) :
    canonicalDensity A u = 0 := by
  rw [canonicalDensity, windowLevel_eq_one h0 h]; rfl

/-- **Prime-free windows are archimedean**: `Q(H) = Ω(0)‖H‖² + J_∞(H) + pole` for `A < log 2`. -/
theorem weilQuad_eq_arch_of_primeFree (hH : IsWindowTest A H) (h0 : 0 ≤ A)
    (h : A < Real.log 2) :
    weilQuad H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  rw [weilQuad_eq_fold_sub_canonical hH, windowLevel_eq_one h0 h]
  simp only [Finset.Icc_self, show ¬ (2 : ℕ) ≤ 1 by norm_num, Finset.Icc_eq_empty,
    not_false_eq_true, Finset.sum_empty]
  simp_rw [canonicalDensity, windowLevel_eq_one h0 h]
  simp

/-! ### The first-prime stage -/

/-- The two ends of a fold by `ℓ` are disjoint when `A < 2ℓ`. -/
theorem ends_disjoint (h : A < 2 * ℓ) : Disjoint (Icc (-A) (-ℓ)) (Icc (ℓ - A) 0) := by
  rw [Set.disjoint_left]
  intro u h1 h2
  linarith [h1.2, h2.1]

theorem ends_disjoint_of_lt_two_log_two (h : A < 2 * Real.log 2) :
    Disjoint (Icc (-A) (-Real.log 2)) (Icc (Real.log 2 - A) 0) :=
  ends_disjoint h

/-- On disjoint ends every point has at most one in-window neighbour. -/
theorem inWindowCount_le_one (h : A < 2 * ℓ) (u : ℝ) : inWindowCount A ℓ u ≤ 1 := by
  unfold inWindowCount
  by_cases h1 : u ∈ Icc (-A) (-ℓ)
  · have h2 : u ∉ Icc (ℓ - A) 0 := Set.disjoint_left.mp (ends_disjoint h) h1
    simp [h1, h2]
  · by_cases h2 : u ∈ Icc (ℓ - A) 0 <;> simp [h1, h2]

/-- **The first-prime fold**: for `log 2 ≤ A < log 3` only `T₂` acts, by one fold. -/
theorem weilQuad_eq_firstPrimeFold (hH : IsWindowTest A H) (h2 : Real.log 2 ≤ A)
    (h3 : A < Real.log 3) :
    weilQuad H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
      primeJumpWeight 2 * (foldEnergy A (Real.log 2) H -
        ∫ u, inWindowCount A (Real.log 2) u * H u ^ 2) +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  rw [weilQuad_eq_fold_sub_canonical hH, integral_canonicalDensity_mul hH.continuous
    hH.hasCompactSupport, windowLevel_eq_two h2 h3]
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat]
  ring

/-! ### Half-folded and extremal tests -/

/-- **Half-folded tests see no prime**: a test vanishing on the left end of a fold is not acted on. -/
theorem foldEnergy_sub_count_eq_zero_of_vanish_left (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (hl : ∀ u ∈ Icc (-A) (-ℓ), H u = 0) :
    foldEnergy A ℓ H - ∫ u, inWindowCount A ℓ u * H u ^ 2 = 0 := by
  rw [foldEnergy_sub_count_eq hc hcs hv]
  have hz : (fun u => H u * H (u + ℓ)) = fun _ => (0 : ℝ) := by
    funext u
    by_cases hu : u ∈ Icc (-A) (-ℓ)
    · rw [hl u hu, zero_mul]
    · by_cases h1 : u ∈ Icc (-A) 0
      · rw [hv (u + ℓ) fun hm => hu ⟨h1.1, by linarith [hm.2]⟩, mul_zero]
      · rw [hv u h1, zero_mul]
  rw [hz, integral_zero, mul_zero]

/-- A **fold-symmetric** test, `H(u + ℓ) = H(u)` on the left end, has zero fold energy: it pays the
full end mass. -/
theorem foldEnergy_eq_zero_of_symmetric (hs : ∀ u ∈ Icc (-A) (-ℓ), H (u + ℓ) = H u) :
    foldEnergy A ℓ H = 0 := by
  unfold foldEnergy
  have hz : (Icc (-A) (-ℓ)).indicator (fun u => (H u - H (u + ℓ)) ^ 2) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ Icc (-A) (-ℓ)
    · rw [indicator_of_mem hu, hs u hu, sub_self]; ring
    · rw [indicator_of_notMem hu]
  rw [hz, integral_zero]

/-- A **fold-antisymmetric** test, `H(u + ℓ) = −H(u)` on the left end, has fold energy equal to
twice its end mass: the fold gains what the end mass costs. -/
theorem foldEnergy_eq_of_antisymmetric (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (ha : ∀ u ∈ Icc (-A) (-ℓ), H (u + ℓ) = -H u) :
    foldEnergy A ℓ H = 2 * ∫ u, inWindowCount A ℓ u * H u ^ 2 := by
  have h := foldEnergy_sub_count_eq hc hcs hv ℓ
  have hP : ∫ u, H u * H (u + ℓ) = -(1 / 2) * ∫ u, inWindowCount A ℓ u * H u ^ 2 := by
    -- on the left end `H(u)H(u+ℓ) = −H(u)²` and `H(u+ℓ)² = H(u)²`
    have iH := integrable_sq hc hcs
    have hpt : ∀ u, H u * H (u + ℓ) =
        -(1 / 2) * ((Icc (-A) (-ℓ)).indicator (fun u => H u ^ 2) u +
          (Icc (-A) (-ℓ)).indicator (fun u => H (u + ℓ) ^ 2) u) := fun u => by
      by_cases hu : u ∈ Icc (-A) (-ℓ)
      · rw [indicator_of_mem hu, indicator_of_mem hu, ha u hu]; ring
      · rw [indicator_of_notMem hu, indicator_of_notMem hu]
        by_cases h1 : u ∈ Icc (-A) 0
        · rw [hv (u + ℓ) fun hm => hu ⟨h1.1, by linarith [hm.2]⟩]; ring
        · rw [hv u h1]; ring
    have iHs : Integrable fun u => H (u + ℓ) ^ 2 :=
      integrable_sq (hc.comp (continuous_add_const ℓ)) (hasCompactSupport_comp_add hcs ℓ)
    have htr : ∫ u, (Icc (-A) (-ℓ)).indicator (fun u => H (u + ℓ) ^ 2) u =
        ∫ u, (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u := by
      rw [← integral_add_right_eq_self (fun u => (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u) ℓ]
      congr 1
      funext u
      have hiff : u + ℓ ∈ Icc (ℓ - A) 0 ↔ u ∈ Icc (-A) (-ℓ) := by
        simp only [mem_Icc]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
      by_cases hu : u ∈ Icc (-A) (-ℓ)
      · rw [indicator_of_mem hu, indicator_of_mem (hiff.mpr hu)]
      · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mp h))]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
      integral_add (iH.indicator measurableSet_Icc) (iHs.indicator measurableSet_Icc), htr,
      integral_congr_ae (Eventually.of_forall fun u => inWindowCount_mul A ℓ u fun u => H u ^ 2),
      integral_add (iH.indicator measurableSet_Icc) (iH.indicator measurableSet_Icc)]
  rw [hP] at h
  linarith

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
