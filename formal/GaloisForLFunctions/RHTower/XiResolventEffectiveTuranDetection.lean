import GaloisForLFunctions.RHTower.XiResolventEvenTuranMachine

/-!
# The effective Turán detection window

The parity-robust level-cleansing machine consumes even-index minor nonnegativity only up to a
truncation length.  Re-quantifying its master estimate turns the infinitary Cesàro contradiction
into an explicit detection-index bound: if a copy at level `ℓ` lies off the critical line, some
even-index weighted Turán minor with index below

  `(2S²B² / g + B²S² / (ℓ² − ρ₂²)) / (Im(u)² · |W|²)`

is already negative, where `S` bounds the total resolvent mass, `B` the weight, `g` the spectral
gap `‖V² − 1‖` over non-resonant level pairs, `ρ₂` the sub-level moduli, and `Im(u)²|W|²` the
off-line defect of the witness.  The three constants of the master estimate are controlled by
elementary counting: the level holds at most `S/ℓ` copies, each non-resonant pair contributes at
most `8ℓ²B²/g`, and the sub-level tail is a geometric series with ratio `(ρ₂/ℓ)²` and total mass
at most `S²`.

Consequently finitely many even minors certify that a level is clean of zeros down to any given
defect threshold, and — with the constant weight at the maximal modulus — finitely many *plain*
even Turán minors of the raw resolvent moments detect an off-line zero at the top level.
-/

open Complex

namespace RHTower

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **The effective detection window**: any truncation length all of whose even-index weighted
Turán minors are nonnegative is bounded by the explicit ratio of the configuration constants to
the off-line defect of a witness at the level. -/
theorem even_minor_truncation_le_of_offline_level {X : ℝ} (hX : 0 ≤ X)
    {Wf : XiZeroCopy → ℂ} {BW : ℝ} (hWbound : ∀ q, ‖Wf q‖ ≤ BW)
    (hval : ∀ q q' : XiZeroCopy,
      xiResolventPoint X q' = (starRingEnd ℂ) (xiResolventPoint X q) →
      Wf q' = (starRingEnd ℂ) (Wf q))
    {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ → Wf q = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0) (hWqh : Wf qh ≠ 0)
    {N : ℕ} (hminor : ∀ n : ℕ, n < N → 0 ≤ (xiWeightedResolventMoment Wf (2 * n) X *
      xiWeightedResolventMoment Wf (2 * n + 2) X -
      xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ)).re) :
    (N : ℝ) ≤ (2 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g + BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      ((xiResolventPoint X qh).im ^ (2 : ℕ) * Complex.normSq (Wf qh)) := by
  classical
  have hBW0 : 0 ≤ BW := le_trans (norm_nonneg _) (hWbound qh)
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  -- summability of the weighted atoms
  have hatom : ∀ k : ℕ, Summable (fun q : XiZeroCopy => u q ^ (k + 1) * Wf q) := by
    intro k
    refine Summable.of_norm_bounded
      ((summable_norm_xiResolventPoint hX).mul_right BW) fun q => ?_
    rw [norm_mul]
    have h1 : ‖u q ^ (k + 1)‖ ≤ ‖u q‖ := by
      rw [norm_pow, pow_succ']
      have hle1 : ‖u q‖ ^ k ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX q)
      nlinarith [norm_nonneg (u q), pow_nonneg (norm_nonneg (u q)) k]
    exact mul_le_mul h1 (hWbound q) (norm_nonneg _) (norm_nonneg _)
  have hatomnorm : ∀ k : ℕ, Summable (fun q : XiZeroCopy => ‖u q ^ (k + 1) * Wf q‖) :=
    fun k => (hatom k).norm
  -- the weighted moments are the atom sums
  have hmom : ∀ k : ℕ, xiWeightedResolventMoment Wf k X =
      ∑' q : XiZeroCopy, u q ^ (k + 1) * Wf q := fun k => rfl
  -- the weighted pair expansion
  have hpairsummable : ∀ n : ℕ, Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ)) := by
    intro n
    have hsum := summable_mul_of_summable_norm (hatomnorm n) (hatomnorm n)
    have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ) =
        (u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2) *
          (u z.1 - u z.2) ^ (2 : ℕ) := by
      intro z
      ring
    rw [show (fun z : XiZeroCopy × XiZeroCopy =>
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ)) = fun z =>
        (u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2) *
          (u z.1 - u z.2) ^ (2 : ℕ) from funext hpt]
    refine Summable.of_norm_bounded (g := fun z =>
      ‖(u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2)‖ * (2 * 1) ^ (2 : ℕ))
      (hsum.norm.mul_right _) fun z => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_xiResolventPoint_le_one hX z.1)
          (norm_xiResolventPoint_le_one hX z.2)
      _ = 2 * 1 := by ring
  have hpair : ∀ n : ℕ, 2 * (xiWeightedResolventMoment Wf n X *
      xiWeightedResolventMoment Wf (n + 2) X -
      xiWeightedResolventMoment Wf (n + 1) X ^ (2 : ℕ)) =
      ∑' z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ) := by
    intro n
    have hA := tsum_mul_tsum_of_summable_norm (hatomnorm n) (hatomnorm (n + 2))
    have hB := tsum_mul_tsum_of_summable_norm (hatomnorm (n + 1)) (hatomnorm (n + 1))
    have hC := tsum_mul_tsum_of_summable_norm (hatomnorm (n + 2)) (hatomnorm n)
    have hsumA := summable_mul_of_summable_norm (hatomnorm n) (hatomnorm (n + 2))
    have hsumB := summable_mul_of_summable_norm (hatomnorm (n + 1)) (hatomnorm (n + 1))
    have hsumC := summable_mul_of_summable_norm (hatomnorm (n + 2)) (hatomnorm n)
    have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ) =
        (((u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 2 + 1) * Wf z.2) -
          2 * ((u z.1 ^ (n + 1 + 1) * Wf z.1) * (u z.2 ^ (n + 1 + 1) * Wf z.2))) +
          (u z.1 ^ (n + 2 + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2)) := by
      intro z
      ring
    rw [hmom n, hmom (n + 1), hmom (n + 2),
      tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
      hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
    ring
  -- the level as a finite set
  have hSfinset : {q : XiZeroCopy | ℓ ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hℓpos
  set SF : Finset XiZeroCopy :=
    hSfinset.toFinset.filter (fun q => ‖xiResolventPoint X q‖ = ℓ) with hSF
  have hmemSF : ∀ q, q ∈ SF ↔ ‖xiResolventPoint X q‖ = ℓ := by
    intro q
    rw [hSF, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by rw [Set.mem_setOf_eq, h], h⟩
  have hqhSF : qh ∈ SF := (hmemSF qh).mpr hqhℓ
  -- pair machinery
  set V : XiZeroCopy × XiZeroCopy → ℂ := fun z => u z.1 * u z.2 / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)
    with hV
  set TT : Finset (XiZeroCopy × XiZeroCopy) := SF ×ˢ SF with hTT
  have hℓC : (((ℓ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓpos.ne'
  have hprodsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ‖u z.1‖ * ‖u z.2‖) := by
    have h := summable_mul_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using (summable_norm_xiResolventPoint hX))
      (by simpa using (summable_norm_xiResolventPoint hX))
    simpa using h
  set P₀ : ℝ := ∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
    ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ with hP₀
  have hP₀nn : 0 ≤ P₀ :=
    tsum_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- tail term bound
  have htailterm : ∀ n : ℕ, ∀ z : XiZeroCopy × XiZeroCopy, z ∉ TT →
      ‖(u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ)‖ ≤
      (ρ₂ * ℓ) ^ n * ((4 * BW ^ (2 : ℕ)) * (‖u z.1‖ * ‖u z.2‖)) := by
    intro n z hz
    have hcases : ¬ ‖u z.1‖ = ℓ ∨ ¬ ‖u z.2‖ = ℓ := by
      by_contra hcon2
      rw [not_or, not_not, not_not] at hcon2
      refine hz ?_
      rw [hTT, Finset.mem_product]
      exact ⟨(hmemSF z.1).mpr hcon2.1, (hmemSF z.2).mpr hcon2.2⟩
    have hsplit1 : ∀ q : XiZeroCopy, ¬ ‖u q‖ = ℓ →
        Wf q = 0 ∨ ‖u q‖ ≤ ρ₂ := by
      intro q hq
      rcases lt_trichotomy ‖u q‖ ℓ with h | h | h
      · exact Or.inr (hρ₂bound q h)
      · exact absurd h hq
      · exact Or.inl (hkill q h)
    have hdiffb : ‖(u z.1 - u z.2) ^ (2 : ℕ)‖ ≤ 4 := by
      rw [norm_pow]
      have h4 : ‖u z.1 - u z.2‖ ≤ 2 := by
        calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (norm_xiResolventPoint_le_one hX z.1)
              (norm_xiResolventPoint_le_one hX z.2)
          _ = 2 := by norm_num
      nlinarith [norm_nonneg (u z.1 - u z.2)]
    have hzero : Wf z.1 = 0 ∨ Wf z.2 = 0 ∨
        ((‖u z.1‖ ≤ ρ₂ ∧ ‖u z.2‖ ≤ ℓ) ∨ (‖u z.1‖ ≤ ℓ ∧ ‖u z.2‖ ≤ ρ₂)) := by
      rcases hcases with hq | hq
      · rcases hsplit1 z.1 hq with h | h
        · exact Or.inl h
        · rcases lt_or_ge ℓ ‖u z.2‖ with h2 | h2
          · exact Or.inr (Or.inl (hkill z.2 h2))
          · exact Or.inr (Or.inr (Or.inl ⟨h, h2⟩))
      · rcases hsplit1 z.2 hq with h | h
        · exact Or.inr (Or.inl h)
        · rcases lt_or_ge ℓ ‖u z.1‖ with h2 | h2
          · exact Or.inl (hkill z.1 h2)
          · exact Or.inr (Or.inr (Or.inr ⟨h2, h⟩))
    rcases hzero with hi | hi | hb
    · rw [hi]
      simp only [mul_zero, zero_mul, norm_zero]
      positivity
    · rw [hi]
      simp only [mul_zero, zero_mul, norm_zero]
      positivity
    · have hWb : ‖Wf z.1 * Wf z.2‖ ≤ BW ^ (2 : ℕ) := by
        rw [norm_mul]
        calc ‖Wf z.1‖ * ‖Wf z.2‖ ≤ BW * BW :=
              mul_le_mul (hWbound z.1) (hWbound z.2) (norm_nonneg _) hBW0
          _ = BW ^ (2 : ℕ) := by ring
      have hpowb : ‖(u z.1 * u z.2) ^ (n + 1)‖ ≤ (ρ₂ * ℓ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
        rw [norm_pow, norm_mul, mul_pow]
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 : ‖u z.1‖ ^ (n + 1) ≤ ρ₂ ^ n * ‖u z.1‖ := by
            rw [pow_succ']
            calc ‖u z.1‖ * ‖u z.1‖ ^ n ≤ ‖u z.1‖ * ρ₂ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (norm_nonneg _) h1 n) (norm_nonneg _)
              _ = ρ₂ ^ n * ‖u z.1‖ := mul_comm _ _
          have e2 : ‖u z.2‖ ^ (n + 1) ≤ ℓ ^ n * ‖u z.2‖ := by
            rw [pow_succ']
            calc ‖u z.2‖ * ‖u z.2‖ ^ n ≤ ‖u z.2‖ * ℓ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (norm_nonneg _) h2 n) (norm_nonneg _)
              _ = ℓ ^ n * ‖u z.2‖ := mul_comm _ _
          calc ‖u z.1‖ ^ (n + 1) * ‖u z.2‖ ^ (n + 1)
              ≤ (ρ₂ ^ n * ‖u z.1‖) * (ℓ ^ n * ‖u z.2‖) :=
                mul_le_mul e1 e2 (pow_nonneg (norm_nonneg _) _) (by positivity)
            _ = (ρ₂ * ℓ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
                rw [mul_pow]
                ring
        · have e1 : ‖u z.1‖ ^ (n + 1) ≤ ℓ ^ n * ‖u z.1‖ := by
            rw [pow_succ']
            calc ‖u z.1‖ * ‖u z.1‖ ^ n ≤ ‖u z.1‖ * ℓ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (norm_nonneg _) h1 n) (norm_nonneg _)
              _ = ℓ ^ n * ‖u z.1‖ := mul_comm _ _
          have e2 : ‖u z.2‖ ^ (n + 1) ≤ ρ₂ ^ n * ‖u z.2‖ := by
            rw [pow_succ']
            calc ‖u z.2‖ * ‖u z.2‖ ^ n ≤ ‖u z.2‖ * ρ₂ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (norm_nonneg _) h2 n) (norm_nonneg _)
              _ = ρ₂ ^ n * ‖u z.2‖ := mul_comm _ _
          calc ‖u z.1‖ ^ (n + 1) * ‖u z.2‖ ^ (n + 1)
              ≤ (ℓ ^ n * ‖u z.1‖) * (ρ₂ ^ n * ‖u z.2‖) :=
                mul_le_mul e1 e2 (pow_nonneg (norm_nonneg _) _) (by positivity)
            _ = (ρ₂ * ℓ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
                rw [mul_pow]
                ring
      calc ‖(u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ (2 : ℕ)‖
          = ‖(u z.1 * u z.2) ^ (n + 1)‖ * ‖Wf z.1 * Wf z.2‖ *
              ‖(u z.1 - u z.2) ^ (2 : ℕ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ((ρ₂ * ℓ) ^ n * (‖u z.1‖ * ‖u z.2‖)) * BW ^ (2 : ℕ) * 4 := by
            refine mul_le_mul (mul_le_mul hpowb hWb (norm_nonneg _) (by positivity))
              hdiffb (norm_nonneg _) (by positivity)
        _ = (ρ₂ * ℓ) ^ n * ((4 * BW ^ (2 : ℕ)) * (‖u z.1‖ * ‖u z.2‖)) := by ring
  -- unit pair points at the level
  have hVnorm : ∀ z ∈ TT, ‖V z‖ = 1 := by
    intro z hz
    rw [hTT, Finset.mem_product] at hz
    simp only [hV]
    rw [norm_div, norm_mul, norm_pow, (hmemSF z.1).mp hz.1, (hmemSF z.2).mp hz.2,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓpos, pow_two]
    exact div_self (by positivity)
  -- no pair point sits at `-1`: resolvent points have positive real part
  have hVneg : ∀ z ∈ TT, V z ≠ -1 := by
    intro z hz hVz
    rw [hTT, Finset.mem_product] at hz
    have hz1ne : u z.1 ≠ 0 := xiResolventPoint_ne_zero hX z.1
    have h1 : u z.1 * u z.2 = -(((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) := by
      have h0 := hVz
      simp only [hV] at h0
      rw [div_eq_iff (pow_ne_zero 2 hℓC)] at h0
      rw [h0]
      ring
    have h2 : u z.1 * (starRingEnd ℂ) (u z.1) = (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) := by
      rw [Complex.mul_conj, ← Complex.ofReal_pow]
      norm_cast
      rw [← Complex.sq_norm, (hmemSF z.1).mp hz.1]
    have hconj : u z.2 = -(starRingEnd ℂ) (u z.1) := by
      refine mul_left_cancel₀ hz1ne ?_
      rw [h1, mul_neg, h2]
    have hre2 : (u z.2).re = -(u z.1).re := by
      rw [hconj, Complex.neg_re, Complex.conj_re]
    have hp1 : 0 < (u z.1).re := xiResolventPoint_re_pos hX z.1
    have hp2 : 0 < (u z.2).re := xiResolventPoint_re_pos hX z.2
    rw [hre2] at hp2
    linarith
  -- non-resonant pair points have non-resonant squares
  have hV2ne : ∀ z ∈ TT, V z ≠ 1 → V z ^ (2 : ℕ) ≠ 1 := by
    intro z hz hV1 hV2
    have hfac : (V z - 1) * (V z + 1) = 0 := by linear_combination hV2
    rcases mul_eq_zero.mp hfac with h | h
    · exact hV1 (sub_eq_zero.mp h)
    · refine hVneg z hz ?_
      linear_combination h
  -- pair points at `1` are conjugate pairs with nonpositive real weight
  have hP1w : ∀ z ∈ TT, V z = 1 → Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ) =
      ((-(4 * ((u z.1).im ^ (2 : ℕ) * Complex.normSq (Wf z.1))) : ℝ) : ℂ) := by
    intro z hz hVz
    rw [hTT, Finset.mem_product] at hz
    have hz1ne : u z.1 ≠ 0 := xiResolventPoint_ne_zero hX z.1
    have h1 : u z.1 * u z.2 = (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) := by
      have h0 := hVz
      simp only [hV] at h0
      rw [div_eq_iff (pow_ne_zero 2 hℓC), one_mul] at h0
      exact h0
    have h2 : u z.1 * (starRingEnd ℂ) (u z.1) = (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) := by
      rw [Complex.mul_conj, ← Complex.ofReal_pow]
      norm_cast
      rw [← Complex.sq_norm, (hmemSF z.1).mp hz.1]
    have hconj : u z.2 = (starRingEnd ℂ) (u z.1) :=
      mul_left_cancel₀ hz1ne (h1.trans h2.symm)
    have hWconj : Wf z.2 = (starRingEnd ℂ) (Wf z.1) := hval z.1 z.2 hconj
    have hprod : Wf z.1 * Wf z.2 = ((Complex.normSq (Wf z.1) : ℝ) : ℂ) := by
      rw [hWconj, Complex.mul_conj]
    have hdiff : (u z.1 - u z.2) ^ (2 : ℕ) = ((-(4 * (u z.1).im ^ (2 : ℕ)) : ℝ) : ℂ) := by
      rw [hconj, Complex.sub_conj, mul_pow, Complex.I_sq]
      push_cast
      ring
    rw [hprod, hdiff, ← Complex.ofReal_mul]
    push_cast
    ring
  -- the witness conjugate pair
  set zh : XiZeroCopy × XiZeroCopy := (qh, xiZeroCopyLineConjEquiv qh) with hzh
  have hlineconj : u (xiZeroCopyLineConjEquiv qh) = (starRingEnd ℂ) (u qh) :=
    xiResolventPoint_lineConj X qh
  have hconjnorm : ‖xiResolventPoint X (xiZeroCopyLineConjEquiv qh)‖ = ℓ := by
    rw [show ‖xiResolventPoint X (xiZeroCopyLineConjEquiv qh)‖ =
      ‖u (xiZeroCopyLineConjEquiv qh)‖ from rfl, hlineconj, RCLike.norm_conj]
    exact hqhℓ
  have hzhTT : zh ∈ TT := by
    rw [hzh, hTT, Finset.mem_product]
    exact ⟨hqhSF, (hmemSF _).mpr hconjnorm⟩
  have hVzh : V zh = 1 := by
    simp only [hV, hzh]
    rw [show u (qh, xiZeroCopyLineConjEquiv qh).2 = (starRingEnd ℂ) (u qh) from hlineconj]
    rw [show u (qh, xiZeroCopyLineConjEquiv qh).1 = u qh from rfl]
    rw [Complex.mul_conj, ← Complex.ofReal_pow]
    rw [show Complex.normSq (u qh) = ℓ ^ (2 : ℕ) by
      rw [← Complex.sq_norm]
      rw [show ‖u qh‖ = ℓ from hqhℓ]]
    exact div_self (Complex.ofReal_ne_zero.mpr (by positivity))
  -- the strictly positive defect at the witness
  set β : ℝ := (u qh).im ^ (2 : ℕ) * Complex.normSq (Wf qh) with hβdef
  have hβ : 0 < β := by
    rw [hβdef]
    have him := xiResolventPoint_im_ne_zero_of_spectral hX hoff
    have hnsq : 0 < Complex.normSq (Wf qh) :=
      Complex.normSq_pos.mpr hWqh
    positivity
  -- geometric bound and constants, with squared ratio
  have hκ2 : ρ₂ / ℓ < 1 := (div_lt_one hℓpos).mpr hρ₂lt
  have hκ0' : (0 : ℝ) ≤ ρ₂ / ℓ := div_nonneg hρ₂0 hℓpos.le
  have hκsq : (ρ₂ / ℓ) ^ (2 : ℕ) < 1 := by nlinarith
  have h1κ : (0 : ℝ) < 1 - (ρ₂ / ℓ) ^ (2 : ℕ) := by linarith
  have hgeo : ∀ M : ℕ, ∑ n ∈ Finset.range M, ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ n ≤
      1 / (1 - (ρ₂ / ℓ) ^ (2 : ℕ)) := by
    intro M
    rw [geom_sum_eq (ne_of_lt hκsq)]
    rw [show ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ M - 1 = -(1 - ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ M) by ring,
      show (ρ₂ / ℓ) ^ (2 : ℕ) - 1 = -(1 - (ρ₂ / ℓ) ^ (2 : ℕ)) by ring, neg_div_neg_eq]
    rw [div_le_div_iff₀ h1κ h1κ]
    nlinarith [pow_nonneg (pow_nonneg hκ0' 2) M]
  set CT : ℝ := 4 * BW ^ (2 : ℕ) * P₀ / ℓ ^ (2 : ℕ) * (1 / (1 - (ρ₂ / ℓ) ^ (2 : ℕ))) with hCT
  set CP2 : ℝ := ∑ z ∈ TT.filter (fun z => ¬ V z = 1),
    ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ * (2 / ‖V z ^ (2 : ℕ) - 1‖) with hCP2
  -- the tail bound at level n
  have htail : ∀ n : ℕ,
      ‖∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
        (u (↑zc : XiZeroCopy × XiZeroCopy).1 * u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
          (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 * Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 - u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)‖ ≤
        (ρ₂ * ℓ) ^ n * ((4 * BW ^ (2 : ℕ)) * P₀) := by
    intro n
    have hsubpair := ((hpairsummable n).norm.subtype
      ((↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ))
    have hsubprod := hprodsum.subtype ((↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ)
    calc ‖∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
            (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
              Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)‖
        ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)‖ :=
          norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (ρ₂ * ℓ) ^ n * ((4 * BW ^ (2 : ℕ)) *
              (‖u (↑zc : XiZeroCopy × XiZeroCopy).1‖ *
                ‖u (↑zc : XiZeroCopy × XiZeroCopy).2‖)) := by
          refine Summable.tsum_le_tsum (fun zc => ?_) hsubpair
            (((hsubprod.mul_left ((4 * BW ^ (2 : ℕ)))).mul_left ((ρ₂ * ℓ) ^ n)))
          have hznot : (↑zc : XiZeroCopy × XiZeroCopy) ∉ TT := by
            have h := zc.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          exact htailterm n _ hznot
      _ = (ρ₂ * ℓ) ^ n * ((4 * BW ^ (2 : ℕ)) * P₀) := by
          rw [tsum_mul_left, tsum_mul_left, hP₀]
  -- the master estimate at the given truncation
  have hmaster : 0 ≤ -(4 * β) * (N : ℝ) + CP2 + CT := by
    have hlhs : 0 ≤ ∑ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf (2 * n) X *
          xiWeightedResolventMoment Wf (2 * n + 2) X -
          xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ))).re / ℓ ^ (2 * (2 * n + 1)) := by
      refine Finset.sum_nonneg fun n hn => ?_
      have h1 := hminor n (Finset.mem_range.mp hn)
      have h2 : (2 * (xiWeightedResolventMoment Wf (2 * n) X *
          xiWeightedResolventMoment Wf (2 * n + 2) X -
          xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ))).re =
          2 * (xiWeightedResolventMoment Wf (2 * n) X *
            xiWeightedResolventMoment Wf (2 * n + 2) X -
            xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ)).re := by
        simp [Complex.mul_re]
      rw [h2]
      have h3 : (0 : ℝ) < ℓ ^ (2 * (2 * n + 1)) := pow_pos hℓpos _
      positivity
    have hn : ∀ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf (2 * n) X *
          xiWeightedResolventMoment Wf (2 * n + 2) X -
          xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ))).re / ℓ ^ (2 * (2 * n + 1)) =
        (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) * V z ^ (2 * n + 1)).re +
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)).re /
            ℓ ^ (2 * (2 * n + 1)) := by
      intro n _
      have hexp := hpair (2 * n)
      have hsplit := (hpairsummable (2 * n)).sum_add_tsum_compl (s := TT)
      have hEq : (2 : ℂ) * (xiWeightedResolventMoment Wf (2 * n) X *
          xiWeightedResolventMoment Wf (2 * n + 2) X -
          xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (2 * n + 1) * (Wf z.1 * Wf z.2) *
            (u z.1 - u z.2) ^ (2 : ℕ)) +
            ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
                (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ) := by
        rw [hexp]
        exact hsplit.symm
      have hre := congrArg Complex.re hEq
      rw [Complex.add_re] at hre
      rw [hre, add_div]
      congr 1
      have hCfin : (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
          V z ^ (2 * n + 1)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (2 * n + 1) * (Wf z.1 * Wf z.2) *
            (u z.1 - u z.2) ^ (2 : ℕ)) / ((ℓ ^ (2 * (2 * n + 1)) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        have hden : ((((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 * n + 1) =
            ((ℓ ^ (2 * (2 * n + 1)) : ℝ) : ℂ) := by
          push_cast
          ring
        simp only [hV]
        rw [div_pow, hden]
        ring
      rw [hCfin, re_div_ofReal]
    have hdecomp : ∑ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf (2 * n) X *
          xiWeightedResolventMoment Wf (2 * n + 2) X -
          xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ))).re / ℓ ^ (2 * (2 * n + 1)) =
        (∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
            ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re) +
          ∑ n ∈ Finset.range N,
            (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
                (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)).re /
              ℓ ^ (2 * (2 * n + 1)) := by
      rw [Finset.sum_congr rfl hn, Finset.sum_add_distrib]
      congr 1
      calc ∑ n ∈ Finset.range N,
          (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) * V z ^ (2 * n + 1)).re
          = ∑ n ∈ Finset.range N, ∑ z ∈ TT,
              ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) * V z ^ (2 * n + 1)).re :=
            Finset.sum_congr rfl fun n _ => Complex.re_sum _ _
        _ = ∑ z ∈ TT, ∑ n ∈ Finset.range N,
              ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) * V z ^ (2 * n + 1)).re :=
            Finset.sum_comm
        _ = ∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
              ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum, Complex.re_sum]
    have hedge : (∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
        ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re) ≤ -(4 * β) * N + CP2 := by
      rw [← Finset.sum_filter_add_sum_filter_not TT (fun z => V z = 1)]
      have hpart1 : (∑ z ∈ TT.filter (fun z => V z = 1),
          ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
            ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re) ≤ -(4 * β) * N := by
        have hterm : ∀ z ∈ TT.filter (fun z => V z = 1),
            ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
              ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re =
              -(4 * ((u z.1).im ^ (2 : ℕ) * Complex.normSq (Wf z.1))) * (N : ℝ) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [hP1w z hz.1 hz.2, hz.2]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [Finset.sum_congr rfl hterm]
        have hzhfil : zh ∈ TT.filter (fun z => V z = 1) :=
          Finset.mem_filter.mpr ⟨hzhTT, hVzh⟩
        rw [← Finset.add_sum_erase _ _ hzhfil]
        have h1 : -(4 * ((u zh.1).im ^ (2 : ℕ) * Complex.normSq (Wf zh.1))) * (N : ℝ) =
            -(4 * β) * N := by
          simp only [hzh, hβdef]
        have h2 : ∑ z ∈ (TT.filter (fun z => V z = 1)).erase zh,
            -(4 * ((u z.1).im ^ (2 : ℕ) * Complex.normSq (Wf z.1))) * (N : ℝ) ≤ 0 := by
          refine Finset.sum_nonpos fun z _ => ?_
          have h3 : (0 : ℝ) ≤ 4 * ((u z.1).im ^ (2 : ℕ) * Complex.normSq (Wf z.1)) * N := by
            have := Complex.normSq_nonneg (Wf z.1)
            positivity
          linarith
        rw [h1]
        linarith
      have hpart2 : (∑ z ∈ TT.filter (fun z => ¬ V z = 1),
          ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
            ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re) ≤ CP2 := by
        rw [hCP2]
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Finset.mem_filter] at hz
        have hVn1 : ‖V z‖ = 1 := hVnorm z hz.1
        have hV2 : V z ^ (2 : ℕ) ≠ 1 := hV2ne z hz.1 hz.2
        have hsq : ∑ n ∈ Finset.range N, V z ^ (2 * n + 1) =
            V z * ∑ n ∈ Finset.range N, (V z ^ (2 : ℕ)) ^ n := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [pow_succ', ← pow_mul]
        have hb : ‖∑ n ∈ Finset.range N, V z ^ (2 * n + 1)‖ ≤ 2 / ‖V z ^ (2 : ℕ) - 1‖ := by
          rw [hsq, norm_mul, hVn1, one_mul]
          exact GaloisForLFunctions.HTGeometry.norm_geom_sum_le_of_norm_le_one
            (le_of_eq (by rw [norm_pow, hVn1, one_pow])) hV2 N
        calc ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
            ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)).re
            ≤ ‖(Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)) *
                ∑ n ∈ Finset.range N, V z ^ (2 * n + 1)‖ := Complex.re_le_norm _
          _ = ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ *
                ‖∑ n ∈ Finset.range N, V z ^ (2 * n + 1)‖ := norm_mul _ _
          _ ≤ ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ * (2 / ‖V z ^ (2 : ℕ) - 1‖) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      linarith
    have htailN : ∑ n ∈ Finset.range N,
        (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
            (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
              Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)).re /
          ℓ ^ (2 * (2 * n + 1)) ≤ CT := by
      rw [hCT]
      calc ∑ n ∈ Finset.range N,
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ)).re /
            ℓ ^ (2 * (2 * n + 1))
          ≤ ∑ n ∈ Finset.range N, 4 * BW ^ (2 : ℕ) * P₀ / ℓ ^ (2 : ℕ) * ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h1 := htail (2 * n)
            have h2 := Complex.re_le_norm
              (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 * n + 1) *
                  (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                    Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                  (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                    u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (2 : ℕ))
            have hd : (0 : ℝ) < ℓ ^ (2 * (2 * n + 1)) := pow_pos hℓpos _
            rw [div_le_iff₀ hd]
            have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
            have hr : ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ n = ρ₂ ^ (2 * n) / ℓ ^ (2 * n) := by
              rw [← pow_mul, div_pow]
            have h2npow : ℓ ^ (2 * (2 * n + 1)) = ℓ ^ (2 * n) * ℓ ^ (2 * n) * ℓ ^ (2 : ℕ) := by
              rw [← pow_add, ← pow_add]
              congr 1
              ring
            have halg : (ρ₂ * ℓ) ^ (2 * n) * ((4 * BW ^ (2 : ℕ)) * P₀) =
                4 * BW ^ (2 : ℕ) * P₀ / ℓ ^ (2 : ℕ) * ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ n * ℓ ^ (2 * (2 * n + 1)) := by
              rw [hr, h2npow, mul_pow]
              field_simp
            linarith
        _ = 4 * BW ^ (2 : ℕ) * P₀ / ℓ ^ (2 : ℕ) * ∑ n ∈ Finset.range N, ((ρ₂ / ℓ) ^ (2 : ℕ)) ^ n := by
            rw [Finset.mul_sum]
        _ ≤ 4 * BW ^ (2 : ℕ) * P₀ / ℓ ^ (2 : ℕ) * (1 / (1 - (ρ₂ / ℓ) ^ (2 : ℕ))) := by
            refine mul_le_mul_of_nonneg_left (hgeo N) ?_
            positivity
    have hfinal := hlhs
    rw [hdecomp] at hfinal
    linarith
  -- effective bound on the level-pair constant: at most `(S/ℓ)²` pairs, each at most `8ℓ²B²/g`
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  have hS0 : 0 ≤ S :=
    le_trans (tsum_nonneg fun q : XiZeroCopy => norm_nonneg (xiResolventPoint X q)) hS
  have hcardSF : (SF.card : ℝ) * ℓ ≤ S := by
    have h1 : ∑ q ∈ SF, ‖xiResolventPoint X q‖ = (SF.card : ℝ) * ℓ := by
      rw [Finset.sum_congr rfl fun q hq => (hmemSF q).mp hq, Finset.sum_const,
        nsmul_eq_mul]
    have h2 : ∑ q ∈ SF, ‖xiResolventPoint X q‖ ≤
        ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ :=
      (summable_norm_xiResolventPoint hX).sum_le_tsum SF fun q _ => norm_nonneg _
    linarith
  have hCP2bound : CP2 ≤ 8 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g := by
    have hterm : ∀ z ∈ TT.filter (fun z => ¬ V z = 1),
        ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ * (2 / ‖V z ^ (2 : ℕ) - 1‖) ≤
          8 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ) / g := by
      intro z hz
      rw [Finset.mem_filter] at hz
      have hzTT := hz.1
      rw [hTT, Finset.mem_product] at hzTT
      have h1 : ‖xiResolventPoint X z.1‖ = ℓ := (hmemSF z.1).mp hzTT.1
      have h2 : ‖xiResolventPoint X z.2‖ = ℓ := (hmemSF z.2).mp hzTT.2
      have hne : xiResolventPoint X z.1 * xiResolventPoint X z.2 ≠
          (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) := by
        intro hcon
        refine hz.2 ?_
        show u z.1 * u z.2 / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) = 1
        rw [show u z.1 * u z.2 = (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) from hcon]
        exact div_self (pow_ne_zero 2 hℓC)
      have hgapz : g ≤ ‖V z ^ (2 : ℕ) - 1‖ := hgap z.1 z.2 h1 h2 hne
      have hfrac : 2 / ‖V z ^ (2 : ℕ) - 1‖ ≤ 2 / g :=
        div_le_div_of_nonneg_left (by norm_num) hg hgapz
      have hWnorm : ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ ≤ 4 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ) := by
        rw [norm_mul, norm_mul, norm_pow]
        have hd : ‖u z.1 - u z.2‖ ≤ 2 * ℓ := by
          calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
            _ = 2 * ℓ := by
                rw [show ‖u z.1‖ = ℓ from h1, show ‖u z.2‖ = ℓ from h2]
                ring
        have hd2 : ‖u z.1 - u z.2‖ ^ (2 : ℕ) ≤ (2 * ℓ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hd 2
        have hWW : ‖Wf z.1‖ * ‖Wf z.2‖ ≤ BW ^ (2 : ℕ) := by
          calc ‖Wf z.1‖ * ‖Wf z.2‖ ≤ BW * BW :=
                mul_le_mul (hWbound z.1) (hWbound z.2) (norm_nonneg _) hBW0
            _ = BW ^ (2 : ℕ) := by ring
        calc ‖Wf z.1‖ * ‖Wf z.2‖ * ‖u z.1 - u z.2‖ ^ (2 : ℕ) ≤ BW ^ (2 : ℕ) * (2 * ℓ) ^ (2 : ℕ) :=
              mul_le_mul hWW hd2 (by positivity) (by positivity)
          _ = 4 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ) := by ring
      calc ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ (2 : ℕ)‖ * (2 / ‖V z ^ (2 : ℕ) - 1‖)
          ≤ (4 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ)) * (2 / g) := by
            refine mul_le_mul hWnorm hfrac
              (div_nonneg (by norm_num) (norm_nonneg _)) ?_
            positivity
        _ = 8 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ) / g := by ring
    have hstep := Finset.sum_le_card_nsmul (TT.filter (fun z => ¬ V z = 1)) _ _ hterm
    rw [nsmul_eq_mul] at hstep
    have hcardf : ((TT.filter (fun z => ¬ V z = 1)).card : ℝ) ≤
        (SF.card : ℝ) * (SF.card : ℝ) := by
      have hc1 : (TT.filter (fun z => ¬ V z = 1)).card ≤ TT.card :=
        Finset.card_filter_le _ _
      have hc2 : TT.card = SF.card * SF.card := by
        rw [hTT, Finset.card_product]
      exact_mod_cast le_trans hc1 (le_of_eq hc2)
    have hcard2 : ((SF.card : ℝ) * ℓ) ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hcardSF 2
    have hkey : ((TT.filter (fun z => ¬ V z = 1)).card : ℝ) * (8 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ)) ≤
        8 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) := by
      have e1 : ((TT.filter (fun z => ¬ V z = 1)).card : ℝ) * (ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ)) ≤
          ((SF.card : ℝ) * (SF.card : ℝ)) * (ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcardf (by positivity)
      have e2 : ((SF.card : ℝ) * ℓ) ^ (2 : ℕ) * BW ^ (2 : ℕ) ≤ S ^ (2 : ℕ) * BW ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcard2 (sq_nonneg BW)
      nlinarith [e1, e2]
    calc CP2 ≤ ((TT.filter (fun z => ¬ V z = 1)).card : ℝ) *
          (8 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ) / g) := hstep
      _ = ((TT.filter (fun z => ¬ V z = 1)).card : ℝ) * (8 * ℓ ^ (2 : ℕ) * BW ^ (2 : ℕ)) / g := by
          ring
      _ ≤ 8 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g := by
          rw [div_le_div_iff₀ hg hg]
          nlinarith [hkey, hg]
  -- effective bound on the tail constant: complement pair mass at most `S²`
  have hP₀S : P₀ ≤ S ^ (2 : ℕ) := by
    have hsplit := hprodsum.sum_add_tsum_compl (s := TT)
    have hfin : 0 ≤ ∑ z ∈ TT, ‖u z.1‖ * ‖u z.2‖ :=
      Finset.sum_nonneg fun z _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul : (∑' q : XiZeroCopy, ‖u q‖) * (∑' q : XiZeroCopy, ‖u q‖) =
        ∑' z : XiZeroCopy × XiZeroCopy, ‖u z.1‖ * ‖u z.2‖ :=
      tsum_mul_tsum_of_summable_norm
        (by simpa using summable_norm_xiResolventPoint hX)
        (by simpa using summable_norm_xiResolventPoint hX)
    have htu : ∑' q : XiZeroCopy, ‖u q‖ ≤ S := hS
    have ht0 : 0 ≤ ∑' q : XiZeroCopy, ‖u q‖ := tsum_nonneg fun q => norm_nonneg _
    have htot : ∑' z : XiZeroCopy × XiZeroCopy, ‖u z.1‖ * ‖u z.2‖ ≤ S ^ (2 : ℕ) := by
      rw [← hmul]
      nlinarith [htu, ht0]
    have hPeq : P₀ = (∑' z : XiZeroCopy × XiZeroCopy, ‖u z.1‖ * ‖u z.2‖) -
        ∑ z ∈ TT, ‖u z.1‖ * ‖u z.2‖ := by
      rw [hP₀, ← hsplit]
      ring
    rw [hPeq]
    linarith
  have hden : 0 < ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ) := by nlinarith
  have hCTbound : CT ≤ 4 * BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) := by
    have hdenne : ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ) ≠ 0 := ne_of_gt hden
    have hne2 : 1 - (ρ₂ / ℓ) ^ (2 : ℕ) ≠ 0 := ne_of_gt h1κ
    have hCTeq : CT = 4 * BW ^ (2 : ℕ) * P₀ / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) := by
      rw [hCT]
      field_simp
    rw [hCTeq, div_le_div_iff₀ hden hden]
    have e3 : 4 * BW ^ (2 : ℕ) * P₀ ≤ 4 * BW ^ (2 : ℕ) * S ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hP₀S (by positivity)
    nlinarith [e3, hden]
  -- assemble the window
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) := ⟨_, rfl⟩
  have hCP2' : CP2 ≤ 8 * A := by
    rw [hA, show (8 : ℝ) * (S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g) = 8 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g by ring]
    exact hCP2bound
  have hCT' : CT ≤ 4 * B := by
    rw [hB, show (4 : ℝ) * (BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) =
      4 * BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) by ring]
    exact hCTbound
  have hgoal : (N : ℝ) * β ≤ 2 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g + BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) := by
    rw [show 2 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g + BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ)) = 2 * A + B by
      rw [hA, hB]; ring]
    linarith [hmaster, hCP2', hCT']
  exact (le_div_iff₀ hβ).mpr hgoal

/-- **The detection form**: past the explicit window, some even-index weighted Turán minor is
already negative whenever the level holds an off-line copy with nonvanishing weight. -/
theorem exists_neg_even_minor_of_offline_level {X : ℝ} (hX : 0 ≤ X)
    {Wf : XiZeroCopy → ℂ} {BW : ℝ} (hWbound : ∀ q, ‖Wf q‖ ≤ BW)
    (hval : ∀ q q' : XiZeroCopy,
      xiResolventPoint X q' = (starRingEnd ℂ) (xiResolventPoint X q) →
      Wf q' = (starRingEnd ℂ) (Wf q))
    {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ → Wf q = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0) (hWqh : Wf qh ≠ 0)
    {N : ℕ} (hN : (2 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g + BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      ((xiResolventPoint X qh).im ^ (2 : ℕ) * Complex.normSq (Wf qh)) < (N : ℝ)) :
    ∃ n : ℕ, n < N ∧ (xiWeightedResolventMoment Wf (2 * n) X *
      xiWeightedResolventMoment Wf (2 * n + 2) X -
      xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ)).re < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hle := even_minor_truncation_le_of_offline_level hX hWbound hval hℓpos hkill
    hρ₂0 hρ₂lt hρ₂bound hS hg hgap hqhℓ hoff hWqh hcon
  linarith

/-- **The finite jet certificate**: nonnegativity of the even-index weighted Turán minors on a
finite window cleans the level of every copy whose off-line defect would place its detection
window inside the checked range. -/
theorem level_criticalLine_of_even_minors_window {X : ℝ} (hX : 0 ≤ X)
    {Wf : XiZeroCopy → ℂ} {BW : ℝ} (hWbound : ∀ q, ‖Wf q‖ ≤ BW)
    (hval : ∀ q q' : XiZeroCopy,
      xiResolventPoint X q' = (starRingEnd ℂ) (xiResolventPoint X q) →
      Wf q' = (starRingEnd ℂ) (Wf q))
    {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ → Wf q = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {N : ℕ} (hminor : ∀ n : ℕ, n < N → 0 ≤ (xiWeightedResolventMoment Wf (2 * n) X *
      xiWeightedResolventMoment Wf (2 * n + 2) X -
      xiWeightedResolventMoment Wf (2 * n + 1) X ^ (2 : ℕ)).re) :
    ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → Wf q ≠ 0 →
      (2 * S ^ (2 : ℕ) * BW ^ (2 : ℕ) / g + BW ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
        ((xiResolventPoint X q).im ^ (2 : ℕ) * Complex.normSq (Wf q)) < (N : ℝ) →
      (xiSpectralPoint q).im = 0 := by
  intro q hq hWq hlt
  by_contra hoff
  have hle := even_minor_truncation_le_of_offline_level hX hWbound hval hℓpos hkill
    hρ₂0 hρ₂lt hρ₂bound hS hg hgap hq hoff hWq hminor
  linarith

/-- The constant weight `1` turns the weighted moments into the raw resolvent moments. -/
theorem xiWeightedResolventMoment_one (k : ℕ) (X : ℝ) :
    xiWeightedResolventMoment (fun _ => (1 : ℂ)) k X = xiResolventMoment k X :=
  tsum_congr fun _ => mul_one _

/-- **Top-level plain detection**: past the explicit window, some *plain* even-index Turán minor
of the raw resolvent moments is negative whenever the maximal resolvent modulus carries an
off-line copy. -/
theorem exists_neg_even_plain_minor_of_offline_top {X : ℝ} (hX : 0 ≤ X)
    {ℓ : ℝ} (hℓpos : 0 < ℓ) (htop : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ ℓ)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0)
    {N : ℕ} (hN : (2 * S ^ (2 : ℕ) / g + S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      (xiResolventPoint X qh).im ^ (2 : ℕ) < (N : ℝ)) :
    ∃ n : ℕ, n < N ∧ (xiResolventMoment (2 * n) X * xiResolventMoment (2 * n + 2) X -
      xiResolventMoment (2 * n + 1) X ^ (2 : ℕ)).re < 0 := by
  have hN' : (2 * S ^ (2 : ℕ) * (1 : ℝ) ^ (2 : ℕ) / g + (1 : ℝ) ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      ((xiResolventPoint X qh).im ^ (2 : ℕ) * Complex.normSq (1 : ℂ)) < (N : ℝ) := by
    simpa [Complex.normSq_one] using hN
  obtain ⟨n, hn, hneg⟩ := exists_neg_even_minor_of_offline_level (Wf := fun _ => (1 : ℂ))
    (BW := 1) hX (fun q => by simp) (fun q q' _ => by simp) hℓpos
    (fun q hq => absurd hq (not_lt.mpr (htop q)))
    hρ₂0 hρ₂lt hρ₂bound hS hg hgap hqhℓ hoff one_ne_zero hN'
  refine ⟨n, hn, ?_⟩
  rwa [xiWeightedResolventMoment_one, xiWeightedResolventMoment_one,
    xiWeightedResolventMoment_one] at hneg

end

end RHTower
