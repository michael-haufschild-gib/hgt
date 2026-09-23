import GaloisForLFunctions.RHTower.XiResolventTuranEdgeCleansing
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction
import GaloisForLFunctions.HTGeometry.WeightedUnitPowerSumOscillation

/-!
# Deflation: the Turán minors see the second modulus level

Turán minor positivity at one shift cleanses the spectral edge: every maximal-modulus copy lies
on the critical line, so all edge resolvent values collapse to the single real atom `r`.  This
file performs the resulting **deflation step**.  Substituting `R k = m r^(k+1) + R' k` (with `m`
the edge multiplicity and `R'` the sub-edge moments) into the minor gives the exact identity

`R n R (n+2) - R (n+1)^(2 : ℕ) = m r^(n+1) D n + (R' n R' (n+2) - R' (n+1)^(2 : ℕ))`,

`D n = sum_q u_q^(n+1) (u_q - r)^(2 : ℕ)` — a **weighted** moment sequence over the sub-edge divisor
with the conjugation-symmetric, class-constant, nonvanishing weights `(u_q - r)^(2 : ℕ)`, the edge
terms vanishing identically.  The deflated minor is geometrically smaller than the leading
scale, so minor positivity descends to a decaying floor for the weighted power sums of the
**second modulus level**; the weighted oscillation theorem then forces a real point there.

**Theorem**: if every consecutive Turán minor at one shift is nonnegative, then among the copies
of maximal resolvent modulus *below the edge* — the second level of lowest zeros — at least one
lies on the critical line.  Rank-two Hankel data thus cleans the first level and sees the
second: the deflation ladder takes its first step down the zero spectrum.
-/

open Complex

namespace RHTower

noncomputable section

/-- On-critical spectral points have real resolvent values. -/
theorem xiResolventPoint_im_eq_zero_of_spectral {X : ℝ} {q : XiZeroCopy}
    (h : (xiSpectralPoint q).im = 0) : (xiResolventPoint X q).im = 0 := by
  rw [xiResolventPoint, Complex.inv_im]
  have him : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im = 0 := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero, sq, Complex.mul_im, h]
    ring
  rw [him]
  simp

/-- A real resolvent value of maximal modulus is the positive real atom. -/
theorem xiResolventPoint_eq_ofReal_of_im_eq_zero {X : ℝ} (hX : 0 ≤ X) {q : XiZeroCopy}
    {t : ℝ} (ht : 0 < t) (him : (xiResolventPoint X q).im = 0)
    (hnrm : ‖xiResolventPoint X q‖ = t) : xiResolventPoint X q = ((t : ℝ) : ℂ) := by
  have hre : 0 < (xiResolventPoint X q).re := xiResolventPoint_re_pos hX q
  have h1 : t ^ (2 : ℕ) = (xiResolventPoint X q).re ^ (2 : ℕ) := by
    rw [← hnrm, Complex.sq_norm, Complex.normSq_apply, him]
    ring
  have h2 : ((xiResolventPoint X q).re - t) * ((xiResolventPoint X q).re + t) = 0 := by
    linear_combination -h1
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith [sub_eq_zero.mp h3]
    · linarith
  · rw [him, Complex.ofReal_im]

set_option maxHeartbeats 1600000 in
/-- **Deflation: the minors see the second level.**  If every consecutive Turán minor at one
shift is nonnegative, then among the divisor copies of maximal resolvent modulus strictly below
the edge — the second level of lowest zeros — at least one lies on the critical line. -/
theorem exists_secondLevel_criticalLine_of_forall_turanMinor_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hminor : ∀ n : ℕ, 0 ≤ (xiResolventMoment n X * xiResolventMoment (n + 2) X -
      xiResolventMoment (n + 1) X ^ (2 : ℕ)).re) :
    ∃ q : XiZeroCopy, (xiSpectralPoint q).im = 0 ∧
      (∃ q₀, ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q₀‖) ∧
      ∀ q', (∃ q₀', ‖xiResolventPoint X q'‖ < ‖xiResolventPoint X q₀'‖) →
        ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖ := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_max_norm_xiResolventPoint hX
  set r : ℝ := ‖xiResolventPoint X q₀‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (xiResolventPoint_ne_zero hX q₀)
  have hTfin : {q : XiZeroCopy | r ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hrpos
  set T : Finset XiZeroCopy := hTfin.toFinset with hT
  have hmemT : ∀ q, q ∈ T ↔ r ≤ ‖xiResolventPoint X q‖ := by
    intro q
    rw [hT, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hTval : ∀ q ∈ T, ‖xiResolventPoint X q‖ = r := fun q hq =>
    le_antisymm (hq₀ q) ((hmemT q).mp hq)
  have hq₀T : q₀ ∈ T := (hmemT q₀).mpr le_rfl
  -- the cleansed edge collapses to the atom r
  have hclean := forall_edge_criticalLine_of_forall_turanMinor_re_nonneg hX hminor
  have hedgeval : ∀ q ∈ T, xiResolventPoint X q = ((r : ℝ) : ℂ) := by
    intro q hq
    have hmax : ∀ q', ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖ := by
      intro q'
      rw [hTval q hq]
      exact hq₀ q'
    exact xiResolventPoint_eq_ofReal_of_im_eq_zero hX hrpos
      (xiResolventPoint_im_eq_zero_of_spectral (hclean q hmax)) (hTval q hq)
  -- a copy below the edge exists
  obtain ⟨q₁, hq₁T⟩ := Infinite.exists_notMem_finset T
  have hq₁pos : 0 < ‖xiResolventPoint X q₁‖ :=
    norm_pos_iff.mpr (xiResolventPoint_ne_zero hX q₁)
  -- the second-level maximum
  obtain ⟨qs, hqsnT, hqsmax⟩ : ∃ qs, qs ∉ T ∧ ∀ q, q ∉ T →
      ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X qs‖ := by
    have hFfin : {q : XiZeroCopy | ‖xiResolventPoint X q₁‖ ≤
        ‖xiResolventPoint X q‖}.Finite :=
      finite_setOf_le_norm_xiResolventPoint hX hq₁pos
    set F : Finset XiZeroCopy := hFfin.toFinset \ T with hF
    have hq₁F : q₁ ∈ F := by
      rw [hF, Finset.mem_sdiff, Set.Finite.mem_toFinset]
      refine ⟨?_, hq₁T⟩
      show ‖xiResolventPoint X q₁‖ ≤ ‖xiResolventPoint X q₁‖
      exact le_rfl
    obtain ⟨qs, hqsF, hqsmax⟩ := F.exists_max_image
      (fun q => ‖xiResolventPoint X q‖) ⟨q₁, hq₁F⟩
    have hqsnT : qs ∉ T := by
      rw [hF, Finset.mem_sdiff] at hqsF
      exact hqsF.2
    refine ⟨qs, hqsnT, fun q hq => ?_⟩
    by_cases hq2 : ‖xiResolventPoint X q₁‖ ≤ ‖xiResolventPoint X q‖
    · have hqF : q ∈ F := by
        rw [hF, Finset.mem_sdiff, Set.Finite.mem_toFinset]
        exact ⟨hq2, hq⟩
      exact hqsmax q hqF
    · exact le_trans (not_le.mp hq2).le (hqsmax q₁ hq₁F)
  set ρ : ℝ := ‖xiResolventPoint X qs‖ with hρ
  have hρpos : 0 < ρ := norm_pos_iff.mpr (xiResolventPoint_ne_zero hX qs)
  have hρlt : ρ < r := lt_of_le_of_ne (hq₀ qs) fun h => hqsnT ((hmemT qs).mpr h.ge)
  -- the second level as a finite set
  have hSfinset : {q : XiZeroCopy | ρ ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hρpos
  set SF : Finset XiZeroCopy := hSfinset.toFinset \ T with hSF
  have hmemSF : ∀ q, q ∈ SF ↔ (ρ ≤ ‖xiResolventPoint X q‖ ∧ q ∉ T) := by
    intro q
    rw [hSF, Finset.mem_sdiff, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hSFval : ∀ q ∈ SF, ‖xiResolventPoint X q‖ = ρ := by
    intro q hq
    rw [hmemSF] at hq
    exact le_antisymm (hqsmax q hq.2) hq.1
  have hqsSF : qs ∈ SF := (hmemSF qs).mpr ⟨le_rfl, hqsnT⟩
  -- by contradiction: no second-level copy on the line
  by_contra hcon
  have hSFoff : ∀ q ∈ SF, (xiSpectralPoint q).im ≠ 0 := by
    intro q hq him
    rw [hmemSF] at hq
    refine hcon ⟨q, him, ⟨q₀, ?_⟩, fun q' hq' => ?_⟩
    · rw [hSFval q ((hmemSF q).mpr hq), ← hr]
      exact hρlt.trans_le (hTval q₀ hq₀T).ge
    · obtain ⟨q₀', hq₀'⟩ := hq'
      have hq'nT : q' ∉ T := by
        intro hq'T
        have h1 := hTval q' hq'T
        have h2 := hq₀ q₀'
        rw [h1] at hq₀'
        linarith
      rw [hSFval q ((hmemSF q).mpr hq)]
      exact hqsmax q' hq'nT
  -- third-level bound
  obtain ⟨ρ₂, hρ₂0, hρ₂lt, hρ₂bound⟩ :
      ∃ ρ₂, 0 ≤ ρ₂ ∧ ρ₂ < ρ ∧ ∀ q, q ∉ T → q ∉ SF → ‖xiResolventPoint X q‖ ≤ ρ₂ := by
    have hhalf : (0 : ℝ) < ρ / 2 := by linarith
    have hDfin : {q : XiZeroCopy | ρ / 2 ≤ ‖xiResolventPoint X q‖}.Finite :=
      finite_setOf_le_norm_xiResolventPoint hX hhalf
    set D : Finset XiZeroCopy := (hDfin.toFinset \ T) \ SF with hD
    rcases D.eq_empty_or_nonempty with hDe | hDne
    · refine ⟨ρ / 2, by linarith, by linarith, fun q hq1 hq2 => ?_⟩
      by_contra hgt
      rw [not_le] at hgt
      have hqD : q ∈ D := by
        rw [hD, Finset.mem_sdiff, Finset.mem_sdiff, Set.Finite.mem_toFinset]
        exact ⟨⟨le_of_lt hgt, hq1⟩, hq2⟩
      rw [hDe] at hqD
      exact absurd hqD (Finset.notMem_empty q)
    · obtain ⟨qd, hqdD, hqdmax⟩ := D.exists_max_image
        (fun q => ‖xiResolventPoint X q‖) hDne
      have hqdmem := hqdD
      rw [hD, Finset.mem_sdiff, Finset.mem_sdiff] at hqdmem
      have hqdρ : ‖xiResolventPoint X qd‖ < ρ := by
        rcases lt_or_ge ‖xiResolventPoint X qd‖ ρ with h | h
        · exact h
        · exact absurd ((hmemSF qd).mpr ⟨h, hqdmem.1.2⟩) hqdmem.2
      refine ⟨max ‖xiResolventPoint X qd‖ (ρ / 2),
        le_trans (by linarith) (le_max_right _ _), ?_, ?_⟩
      · rw [max_lt_iff]
        exact ⟨hqdρ, by linarith⟩
      · intro q hq1 hq2
        by_cases hq3 : ρ / 2 ≤ ‖xiResolventPoint X q‖
        · have hqD : q ∈ D := by
            rw [hD, Finset.mem_sdiff, Finset.mem_sdiff, Set.Finite.mem_toFinset]
            exact ⟨⟨hq3, hq1⟩, hq2⟩
          exact le_trans (hqdmax q hqD) (le_max_left _ _)
        · exact le_trans (not_le.mp hq3).le (le_max_right _ _)
  -- weighted second-level system
  set c : ℂ := ((r : ℝ) : ℂ) with hc
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  set W : XiZeroCopy → ℂ := fun q => (u q - c) ^ (2 : ℕ) with hW
  set v : XiZeroCopy → ℂ := fun q => u q / ((ρ : ℝ) : ℂ) with hv
  have hρC : (((ρ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρpos.ne'
  -- summability of the weighted full sums
  have hwsum : ∀ n : ℕ, Summable (fun q : XiZeroCopy => u q ^ (n + 1) * W q) := by
    intro n
    refine Summable.of_norm_bounded
      ((summable_norm_xiResolventPoint hX).mul_right ((2 * r) ^ (2 : ℕ))) fun q => ?_
    rw [norm_mul]
    simp only [hW]
    have h1 : ‖u q ^ (n + 1)‖ ≤ ‖u q‖ := by
      rw [norm_pow, pow_succ']
      have hle1 : ‖u q‖ ^ n ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX q)
      nlinarith [norm_nonneg (u q), pow_nonneg (norm_nonneg (u q)) n]
    have h2 : ‖(u q - c) ^ (2 : ℕ)‖ ≤ (2 * r) ^ (2 : ℕ) := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖u q - c‖ ≤ ‖u q‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ r + r := by
            refine add_le_add (hq₀ q) ?_
            rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
        _ = 2 * r := by ring
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  -- edge moments and sub-edge moments
  set R' : ℕ → ℂ := fun k =>
    ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (k + 1) with hR'
  have hmomsplit : ∀ k : ℕ, xiResolventMoment k X =
      (T.card : ℂ) * c ^ (k + 1) + R' k := by
    intro k
    rw [xiResolventMoment, ← (summable_xiResolventPoint_pow hX k).sum_add_tsum_compl (s := T)]
    congr 1
    calc ∑ q ∈ T, xiResolventPoint X q ^ (k + 1)
        = ∑ _q ∈ T, c ^ (k + 1) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          rw [hedgeval q hq, hc]
      _ = (T.card : ℂ) * c ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- summability of sub-edge moments
  have hsubpow : ∀ k : ℕ, Summable (fun qc : ↑(↑T : Set XiZeroCopy)ᶜ =>
      u (↑qc : XiZeroCopy) ^ (k + 1)) := fun k =>
    (summable_xiResolventPoint_pow hX k).subtype _
  -- the deflation identity
  have hdefl : ∀ n : ℕ, xiResolventMoment n X * xiResolventMoment (n + 2) X -
      xiResolventMoment (n + 1) X ^ (2 : ℕ) =
      (T.card : ℂ) * c ^ (n + 1) *
        (R' (n + 2) - 2 * c * R' (n + 1) + c ^ (2 : ℕ) * R' n) +
        (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)) := by
    intro n
    rw [hmomsplit n, hmomsplit (n + 1), hmomsplit (n + 2)]
    ring
  -- the weighted representation of the deflated diagonal
  have hDrep : ∀ n : ℕ, R' (n + 2) - 2 * c * R' (n + 1) + c ^ (2 : ℕ) * R' n =
      ∑' q : XiZeroCopy, u q ^ (n + 1) * W q := by
    intro n
    have hfull : ∑' q : XiZeroCopy, u q ^ (n + 1) * W q =
        (∑ q ∈ T, u q ^ (n + 1) * W q) +
          ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
            W (↑qc : XiZeroCopy) :=
      ((hwsum n).sum_add_tsum_compl (s := T)).symm
    have hTzero : (∑ q ∈ T, u q ^ (n + 1) * W q) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      simp only [hW]
      rw [show u q = c from hedgeval q hq]
      ring
    have hcompl : ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
        W (↑qc : XiZeroCopy) =
        R' (n + 2) - 2 * c * R' (n + 1) + c ^ (2 : ℕ) * R' n := by
      have hpt : ∀ qc : ↑(↑T : Set XiZeroCopy)ᶜ,
          u (↑qc : XiZeroCopy) ^ (n + 1) * W (↑qc : XiZeroCopy) =
          (u (↑qc : XiZeroCopy) ^ (n + 2 + 1) -
            2 * c * u (↑qc : XiZeroCopy) ^ (n + 1 + 1)) +
            c ^ (2 : ℕ) * u (↑qc : XiZeroCopy) ^ (n + 1) := by
        intro qc
        simp only [hW]
        ring
      rw [tsum_congr hpt]
      rw [((hsubpow (n + 2)).sub ((hsubpow (n + 1)).mul_left (2 * c))).tsum_add
        ((hsubpow n).mul_left (c ^ (2 : ℕ)))]
      rw [(hsubpow (n + 2)).tsum_sub ((hsubpow (n + 1)).mul_left (2 * c))]
      rw [tsum_mul_left, tsum_mul_left, hR']
    rw [hfull, hTzero, zero_add, hcompl]
  -- floor for the weighted second-level power sums
  have hm1 : (1 : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨q₀, hq₀T⟩)
  set S₀' : ℝ := ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, ‖u (↑qc : XiZeroCopy)‖ with hS₀'
  have hS₀'nn : 0 ≤ S₀' := tsum_nonneg fun qc => norm_nonneg _
  have hsubnorm : Summable (fun qc : ↑(↑T : Set XiZeroCopy)ᶜ =>
      ‖u (↑qc : XiZeroCopy)‖) := (summable_norm_xiResolventPoint hX).subtype _
  have hR'bound : ∀ k : ℕ, ‖R' k‖ ≤ ρ ^ k * S₀' := by
    intro k
    rw [hR']
    calc ‖∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (k + 1)‖
        ≤ ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, ‖u (↑qc : XiZeroCopy) ^ (k + 1)‖ :=
          norm_tsum_le_tsum_norm ((hsubpow k).norm)
      _ ≤ ∑' qc : ↑(↑T : Set XiZeroCopy)ᶜ, ρ ^ k * ‖u (↑qc : XiZeroCopy)‖ := by
          refine Summable.tsum_le_tsum (fun qc => ?_) ((hsubpow k).norm)
            (hsubnorm.mul_left _)
          have hqnT : (↑qc : XiZeroCopy) ∉ T := by
            have h := qc.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          rw [norm_pow, pow_succ']
          calc ‖u (↑qc : XiZeroCopy)‖ * ‖u (↑qc : XiZeroCopy)‖ ^ k
              ≤ ‖u (↑qc : XiZeroCopy)‖ * ρ ^ k :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) (hqsmax _ hqnT) k) (norm_nonneg _)
            _ = ρ ^ k * ‖u (↑qc : XiZeroCopy)‖ := mul_comm _ _
      _ = ρ ^ k * S₀' := by
          rw [tsum_mul_left]
  -- the second-level tail
  set P₁ : ℝ := ∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, ‖u (↑qc : XiZeroCopy)‖ with hP₁
  have hP₁nn : 0 ≤ P₁ := tsum_nonneg fun _ => norm_nonneg _
  have hsfnorm : Summable (fun qc : ↑(↑SF : Set XiZeroCopy)ᶜ =>
      ‖u (↑qc : XiZeroCopy)‖) := (summable_norm_xiResolventPoint hX).subtype _
  have htailW : ∀ n : ℕ,
      ‖∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
        W (↑qc : XiZeroCopy)‖ ≤ ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * P₁) := by
    intro n
    calc ‖∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
          W (↑qc : XiZeroCopy)‖
        ≤ ∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, ‖u (↑qc : XiZeroCopy) ^ (n + 1) *
            W (↑qc : XiZeroCopy)‖ := norm_tsum_le_tsum_norm ((hwsum n).norm.subtype _)
      _ ≤ ∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ,
            ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * ‖u (↑qc : XiZeroCopy)‖) := by
          refine Summable.tsum_le_tsum (fun qc => ?_) ((hwsum n).norm.subtype _)
            ((hsfnorm.mul_left ((2 * r) ^ (2 : ℕ))).mul_left (ρ₂ ^ n))
          have hqnSF : (↑qc : XiZeroCopy) ∉ SF := by
            have h := qc.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          by_cases hqT : (↑qc : XiZeroCopy) ∈ T
          · have hWz : W (↑qc : XiZeroCopy) = 0 := by
              simp only [hW]
              rw [show u (↑qc : XiZeroCopy) = c from hedgeval _ hqT]
              ring
            rw [hWz, mul_zero, norm_zero]
            positivity
          · rw [norm_mul]
            have h1 : ‖u (↑qc : XiZeroCopy) ^ (n + 1)‖ ≤
                ρ₂ ^ n * ‖u (↑qc : XiZeroCopy)‖ := by
              rw [norm_pow, pow_succ']
              calc ‖u (↑qc : XiZeroCopy)‖ * ‖u (↑qc : XiZeroCopy)‖ ^ n
                  ≤ ‖u (↑qc : XiZeroCopy)‖ * ρ₂ ^ n :=
                    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
                      (hρ₂bound _ hqT hqnSF) n) (norm_nonneg _)
                _ = ρ₂ ^ n * ‖u (↑qc : XiZeroCopy)‖ := mul_comm _ _
            have h2 : ‖W (↑qc : XiZeroCopy)‖ ≤ (2 * r) ^ (2 : ℕ) := by
              simp only [hW]
              rw [norm_pow]
              refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
              calc ‖u (↑qc : XiZeroCopy) - c‖ ≤ ‖u (↑qc : XiZeroCopy)‖ + ‖c‖ :=
                    norm_sub_le _ _
                _ ≤ r + r := by
                    refine add_le_add (hq₀ _) ?_
                    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
                _ = 2 * r := by ring
            calc ‖u (↑qc : XiZeroCopy) ^ (n + 1)‖ * ‖W (↑qc : XiZeroCopy)‖
                ≤ (ρ₂ ^ n * ‖u (↑qc : XiZeroCopy)‖) * (2 * r) ^ (2 : ℕ) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
              _ = ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * ‖u (↑qc : XiZeroCopy)‖) := by ring
      _ = ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * P₁) := by
          rw [tsum_mul_left, tsum_mul_left, hP₁]
  -- the decaying floor for the weighted second-level power sums
  have hκr : ρ / r < 1 := (div_lt_one hrpos).mpr hρlt
  have hκ2 : ρ₂ / ρ < 1 := (div_lt_one hρpos).mpr hρ₂lt
  set κ : ℝ := max (ρ / r) (ρ₂ / ρ) with hκ
  have hκ0 : (0 : ℝ) ≤ κ :=
    le_trans (div_nonneg hρpos.le hrpos.le) (le_max_left _ _)
  have hκ1 : κ < 1 := max_lt hκr hκ2
  set C₀ : ℝ := 2 * S₀' ^ (2 : ℕ) + 4 * r ^ (2 : ℕ) * P₁ / ρ with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    positivity
  have hAfloor : ∀ n : ℕ, -(C₀ * κ ^ n) ≤ (∑ q ∈ SF, W q * v q ^ (n + 1)).re := by
    intro n
    -- the diagonal of the deflation
    have hDsplit : (∑' q : XiZeroCopy, u q ^ (n + 1) * W q) =
        (∑ q ∈ SF, u q ^ (n + 1) * W q) +
          ∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
            W (↑qc : XiZeroCopy) := ((hwsum n).sum_add_tsum_compl (s := SF)).symm
    -- SF-part in normalized coordinates
    have hSFnorm : (∑ q ∈ SF, u q ^ (n + 1) * W q) =
        ((ρ ^ (n + 1) : ℝ) : ℂ) * ∑ q ∈ SF, W q * v q ^ (n + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have huq : u q = ((ρ : ℝ) : ℂ) * v q := by
        simp only [hv]
        field_simp
      rw [huq, mul_pow, ← Complex.ofReal_pow]
      ring
    -- the sub-edge minor bound
    have hminor' : ‖R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)‖ ≤ 2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) := by
      calc ‖R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)‖
          ≤ ‖R' n * R' (n + 2)‖ + ‖R' (n + 1) ^ (2 : ℕ)‖ := norm_sub_le _ _
        _ = ‖R' n‖ * ‖R' (n + 2)‖ + ‖R' (n + 1)‖ ^ (2 : ℕ) := by rw [norm_mul, norm_pow]
        _ ≤ (ρ ^ n * S₀') * (ρ ^ (n + 2) * S₀') + (ρ ^ (n + 1) * S₀') ^ (2 : ℕ) := by
            refine add_le_add (mul_le_mul (hR'bound n) (hR'bound (n + 2))
              (norm_nonneg _) (by positivity)) ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hR'bound (n + 1)) 2
        _ = 2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) := by ring
    -- minor positivity transfers to the weighted diagonal
    have hMc : (T.card : ℂ) * c ^ (n + 1) = (((T.card : ℝ) * r ^ (n + 1) : ℝ) : ℂ) := by
      rw [hc]
      push_cast
      ring
    have hminre := hminor n
    have hkey : 0 ≤ (T.card : ℝ) * r ^ (n + 1) *
        (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re +
        (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)).re := by
      have h1 := hdefl n
      rw [hDrep n] at h1
      have h2 := congrArg Complex.re h1
      rw [Complex.add_re, hMc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at h2
      linarith
    have hminre' : -(2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2)) ≤
        (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)).re := by
      have h1 := Complex.abs_re_le_norm (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ))
      have h2 := neg_abs_le (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)).re
      linarith [hminor']
    -- assemble the floor
    have hcard : (1 : ℝ) ≤ (T.card : ℝ) := hm1
    have hrn : (0 : ℝ) < r ^ (n + 1) := pow_pos hrpos _
    have hρn : (0 : ℝ) < ρ ^ (n + 1) := pow_pos hρpos _
    have hDre : -(2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) / r ^ (n + 1)) ≤
        (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re := by
      rw [← neg_div, div_le_iff₀ hrn]
      have hcardpos : (0 : ℝ) < (T.card : ℝ) := by linarith
      have hminre2 : (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)).re ≤
          2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) := by
        have h1 := Complex.abs_re_le_norm (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ))
        have h2 := le_abs_self (R' n * R' (n + 2) - R' (n + 1) ^ (2 : ℕ)).re
        linarith [hminor']
      have hDnn : -(2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2)) ≤
          (T.card : ℝ) * r ^ (n + 1) * (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re := by
        linarith
      by_cases hsign : 0 ≤ (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re
      · have : (0:ℝ) ≤ (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re * r ^ (n + 1) :=
          mul_nonneg hsign hrn.le
        nlinarith [mul_nonneg (mul_nonneg hS₀'nn hS₀'nn) (pow_nonneg hρpos.le (2 * n + 2))]
      · rw [not_le] at hsign
        have hmul : (T.card : ℝ) * r ^ (n + 1) *
            (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re ≤
            1 * r ^ (n + 1) * (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re := by
          have := mul_le_mul_of_nonpos_right
            (mul_le_mul_of_nonneg_right hcard hrn.le) hsign.le
          linarith [this]
        nlinarith
    have hAre : (∑ q ∈ SF, W q * v q ^ (n + 1)).re =
        ((∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re -
          (∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
            W (↑qc : XiZeroCopy)).re) / ρ ^ (n + 1) := by
      have h1 := congrArg Complex.re hDsplit
      rw [Complex.add_re, hSFnorm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at h1
      rw [eq_div_iff (ne_of_gt hρn)]
      linarith
    rw [hAre]
    have htre : -(ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * P₁)) ≤
        -(∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
          W (↑qc : XiZeroCopy)).re := by
      have h1 := htailW n
      have h2 := Complex.abs_re_le_norm
        (∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
          W (↑qc : XiZeroCopy))
      have h3 := le_abs_self
        (∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
          W (↑qc : XiZeroCopy)).re
      linarith
    rw [le_div_iff₀ hρn]
    have hb1 : 2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) / r ^ (n + 1) ≤
        2 * S₀' ^ (2 : ℕ) * κ ^ n * ρ ^ (n + 1) := by
      rw [div_le_iff₀ hrn]
      have h1 : (ρ / r) ^ n ≤ κ ^ n :=
        pow_le_pow_left₀ (div_nonneg hρpos.le hrpos.le) (le_max_left _ _) n
      have h2 : (ρ / r) ^ n * r ^ n = ρ ^ n := by
        rw [div_pow]
        field_simp
      have hρn' : ρ ^ n ≤ κ ^ n * r ^ n := by
        nlinarith [mul_le_mul_of_nonneg_right h1 (pow_nonneg hrpos.le n)]
      have hρn1 : ρ ^ (n + 1) ≤ κ ^ n * r ^ (n + 1) := by
        calc ρ ^ (n + 1) = ρ * ρ ^ n := pow_succ' ρ n
          _ ≤ ρ * (κ ^ n * r ^ n) := mul_le_mul_of_nonneg_left hρn' hρpos.le
          _ ≤ r * (κ ^ n * r ^ n) := mul_le_mul_of_nonneg_right hρlt.le (by positivity)
          _ = κ ^ n * r ^ (n + 1) := by ring
      have h4 : ρ ^ (2 * n + 2) = ρ ^ (n + 1) * ρ ^ (n + 1) := by ring
      rw [h4]
      nlinarith [mul_le_mul_of_nonneg_left hρn1
        (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * S₀' ^ (2 : ℕ)) (pow_nonneg hρpos.le (n + 1)))]
    have hb2 : ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * P₁) ≤
        4 * r ^ (2 : ℕ) * P₁ / ρ * κ ^ n * ρ ^ (n + 1) := by
      have h1 : (ρ₂ / ρ) ^ n ≤ κ ^ n :=
        pow_le_pow_left₀ (div_nonneg hρ₂0 hρpos.le) (le_max_right _ _) n
      have h3 : (ρ₂ / ρ) ^ n * ρ ^ n = ρ₂ ^ n := by
        rw [div_pow]
        field_simp
      have h2 : ρ₂ ^ n ≤ κ ^ n * ρ ^ n := by
        nlinarith [mul_le_mul_of_nonneg_right h1 (pow_nonneg hρpos.le n)]
      have h4 : 4 * r ^ (2 : ℕ) * P₁ / ρ * κ ^ n * ρ ^ (n + 1) =
          4 * r ^ (2 : ℕ) * P₁ * (κ ^ n * ρ ^ n) := by
        field_simp
        ring
      rw [h4, mul_comm (ρ₂ ^ n) ((2 * r) ^ (2 : ℕ) * P₁),
        show ((2 * r) ^ (2 : ℕ) * P₁ : ℝ) = 4 * r ^ (2 : ℕ) * P₁ by ring]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc -(C₀ * κ ^ n) * ρ ^ (n + 1)
        = -(2 * S₀' ^ (2 : ℕ) * κ ^ n * ρ ^ (n + 1) +
            4 * r ^ (2 : ℕ) * P₁ / ρ * κ ^ n * ρ ^ (n + 1)) := by
          rw [hC₀]
          ring
      _ ≤ -(2 * S₀' ^ (2 : ℕ) * ρ ^ (2 * n + 2) / r ^ (n + 1) +
            ρ₂ ^ n * ((2 * r) ^ (2 : ℕ) * P₁)) := by
          linarith
      _ ≤ (∑' q : XiZeroCopy, u q ^ (n + 1) * W q).re -
            (∑' qc : ↑(↑SF : Set XiZeroCopy)ᶜ, u (↑qc : XiZeroCopy) ^ (n + 1) *
              W (↑qc : XiZeroCopy)).re := by
          linarith [hDre, htre]
  -- the engine hypotheses on the second level
  have hvnorm : ∀ q ∈ SF, ‖v q‖ = 1 := by
    intro q hq
    simp only [hv]
    rw [norm_div, hSFval q hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    exact div_self hρpos.ne'
  have hvne : ∀ q ∈ SF, v q ≠ 1 := by
    intro q hq h1
    have huρ : u q = ((ρ : ℝ) : ℂ) := by
      simp only [hv] at h1
      rw [div_eq_iff hρC, one_mul] at h1
      exact h1
    have himu : (u q).im = 0 := by
      rw [huρ, Complex.ofReal_im]
    have hspec : (xiSpectralPoint q).im = 0 := by
      by_contra hspec
      exact xiResolventPoint_im_ne_zero_of_spectral hX hspec himu
    exact hSFoff q hq hspec
  have hvclass : ∀ q ∈ SF, ∀ q' ∈ SF, v q = v q' → W q = W q' := by
    intro q _ q' _ h1
    have h2 : u q = u q' := by
      have h3 : u q = ((ρ : ℝ) : ℂ) * v q := by
        simp only [hv]
        field_simp
      have h4 : u q' = ((ρ : ℝ) : ℂ) * v q' := by
        simp only [hv]
        field_simp
      rw [h3, h4, h1]
    simp only [hW]
    rw [h2]
  have hvconj : ∀ q ∈ SF, ∀ q' ∈ SF, v q' = (starRingEnd ℂ) (v q) →
      W q' = (starRingEnd ℂ) (W q) := by
    intro q _ q' _ h1
    have h2 : u q' = (starRingEnd ℂ) (u q) := by
      have h3 : u q' = ((ρ : ℝ) : ℂ) * v q' := by
        simp only [hv]
        field_simp
      rw [h3, h1, ← Complex.conj_ofReal ρ, ← map_mul]
      congr 1
      simp only [hv]
      field_simp
    simp only [hW]
    rw [h2, hc, map_pow, map_sub, Complex.conj_ofReal]
  have hWqs : W qs ≠ 0 := by
    simp only [hW]
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h1 => ?_)
    have h2 : ‖u qs‖ = ‖c‖ := by rw [h1]
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] at h2
    have h3 : ‖u qs‖ = ρ := hSFval qs hqsSF
    linarith [h2, h3, hρlt]
  exact GaloisForLFunctions.HTGeometry.weightedUnitPowerSum_no_decaying_lower_bound
    hvnorm hvne hvclass hvconj hqsSF hWqs hC₀nn hκ0 hκ1 hAfloor

end

end RHTower
