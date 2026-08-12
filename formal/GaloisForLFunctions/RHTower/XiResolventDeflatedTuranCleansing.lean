import GaloisForLFunctions.RHTower.XiResolventDeflationSecondLevel

/-!
# Deflated Turán minors cleanse the second level

The `t`-deflated moments `M_t k = R (k+2) - 2t R (k+1) + t^2 R k` are the moments of the divisor
functional reweighted by `(u - t)^2`; their Turán minors are the `2×2` minors of the cubic
Hankel sections in the deflating basis `{u - t, u (u - t)}`, so their nonnegativity for all real
`t` is part of the rank-three positivity data of the ladder.

**Theorem**: if all plain and all `t`-deflated Turán minors at one shift are nonnegative, then
**every** divisor copy of maximal resolvent modulus strictly below the edge lies on the critical
line.  With the earlier rungs this completes the pattern through depth two: the diagonal sees
level one, the plain minors clean level one and see level two, and the deflated minors clean
level two.

Mechanism.  The plain minors cleanse the edge to the real atom `r`; the deflation weight
`(u - r)^2` then vanishes identically on the edge, so the deflated pair expansion

`2 (M_r n M_r (n+2) - M_r (n+1)^2)
   = sum_(q,q') (u_q u_q')^(n+1) (u_q - r)^2 (u_q' - r)^2 (u_q - u_q')^2`

has its maximal pair points on the second modulus level.  The pair points equal to `rho^2` are
the conjugate pairs, with weights `-4 (Im u)^2 normSq ((u - r)^2)` — strictly negative at an
off-critical second-level copy — and the first-moment Cesàro argument of the edge-cleansing
theorem repeats verbatim one level down.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `t`-deflated resolvent moments: the moments of the divisor reweighted by `(u - t)^2`. -/
def xiDeflatedMoment (t : ℝ) (k : ℕ) (X : ℝ) : ℂ :=
  xiResolventMoment (k + 2) X - 2 * (t : ℂ) * xiResolventMoment (k + 1) X +
    (t : ℂ) ^ 2 * xiResolventMoment k X

/-- The deflated moments are the weighted divisor sums. -/
theorem xiDeflatedMoment_eq_tsum {X : ℝ} (hX : 0 ≤ X) (t : ℝ) (k : ℕ) :
    xiDeflatedMoment t k X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (k + 1) * (xiResolventPoint X q - (t : ℂ)) ^ 2 := by
  have hpt : ∀ q : XiZeroCopy,
      xiResolventPoint X q ^ (k + 1) * (xiResolventPoint X q - (t : ℂ)) ^ 2 =
      (xiResolventPoint X q ^ (k + 2 + 1) -
        2 * (t : ℂ) * xiResolventPoint X q ^ (k + 1 + 1)) +
        (t : ℂ) ^ 2 * xiResolventPoint X q ^ (k + 1) := by
    intro q
    ring
  rw [tsum_congr hpt]
  rw [((summable_xiResolventPoint_pow hX (k + 2)).sub
    ((summable_xiResolventPoint_pow hX (k + 1)).mul_left (2 * (t : ℂ)))).tsum_add
    ((summable_xiResolventPoint_pow hX k).mul_left ((t : ℂ) ^ 2))]
  rw [(summable_xiResolventPoint_pow hX (k + 2)).tsum_sub
    ((summable_xiResolventPoint_pow hX (k + 1)).mul_left (2 * (t : ℂ)))]
  rw [tsum_mul_left, tsum_mul_left]
  rw [xiDeflatedMoment, xiResolventMoment, xiResolventMoment, xiResolventMoment]

/-- Norm-summability of the deflated atoms. -/
theorem summable_norm_deflatedAtom {X : ℝ} (hX : 0 ≤ X) (t : ℝ) (k : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖xiResolventPoint X q ^ (k + 1) * (xiResolventPoint X q - (t : ℂ)) ^ 2‖) := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((summable_norm_xiResolventPoint hX).mul_right ((1 + |t|) ^ 2))
  rw [norm_mul]
  have h1 : ‖xiResolventPoint X q ^ (k + 1)‖ ≤ ‖xiResolventPoint X q‖ := by
    rw [norm_pow, pow_succ']
    have hle1 : ‖xiResolventPoint X q‖ ^ k ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX q)
    nlinarith [norm_nonneg (xiResolventPoint X q),
      pow_nonneg (norm_nonneg (xiResolventPoint X q)) k]
  have h2 : ‖(xiResolventPoint X q - (t : ℂ)) ^ 2‖ ≤ (1 + |t|) ^ 2 := by
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖xiResolventPoint X q - (t : ℂ)‖
        ≤ ‖xiResolventPoint X q‖ + ‖((t : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + |t| := by
          refine add_le_add (norm_xiResolventPoint_le_one hX q) ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

/-- **The weighted variance expansion of the `t`-deflated Turán minor.** -/
theorem two_mul_deflatedTuranMinorAt_eq_tsum_pair {X : ℝ} (hX : 0 ≤ X) (t : ℝ) (n : ℕ) :
    2 * (xiDeflatedMoment t n X * xiDeflatedMoment t (n + 2) X -
        xiDeflatedMoment t (n + 1) X ^ 2) =
      ∑' z : XiZeroCopy × XiZeroCopy,
        (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          ((xiResolventPoint X z.1 - (t : ℂ)) ^ 2 *
            (xiResolventPoint X z.2 - (t : ℂ)) ^ 2) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ 2 := by
  have h0 := summable_norm_deflatedAtom hX t n
  have h1 := summable_norm_deflatedAtom hX t (n + 1)
  have h2 := summable_norm_deflatedAtom hX t (n + 2)
  have hA := tsum_mul_tsum_of_summable_norm h0 h2
  have hB := tsum_mul_tsum_of_summable_norm h1 h1
  have hC := tsum_mul_tsum_of_summable_norm h2 h0
  have hsumA := summable_mul_of_summable_norm h0 h2
  have hsumB := summable_mul_of_summable_norm h1 h1
  have hsumC := summable_mul_of_summable_norm h2 h0
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          ((xiResolventPoint X z.1 - (t : ℂ)) ^ 2 *
            (xiResolventPoint X z.2 - (t : ℂ)) ^ 2) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ 2 =
        (((xiResolventPoint X z.1 ^ (n + 1) * (xiResolventPoint X z.1 - (t : ℂ)) ^ 2) *
            (xiResolventPoint X z.2 ^ (n + 2 + 1) *
              (xiResolventPoint X z.2 - (t : ℂ)) ^ 2) -
          2 * ((xiResolventPoint X z.1 ^ (n + 1 + 1) *
              (xiResolventPoint X z.1 - (t : ℂ)) ^ 2) *
            (xiResolventPoint X z.2 ^ (n + 1 + 1) *
              (xiResolventPoint X z.2 - (t : ℂ)) ^ 2))) +
          (xiResolventPoint X z.1 ^ (n + 2 + 1) *
            (xiResolventPoint X z.1 - (t : ℂ)) ^ 2) *
            (xiResolventPoint X z.2 ^ (n + 1) *
              (xiResolventPoint X z.2 - (t : ℂ)) ^ 2)) := by
    intro z
    ring
  rw [xiDeflatedMoment_eq_tsum hX t n, xiDeflatedMoment_eq_tsum hX t (n + 1),
    xiDeflatedMoment_eq_tsum hX t (n + 2),
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

set_option maxHeartbeats 1600000 in
/-- **Deflated Turán minors cleanse the second level.**  If all plain and all `t`-deflated Turán
minors at one shift are nonnegative, then every divisor copy of maximal resolvent modulus
strictly below the edge lies on the critical line. -/
theorem forall_secondLevel_criticalLine_of_forall_deflatedTuranMinor_re_nonneg {X : ℝ}
    (hX : 0 ≤ X)
    (hminor : ∀ n : ℕ, 0 ≤ (xiResolventMoment n X * xiResolventMoment (n + 2) X -
      xiResolventMoment (n + 1) X ^ 2).re)
    (hdefl : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ (xiDeflatedMoment t n X * xiDeflatedMoment t (n + 2) X -
      xiDeflatedMoment t (n + 1) X ^ 2).re) :
    ∀ q : XiZeroCopy, (∃ q₀, ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q₀‖) →
      (∀ q', (∃ q₀', ‖xiResolventPoint X q'‖ < ‖xiResolventPoint X q₀'‖) →
        ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖) →
      (xiSpectralPoint q).im = 0 := by
  classical
  intro qh hbelow hqhmax
  by_contra hqhoff
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
  have hclean := forall_edge_criticalLine_of_forall_turanMinor_re_nonneg hX hminor
  have hedgeval : ∀ q ∈ T, xiResolventPoint X q = ((r : ℝ) : ℂ) := by
    intro q hq
    have hmax : ∀ q', ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖ := by
      intro q'
      rw [hTval q hq]
      exact hq₀ q'
    exact xiResolventPoint_eq_ofReal_of_im_eq_zero hX hrpos
      (xiResolventPoint_im_eq_zero_of_spectral (hclean q hmax)) (hTval q hq)
  -- qh is a maximal below-edge copy
  have hqhnT : qh ∉ T := by
    intro hqhT
    obtain ⟨qb, hqb⟩ := hbelow
    have h1 := hTval qh hqhT
    have h2 := hq₀ qb
    rw [h1] at hqb
    linarith
  set ρ : ℝ := ‖xiResolventPoint X qh‖ with hρ
  have hρpos : 0 < ρ := norm_pos_iff.mpr (xiResolventPoint_ne_zero hX qh)
  have hρlt : ρ < r := lt_of_le_of_ne (hq₀ qh) fun h => hqhnT ((hmemT qh).mpr h.ge)
  have hqhmax' : ∀ q, q ∉ T → ‖xiResolventPoint X q‖ ≤ ρ := by
    intro q hq
    refine hqhmax q ⟨q₀, ?_⟩
    refine lt_of_le_of_ne (hq₀ q) fun h => hq ((hmemT q).mpr h.ge)
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
    exact le_antisymm (hqhmax' q hq.2) hq.1
  have hqhSF : qh ∈ SF := (hmemSF qh).mpr ⟨le_rfl, hqhnT⟩
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
  -- the deflated pair machinery at t = r
  set c : ℂ := ((r : ℝ) : ℂ) with hc
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  set Wt : XiZeroCopy × XiZeroCopy → ℂ := fun z =>
    ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) * (u z.1 - u z.2) ^ 2 with hWt
  set V : XiZeroCopy × XiZeroCopy → ℂ := fun z => u z.1 * u z.2 / (((ρ : ℝ) : ℂ)) ^ 2 with hV
  set TT : Finset (XiZeroCopy × XiZeroCopy) := SF ×ˢ SF with hTT
  have hρC : (((ρ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρpos.ne'
  -- summability of the pair terms
  have hpairsummable : ∀ n : ℕ, Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (u z.1 * u z.2) ^ (n + 1) * ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) *
        (u z.1 - u z.2) ^ 2) := by
    intro n
    have h0 := summable_norm_deflatedAtom hX r n
    have hsum := summable_mul_of_summable_norm h0 h0
    have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) *
          (u z.1 - u z.2) ^ 2 =
        (u z.1 ^ (n + 1) * (u z.1 - c) ^ 2) * (u z.2 ^ (n + 1) * (u z.2 - c) ^ 2) *
          (u z.1 - u z.2) ^ 2 := by
      intro z
      ring
    rw [show (fun z : XiZeroCopy × XiZeroCopy =>
        (u z.1 * u z.2) ^ (n + 1) * ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) *
          (u z.1 - u z.2) ^ 2) = fun z =>
        (u z.1 ^ (n + 1) * (u z.1 - c) ^ 2) * (u z.2 ^ (n + 1) * (u z.2 - c) ^ 2) *
          (u z.1 - u z.2) ^ 2 from funext hpt]
    refine Summable.of_norm_bounded (g := fun z =>
      ‖(u z.1 ^ (n + 1) * (u z.1 - c) ^ 2) * (u z.2 ^ (n + 1) * (u z.2 - c) ^ 2)‖ *
        (2 * 1) ^ 2) (hsum.norm.mul_right _) fun z => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_xiResolventPoint_le_one hX z.1)
          (norm_xiResolventPoint_le_one hX z.2)
      _ = 2 * 1 := by ring
  -- the tail mass over non-second-level pairs
  set P₀ : ℝ := ∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
    ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ with hP₀
  have hprodsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ‖u z.1‖ * ‖u z.2‖) := by
    have h := summable_mul_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using (summable_norm_xiResolventPoint hX))
      (by simpa using (summable_norm_xiResolventPoint hX))
    simpa using h
  have hP₀nn : 0 ≤ P₀ :=
    tsum_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- per-pair tail bound: either a coordinate is on the cleansed edge (weight zero), or a
  -- coordinate is at most `ρ₂`
  have htailterm : ∀ n : ℕ, ∀ z : XiZeroCopy × XiZeroCopy, z ∉ TT →
      ‖(u z.1 * u z.2) ^ (n + 1) * ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) *
        (u z.1 - u z.2) ^ 2‖ ≤
      (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 * (‖u z.1‖ * ‖u z.2‖)) := by
    intro n z hz
    by_cases hT1 : z.1 ∈ T
    · rw [show u z.1 = c from hedgeval z.1 hT1]
      rw [show (c - c) ^ 2 = 0 by ring]
      simp only [zero_mul, mul_zero, norm_zero]
      positivity
    by_cases hT2 : z.2 ∈ T
    · rw [show u z.2 = c from hedgeval z.2 hT2]
      rw [show (c - c) ^ 2 = 0 by ring]
      simp only [zero_mul, mul_zero, norm_zero]
      positivity
    have hcases : z.1 ∉ SF ∨ z.2 ∉ SF := by
      by_contra hcon2
      rw [not_or, not_not, not_not] at hcon2
      exact hz (by rw [hTT, Finset.mem_product]; exact hcon2)
    have hbound1 : ∀ q : XiZeroCopy, ‖(u q - c) ^ 2‖ ≤ (2 * r) ^ 2 := by
      intro q
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖u q - c‖ ≤ ‖u q‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ r + r := by
            refine add_le_add (hq₀ q) ?_
            rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
        _ = 2 * r := by ring
    have hbound2 : ‖(u z.1 - u z.2) ^ 2‖ ≤ (2 * r) ^ 2 := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
        _ ≤ r + r := add_le_add (hq₀ z.1) (hq₀ z.2)
        _ = 2 * r := by ring
    have hpow : ‖(u z.1 * u z.2) ^ (n + 1)‖ ≤ (ρ₂ * ρ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
      rw [norm_pow, norm_mul, mul_pow]
      rcases hcases with hc1 | hc1
      · have e1 : ‖u z.1‖ ^ (n + 1) ≤ ρ₂ ^ n * ‖u z.1‖ := by
          rw [pow_succ']
          calc ‖u z.1‖ * ‖u z.1‖ ^ n ≤ ‖u z.1‖ * ρ₂ ^ n :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
                  (hρ₂bound _ hT1 hc1) n) (norm_nonneg _)
            _ = ρ₂ ^ n * ‖u z.1‖ := mul_comm _ _
        have e2 : ‖u z.2‖ ^ (n + 1) ≤ ρ ^ n * ‖u z.2‖ := by
          rw [pow_succ']
          calc ‖u z.2‖ * ‖u z.2‖ ^ n ≤ ‖u z.2‖ * ρ ^ n :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
                  (hqhmax' _ hT2) n) (norm_nonneg _)
            _ = ρ ^ n * ‖u z.2‖ := mul_comm _ _
        calc ‖u z.1‖ ^ (n + 1) * ‖u z.2‖ ^ (n + 1)
            ≤ (ρ₂ ^ n * ‖u z.1‖) * (ρ ^ n * ‖u z.2‖) :=
              mul_le_mul e1 e2 (pow_nonneg (norm_nonneg _) _) (by positivity)
          _ = (ρ₂ * ρ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
              rw [mul_pow]
              ring
      · have e1 : ‖u z.1‖ ^ (n + 1) ≤ ρ ^ n * ‖u z.1‖ := by
          rw [pow_succ']
          calc ‖u z.1‖ * ‖u z.1‖ ^ n ≤ ‖u z.1‖ * ρ ^ n :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
                  (hqhmax' _ hT1) n) (norm_nonneg _)
            _ = ρ ^ n * ‖u z.1‖ := mul_comm _ _
        have e2 : ‖u z.2‖ ^ (n + 1) ≤ ρ₂ ^ n * ‖u z.2‖ := by
          rw [pow_succ']
          calc ‖u z.2‖ * ‖u z.2‖ ^ n ≤ ‖u z.2‖ * ρ₂ ^ n :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
                  (hρ₂bound _ hT2 hc1) n) (norm_nonneg _)
            _ = ρ₂ ^ n * ‖u z.2‖ := mul_comm _ _
        calc ‖u z.1‖ ^ (n + 1) * ‖u z.2‖ ^ (n + 1)
            ≤ (ρ ^ n * ‖u z.1‖) * (ρ₂ ^ n * ‖u z.2‖) :=
              mul_le_mul e1 e2 (pow_nonneg (norm_nonneg _) _) (by positivity)
          _ = (ρ₂ * ρ) ^ n * (‖u z.1‖ * ‖u z.2‖) := by
              rw [mul_pow]
              ring
    calc ‖(u z.1 * u z.2) ^ (n + 1) * ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) *
          (u z.1 - u z.2) ^ 2‖
        = ‖(u z.1 * u z.2) ^ (n + 1)‖ * (‖(u z.1 - c) ^ 2‖ * ‖(u z.2 - c) ^ 2‖) *
            ‖(u z.1 - u z.2) ^ 2‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ ((ρ₂ * ρ) ^ n * (‖u z.1‖ * ‖u z.2‖)) * ((2 * r) ^ 2 * (2 * r) ^ 2) *
            (2 * r) ^ 2 := by
          refine mul_le_mul (mul_le_mul hpow
            (mul_le_mul (hbound1 z.1) (hbound1 z.2) (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)) hbound2 (norm_nonneg _) (by positivity)
      _ = (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 * (‖u z.1‖ * ‖u z.2‖)) := by ring
  -- the truncated Cesàro assembly
  have hκ2 : ρ₂ / ρ < 1 := (div_lt_one hρpos).mpr hρ₂lt
  have hβ : 0 < (u qh).im ^ 2 * Complex.normSq ((u qh - c) ^ 2) := by
    have him := xiResolventPoint_im_ne_zero_of_spectral hX hqhoff
    have hne : u qh - c ≠ 0 := by
      intro h1
      have h2 : u qh = c := by
        have := sub_eq_zero.mp h1
        exact this
      have h3 : ‖u qh‖ = ‖c‖ := by rw [h2]
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] at h3
      rw [← hρ] at h3
      linarith
    have hnsq : 0 < Complex.normSq ((u qh - c) ^ 2) :=
      Complex.normSq_pos.mpr (pow_ne_zero 2 hne)
    positivity
  set β : ℝ := (u qh).im ^ 2 * Complex.normSq ((u qh - c) ^ 2) with hβdef
  -- unit pair points on the second level
  have hVnorm : ∀ z ∈ TT, ‖V z‖ = 1 := by
    intro z hz
    rw [hTT, Finset.mem_product] at hz
    simp only [hV]
    rw [norm_div, norm_mul, norm_pow, hSFval z.1 hz.1, hSFval z.2 hz.2,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, pow_two]
    exact div_self (by positivity)
  -- second-level pair points at `1` are conjugate pairs with nonpositive real weight
  have hP1w : ∀ z ∈ TT, V z = 1 → Wt z =
      ((-(4 * ((u z.1).im ^ 2 * Complex.normSq ((u z.1 - c) ^ 2))) : ℝ) : ℂ) := by
    intro z hz hVz
    rw [hTT, Finset.mem_product] at hz
    have hz1ne : u z.1 ≠ 0 := xiResolventPoint_ne_zero hX z.1
    have h1 : u z.1 * u z.2 = (((ρ : ℝ)) : ℂ) ^ 2 := by
      have h0 := hVz
      simp only [hV] at h0
      rw [div_eq_iff (pow_ne_zero 2 hρC), one_mul] at h0
      exact h0
    have h2 : u z.1 * (starRingEnd ℂ) (u z.1) = (((ρ : ℝ)) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, ← Complex.ofReal_pow]
      norm_cast
      rw [← Complex.sq_norm, hSFval z.1 hz.1]
    have hconj : u z.2 = (starRingEnd ℂ) (u z.1) :=
      mul_left_cancel₀ hz1ne (h1.trans h2.symm)
    have hWconj : (u z.2 - c) ^ 2 = (starRingEnd ℂ) ((u z.1 - c) ^ 2) := by
      rw [map_pow, map_sub, hconj, hc, Complex.conj_ofReal]
    have hprod : (u z.1 - c) ^ 2 * (u z.2 - c) ^ 2 =
        ((Complex.normSq ((u z.1 - c) ^ 2) : ℝ) : ℂ) := by
      rw [hWconj, Complex.mul_conj]
    have hdiff : (u z.1 - u z.2) ^ 2 = ((-(4 * (u z.1).im ^ 2) : ℝ) : ℂ) := by
      rw [hconj, Complex.sub_conj, mul_pow, Complex.I_sq]
      push_cast
      ring
    simp only [hWt]
    rw [hprod, hdiff, ← Complex.ofReal_mul]
    push_cast
    ring
  -- the witness conjugate pair
  set zh : XiZeroCopy × XiZeroCopy := (qh, xiZeroCopyLineConjEquiv qh) with hzh
  have hlineconj : u (xiZeroCopyLineConjEquiv qh) = (starRingEnd ℂ) (u qh) :=
    xiResolventPoint_lineConj X qh
  have hconjnorm : ‖xiResolventPoint X (xiZeroCopyLineConjEquiv qh)‖ = ρ := by
    rw [show ‖xiResolventPoint X (xiZeroCopyLineConjEquiv qh)‖ =
      ‖u (xiZeroCopyLineConjEquiv qh)‖ from rfl, hlineconj, RCLike.norm_conj]
  have hconjSF : xiZeroCopyLineConjEquiv qh ∈ SF := by
    refine (hmemSF _).mpr ⟨hconjnorm.ge, fun hT1 => ?_⟩
    have := hTval _ hT1
    rw [hconjnorm] at this
    linarith
  have hzhTT : zh ∈ TT := by
    rw [hzh, hTT, Finset.mem_product]
    exact ⟨hqhSF, hconjSF⟩
  have hVzh : V zh = 1 := by
    simp only [hV, hzh]
    rw [show u (qh, xiZeroCopyLineConjEquiv qh).2 = (starRingEnd ℂ) (u qh) from hlineconj]
    rw [show u (qh, xiZeroCopyLineConjEquiv qh).1 = u qh from rfl]
    rw [Complex.mul_conj, ← Complex.ofReal_pow]
    rw [show Complex.normSq (u qh) = ρ ^ 2 by rw [← Complex.sq_norm]]
    exact div_self (Complex.ofReal_ne_zero.mpr (by positivity))
  -- geometric bound and constants
  have hκ0' : (0 : ℝ) ≤ ρ₂ / ρ := div_nonneg hρ₂0 hρpos.le
  have h1κ : (0 : ℝ) < 1 - ρ₂ / ρ := by linarith
  have hgeo : ∀ N : ℕ, ∑ n ∈ Finset.range N, (ρ₂ / ρ) ^ n ≤ 1 / (1 - ρ₂ / ρ) := by
    intro N
    rw [geom_sum_eq (ne_of_lt hκ2)]
    rw [show (ρ₂ / ρ) ^ N - 1 = -(1 - (ρ₂ / ρ) ^ N) by ring,
      show ρ₂ / ρ - 1 = -(1 - ρ₂ / ρ) by ring, neg_div_neg_eq]
    rw [div_le_div_iff₀ h1κ h1κ]
    nlinarith [pow_nonneg hκ0' N]
  set CT : ℝ := (2 * r) ^ 6 * P₀ / ρ ^ 2 * (1 / (1 - ρ₂ / ρ)) with hCT
  set CP2 : ℝ := ∑ z ∈ TT.filter (fun z => ¬ V z = 1), ‖Wt z‖ * (2 / ‖V z - 1‖) with hCP2
  -- the tail bound at level n
  have htail : ∀ n : ℕ,
      ‖∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
        (u (↑zc : XiZeroCopy × XiZeroCopy).1 * u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
          ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
            (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 - u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖ ≤
        (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 * P₀) := by
    intro n
    have hsubpair := ((hpairsummable n).norm.subtype
      ((↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ))
    have hsubprod := hprodsum.subtype ((↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ)
    calc ‖∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
            ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
              (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 - u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖
        ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 *
              (‖u (↑zc : XiZeroCopy × XiZeroCopy).1‖ *
                ‖u (↑zc : XiZeroCopy × XiZeroCopy).2‖)) := by
          refine Summable.tsum_le_tsum (fun zc => ?_) hsubpair
            (((hsubprod.mul_left ((2 * r) ^ 6)).mul_left ((ρ₂ * ρ) ^ n)))
          have hznot : (↑zc : XiZeroCopy × XiZeroCopy) ∉ TT := by
            have h := zc.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          exact htailterm n _ hznot
      _ = (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 * P₀) := by
          rw [tsum_mul_left, tsum_mul_left, hP₀]
  -- the master estimate at every truncation
  have hmaster : ∀ N : ℕ, 0 ≤ -(4 * β) * N + CP2 + CT := by
    intro N
    have hlhs : 0 ≤ ∑ n ∈ Finset.range N,
        (2 * (xiDeflatedMoment r n X * xiDeflatedMoment r (n + 2) X -
          xiDeflatedMoment r (n + 1) X ^ 2)).re / ρ ^ (2 * (n + 1)) := by
      refine Finset.sum_nonneg fun n _ => ?_
      have h1 := hdefl r n
      have h2 : (2 * (xiDeflatedMoment r n X * xiDeflatedMoment r (n + 2) X -
          xiDeflatedMoment r (n + 1) X ^ 2)).re = 2 * (xiDeflatedMoment r n X *
            xiDeflatedMoment r (n + 2) X - xiDeflatedMoment r (n + 1) X ^ 2).re := by
        simp [Complex.mul_re]
      rw [h2]
      have h3 : (0 : ℝ) < ρ ^ (2 * (n + 1)) := pow_pos hρpos _
      positivity
    have hn : ∀ n ∈ Finset.range N,
        (2 * (xiDeflatedMoment r n X * xiDeflatedMoment r (n + 2) X -
          xiDeflatedMoment r (n + 1) X ^ 2)).re / ρ ^ (2 * (n + 1)) =
        (∑ z ∈ TT, Wt z * V z ^ (n + 1)).re +
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
            ρ ^ (2 * (n + 1)) := by
      intro n _
      have hexp := two_mul_deflatedTuranMinorAt_eq_tsum_pair hX r n
      have hsplit := (hpairsummable n).sum_add_tsum_compl (s := TT)
      have hEq : (2 : ℂ) * (xiDeflatedMoment r n X * xiDeflatedMoment r (n + 2) X -
          xiDeflatedMoment r (n + 1) X ^ 2) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) *
            ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) * (u z.1 - u z.2) ^ 2) +
            ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                  (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2 := by
        rw [hexp]
        exact hsplit.symm
      have hre := congrArg Complex.re hEq
      rw [Complex.add_re] at hre
      rw [hre, add_div]
      congr 1
      have hCfin : (∑ z ∈ TT, Wt z * V z ^ (n + 1)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) *
            ((u z.1 - c) ^ 2 * (u z.2 - c) ^ 2) * (u z.1 - u z.2) ^ 2) /
            ((ρ ^ (2 * (n + 1)) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        have hden : ((((ρ : ℝ)) : ℂ) ^ 2) ^ (n + 1) = ((ρ ^ (2 * (n + 1)) : ℝ) : ℂ) := by
          push_cast
          ring
        simp only [hV, hWt]
        rw [div_pow, hden]
        ring
      rw [hCfin, re_div_ofReal]
    have hdecomp : ∑ n ∈ Finset.range N,
        (2 * (xiDeflatedMoment r n X * xiDeflatedMoment r (n + 2) X -
          xiDeflatedMoment r (n + 1) X ^ 2)).re / ρ ^ (2 * (n + 1)) =
        (∑ z ∈ TT, (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) +
          ∑ n ∈ Finset.range N,
            (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                  (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
              ρ ^ (2 * (n + 1)) := by
      rw [Finset.sum_congr rfl hn, Finset.sum_add_distrib]
      congr 1
      calc ∑ n ∈ Finset.range N, (∑ z ∈ TT, Wt z * V z ^ (n + 1)).re
          = ∑ n ∈ Finset.range N, ∑ z ∈ TT, (Wt z * V z ^ (n + 1)).re :=
            Finset.sum_congr rfl fun n _ => Complex.re_sum _ _
        _ = ∑ z ∈ TT, ∑ n ∈ Finset.range N, (Wt z * V z ^ (n + 1)).re :=
            Finset.sum_comm
        _ = ∑ z ∈ TT, (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum, Complex.re_sum]
    have hedge : (∑ z ∈ TT, (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤
        -(4 * β) * N + CP2 := by
      rw [← Finset.sum_filter_add_sum_filter_not TT (fun z => V z = 1)]
      have hpart1 : (∑ z ∈ TT.filter (fun z => V z = 1),
          (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ -(4 * β) * N := by
        have hterm : ∀ z ∈ TT.filter (fun z => V z = 1),
            (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re =
              -(4 * ((u z.1).im ^ 2 * Complex.normSq ((u z.1 - c) ^ 2))) * (N : ℝ) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [hP1w z hz.1 hz.2, hz.2]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [Finset.sum_congr rfl hterm]
        have hzhfil : zh ∈ TT.filter (fun z => V z = 1) :=
          Finset.mem_filter.mpr ⟨hzhTT, hVzh⟩
        rw [← Finset.add_sum_erase _ _ hzhfil]
        have h1 : -(4 * ((u zh.1).im ^ 2 * Complex.normSq ((u zh.1 - c) ^ 2))) * (N : ℝ) =
            -(4 * β) * N := by
          simp only [hzh, hβdef]
        have h2 : ∑ z ∈ (TT.filter (fun z => V z = 1)).erase zh,
            -(4 * ((u z.1).im ^ 2 * Complex.normSq ((u z.1 - c) ^ 2))) * (N : ℝ) ≤ 0 := by
          refine Finset.sum_nonpos fun z _ => ?_
          have h3 : (0 : ℝ) ≤ 4 * ((u z.1).im ^ 2 *
              Complex.normSq ((u z.1 - c) ^ 2)) * N := by
            have := Complex.normSq_nonneg ((u z.1 - c) ^ 2)
            positivity
          linarith
        rw [h1]
        linarith
      have hpart2 : (∑ z ∈ TT.filter (fun z => ¬ V z = 1),
          (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ CP2 := by
        rw [hCP2]
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Finset.mem_filter] at hz
        have hb := GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le
          (le_of_eq (hVnorm z hz.1)) hz.2 N
        calc (Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re
            ≤ ‖Wt z * ∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := Complex.re_le_norm _
          _ = ‖Wt z‖ * ‖∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := norm_mul _ _
          _ ≤ ‖Wt z‖ * (2 / ‖V z - 1‖) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      linarith
    have htailN : ∑ n ∈ Finset.range N,
        (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
            ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
              (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
          ρ ^ (2 * (n + 1)) ≤ CT := by
      rw [hCT]
      calc ∑ n ∈ Finset.range N,
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
            ρ ^ (2 * (n + 1))
          ≤ ∑ n ∈ Finset.range N, (2 * r) ^ 6 * P₀ / ρ ^ 2 * (ρ₂ / ρ) ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h1 := htail n
            have h2 := Complex.re_le_norm
              (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                  ((u (↑zc : XiZeroCopy × XiZeroCopy).1 - c) ^ 2 *
                    (u (↑zc : XiZeroCopy × XiZeroCopy).2 - c) ^ 2) *
                  (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                    u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2)
            have hd : (0 : ℝ) < ρ ^ (2 * (n + 1)) := pow_pos hρpos _
            rw [div_le_iff₀ hd]
            have halg : (ρ₂ * ρ) ^ n * ((2 * r) ^ 6 * P₀) =
                (2 * r) ^ 6 * P₀ / ρ ^ 2 * (ρ₂ / ρ) ^ n * ρ ^ (2 * (n + 1)) := by
              rw [div_pow, mul_pow]
              field_simp
              ring
            linarith
        _ = (2 * r) ^ 6 * P₀ / ρ ^ 2 * ∑ n ∈ Finset.range N, (ρ₂ / ρ) ^ n := by
            rw [Finset.mul_sum]
        _ ≤ (2 * r) ^ 6 * P₀ / ρ ^ 2 * (1 / (1 - ρ₂ / ρ)) := by
            refine mul_le_mul_of_nonneg_left (hgeo N) ?_
            positivity
    have hfinal := hlhs
    rw [hdecomp] at hfinal
    linarith
  -- the contradiction
  obtain ⟨N, hN⟩ := exists_nat_gt ((CP2 + CT) / (4 * β))
  have h1 := hmaster N
  rw [div_lt_iff₀ (by positivity)] at hN
  nlinarith

end

end RHTower
