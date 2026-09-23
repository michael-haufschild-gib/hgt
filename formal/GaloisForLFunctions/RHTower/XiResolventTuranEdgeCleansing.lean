import GaloisForLFunctions.RHTower.XiResolventDiagonalEdgeDetection

/-!
# Turán minors cleanse the spectral edge

Diagonal moment positivity places one lowest zero on the critical line
(`exists_criticalLine_copy_of_forall_moment_re_nonneg`).  This file proves that the next layer of
the Hankel criterion — nonnegativity of all consecutive **Turán minors**
`R n * R (n+2) - R (n+1)^(2 : ℕ)` at one shift — cleanses the edge completely: **every** divisor copy
of maximal resolvent modulus lies on the critical line.

Mechanism.  The variance expansion identifies twice the level-`n` minor with the pair sum
`sum_(q,r) (u_q u_r)^(n+1) (u_q - u_r)^(2 : ℕ)`.  Normalizing by `r^(2(n+1))`, the maximal pair points
`u_q u_r` of modulus `r^(2 : ℕ)` land on the unit circle; those equal to `r^(2 : ℕ)` itself are exactly the
conjugate pairs `u_r = conj u_q`, and their weights are the exact negative reals
`-4 (Im u_q)^(2 : ℕ)`.  Summing over `n < N`: the conjugate-pair contribution is `-4 (Im u_q)^(2 : ℕ) * N`
per off-critical edge copy, all remaining unit pair points contribute boundedly (geometric sums),
and the sub-maximal tail is a convergent geometric series.  Minor nonnegativity therefore forces
`(Im u_q)^(2 : ℕ) * N` bounded in `N`, i.e. every edge copy has real resolvent value, and the height
gap lifts this to the critical line.

Together with diagonal edge detection this grades the Hankel criterion by depth: the diagonal
sees the edge, the first minors clean it.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The variance expansion of the level-`n` Turán minor.** -/
theorem two_mul_turanMinorAt_eq_tsum_pair {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    2 * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
        xiResolventMoment (n + 1) X ^ (2 : ℕ)) =
      ∑' z : XiZeroCopy × XiZeroCopy,
        (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ (2 : ℕ) := by
  have h0 := summable_norm_xiResolventPoint_pow hX n
  have h1 := summable_norm_xiResolventPoint_pow hX (n + 1)
  have h2 := summable_norm_xiResolventPoint_pow hX (n + 2)
  have hA := tsum_mul_tsum_of_summable_norm h0 h2
  have hB := tsum_mul_tsum_of_summable_norm h1 h1
  have hC := tsum_mul_tsum_of_summable_norm h2 h0
  have hsumA := summable_mul_of_summable_norm h0 h2
  have hsumB := summable_mul_of_summable_norm h1 h1
  have hsumC := summable_mul_of_summable_norm h2 h0
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ (2 : ℕ) =
        ((xiResolventPoint X z.1 ^ (n + 1) * xiResolventPoint X z.2 ^ (n + 2 + 1) -
            2 * (xiResolventPoint X z.1 ^ (n + 1 + 1) *
              xiResolventPoint X z.2 ^ (n + 1 + 1))) +
          xiResolventPoint X z.1 ^ (n + 2 + 1) * xiResolventPoint X z.2 ^ (n + 1)) := by
    intro z
    ring
  rw [xiResolventMoment, xiResolventMoment, xiResolventMoment,
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

/-- Off-critical spectral points have off-real resolvent values. -/
theorem xiResolventPoint_im_ne_zero_of_spectral {X : ℝ} (hX : 0 ≤ X) {q : XiZeroCopy}
    (h : (xiSpectralPoint q).im ≠ 0) : (xiResolventPoint X q).im ≠ 0 := by
  have hne := xiSpectralSq_add_ofReal_ne_zero hX q
  have hnsq : Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ≠ 0 :=
    fun hc => hne (Complex.normSq_eq_zero.mp hc)
  have hrene : (xiSpectralPoint q).re ≠ 0 := by
    have hg := xiZeroCopy_two_lt_im_sq q
    rw [← xiSpectralPoint_re_eq] at hg
    intro h0
    rw [h0] at hg
    norm_num at hg
  have himw : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im ≠ 0 := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero, sq, Complex.mul_im]
    intro h0
    rcases mul_eq_zero.mp (by linarith [h0] : (xiSpectralPoint q).re *
        (xiSpectralPoint q).im * 2 = 0) with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hrene h2
      · exact h h2
    · norm_num at h1
  rw [xiResolventPoint, Complex.inv_im]
  intro h0
  rcases div_eq_zero_iff.mp h0 with h1 | h1
  · exact himw (neg_eq_zero.mp h1)
  · exact hnsq h1

/-- Real part of division by a real scalar. -/
theorem re_div_ofReal (z : ℂ) (a : ℝ) : (z / (a : ℂ)).re = z.re / a := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]

/-- **Turán minors cleanse the edge**: if every consecutive Turán minor
`R n * R (n+2) - R (n+1)^(2 : ℕ)` at one shift is nonnegative, then every divisor copy of maximal
resolvent modulus lies on the critical line. -/
theorem forall_edge_criticalLine_of_forall_turanMinor_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hminor : ∀ n : ℕ, 0 ≤ (xiResolventMoment n X * xiResolventMoment (n + 2) X -
      xiResolventMoment (n + 1) X ^ (2 : ℕ)).re) :
    ∀ q : XiZeroCopy, (∀ q', ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖) →
      (xiSpectralPoint q).im = 0 := by
  classical
  intro qh hqhmax
  by_contra hqhoff
  -- the edge data
  set r : ℝ := ‖xiResolventPoint X qh‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (xiResolventPoint_ne_zero hX qh)
  have hTfin : {q : XiZeroCopy | r ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hrpos
  set T : Finset XiZeroCopy := hTfin.toFinset with hT
  have hmemT : ∀ q, q ∈ T ↔ r ≤ ‖xiResolventPoint X q‖ := by
    intro q
    rw [hT, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hTval : ∀ q ∈ T, ‖xiResolventPoint X q‖ = r := fun q hq =>
    le_antisymm (hqhmax q) ((hmemT q).mp hq)
  have hqhT : qh ∈ T := (hmemT qh).mpr le_rfl
  -- the second modulus level
  obtain ⟨ρ, hρ0, hρlt, hρbound⟩ :
      ∃ ρ, 0 ≤ ρ ∧ ρ < r ∧ ∀ q, q ∉ T → ‖xiResolventPoint X q‖ ≤ ρ := by
    have hhalf : (0 : ℝ) < r / 2 := by linarith
    have hS2fin : {q : XiZeroCopy | r / 2 ≤ ‖xiResolventPoint X q‖}.Finite :=
      finite_setOf_le_norm_xiResolventPoint hX hhalf
    set D : Finset XiZeroCopy := hS2fin.toFinset \ T with hD
    rcases D.eq_empty_or_nonempty with hDe | hDne
    · refine ⟨r / 2, by linarith, by linarith, fun q hq => ?_⟩
      by_contra hgt
      rw [not_le] at hgt
      have hqD : q ∈ D := by
        rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
        exact ⟨le_of_lt hgt, hq⟩
      rw [hDe] at hqD
      exact absurd hqD (Finset.notMem_empty q)
    · obtain ⟨qd, hqdD, hqdmax⟩ := D.exists_max_image
        (fun q => ‖xiResolventPoint X q‖) hDne
      have hqdT : qd ∉ T := by
        rw [hD, Finset.mem_sdiff] at hqdD
        exact hqdD.2
      refine ⟨max ‖xiResolventPoint X qd‖ (r / 2),
        le_trans (by linarith) (le_max_right _ _), ?_, ?_⟩
      · rw [max_lt_iff]
        refine ⟨?_, by linarith⟩
        exact lt_of_not_ge fun hge => hqdT ((hmemT qd).mpr hge)
      · intro q hq
        by_cases hq2 : r / 2 ≤ ‖xiResolventPoint X q‖
        · have hqD : q ∈ D := by
            rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
            exact ⟨hq2, hq⟩
          exact le_trans (hqdmax q hqD) (le_max_left _ _)
        · exact le_trans (not_le.mp hq2).le (le_max_right _ _)
  -- pair machinery
  set c : ℂ := ((r : ℝ) : ℂ) with hc
  have hcne : c ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  set w : XiZeroCopy × XiZeroCopy → ℂ := fun z => (u z.1 - u z.2) ^ (2 : ℕ) with hw
  set V : XiZeroCopy × XiZeroCopy → ℂ := fun z => u z.1 * u z.2 / c ^ (2 : ℕ) with hV
  set TT : Finset (XiZeroCopy × XiZeroCopy) := T ×ˢ T with hTT
  -- the tail mass
  have hprodsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ‖u z.1‖ * ‖u z.2‖) := by
    have h := summable_mul_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using (summable_norm_xiResolventPoint hX))
      (by simpa using (summable_norm_xiResolventPoint hX))
    simpa using h
  have hsubprod : Summable (fun z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ =>
      ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) :=
    hprodsum.subtype _
  set P₀ : ℝ := ∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
    ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ with hP₀
  have hP₀nn : 0 ≤ P₀ :=
    tsum_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- per-level pair term and its summability
  have hpairsummable : ∀ n : ℕ, Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (u z.1 * u z.2) ^ (n + 1) * w z) := by
    intro n
    refine Summable.of_norm_bounded (hprodsum.mul_right ((2 * r) ^ (2 : ℕ))) fun z => ?_
    rw [norm_mul, mul_pow, norm_mul]
    simp only [hw]
    have h1 : ‖u z.1 ^ (n + 1)‖ ≤ ‖u z.1‖ := by
      rw [norm_pow, pow_succ']
      have hle1 : ‖u z.1‖ ^ n ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX z.1)
      nlinarith [norm_nonneg (u z.1), pow_nonneg (norm_nonneg (u z.1)) n]
    have h2 : ‖u z.2 ^ (n + 1)‖ ≤ ‖u z.2‖ := by
      rw [norm_pow, pow_succ']
      have hle1 : ‖u z.2‖ ^ n ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX z.2)
      nlinarith [norm_nonneg (u z.2), pow_nonneg (norm_nonneg (u z.2)) n]
    have h3 : ‖(u z.1 - u z.2) ^ (2 : ℕ)‖ ≤ (2 * r) ^ (2 : ℕ) := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
        _ ≤ r + r := add_le_add (hqhmax z.1) (hqhmax z.2)
        _ = 2 * r := by ring
    calc ‖u z.1 ^ (n + 1)‖ * ‖u z.2 ^ (n + 1)‖ * ‖(u z.1 - u z.2) ^ (2 : ℕ)‖
        ≤ (‖u z.1‖ * ‖u z.2‖) * (2 * r) ^ (2 : ℕ) := by
          have := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)) h3
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          linarith
      _ = ‖u z.1‖ * ‖u z.2‖ * (2 * r) ^ (2 : ℕ) := by ring
  -- tail bound at level n
  have htail : ∀ n : ℕ,
      ‖∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
        (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
          w ↑z‖ ≤ (ρ * r) ^ n * ((2 * r) ^ (2 : ℕ) * P₀) := by
    intro n
    have hsubpair : Summable (fun z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ =>
        ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
          w ↑z‖) := ((hpairsummable n).norm.subtype _)
    calc ‖∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
            w ↑z‖
        ≤ ∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              w ↑z‖ := norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' z : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (ρ * r) ^ n * ((2 * r) ^ (2 : ℕ) *
              (‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖)) := by
          refine Summable.tsum_le_tsum (fun z => ?_) hsubpair
            (((hsubprod.mul_left ((2 * r) ^ (2 : ℕ))).mul_left ((ρ * r) ^ n)))
          obtain ⟨z', hz'⟩ := z
          have hznot : z' ∉ TT := by
            simp only [Set.mem_compl_iff, Finset.mem_coe] at hz'
            exact hz'
          have hcases : z'.1 ∉ T ∨ z'.2 ∉ T := by
            by_contra hcon2
            rw [not_or, not_not, not_not] at hcon2
            exact hznot (by rw [hTT, Finset.mem_product]; exact hcon2)
          have hb1 : ‖u z'.1 ^ (n + 1)‖ * ‖u z'.2 ^ (n + 1)‖ ≤
              (ρ * r) ^ n * (‖u z'.1‖ * ‖u z'.2‖) := by
            rcases hcases with hc1 | hc1
            · have e1 : ‖u z'.1 ^ (n + 1)‖ ≤ ρ ^ n * ‖u z'.1‖ := by
                rw [norm_pow, pow_succ']
                calc ‖u z'.1‖ * ‖u z'.1‖ ^ n ≤ ‖u z'.1‖ * ρ ^ n :=
                      mul_le_mul_of_nonneg_left
                        (pow_le_pow_left₀ (norm_nonneg _) (hρbound _ hc1) n) (norm_nonneg _)
                  _ = ρ ^ n * ‖u z'.1‖ := mul_comm _ _
              have e2 : ‖u z'.2 ^ (n + 1)‖ ≤ r ^ n * ‖u z'.2‖ := by
                rw [norm_pow, pow_succ']
                calc ‖u z'.2‖ * ‖u z'.2‖ ^ n ≤ ‖u z'.2‖ * r ^ n :=
                      mul_le_mul_of_nonneg_left
                        (pow_le_pow_left₀ (norm_nonneg _) (hqhmax z'.2) n) (norm_nonneg _)
                  _ = r ^ n * ‖u z'.2‖ := mul_comm _ _
              calc ‖u z'.1 ^ (n + 1)‖ * ‖u z'.2 ^ (n + 1)‖
                  ≤ (ρ ^ n * ‖u z'.1‖) * (r ^ n * ‖u z'.2‖) :=
                    mul_le_mul e1 e2 (norm_nonneg _)
                      (by positivity)
                _ = (ρ * r) ^ n * (‖u z'.1‖ * ‖u z'.2‖) := by
                    rw [mul_pow]
                    ring
            · have e1 : ‖u z'.1 ^ (n + 1)‖ ≤ r ^ n * ‖u z'.1‖ := by
                rw [norm_pow, pow_succ']
                calc ‖u z'.1‖ * ‖u z'.1‖ ^ n ≤ ‖u z'.1‖ * r ^ n :=
                      mul_le_mul_of_nonneg_left
                        (pow_le_pow_left₀ (norm_nonneg _) (hqhmax z'.1) n) (norm_nonneg _)
                  _ = r ^ n * ‖u z'.1‖ := mul_comm _ _
              have e2 : ‖u z'.2 ^ (n + 1)‖ ≤ ρ ^ n * ‖u z'.2‖ := by
                rw [norm_pow, pow_succ']
                calc ‖u z'.2‖ * ‖u z'.2‖ ^ n ≤ ‖u z'.2‖ * ρ ^ n :=
                      mul_le_mul_of_nonneg_left
                        (pow_le_pow_left₀ (norm_nonneg _) (hρbound _ hc1) n) (norm_nonneg _)
                  _ = ρ ^ n * ‖u z'.2‖ := mul_comm _ _
              calc ‖u z'.1 ^ (n + 1)‖ * ‖u z'.2 ^ (n + 1)‖
                  ≤ (r ^ n * ‖u z'.1‖) * (ρ ^ n * ‖u z'.2‖) :=
                    mul_le_mul e1 e2 (norm_nonneg _)
                      (by positivity)
                _ = (ρ * r) ^ n * (‖u z'.1‖ * ‖u z'.2‖) := by
                    rw [mul_pow]
                    ring
          have hb2 : ‖(u z'.1 - u z'.2) ^ (2 : ℕ)‖ ≤ (2 * r) ^ (2 : ℕ) := by
            rw [norm_pow]
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            calc ‖u z'.1 - u z'.2‖ ≤ ‖u z'.1‖ + ‖u z'.2‖ := norm_sub_le _ _
              _ ≤ r + r := add_le_add (hqhmax z'.1) (hqhmax z'.2)
              _ = 2 * r := by ring
          rw [norm_mul, mul_pow, norm_mul]
          simp only [hw]
          calc ‖u z'.1 ^ (n + 1)‖ * ‖u z'.2 ^ (n + 1)‖ * ‖(u z'.1 - u z'.2) ^ (2 : ℕ)‖
              ≤ ((ρ * r) ^ n * (‖u z'.1‖ * ‖u z'.2‖)) * (2 * r) ^ (2 : ℕ) := by
                have hnn : (0 : ℝ) ≤ ‖u z'.1 ^ (n + 1)‖ * ‖u z'.2 ^ (n + 1)‖ :=
                  mul_nonneg (norm_nonneg _) (norm_nonneg _)
                have := mul_le_mul hb1 hb2 (norm_nonneg _)
                  (by positivity)
                linarith
            _ = (ρ * r) ^ n * ((2 * r) ^ (2 : ℕ) * (‖u z'.1‖ * ‖u z'.2‖)) := by ring
      _ = (ρ * r) ^ n * ((2 * r) ^ (2 : ℕ) * P₀) := by
          rw [tsum_mul_left, tsum_mul_left, hP₀]
  -- unit pair points on the edge
  have hVnorm : ∀ z ∈ TT, ‖V z‖ = 1 := by
    intro z hz
    rw [hTT, Finset.mem_product] at hz
    simp only [hV]
    rw [norm_div, norm_mul, norm_pow, hTval z.1 hz.1, hTval z.2 hz.2, hc,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [pow_two]
    exact div_self (by positivity)
  -- edge pair points at `1` are conjugate pairs with nonpositive real weight
  have hP1w : ∀ z ∈ TT, V z = 1 → w z = ((-(4 * (u z.1).im ^ (2 : ℕ)) : ℝ) : ℂ) := by
    intro z hz hVz
    rw [hTT, Finset.mem_product] at hz
    have hz1ne : u z.1 ≠ 0 := xiResolventPoint_ne_zero hX z.1
    have h1 : u z.1 * u z.2 = c ^ (2 : ℕ) := by
      have h0 := hVz
      simp only [hV] at h0
      rw [div_eq_iff (pow_ne_zero 2 hcne), one_mul] at h0
      exact h0
    have h2 : u z.1 * (starRingEnd ℂ) (u z.1) = c ^ (2 : ℕ) := by
      rw [Complex.mul_conj, hc, ← Complex.ofReal_pow]
      norm_cast
      rw [← Complex.sq_norm, hTval z.1 hz.1]
    have hconj : u z.2 = (starRingEnd ℂ) (u z.1) :=
      mul_left_cancel₀ hz1ne (h1.trans h2.symm)
    simp only [hw]
    rw [hconj, Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring
  -- the witness conjugate pair on the edge
  set zh : XiZeroCopy × XiZeroCopy := (qh, xiZeroCopyLineConjEquiv qh) with hzh
  have hlineconj : u (xiZeroCopyLineConjEquiv qh) = (starRingEnd ℂ) (u qh) :=
    xiResolventPoint_lineConj X qh
  have hconjT : xiZeroCopyLineConjEquiv qh ∈ T := by
    refine (hmemT _).mpr ?_
    rw [show ‖xiResolventPoint X (xiZeroCopyLineConjEquiv qh)‖ =
      ‖u (xiZeroCopyLineConjEquiv qh)‖ from rfl, hlineconj, RCLike.norm_conj]
  have hzhTT : zh ∈ TT := by
    rw [hzh, hTT, Finset.mem_product]
    exact ⟨hqhT, hconjT⟩
  have hprodzh : u zh.1 * u zh.2 = c ^ (2 : ℕ) := by
    rw [hzh]
    show u qh * u (xiZeroCopyLineConjEquiv qh) = c ^ (2 : ℕ)
    rw [hlineconj, Complex.mul_conj, hc, ← Complex.ofReal_pow]
    norm_cast
    rw [← Complex.sq_norm, hTval qh hqhT]
  have hVzh : V zh = 1 := by
    simp only [hV]
    rw [hprodzh]
    exact div_self (pow_ne_zero 2 hcne)
  -- geometric bound and the constants
  have hκ1 : ρ / r < 1 := (div_lt_one hrpos).mpr hρlt
  have hκ0 : (0 : ℝ) ≤ ρ / r := div_nonneg hρ0 hrpos.le
  have h1κ : (0 : ℝ) < 1 - ρ / r := by linarith
  have hgeo : ∀ N : ℕ, ∑ n ∈ Finset.range N, (ρ / r) ^ n ≤ 1 / (1 - ρ / r) := by
    intro N
    rw [geom_sum_eq (ne_of_lt hκ1)]
    rw [show (ρ / r) ^ N - 1 = -(1 - (ρ / r) ^ N) by ring,
      show ρ / r - 1 = -(1 - ρ / r) by ring, neg_div_neg_eq]
    rw [div_le_div_iff₀ h1κ h1κ]
    nlinarith [pow_nonneg hκ0 N]
  set CT : ℝ := 4 * P₀ * (1 / (1 - ρ / r)) with hCT
  set CP2 : ℝ := ∑ z ∈ TT.filter (fun z => ¬ V z = 1), ‖w z‖ * (2 / ‖V z - 1‖) with hCP2
  set β : ℝ := (u qh).im ^ (2 : ℕ) with hβ
  have hβpos : 0 < β := by
    rw [hβ]
    have him := xiResolventPoint_im_ne_zero_of_spectral hX hqhoff
    positivity
  -- the master estimate at every truncation
  have hmaster : ∀ N : ℕ, 0 ≤ -(4 * β) * N + CP2 + CT := by
    intro N
    have hlhs : 0 ≤ ∑ n ∈ Finset.range N,
        (2 * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
          xiResolventMoment (n + 1) X ^ (2 : ℕ))).re / r ^ (2 * (n + 1)) := by
      refine Finset.sum_nonneg fun n _ => ?_
      have h1 := hminor n
      have h2 : (2 * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
          xiResolventMoment (n + 1) X ^ (2 : ℕ))).re = 2 * (xiResolventMoment n X *
            xiResolventMoment (n + 2) X - xiResolventMoment (n + 1) X ^ (2 : ℕ)).re := by
        simp [Complex.mul_re]
      rw [h2]
      have h3 : (0 : ℝ) < r ^ (2 * (n + 1)) := pow_pos hrpos _
      positivity
    have hn : ∀ n ∈ Finset.range N,
        (2 * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
          xiResolventMoment (n + 1) X ^ (2 : ℕ))).re / r ^ (2 * (n + 1)) =
        (∑ z ∈ TT, w z * V z ^ (n + 1)).re +
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc).re /
            r ^ (2 * (n + 1)) := by
      intro n _
      have hexp := two_mul_turanMinorAt_eq_tsum_pair hX n
      have hsplit := (hpairsummable n).sum_add_tsum_compl (s := TT)
      have hEq : (2 : ℂ) * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
          xiResolventMoment (n + 1) X ^ (2 : ℕ)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) * w z) +
            ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc := by
        rw [hexp]
        exact hsplit.symm
      have hre := congrArg Complex.re hEq
      rw [Complex.add_re] at hre
      rw [hre, add_div]
      congr 1
      have hCfin : (∑ z ∈ TT, w z * V z ^ (n + 1)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) * w z) /
            ((r ^ (2 * (n + 1)) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        have hden : (c ^ (2 : ℕ)) ^ (n + 1) = ((r ^ (2 * (n + 1)) : ℝ) : ℂ) := by
          rw [hc]
          push_cast
          ring
        simp only [hV]
        rw [div_pow, hden]
        ring
      rw [hCfin, re_div_ofReal]
    have hdecomp : ∑ n ∈ Finset.range N,
        (2 * (xiResolventMoment n X * xiResolventMoment (n + 2) X -
          xiResolventMoment (n + 1) X ^ (2 : ℕ))).re / r ^ (2 * (n + 1)) =
        (∑ z ∈ TT, (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) +
          ∑ n ∈ Finset.range N,
            (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc).re /
              r ^ (2 * (n + 1)) := by
      rw [Finset.sum_congr rfl hn, Finset.sum_add_distrib]
      congr 1
      calc ∑ n ∈ Finset.range N, (∑ z ∈ TT, w z * V z ^ (n + 1)).re
          = ∑ n ∈ Finset.range N, ∑ z ∈ TT, (w z * V z ^ (n + 1)).re :=
            Finset.sum_congr rfl fun n _ => Complex.re_sum _ _
        _ = ∑ z ∈ TT, ∑ n ∈ Finset.range N, (w z * V z ^ (n + 1)).re :=
            Finset.sum_comm
        _ = ∑ z ∈ TT, (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum, Complex.re_sum]
    have hedge : (∑ z ∈ TT, (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤
        -(4 * β) * N + CP2 := by
      rw [← Finset.sum_filter_add_sum_filter_not TT (fun z => V z = 1)]
      have hpart1 : (∑ z ∈ TT.filter (fun z => V z = 1),
          (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ -(4 * β) * N := by
        have hterm : ∀ z ∈ TT.filter (fun z => V z = 1),
            (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re =
              -(4 * (u z.1).im ^ (2 : ℕ)) * (N : ℝ) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [hP1w z hz.1 hz.2, hz.2]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [Finset.sum_congr rfl hterm]
        have hzhfil : zh ∈ TT.filter (fun z => V z = 1) :=
          Finset.mem_filter.mpr ⟨hzhTT, hVzh⟩
        rw [← Finset.add_sum_erase _ _ hzhfil]
        have h1 : -(4 * (u zh.1).im ^ (2 : ℕ)) * (N : ℝ) = -(4 * β) * N := by
          simp only [hzh, hβ]
        have h2 : ∑ z ∈ (TT.filter (fun z => V z = 1)).erase zh,
            -(4 * (u z.1).im ^ (2 : ℕ)) * (N : ℝ) ≤ 0 := by
          refine Finset.sum_nonpos fun z _ => ?_
          have h3 : (0 : ℝ) ≤ 4 * (u z.1).im ^ (2 : ℕ) * N := by positivity
          linarith
        rw [h1]
        linarith
      have hpart2 : (∑ z ∈ TT.filter (fun z => ¬ V z = 1),
          (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ CP2 := by
        rw [hCP2]
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Finset.mem_filter] at hz
        have hb := GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le
          (le_of_eq (hVnorm z hz.1)) hz.2 N
        calc (w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)).re
            ≤ ‖w z * ∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := Complex.re_le_norm _
          _ = ‖w z‖ * ‖∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := norm_mul _ _
          _ ≤ ‖w z‖ * (2 / ‖V z - 1‖) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      linarith
    have htailN : ∑ n ∈ Finset.range N,
        (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc).re /
          r ^ (2 * (n + 1)) ≤ CT := by
      rw [hCT]
      calc ∑ n ∈ Finset.range N,
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc).re /
            r ^ (2 * (n + 1))
          ≤ ∑ n ∈ Finset.range N, 4 * P₀ * (ρ / r) ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h1 := htail n
            have h2 := Complex.re_le_norm
              (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) * w ↑zc)
            have hd : (0 : ℝ) < r ^ (2 * (n + 1)) := pow_pos hrpos _
            rw [div_le_iff₀ hd]
            have halg : (ρ * r) ^ n * ((2 * r) ^ (2 : ℕ) * P₀) =
                4 * P₀ * (ρ / r) ^ n * r ^ (2 * (n + 1)) := by
              rw [div_pow, mul_pow]
              field_simp
              ring
            linarith
        _ = 4 * P₀ * ∑ n ∈ Finset.range N, (ρ / r) ^ n := by
            rw [Finset.mul_sum]
        _ ≤ 4 * P₀ * (1 / (1 - ρ / r)) :=
            mul_le_mul_of_nonneg_left (hgeo N) (by positivity)
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
