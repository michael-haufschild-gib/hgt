import GaloisForLFunctions.RHTower.XiResolventDeflatedTuranCleansing

/-!
# The universal level-cleansing machine

The edge-cleansing and second-level-cleansing arguments are two instances of one machine, proved
here once and for all: for any conjugation-symmetric weight `Wf` on the divisor that vanishes
above a level `ℓ` and is nonzero on it, nonnegativity of the Turán minors of the `Wf`-weighted
moments `M k = sum_q u_q^(k+1) Wf q` forces **every** copy at level `ℓ` onto the critical line.

The weighted pair expansion places the maximal pair points of the weighted system at `ℓ^2`;
those equal to `ℓ^2` are the conjugate pairs, whose weights `Wf q * Wf q' = normSq (Wf q)` are
nonnegative reals multiplying the exact negative core `-4 (Im u)^2`; an off-critical copy at the
level contributes `-4 (Im u)^2 normSq (Wf q) N` after `N` Cesàro steps, the remaining unit pair
points contribute boundedly, and the sub-level tail is geometric.  Weight symmetry is demanded
in value form — `u q' = conj (u q)` forces `Wf q' = conj (Wf q)` — which holds for every weight
of the shape `g (u q)` with `g` real on the reals, in particular for squared real polynomials.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `Wf`-weighted resolvent moments. -/
def xiWeightedResolventMoment (Wf : XiZeroCopy → ℂ) (k : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiResolventPoint X q ^ (k + 1) * Wf q

set_option maxHeartbeats 1600000 in
/-- **The universal level-cleansing machine.** -/
theorem forall_level_criticalLine_of_weighted_turanMinors {X : ℝ} (hX : 0 ≤ X)
    {Wf : XiZeroCopy → ℂ} {BW : ℝ} (hWbound : ∀ q, ‖Wf q‖ ≤ BW)
    (hval : ∀ q q' : XiZeroCopy,
      xiResolventPoint X q' = (starRingEnd ℂ) (xiResolventPoint X q) →
      Wf q' = (starRingEnd ℂ) (Wf q))
    {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ → Wf q = 0)
    (hnz : ∀ q, ‖xiResolventPoint X q‖ = ℓ → Wf q ≠ 0)
    (hminorW : ∀ n : ℕ, 0 ≤ (xiWeightedResolventMoment Wf n X *
      xiWeightedResolventMoment Wf (n + 2) X -
      xiWeightedResolventMoment Wf (n + 1) X ^ 2).re) :
    ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → (xiSpectralPoint q).im = 0 := by
  classical
  intro qh hqhℓ
  by_contra hqhoff
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
      (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2) := by
    intro n
    have hsum := summable_mul_of_summable_norm (hatomnorm n) (hatomnorm n)
    have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2 =
        (u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2) *
          (u z.1 - u z.2) ^ 2 := by
      intro z
      ring
    rw [show (fun z : XiZeroCopy × XiZeroCopy =>
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2) = fun z =>
        (u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2) *
          (u z.1 - u z.2) ^ 2 from funext hpt]
    refine Summable.of_norm_bounded (g := fun z =>
      ‖(u z.1 ^ (n + 1) * Wf z.1) * (u z.2 ^ (n + 1) * Wf z.2)‖ * (2 * 1) ^ 2)
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
      xiWeightedResolventMoment Wf (n + 1) X ^ 2) =
      ∑' z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2 := by
    intro n
    have hA := tsum_mul_tsum_of_summable_norm (hatomnorm n) (hatomnorm (n + 2))
    have hB := tsum_mul_tsum_of_summable_norm (hatomnorm (n + 1)) (hatomnorm (n + 1))
    have hC := tsum_mul_tsum_of_summable_norm (hatomnorm (n + 2)) (hatomnorm n)
    have hsumA := summable_mul_of_summable_norm (hatomnorm n) (hatomnorm (n + 2))
    have hsumB := summable_mul_of_summable_norm (hatomnorm (n + 1)) (hatomnorm (n + 1))
    have hsumC := summable_mul_of_summable_norm (hatomnorm (n + 2)) (hatomnorm n)
    have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2 =
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
  -- sub-level bound
  obtain ⟨ρ₂, hρ₂0, hρ₂lt, hρ₂bound⟩ :
      ∃ ρ₂, 0 ≤ ρ₂ ∧ ρ₂ < ℓ ∧ ∀ q, ‖xiResolventPoint X q‖ < ℓ →
        ‖xiResolventPoint X q‖ ≤ ρ₂ := by
    have hhalf : (0 : ℝ) < ℓ / 2 := by linarith
    have hDfin : {q : XiZeroCopy | ℓ / 2 ≤ ‖xiResolventPoint X q‖}.Finite :=
      finite_setOf_le_norm_xiResolventPoint hX hhalf
    set D : Finset XiZeroCopy :=
      hDfin.toFinset.filter (fun q => ‖xiResolventPoint X q‖ < ℓ) with hD
    rcases D.eq_empty_or_nonempty with hDe | hDne
    · refine ⟨ℓ / 2, by linarith, by linarith, fun q hq1 => ?_⟩
      by_contra hgt
      rw [not_le] at hgt
      have hqD : q ∈ D := by
        rw [hD, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨by rw [Set.mem_setOf_eq]; linarith, hq1⟩
      rw [hDe] at hqD
      exact absurd hqD (Finset.notMem_empty q)
    · obtain ⟨qd, hqdD, hqdmax⟩ := D.exists_max_image
        (fun q => ‖xiResolventPoint X q‖) hDne
      have hqdlt : ‖xiResolventPoint X qd‖ < ℓ := by
        rw [hD, Finset.mem_filter] at hqdD
        exact hqdD.2
      refine ⟨max ‖xiResolventPoint X qd‖ (ℓ / 2),
        le_trans (by linarith) (le_max_right _ _), ?_, ?_⟩
      · rw [max_lt_iff]
        exact ⟨hqdlt, by linarith⟩
      · intro q hq1
        by_cases hq3 : ℓ / 2 ≤ ‖xiResolventPoint X q‖
        · have hqD : q ∈ D := by
            rw [hD, Finset.mem_filter, Set.Finite.mem_toFinset]
            exact ⟨by rw [Set.mem_setOf_eq]; linarith, hq1⟩
          exact le_trans (hqdmax q hqD) (le_max_left _ _)
        · exact le_trans (not_le.mp hq3).le (le_max_right _ _)
  -- pair machinery
  set V : XiZeroCopy × XiZeroCopy → ℂ := fun z => u z.1 * u z.2 / (((ℓ : ℝ)) : ℂ) ^ 2
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
      ‖(u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2‖ ≤
      (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) * (‖u z.1‖ * ‖u z.2‖)) := by
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
    have hdiffb : ‖(u z.1 - u z.2) ^ 2‖ ≤ 4 := by
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
    · have hWb : ‖Wf z.1 * Wf z.2‖ ≤ BW ^ 2 := by
        rw [norm_mul]
        calc ‖Wf z.1‖ * ‖Wf z.2‖ ≤ BW * BW :=
              mul_le_mul (hWbound z.1) (hWbound z.2) (norm_nonneg _) hBW0
          _ = BW ^ 2 := by ring
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
      calc ‖(u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) * (u z.1 - u z.2) ^ 2‖
          = ‖(u z.1 * u z.2) ^ (n + 1)‖ * ‖Wf z.1 * Wf z.2‖ *
              ‖(u z.1 - u z.2) ^ 2‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ((ρ₂ * ℓ) ^ n * (‖u z.1‖ * ‖u z.2‖)) * BW ^ 2 * 4 := by
            refine mul_le_mul (mul_le_mul hpowb hWb (norm_nonneg _) (by positivity))
              hdiffb (norm_nonneg _) (by positivity)
        _ = (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) * (‖u z.1‖ * ‖u z.2‖)) := by ring
  -- unit pair points at the level
  have hVnorm : ∀ z ∈ TT, ‖V z‖ = 1 := by
    intro z hz
    rw [hTT, Finset.mem_product] at hz
    simp only [hV]
    rw [norm_div, norm_mul, norm_pow, (hmemSF z.1).mp hz.1, (hmemSF z.2).mp hz.2,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓpos, pow_two]
    exact div_self (by positivity)
  -- pair points at `1` are conjugate pairs with nonpositive real weight
  have hP1w : ∀ z ∈ TT, V z = 1 → Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2 =
      ((-(4 * ((u z.1).im ^ 2 * Complex.normSq (Wf z.1))) : ℝ) : ℂ) := by
    intro z hz hVz
    rw [hTT, Finset.mem_product] at hz
    have hz1ne : u z.1 ≠ 0 := xiResolventPoint_ne_zero hX z.1
    have h1 : u z.1 * u z.2 = (((ℓ : ℝ)) : ℂ) ^ 2 := by
      have h0 := hVz
      simp only [hV] at h0
      rw [div_eq_iff (pow_ne_zero 2 hℓC), one_mul] at h0
      exact h0
    have h2 : u z.1 * (starRingEnd ℂ) (u z.1) = (((ℓ : ℝ)) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, ← Complex.ofReal_pow]
      norm_cast
      rw [← Complex.sq_norm, (hmemSF z.1).mp hz.1]
    have hconj : u z.2 = (starRingEnd ℂ) (u z.1) :=
      mul_left_cancel₀ hz1ne (h1.trans h2.symm)
    have hWconj : Wf z.2 = (starRingEnd ℂ) (Wf z.1) := hval z.1 z.2 hconj
    have hprod : Wf z.1 * Wf z.2 = ((Complex.normSq (Wf z.1) : ℝ) : ℂ) := by
      rw [hWconj, Complex.mul_conj]
    have hdiff : (u z.1 - u z.2) ^ 2 = ((-(4 * (u z.1).im ^ 2) : ℝ) : ℂ) := by
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
    rw [show Complex.normSq (u qh) = ℓ ^ 2 by
      rw [← Complex.sq_norm]
      rw [show ‖u qh‖ = ℓ from hqhℓ]]
    exact div_self (Complex.ofReal_ne_zero.mpr (by positivity))
  -- the strictly positive defect at the witness
  set β : ℝ := (u qh).im ^ 2 * Complex.normSq (Wf qh) with hβdef
  have hβ : 0 < β := by
    rw [hβdef]
    have him := xiResolventPoint_im_ne_zero_of_spectral hX hqhoff
    have hnsq : 0 < Complex.normSq (Wf qh) :=
      Complex.normSq_pos.mpr (hnz qh hqhℓ)
    positivity
  -- geometric bound and constants
  have hκ2 : ρ₂ / ℓ < 1 := (div_lt_one hℓpos).mpr hρ₂lt
  have hκ0' : (0 : ℝ) ≤ ρ₂ / ℓ := div_nonneg hρ₂0 hℓpos.le
  have h1κ : (0 : ℝ) < 1 - ρ₂ / ℓ := by linarith
  have hgeo : ∀ N : ℕ, ∑ n ∈ Finset.range N, (ρ₂ / ℓ) ^ n ≤ 1 / (1 - ρ₂ / ℓ) := by
    intro N
    rw [geom_sum_eq (ne_of_lt hκ2)]
    rw [show (ρ₂ / ℓ) ^ N - 1 = -(1 - (ρ₂ / ℓ) ^ N) by ring,
      show ρ₂ / ℓ - 1 = -(1 - ρ₂ / ℓ) by ring, neg_div_neg_eq]
    rw [div_le_div_iff₀ h1κ h1κ]
    nlinarith [pow_nonneg hκ0' N]
  set CT : ℝ := 4 * BW ^ 2 * P₀ / ℓ ^ 2 * (1 / (1 - ρ₂ / ℓ)) with hCT
  set CP2 : ℝ := ∑ z ∈ TT.filter (fun z => ¬ V z = 1),
    ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2‖ * (2 / ‖V z - 1‖) with hCP2
  -- the tail bound at level n
  have htail : ∀ n : ℕ,
      ‖∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
        (u (↑zc : XiZeroCopy × XiZeroCopy).1 * u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
          (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 * Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 - u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖ ≤
        (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) * P₀) := by
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
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖
        ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) *
              (‖u (↑zc : XiZeroCopy × XiZeroCopy).1‖ *
                ‖u (↑zc : XiZeroCopy × XiZeroCopy).2‖)) := by
          refine Summable.tsum_le_tsum (fun zc => ?_) hsubpair
            (((hsubprod.mul_left ((4 * BW ^ 2))).mul_left ((ρ₂ * ℓ) ^ n)))
          have hznot : (↑zc : XiZeroCopy × XiZeroCopy) ∉ TT := by
            have h := zc.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          exact htailterm n _ hznot
      _ = (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) * P₀) := by
          rw [tsum_mul_left, tsum_mul_left, hP₀]
  -- the master estimate at every truncation
  have hmaster : ∀ N : ℕ, 0 ≤ -(4 * β) * N + CP2 + CT := by
    intro N
    have hlhs : 0 ≤ ∑ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf n X * xiWeightedResolventMoment Wf (n + 2) X -
          xiWeightedResolventMoment Wf (n + 1) X ^ 2)).re / ℓ ^ (2 * (n + 1)) := by
      refine Finset.sum_nonneg fun n _ => ?_
      have h1 := hminorW n
      have h2 : (2 * (xiWeightedResolventMoment Wf n X *
          xiWeightedResolventMoment Wf (n + 2) X -
          xiWeightedResolventMoment Wf (n + 1) X ^ 2)).re =
          2 * (xiWeightedResolventMoment Wf n X *
            xiWeightedResolventMoment Wf (n + 2) X -
            xiWeightedResolventMoment Wf (n + 1) X ^ 2).re := by
        simp [Complex.mul_re]
      rw [h2]
      have h3 : (0 : ℝ) < ℓ ^ (2 * (n + 1)) := pow_pos hℓpos _
      positivity
    have hn : ∀ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf n X * xiWeightedResolventMoment Wf (n + 2) X -
          xiWeightedResolventMoment Wf (n + 1) X ^ 2)).re / ℓ ^ (2 * (n + 1)) =
        (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) * V z ^ (n + 1)).re +
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
            ℓ ^ (2 * (n + 1)) := by
      intro n _
      have hexp := hpair n
      have hsplit := (hpairsummable n).sum_add_tsum_compl (s := TT)
      have hEq : (2 : ℂ) * (xiWeightedResolventMoment Wf n X *
          xiWeightedResolventMoment Wf (n + 2) X -
          xiWeightedResolventMoment Wf (n + 1) X ^ 2) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) *
            (u z.1 - u z.2) ^ 2) +
            ∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2 := by
        rw [hexp]
        exact hsplit.symm
      have hre := congrArg Complex.re hEq
      rw [Complex.add_re] at hre
      rw [hre, add_div]
      congr 1
      have hCfin : (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) * V z ^ (n + 1)) =
          (∑ z ∈ TT, (u z.1 * u z.2) ^ (n + 1) * (Wf z.1 * Wf z.2) *
            (u z.1 - u z.2) ^ 2) / ((ℓ ^ (2 * (n + 1)) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        have hden : ((((ℓ : ℝ)) : ℂ) ^ 2) ^ (n + 1) = ((ℓ ^ (2 * (n + 1)) : ℝ) : ℂ) := by
          push_cast
          ring
        simp only [hV]
        rw [div_pow, hden]
        ring
      rw [hCfin, re_div_ofReal]
    have hdecomp : ∑ n ∈ Finset.range N,
        (2 * (xiWeightedResolventMoment Wf n X * xiWeightedResolventMoment Wf (n + 2) X -
          xiWeightedResolventMoment Wf (n + 1) X ^ 2)).re / ℓ ^ (2 * (n + 1)) =
        (∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
            ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) +
          ∑ n ∈ Finset.range N,
            (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
              ℓ ^ (2 * (n + 1)) := by
      rw [Finset.sum_congr rfl hn, Finset.sum_add_distrib]
      congr 1
      calc ∑ n ∈ Finset.range N,
          (∑ z ∈ TT, (Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) * V z ^ (n + 1)).re
          = ∑ n ∈ Finset.range N, ∑ z ∈ TT,
              ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) * V z ^ (n + 1)).re :=
            Finset.sum_congr rfl fun n _ => Complex.re_sum _ _
        _ = ∑ z ∈ TT, ∑ n ∈ Finset.range N,
              ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) * V z ^ (n + 1)).re :=
            Finset.sum_comm
        _ = ∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
              ∑ n ∈ Finset.range N, V z ^ (n + 1)).re := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum, Complex.re_sum]
    have hedge : (∑ z ∈ TT, ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
        ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ -(4 * β) * N + CP2 := by
      rw [← Finset.sum_filter_add_sum_filter_not TT (fun z => V z = 1)]
      have hpart1 : (∑ z ∈ TT.filter (fun z => V z = 1),
          ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
            ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ -(4 * β) * N := by
        have hterm : ∀ z ∈ TT.filter (fun z => V z = 1),
            ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
              ∑ n ∈ Finset.range N, V z ^ (n + 1)).re =
              -(4 * ((u z.1).im ^ 2 * Complex.normSq (Wf z.1))) * (N : ℝ) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [hP1w z hz.1 hz.2, hz.2]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [Finset.sum_congr rfl hterm]
        have hzhfil : zh ∈ TT.filter (fun z => V z = 1) :=
          Finset.mem_filter.mpr ⟨hzhTT, hVzh⟩
        rw [← Finset.add_sum_erase _ _ hzhfil]
        have h1 : -(4 * ((u zh.1).im ^ 2 * Complex.normSq (Wf zh.1))) * (N : ℝ) =
            -(4 * β) * N := by
          simp only [hzh, hβdef]
        have h2 : ∑ z ∈ (TT.filter (fun z => V z = 1)).erase zh,
            -(4 * ((u z.1).im ^ 2 * Complex.normSq (Wf z.1))) * (N : ℝ) ≤ 0 := by
          refine Finset.sum_nonpos fun z _ => ?_
          have h3 : (0 : ℝ) ≤ 4 * ((u z.1).im ^ 2 * Complex.normSq (Wf z.1)) * N := by
            have := Complex.normSq_nonneg (Wf z.1)
            positivity
          linarith
        rw [h1]
        linarith
      have hpart2 : (∑ z ∈ TT.filter (fun z => ¬ V z = 1),
          ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
            ∑ n ∈ Finset.range N, V z ^ (n + 1)).re) ≤ CP2 := by
        rw [hCP2]
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Finset.mem_filter] at hz
        have hb := GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le
          (le_of_eq (hVnorm z hz.1)) hz.2 N
        calc ((Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
            ∑ n ∈ Finset.range N, V z ^ (n + 1)).re
            ≤ ‖(Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2) *
                ∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := Complex.re_le_norm _
          _ = ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2‖ *
                ‖∑ n ∈ Finset.range N, V z ^ (n + 1)‖ := norm_mul _ _
          _ ≤ ‖Wf z.1 * Wf z.2 * (u z.1 - u z.2) ^ 2‖ * (2 / ‖V z - 1‖) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      linarith
    have htailN : ∑ n ∈ Finset.range N,
        (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
            u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
            (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
              Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
          ℓ ^ (2 * (n + 1)) ≤ CT := by
      rw [hCT]
      calc ∑ n ∈ Finset.range N,
          (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
              u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
              (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
              (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2).re /
            ℓ ^ (2 * (n + 1))
          ≤ ∑ n ∈ Finset.range N, 4 * BW ^ 2 * P₀ / ℓ ^ 2 * (ρ₂ / ℓ) ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            have h1 := htail n
            have h2 := Complex.re_le_norm
              (∑' zc : ↑(↑TT : Set (XiZeroCopy × XiZeroCopy))ᶜ,
                (u (↑zc : XiZeroCopy × XiZeroCopy).1 *
                  u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ (n + 1) *
                  (Wf (↑zc : XiZeroCopy × XiZeroCopy).1 *
                    Wf (↑zc : XiZeroCopy × XiZeroCopy).2) *
                  (u (↑zc : XiZeroCopy × XiZeroCopy).1 -
                    u (↑zc : XiZeroCopy × XiZeroCopy).2) ^ 2)
            have hd : (0 : ℝ) < ℓ ^ (2 * (n + 1)) := pow_pos hℓpos _
            rw [div_le_iff₀ hd]
            have halg : (ρ₂ * ℓ) ^ n * ((4 * BW ^ 2) * P₀) =
                4 * BW ^ 2 * P₀ / ℓ ^ 2 * (ρ₂ / ℓ) ^ n * ℓ ^ (2 * (n + 1)) := by
              rw [div_pow, mul_pow]
              field_simp
              ring
            linarith
        _ = 4 * BW ^ 2 * P₀ / ℓ ^ 2 * ∑ n ∈ Finset.range N, (ρ₂ / ℓ) ^ n := by
            rw [Finset.mul_sum]
        _ ≤ 4 * BW ^ 2 * P₀ / ℓ ^ 2 * (1 / (1 - ρ₂ / ℓ)) := by
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
