import GaloisForLFunctions.RHTower.XiResolventTraceCauchySchwarz

/-!
# Supplying the first Turán datum from partial line placement

The index-`0` plain Turán minor — the `p = 1` instance of the single-minor criterion — is
not a consequence of the abstract structure of the resolvent chart: a conjugation-symmetric
configuration with one non-real pair and a small tail makes it negative.  It becomes a
theorem the moment two genuinely arithmetic inputs are supplied: every divisor copy above a
resolvent modulus `δ` lies on the critical line, and the two-scale mass inequality
`8 ε S ≤ 2 r₁ r₂ (r₁ - r₂)^2` holds, where `ε` is the sub-`δ` tail of the norm mass, `S` the
total norm mass, and `r₁ ≠ r₂` the moduli of two above-`δ` copies.

The proof splits the variance pair expansion at the scale `δ`: above `δ` all atoms are
positive reals, so the block is a sum of nonnegative terms dominating the separated witness
pair; the remaining pair interactions are controlled by `4 (S^2 - (S - ε)^2) ≤ 8 ε S`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `p = 1` weighted moments are the plain resolvent moments. -/
theorem xiPolyMoment_one (k : ℕ) (X : ℝ) : xiPolyMoment 1 k X = xiResolventMoment k X := by
  rw [show xiPolyMoment 1 k X = ∑' q : XiZeroCopy, xiResolventPoint X q ^ (k + 1) *
      evalRealPolynomial 1 (xiResolventPoint X q) ^ 2 from rfl,
    show xiResolventMoment k X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (k + 1) from rfl]
  refine tsum_congr fun q => ?_
  rw [evalRealPolynomial_one]
  ring

set_option maxHeartbeats 800000 in
/-- **Two-scale supply of the first Turán datum**: line placement above modulus `δ` plus the
tail-mass inequality force the index-`0` plain Turán minor to be nonnegative. -/
theorem xiResolventTuranMinor_zero_re_nonneg_of_partial_line {X δ : ℝ} (hX : 0 ≤ X)
    (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖) *
        (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      2 * (‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ 2) :
    0 ≤ (xiResolventMoment 0 X * xiResolventMoment 2 X -
      xiResolventMoment 1 X ^ 2).re := by
  classical
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  set S : ℝ := ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ with hS
  have hsummS : Summable (fun q : XiZeroCopy => ‖xiResolventPoint X q‖) :=
    summable_norm_xiResolventPoint hX
  -- the above-`δ` block as a finite set
  have hFfin : {q : XiZeroCopy | δ ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hδ
  set F : Finset XiZeroCopy := hFfin.toFinset with hF
  have hmemF : ∀ q, q ∈ F ↔ δ ≤ ‖xiResolventPoint X q‖ := by
    intro q
    rw [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  -- atoms above `δ` are positive reals
  have hreal : ∀ q, δ ≤ ‖xiResolventPoint X q‖ →
      u q = ((‖xiResolventPoint X q‖ : ℝ) : ℂ) := by
    intro q hq
    exact xiResolventPoint_eq_ofReal_of_im_eq_zero hX (lt_of_lt_of_le hδ hq)
      (xiResolventPoint_im_eq_zero_of_spectral (hline q hq)) rfl
  -- pair summability
  have hprodsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ‖u z.1‖ * ‖u z.2‖) := by
    have h := summable_mul_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using hsummS) (by simpa using hsummS)
    simpa using h
  have hpairsummable : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (u z.1 * u z.2) ^ (0 + 1) * (u z.1 - u z.2) ^ 2) := by
    refine Summable.of_norm_bounded (g := fun z => ‖u z.1‖ * ‖u z.2‖ * 4)
      (hprodsum.mul_right 4) fun z => ?_
    rw [norm_mul, norm_pow, norm_mul, pow_one]
    have hd : ‖u z.1 - u z.2‖ ^ 2 ≤ 4 := by
      have h4 : ‖u z.1 - u z.2‖ ≤ 2 := by
        calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (norm_xiResolventPoint_le_one hX z.1)
              (norm_xiResolventPoint_le_one hX z.2)
          _ = 2 := by norm_num
      nlinarith [norm_nonneg (u z.1 - u z.2)]
    have hd2 : ‖(u z.1 - u z.2) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      exact hd
    exact mul_le_mul_of_nonneg_left hd2 (by positivity)
  -- the pair expansion split at scale `δ`
  have hpair := two_mul_turanMinorAt_eq_tsum_pair hX 0
  have hsplit := hpairsummable.sum_add_tsum_compl (s := F ×ˢ F)
  -- the finite block dominates the separated witness pair
  have hq1F : q₁ ∈ F := (hmemF q₁).mpr h1
  have hq2F : q₂ ∈ F := (hmemF q₂).mpr h2
  have hqne : q₁ ≠ q₂ := fun h => hne (by rw [h])
  set r₁ : ℝ := ‖xiResolventPoint X q₁‖ with hr₁
  set r₂ : ℝ := ‖xiResolventPoint X q₂‖ with hr₂
  have hterm_re : ∀ z : XiZeroCopy × XiZeroCopy, z ∈ F ×ˢ F →
      ((u z.1 * u z.2) ^ (0 + 1) * (u z.1 - u z.2) ^ 2).re =
      (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) *
        (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 := by
    intro z hz
    rw [Finset.mem_product] at hz
    rw [hreal z.1 ((hmemF z.1).mp hz.1), hreal z.2 ((hmemF z.2).mp hz.2),
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hblock : 2 * (r₁ * r₂) * (r₁ - r₂) ^ 2 ≤
      (∑ z ∈ F ×ˢ F, (u z.1 * u z.2) ^ (0 + 1) * (u z.1 - u z.2) ^ 2).re := by
    rw [Complex.re_sum, Finset.sum_congr rfl hterm_re]
    have hsub : ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)) ⊆ F ×ˢ F := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> rw [Finset.mem_product] <;> exact ⟨‹_›, ‹_›⟩
    have hpairne : (q₁, q₂) ≠ (q₂, q₁) := by
      intro h
      exact hqne (congrArg Prod.fst h)
    have hpairsum : ∑ z ∈ ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)),
        (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) *
          (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 =
        2 * (r₁ * r₂) * (r₁ - r₂) ^ 2 := by
      rw [Finset.sum_pair hpairne]
      ring_nf
      nlinarith [sq_nonneg (r₁ - r₂), sq_nonneg (r₂ - r₁)]
    calc 2 * (r₁ * r₂) * (r₁ - r₂) ^ 2
        = ∑ z ∈ ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)),
            (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) *
              (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 := hpairsum.symm
      _ ≤ ∑ z ∈ F ×ˢ F, (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) *
            (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => ?_
          positivity
  -- the tail mass
  set ε : ℝ := ∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
    ‖xiResolventPoint X (q : XiZeroCopy)‖ with hε
  have hεnn : 0 ≤ ε := tsum_nonneg fun q => norm_nonneg _
  have hSnn : 0 ≤ S := tsum_nonneg fun q => norm_nonneg _
  have hcomplset : ((↑F : Set XiZeroCopy)ᶜ) =
      {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, hmemF q, not_le, Set.mem_setOf_eq]
  have hFS : ∑ q ∈ F, ‖xiResolventPoint X q‖ + ε = S := by
    have h := hsummS.sum_add_tsum_compl (s := F)
    rw [hε, ← hcomplset]
    exact h
  have hFSnn : 0 ≤ ∑ q ∈ F, ‖xiResolventPoint X q‖ :=
    Finset.sum_nonneg fun q _ => norm_nonneg _
  -- the complement pair mass is at most `2 ε S`
  have htotprod : (∑' z : XiZeroCopy × XiZeroCopy, ‖u z.1‖ * ‖u z.2‖) = S * S := by
    have h := tsum_mul_tsum_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using hsummS) (by simpa using hsummS)
    rw [hS]
    exact h.symm
  have hFprod : (∑ z ∈ F ×ˢ F, ‖u z.1‖ * ‖u z.2‖) =
      (∑ q ∈ F, ‖xiResolventPoint X q‖) * (∑ q ∈ F, ‖xiResolventPoint X q‖) := by
    rw [Finset.sum_product]
    rw [Finset.sum_mul_sum]
  have hsplitprod := hprodsum.sum_add_tsum_compl (s := F ×ˢ F)
  have hcomplprod : (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
      ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) ≤
      2 * ε * S := by
    have hval : (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
        ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ * ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) =
        S * S - (∑ q ∈ F, ‖xiResolventPoint X q‖) *
          (∑ q ∈ F, ‖xiResolventPoint X q‖) := by
      have h := hsplitprod
      rw [htotprod, hFprod] at h
      linarith
    rw [hval]
    nlinarith [hFS, hεnn, hSnn, hFSnn]
  -- the complement pair term is controlled by the complement pair mass
  have hcompl : ‖∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
      (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
        (u (↑z : XiZeroCopy × XiZeroCopy).1 - u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖ ≤
      4 * (2 * ε * S) := by
    have hsubpair := (hpairsummable.norm.subtype
      ((↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ))
    have hsubprod := hprodsum.subtype ((↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ)
    calc ‖∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 *
            u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖
        ≤ ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 *
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
              (u (↑z : XiZeroCopy × XiZeroCopy).1 -
                u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            4 * (‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
              ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) := by
          refine Summable.tsum_le_tsum (fun z => ?_) hsubpair (hsubprod.mul_left 4)
          rw [norm_mul, norm_pow, norm_mul, pow_one]
          have hd : ‖u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2‖ ^ 2 ≤ 4 := by
            have h4 : ‖u (↑z : XiZeroCopy × XiZeroCopy).1 -
                u (↑z : XiZeroCopy × XiZeroCopy).2‖ ≤ 2 := by
              calc ‖u (↑z : XiZeroCopy × XiZeroCopy).1 -
                  u (↑z : XiZeroCopy × XiZeroCopy).2‖
                  ≤ ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ +
                    ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ := norm_sub_le _ _
                _ ≤ 1 + 1 := add_le_add (norm_xiResolventPoint_le_one hX _)
                    (norm_xiResolventPoint_le_one hX _)
                _ = 2 := by norm_num
            nlinarith [norm_nonneg (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2)]
          have hd2 : ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖ ≤ 4 := by
            rw [norm_pow]
            exact hd
          calc ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
              ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ *
              ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 -
                u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖
              ≤ ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
                ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ * 4 := by
                exact mul_le_mul_of_nonneg_left hd2 (by positivity)
            _ = 4 * (‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
                ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) := by ring
      _ = 4 * ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
              ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ := tsum_mul_left
      _ ≤ 4 * (2 * ε * S) := by
          refine mul_le_mul_of_nonneg_left hcomplprod (by norm_num)
  -- assemble
  have hmain : 0 ≤ (2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
      xiResolventMoment 1 X ^ 2)).re := by
    rw [hpair]
    have hEq : (∑' z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (0 + 1) * (u z.1 - u z.2) ^ 2) =
        (∑ z ∈ F ×ˢ F, (u z.1 * u z.2) ^ (0 + 1) * (u z.1 - u z.2) ^ 2) +
        ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 *
            u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2 := hsplit.symm
    rw [hEq, Complex.add_re]
    have htailre : -(4 * (2 * ε * S)) ≤
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 *
            u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2).re := by
      have ha := Complex.abs_re_le_norm
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 *
            u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2)
      have hb := neg_abs_le
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 *
            u (↑z : XiZeroCopy × XiZeroCopy).2) ^ (0 + 1) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2).re
      linarith
    linarith [hmass]
  have h2 : (2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
      xiResolventMoment 1 X ^ 2)).re =
      2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
        xiResolventMoment 1 X ^ 2).re := by
    simp [Complex.mul_re]
  rw [h2] at hmain
  linarith

/-- The two-scale supply theorem, phrased for the `p = 1` instance of the single-minor
criterion. -/
theorem polyTuranMinor_one_zero_re_nonneg_of_partial_line {X δ : ℝ} (hX : 0 ≤ X)
    (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖) *
        (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      2 * (‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ 2) :
    0 ≤ (xiPolyMoment 1 0 X * xiPolyMoment 1 2 X - xiPolyMoment 1 1 X ^ 2).re := by
  rw [xiPolyMoment_one, xiPolyMoment_one, xiPolyMoment_one]
  exact xiResolventTuranMinor_zero_re_nonneg_of_partial_line hX hδ hline h1 h2 hne hmass

end

end RHTower
