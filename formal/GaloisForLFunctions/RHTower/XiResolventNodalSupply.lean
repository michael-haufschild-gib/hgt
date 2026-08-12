import GaloisForLFunctions.RHTower.XiResolventRationalNodeCriterion

/-!
# The universal supply theorem: pricing every entry of the countable list

Every single-minor datum of the rational-nodal criterion is supplied by the same two arithmetic
inputs as the plain first datum: line placement above one resolvent scale `δ`, and one explicit
two-scale mass inequality.  For a real polynomial `p` bounded by `B` on the closed unit disk,
the `(0,2,1)` datum of `X^m·p` follows from

  `8·B⁴·ε·S ≤ 2·(r₁r₂)^{2m+1}·(eval_{r₁} p)²·(eval_{r₂} p)²·(r₁ − r₂)²`,

where `ε` is the sub-`δ` norm mass, `S` the total norm mass, and `r₁ ≠ r₂` the moduli of two
above-`δ` copies.  The proof splits the polynomially weighted pair expansion at the scale `δ`:
above `δ` all atoms are positive reals and the weights are squares of real evaluations, so the
block dominates the separated witness pair; the complement is controlled by `4B⁴` times the
complement pair mass.

For the nodal instances `p = ∏(X − c_i)` with nodes in `[0,1]` the disk bound is `B = 2^j`, so
the cost of the list entry `(j, m, c)` degrades exponentially in `m` through `(r₁r₂)^{2m+1}`
and in `j` through `2^{4j}` and the node-witness distances `∏(r_k − c_i)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Real evaluation of a tuple-nodal polynomial is the product of the node offsets. -/
theorem eval_finNodalPolynomial {j : ℕ} (c : Fin j → ℝ) (r : ℝ) :
    Polynomial.eval r (finNodalPolynomial c) = ∏ i, (r - c i) := by
  rw [finNodalPolynomial, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

set_option maxHeartbeats 800000 in
/-- **The universal two-scale supply theorem**: line placement above modulus `δ` plus one
explicit mass inequality force the `(0,2,1)` single-minor datum of `X^m·p` to be nonnegative,
for any real polynomial `p` bounded by `B` on the closed unit disk. -/
theorem polyTuranMinor_supply_of_partial_line {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    (p : Polynomial ℝ) (m : ℕ) {B : ℝ}
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖evalRealPolynomial p z‖ ≤ B)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * B ^ 4 * (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖) *
        (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        (Polynomial.eval ‖xiResolventPoint X q₁‖ p ^ 2 *
          Polynomial.eval ‖xiResolventPoint X q₂‖ p ^ 2) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ 2)) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * p) 0 X *
      xiPolyMoment (Polynomial.X ^ m * p) 2 X -
      xiPolyMoment (Polynomial.X ^ m * p) 1 X ^ 2).re := by
  classical
  have e0 : xiPolyMoment (Polynomial.X ^ m * p) 0 X = xiPolyMoment p (2 * m) X := by
    have h := xiPolyMoment_X_pow_mul m p 0 X
    simpa only [Nat.zero_add] using h
  have e2 : xiPolyMoment (Polynomial.X ^ m * p) 2 X = xiPolyMoment p (2 * m + 2) X := by
    have h := xiPolyMoment_X_pow_mul m p 2 X
    rw [show 2 + 2 * m = 2 * m + 2 from by omega] at h
    exact h
  have e1 : xiPolyMoment (Polynomial.X ^ m * p) 1 X = xiPolyMoment p (2 * m + 1) X := by
    have h := xiPolyMoment_X_pow_mul m p 1 X
    rw [show 1 + 2 * m = 2 * m + 1 from by omega] at h
    exact h
  rw [e0, e2, e1]
  set u : XiZeroCopy → ℂ := fun q => xiResolventPoint X q with hu
  set S : ℝ := ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ with hS
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp))
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
  -- pair summability with polynomial weights
  have hprodsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ‖u z.1‖ * ‖u z.2‖) := by
    have h := summable_mul_of_summable_norm (f := fun q => ‖xiResolventPoint X q‖)
      (g := fun q => ‖xiResolventPoint X q‖)
      (by simpa using hsummS) (by simpa using hsummS)
    simpa using h
  have hatombound : ∀ z : XiZeroCopy × XiZeroCopy,
      ‖(u z.1 * u z.2) ^ (2 * m + 1) *
        (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
        (u z.1 - u z.2) ^ 2‖ ≤ ‖u z.1‖ * ‖u z.2‖ * (4 * B ^ 4) := by
    intro z
    rw [norm_mul, norm_mul]
    have hu1 : ‖u z.1‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.1
    have hu2 : ‖u z.2‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.2
    have hA : ‖(u z.1 * u z.2) ^ (2 * m + 1)‖ ≤ ‖u z.1‖ * ‖u z.2‖ := by
      rw [norm_pow, norm_mul, mul_pow]
      have hp1 : ‖u z.1‖ ^ (2 * m + 1) ≤ ‖u z.1‖ := by
        calc ‖u z.1‖ ^ (2 * m + 1) = ‖u z.1‖ * ‖u z.1‖ ^ (2 * m) := pow_succ' _ _
          _ ≤ ‖u z.1‖ * 1 := mul_le_mul_of_nonneg_left
              (pow_le_one₀ (norm_nonneg _) hu1) (norm_nonneg _)
          _ = ‖u z.1‖ := mul_one _
      have hp2 : ‖u z.2‖ ^ (2 * m + 1) ≤ ‖u z.2‖ := by
        calc ‖u z.2‖ ^ (2 * m + 1) = ‖u z.2‖ * ‖u z.2‖ ^ (2 * m) := pow_succ' _ _
          _ ≤ ‖u z.2‖ * 1 := mul_le_mul_of_nonneg_left
              (pow_le_one₀ (norm_nonneg _) hu2) (norm_nonneg _)
          _ = ‖u z.2‖ := mul_one _
      exact mul_le_mul hp1 hp2 (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    have hW : ‖evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2‖ ≤
        B ^ 4 := by
      rw [norm_mul, norm_pow, norm_pow]
      have b1 : ‖evalRealPolynomial p (u z.1)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hB _ hu1) 2
      have b2 : ‖evalRealPolynomial p (u z.2)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hB _ hu2) 2
      calc ‖evalRealPolynomial p (u z.1)‖ ^ 2 * ‖evalRealPolynomial p (u z.2)‖ ^ 2
          ≤ B ^ 2 * B ^ 2 := mul_le_mul b1 b2 (by positivity) (by positivity)
        _ = B ^ 4 := by ring
    have hD : ‖(u z.1 - u z.2) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      have h4 : ‖u z.1 - u z.2‖ ≤ 2 := by
        calc ‖u z.1 - u z.2‖ ≤ ‖u z.1‖ + ‖u z.2‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add hu1 hu2
          _ = 2 := by norm_num
      nlinarith [norm_nonneg (u z.1 - u z.2)]
    calc ‖(u z.1 * u z.2) ^ (2 * m + 1)‖ *
        ‖evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2‖ *
        ‖(u z.1 - u z.2) ^ 2‖
        ≤ (‖u z.1‖ * ‖u z.2‖) * B ^ 4 * 4 := by
          refine mul_le_mul (mul_le_mul hA hW (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hD (norm_nonneg _) ?_
          positivity
      _ = ‖u z.1‖ * ‖u z.2‖ * (4 * B ^ 4) := by ring
  have hpairsummable : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (u z.1 * u z.2) ^ (2 * m + 1) *
        (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
        (u z.1 - u z.2) ^ 2) :=
    Summable.of_norm_bounded (hprodsum.mul_right (4 * B ^ 4)) hatombound
  -- the weighted pair expansion split at scale `δ`
  have hpair := two_mul_polyTuranMinorAt_eq_tsum_pair hX p (2 * m)
  have hsplit := hpairsummable.sum_add_tsum_compl (s := F ×ˢ F)
  -- the finite block dominates the separated witness pair
  have hq1F : q₁ ∈ F := (hmemF q₁).mpr h1
  have hq2F : q₂ ∈ F := (hmemF q₂).mpr h2
  have hqne : q₁ ≠ q₂ := fun h => hne (by rw [h])
  set r₁ : ℝ := ‖xiResolventPoint X q₁‖ with hr₁
  set r₂ : ℝ := ‖xiResolventPoint X q₂‖ with hr₂
  have hterm_re : ∀ z : XiZeroCopy × XiZeroCopy, z ∈ F ×ˢ F →
      ((u z.1 * u z.2) ^ (2 * m + 1) *
        (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
        (u z.1 - u z.2) ^ 2).re =
      (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) ^ (2 * m + 1) *
        (Polynomial.eval ‖xiResolventPoint X z.1‖ p ^ 2 *
          Polynomial.eval ‖xiResolventPoint X z.2‖ p ^ 2) *
        (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 := by
    intro z hz
    rw [Finset.mem_product] at hz
    rw [hreal z.1 ((hmemF z.1).mp hz.1), hreal z.2 ((hmemF z.2).mp hz.2),
      evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
    norm_cast
  have hblock : 2 * ((r₁ * r₂) ^ (2 * m + 1) *
      (Polynomial.eval r₁ p ^ 2 * Polynomial.eval r₂ p ^ 2) * (r₁ - r₂) ^ 2) ≤
      (∑ z ∈ F ×ˢ F, (u z.1 * u z.2) ^ (2 * m + 1) *
        (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
        (u z.1 - u z.2) ^ 2).re := by
    rw [Complex.re_sum, Finset.sum_congr rfl hterm_re]
    have hsub : ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)) ⊆ F ×ˢ F := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> rw [Finset.mem_product] <;> exact ⟨‹_›, ‹_›⟩
    have hpairne : (q₁, q₂) ≠ (q₂, q₁) := by
      intro h
      exact hqne (congrArg Prod.fst h)
    have hpairsum : ∑ z ∈ ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)),
        (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) ^ (2 * m + 1) *
          (Polynomial.eval ‖xiResolventPoint X z.1‖ p ^ 2 *
            Polynomial.eval ‖xiResolventPoint X z.2‖ p ^ 2) *
          (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 =
        2 * ((r₁ * r₂) ^ (2 * m + 1) *
          (Polynomial.eval r₁ p ^ 2 * Polynomial.eval r₂ p ^ 2) * (r₁ - r₂) ^ 2) := by
      rw [Finset.sum_pair hpairne]
      ring_nf
      nlinarith [sq_nonneg (r₁ - r₂), sq_nonneg (r₂ - r₁)]
    calc 2 * ((r₁ * r₂) ^ (2 * m + 1) *
        (Polynomial.eval r₁ p ^ 2 * Polynomial.eval r₂ p ^ 2) * (r₁ - r₂) ^ 2)
        = ∑ z ∈ ({(q₁, q₂), (q₂, q₁)} : Finset (XiZeroCopy × XiZeroCopy)),
            (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) ^ (2 * m + 1) *
              (Polynomial.eval ‖xiResolventPoint X z.1‖ p ^ 2 *
                Polynomial.eval ‖xiResolventPoint X z.2‖ p ^ 2) *
              (‖xiResolventPoint X z.1‖ - ‖xiResolventPoint X z.2‖) ^ 2 := hpairsum.symm
      _ ≤ ∑ z ∈ F ×ˢ F,
            (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) ^ (2 * m + 1) *
              (Polynomial.eval ‖xiResolventPoint X z.1‖ p ^ 2 *
                Polynomial.eval ‖xiResolventPoint X z.2‖ p ^ 2) *
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
      (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
          (2 * m + 1) *
        (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
          evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
        (u (↑z : XiZeroCopy × XiZeroCopy).1 - u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖ ≤
      4 * B ^ 4 * (2 * ε * S) := by
    have hsubpair := (hpairsummable.norm.subtype
      ((↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ))
    have hsubprod := hprodsum.subtype ((↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ)
    calc ‖∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
              (2 * m + 1) *
            (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
              evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖
        ≤ ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖(u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
                (2 * m + 1) *
              (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
                evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
              (u (↑z : XiZeroCopy × XiZeroCopy).1 -
                u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsubpair
      _ ≤ ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
              ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖ * (4 * B ^ 4) := by
          refine Summable.tsum_le_tsum (fun z => hatombound _) hsubpair
            (hsubprod.mul_right (4 * B ^ 4))
      _ = (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
            ‖u (↑z : XiZeroCopy × XiZeroCopy).1‖ *
              ‖u (↑z : XiZeroCopy × XiZeroCopy).2‖) * (4 * B ^ 4) := tsum_mul_right
      _ ≤ 2 * ε * S * (4 * B ^ 4) := by
          refine mul_le_mul_of_nonneg_right hcomplprod (by positivity)
      _ = 4 * B ^ 4 * (2 * ε * S) := by ring
  -- assemble
  have hmain : 0 ≤ (2 * (xiPolyMoment p (2 * m) X * xiPolyMoment p (2 * m + 2) X -
      xiPolyMoment p (2 * m + 1) X ^ 2)).re := by
    rw [hpair]
    have hEq : (∑' z : XiZeroCopy × XiZeroCopy,
        (u z.1 * u z.2) ^ (2 * m + 1) *
          (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
          (u z.1 - u z.2) ^ 2) =
        (∑ z ∈ F ×ˢ F, (u z.1 * u z.2) ^ (2 * m + 1) *
          (evalRealPolynomial p (u z.1) ^ 2 * evalRealPolynomial p (u z.2) ^ 2) *
          (u z.1 - u z.2) ^ 2) +
        ∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
              (2 * m + 1) *
            (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
              evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2 := hsplit.symm
    rw [hEq, Complex.add_re]
    have htailre : -(4 * B ^ 4 * (2 * ε * S)) ≤
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
              (2 * m + 1) *
            (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
              evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2).re := by
      have ha := Complex.abs_re_le_norm
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
              (2 * m + 1) *
            (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
              evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2)
      have hb := neg_abs_le
        (∑' z : ↑(↑(F ×ˢ F) : Set (XiZeroCopy × XiZeroCopy))ᶜ,
          (u (↑z : XiZeroCopy × XiZeroCopy).1 * u (↑z : XiZeroCopy × XiZeroCopy).2) ^
              (2 * m + 1) *
            (evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).1) ^ 2 *
              evalRealPolynomial p (u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2) *
            (u (↑z : XiZeroCopy × XiZeroCopy).1 -
              u (↑z : XiZeroCopy × XiZeroCopy).2) ^ 2).re
      linarith
    linarith [hmass]
  have h2re : (2 * (xiPolyMoment p (2 * m) X * xiPolyMoment p (2 * m + 2) X -
      xiPolyMoment p (2 * m + 1) X ^ 2)).re =
      2 * (xiPolyMoment p (2 * m) X * xiPolyMoment p (2 * m + 2) X -
        xiPolyMoment p (2 * m + 1) X ^ 2).re := by
    simp [Complex.mul_re]
  rw [h2re] at hmain
  linarith

/-- **Pricing the countable list**: every rational-nodal single-minor datum follows from line
placement above one scale plus one explicit mass inequality, with disk bound `2^{4j}` and
node-witness distances `∏(r_k − c_i)`. -/
theorem rational_nodal_datum_of_partial_line {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    {j : ℕ} (c : Fin j → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (m : ℕ)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * 2 ^ (4 * j) * (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖) *
        (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        ((∏ i, (‖xiResolventPoint X q₁‖ - c i)) ^ 2 *
          (∏ i, (‖xiResolventPoint X q₂‖ - c i)) ^ 2) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ 2)) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2).re := by
  have hB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖evalRealPolynomial (finNodalPolynomial c) z‖ ≤ 2 ^ j := by
    intro z hz
    rw [evalRealPolynomial_finNodalPolynomial, norm_prod]
    calc ∏ i, ‖z - ((c i : ℝ) : ℂ)‖ ≤ ∏ _i : Fin j, (2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_sub_node_le hz (hc i).1 (hc i).2)
      _ = 2 ^ j := by rw [Finset.prod_const, Finset.card_fin]
  have hBpow : ((2 : ℝ) ^ j) ^ 4 = 2 ^ (4 * j) := by
    rw [← pow_mul, mul_comm]
  refine polyTuranMinor_supply_of_partial_line hX hδ hline (finNodalPolynomial c) m hB
    h1 h2 hne ?_
  rw [hBpow, eval_finNodalPolynomial, eval_finNodalPolynomial]
  exact hmass

end

end RHTower
