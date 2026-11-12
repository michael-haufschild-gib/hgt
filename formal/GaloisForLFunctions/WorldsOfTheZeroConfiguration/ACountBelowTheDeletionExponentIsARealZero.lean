import GaloisForLFunctions.WorldsOfTheZeroConfiguration.AdditionsArePaidInFull
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# A count below the exponent of the deleted primes is a real zero

The balance law of an edit was proved for a given continuation of `(s − 1) ζ_B(s)` to
`Re s > 1/2`.  The count supplies a continuation, at every height.

* **The count continues the zeta function** (`exists_continuation_of_count`).  For an
  integer-norm system with `N(x) = A x + O(x^β)`, `0 ≤ β ≤ 1`, the coefficients `a(n) − A` of
  `ζ_B − A ζ` have partial sums `O(x^β)`, so `(s − 1) ζ_B(s)` is holomorphic on `Re s > β`.
  Summation by parts bounds the continuation of `ζ_B − A ζ` by
  `C (1 + |s| Σ_i i^{β − σ₀ − 1})` on `Re s ≥ σ₀ > β`: linear growth on vertical lines
  (`norm_growthCont_le`, `exists_continuation_of_count_linear`).
* **The prime-power remainder of a thin edit** (`differentiableOn_editRem_of_summable`).  If
  `Σ_p |e(p)| p^{−θ} < ∞`, `θ > 0`, then `Q(s) = Σ_p e(p) (−log(1 − p^{−s}) − p^{−s})` is
  holomorphic on `Re s > θ/2`.
* **Landau's zero from the count** (`zero_at_expo_minus_of_count`).  If
  `max(κ₊, β) < κ₋`, the continuation vanishes at `κ₋`: right of `κ₋` it is
  `(s − 1) ζ(s) · exp(D₊ − D₋ + Q)`, and `exp D₋` does not continue across `κ₋` unless the
  continuation vanishes there.
* **Integer density** (`exists_order_of_count`).  The zero has an order `m ≥ 1`, and
  `exp(−Σ_{p deleted} p^{−s}) = (s − κ₋)^m W(s)` right of `κ₋` near `κ₋`, with `W` analytic and
  nonzero at `κ₋`.  On the real axis: `Σ_{p deleted} p^{−σ} = m log(1/(σ − κ₋)) + O(1)`.  The
  deleted primes of an edit whose count beats its thickness have the logarithmic density of `m`
  copies of the primes at the scale `κ₋`.

**Thickness beaten by the count** (`balance_or_zero_of_count`).  Let `β < max(κ₊, κ₋)`.  Then
`κ₊ ≤ κ₋` (additions are paid in full), and either `κ₊ = κ₋` or `ζ_B` has a real zero at `κ₋`.
A delete-only edit whose count exponent is below the exponent of its deleted primes has
Landau's zero there (`zero_of_delete_only_of_count`); this holds at every height in `(0, 1]`,
also left of the line.
-/

open Complex Metric Filter Topology Finset
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.HeckeLFunctions

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits NormCount CountFloor

/-! ## The count continues the zeta function -/

/-- The coefficients `a(n) − A` of `ζ_B − A ζ`. -/
def countDefect (B : BeurlingSystem) (h : HasIntegerNorms B) (A : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (intCount B h n : ℂ) - A

/-- The partial sums of the coefficients `a(n) − A` are the count remainder at integers. -/
theorem norm_sum_countDefect_le {B : BeurlingSystem} (h : HasIntegerNorms B) (hd : B.IsDiscrete)
    {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) (x : ℝ) (hx : 1 ≤ x) :
    ‖∑ k ∈ Icc 1 ⌊x⌋₊, countDefect B h A k‖ ≤ C * x ^ β := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hn1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have hI : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hreal : ∑ k ∈ Ioc 0 ⌊x⌋₊, ((intCount B h k : ℝ) - A) =
      (B.countBall (⌊x⌋₊ : ℝ) : ℝ) - A * (⌊x⌋₊ : ℝ) := by
    rw [Finset.sum_sub_distrib, sum_intCount_eq_countBall h hd, Finset.sum_const, Nat.card_Ioc,
      nsmul_eq_mul, Nat.sub_zero]
    ring
  have hsum : ∑ k ∈ Icc 1 ⌊x⌋₊, countDefect B h A k =
      ((∑ k ∈ Ioc 0 ⌊x⌋₊, ((intCount B h k : ℝ) - A) : ℝ) : ℂ) := by
    rw [hI, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.mp hk).1; omega
    simp [countDefect, hk0]
  rw [hsum, hreal, Complex.norm_real, Real.norm_eq_abs]
  exact (hN _ hn1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by linarith) (Nat.floor_le (by linarith)) hβ) hC)

/-- A count `A x + O(x^β)` with `β ≤ 1` is linear. -/
theorem hasLinearCounting_of_count {B : BeurlingSystem} {A C β : ℝ} (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    B.HasLinearCounting (|A| + C) := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  intro X hX
  have h1 := (abs_le.mp (hN X hX)).2
  have h2 : X ^ β ≤ X := by
    have h5 := Real.rpow_le_rpow_of_exponent_le hX hβ1
    rwa [Real.rpow_one] at h5
  have h3 : A * X ≤ |A| * X := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  have h4 : C * X ^ β ≤ C * X := mul_le_mul_of_nonneg_left h2 hC
  linarith

/-- **Linear growth.**  A Dirichlet series whose coefficients have partial sums `O(x^θ)` is, on
`Re s ≥ σ₀ > θ`, at most `K (1 + |s| Σ_i i^{θ − σ₀ − 1})`. -/
theorem norm_growthCont_le {c : ℕ → ℂ} {θ K : ℝ} (hc0 : c 0 = 0) (hθ : 0 ≤ θ)
    (hK : ∀ x : ℝ, 1 ≤ x → ‖∑ k ∈ Icc 1 ⌊x⌋₊, c k‖ ≤ K * x ^ θ) {σ₀ : ℝ} (hσ₀ : θ < σ₀)
    {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖growthCont c θ s‖ ≤ K * (1 + ‖s‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - σ₀ - 1)) := by
  have hK0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hK 1 le_rfl)
  have hsθ : θ < s.re := lt_of_lt_of_le hσ₀ hs
  -- summation by parts bounds every partial sum
  have hb : ∀ N, ‖∑ n ∈ range N, LSeries.term c s n‖ ≤
      K * (1 + ‖s‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - s.re - 1)) := fun N => by
    simp_rw [term_eq_mul_powNeg_of_zero hc0]
    refine BoundedPartialSums.norm_sum_mul_powNeg_le_of_growth hθ hK0 hc0 (fun n hn => ?_) hsθ N
    rw [BoundedPartialSums.partialSum, HeckeLFunctions.sum_range_succ_eq_sum_Icc hc0]
    simpa using hK n (by exact_mod_cast hn)
  have hlim := le_of_tendsto' (tendsto_sum_term_growthCont hc0 hθ hK hsθ).norm hb
  -- the sum over `i` decreases with the abscissa
  have hS₁ : Summable fun i : ℕ => (i : ℝ) ^ (θ - s.re - 1) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hS₂ : Summable fun i : ℕ => (i : ℝ) ^ (θ - σ₀ - 1) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h0 : ∀ a : ℝ, a < 0 → ((0 : ℕ) : ℝ) ^ a = 0 := fun a ha => by
    rw [Nat.cast_zero, Real.zero_rpow ha.ne]
  have hmono : ∑' i : ℕ, (i : ℝ) ^ (θ - s.re - 1) ≤ ∑' i : ℕ, (i : ℝ) ^ (θ - σ₀ - 1) := by
    refine hasSum_le (fun i => ?_) hS₁.hasSum hS₂.hasSum
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact le_of_eq (by rw [h0 _ (by linarith), h0 _ (by linarith)])
    · exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hi) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hmono (norm_nonneg s)
  exact hlim.trans (mul_le_mul_of_nonneg_left (by linarith) hK0)

/-- **The count continues the zeta function, with linear growth.**  An integer-norm system with
`N(x) = A x + O(x^β)`, `0 ≤ β ≤ 1`, has a holomorphic continuation `G` of `(s − 1) ζ_B(s)` to
`Re s > β`, and `|G(s) − A (s − 1) ζ(s)| ≤ |s − 1| · C (1 + |s| Σ_i i^{β − σ₀ − 1})` on
`Re s ≥ σ₀ > β`. -/
theorem exists_continuation_of_count_linear {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
      ∀ σ₀ : ℝ, β < σ₀ → ∀ s : ℂ, σ₀ ≤ s.re →
        ‖G s - (A : ℂ) * zetaResidueUnit s‖ ≤
          ‖s - 1‖ * (C * (1 + ‖s‖ * ∑' i : ℕ, (i : ℝ) ^ (β - σ₀ - 1))) := by
  have hc0 : countDefect B h A 0 = 0 := by simp [countDefect]
  have hgrow := norm_sum_countDefect_le h hd hβ hN
  have hlin := hasLinearCounting_of_count hβ1 hN
  refine ⟨fun s => (A : ℂ) * zetaResidueUnit s + (s - 1) * growthCont (countDefect B h A) β s,
    ?_, fun s hs => ?_, fun σ₀ hσ₀ s hs => ?_⟩
  · exact ((differentiableOn_const _).mul differentiable_zetaResidueUnit.differentiableOn).add
      ((differentiable_id.sub_const 1).differentiableOn.mul
        (differentiableOn_growthCont hc0 hβ hgrow))
  · have hs1 : s ≠ 1 := fun h1 => by rw [h1] at hs; norm_num at hs
    obtain ⟨hsa, hζB⟩ := zetaSeriesC_eq_LSeries_of_summable h hd
      (BeurlingSystem.summable_intNorm_rpow hd hlin hs)
    have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
    have hterm : LSeries.term (countDefect B h A) s =
        LSeries.term ((fun n => (intCount B h n : ℂ)) - (A : ℂ) • (1 : ℕ → ℂ)) s := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
        congr 1
        simp [countDefect, hn]
    have hsc : LSeriesSummable (countDefect B h A) s := by
      rw [LSeriesSummable, hterm]
      exact hsa.sub (hone.smul (A : ℂ))
    have hLc : LSeries (countDefect B h A) s =
        B.zetaSeriesC s - (A : ℂ) * riemannZeta s := by
      have h1 : LSeries (countDefect B h A) s =
          LSeries ((fun n => (intCount B h n : ℂ)) - (A : ℂ) • (1 : ℕ → ℂ)) s := by
        show ∑' n, LSeries.term (countDefect B h A) s n = ∑' n, LSeries.term _ s n
        rw [hterm]
      rw [h1, LSeries_sub hsa (hone.smul (A : ℂ)), LSeries_smul,
        LSeries_one_eq_riemannZeta hs, hζB]
    show (A : ℂ) * zetaResidueUnit s + (s - 1) * growthCont (countDefect B h A) β s = _
    rw [growthCont_eq_LSeries hc0 hβ hgrow (lt_of_le_of_lt hβ1 hs) hsc, hLc,
      zetaResidueUnit_of_ne hs1]
    ring
  · show ‖(A : ℂ) * zetaResidueUnit s + (s - 1) * growthCont (countDefect B h A) β s -
      (A : ℂ) * zetaResidueUnit s‖ ≤ _
    rw [add_sub_cancel_left, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_growthCont_le hc0 hβ hgrow hσ₀ hs) (norm_nonneg _)

/-- **The count continues the zeta function.**  An integer-norm system with
`N(x) = A x + O(x^β)`, `0 ≤ β ≤ 1`, has a holomorphic continuation of `(s − 1) ζ_B(s)` to
`Re s > β`. -/
theorem exists_continuation_of_count {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s := by
  obtain ⟨G, hG, hGeq, -⟩ := exists_continuation_of_count_linear h hd hβ hβ1 hN
  exact ⟨G, hG, hGeq⟩

/-! ## The prime-power remainder of a thin edit -/

/-- The prime-power remainder of an edit that is summable at `θ > 0` is holomorphic on
`Re s > θ/2`. -/
theorem differentiableOn_editRem_of_summable {e : ℕ → ℤ} {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) :
    DifferentiableOn ℂ (editRem e) {s : ℂ | θ / 2 < s.re} := by
  have hUo : IsOpen {s : ℂ | θ / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmaj : Summable fun p : Nat.Primes =>
      |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) * ((1 - (2 : ℝ) ^ (-(θ / 2)))⁻¹ / 2) :=
    (hS.subtype _).mul_right _
  refine differentiableOn_tsum_of_summable_norm hmaj (fun p => ?_) hUo (fun p w hw => ?_)
  · intro w hw
    have hw' : θ / 2 < w.re := hw
    have hlt : ‖((p : ℕ) : ℂ) ^ (-(w + 0))‖ < 1 := by
      rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; linarith)
    have h := differentiableAt_logRem_cpow (n := (p : ℕ)) p.2.pos (c := 0) (s := w) hlt
    simp only [add_zero] at h
    exact (h.const_mul _).differentiableWithinAt
  · have hw' : θ / 2 < w.re := hw
    have h := norm_logRem_cpow_le (n := (p : ℕ)) p.2.two_le (c := 0) (s := w) (a := θ / 2)
      (σ := θ / 2) (by linarith) le_rfl (by rw [add_zero]; exact hw'.le)
    rw [add_zero, show 2 * (θ / 2) = θ by ring] at h
    rw [norm_mul, Complex.norm_intCast]
    calc |(e p : ℝ)| * ‖logRem (((p : ℕ) : ℂ) ^ (-w))‖
        ≤ |(e p : ℝ)| * (((p : ℕ) : ℝ) ^ (-θ) * (1 - (2 : ℝ) ^ (-(θ / 2)))⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) * ((1 - (2 : ℝ) ^ (-(θ / 2)))⁻¹ / 2) := by ring

/-! ## Landau's zero from the count -/

/-- **The zero at the exponent of the deleted primes and its order.**  If an edit has count
`A x + O(x^β)` and `max(κ₊, β) < κ₋`, the continuation `G` of `(s − 1) ζ_B(s)` to `Re s > β`
vanishes at `κ₋`, and there are `m ≥ 1` and `W`, analytic and nonzero at `κ₋`, with
`exp(−Σ_{p deleted} p^{−s}) = (s − κ₋)^m W(s)` for `s` near `κ₋`, `Re s > κ₋`. -/
theorem exists_order_of_count {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (h : max (expo (plusSet e)) β < expo (minusSet e)) :
    ∃ (G : ℂ → ℂ) (m : ℕ) (W : ℂ → ℂ), DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      G ((expo (minusSet e) : ℝ) : ℂ) = 0 ∧ 1 ≤ m ∧
      AnalyticAt ℂ W ((expo (minusSet e) : ℝ) : ℂ) ∧ W ((expo (minusSet e) : ℝ) : ℂ) ≠ 0 ∧
      ∀ᶠ s in 𝓝 ((expo (minusSet e) : ℝ) : ℂ), expo (minusSet e) < s.re →
        cexp (-gdSeries (wt (minusSet e)) freq s) =
          (s - ((expo (minusSet e) : ℝ) : ℂ)) ^ m * W s := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = expo (minusSet e) := ⟨_, rfl⟩
  rw [← hκdef] at h ⊢
  have hκp : expo (plusSet e) < κ := lt_of_le_of_lt (le_max_left _ _) h
  have hκβ : β < κ := lt_of_le_of_lt (le_max_right _ _) h
  have hκ0 : 0 < κ := lt_of_le_of_lt hβ hκβ
  have hκ1 : κ ≤ 1 := by rw [hκdef]; exact expo_le_one _
  obtain ⟨G, hG, hGeq⟩ := exists_continuation_of_count (hasIntegerNorms_editSystem e)
    (isDiscrete_editSystem e) hβ (by linarith) hN
  -- the edit is summable at `3κ/2`: its prime-power remainder is holomorphic on `Re s > 3κ/4`
  have hp : SummableAt (plusSet e) (3 * κ / 2) := summableAt_of_expo_lt (by linarith)
  have hm : SummableAt (minusSet e) (3 * κ / 2) :=
    summableAt_of_expo_lt (by rw [← hκdef]; linarith)
  have hQ := differentiableOn_editRem_of_summable (θ := 3 * κ / 2) (by linarith)
    (summable_abs_edit_of_summableAt he hp hm)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = max β (3 * κ / 2 / 2) := ⟨_, rfl⟩
  have hc₀κ : c₀ < κ := by rw [hc₀]; exact max_lt hκβ (by linarith)
  have hsubG : {s : ℂ | c₀ < s.re} ⊆ {s : ℂ | β < s.re} := fun z (hz : c₀ < z.re) =>
    show β < z.re from lt_of_le_of_lt (by rw [hc₀]; exact le_max_left _ _) hz
  have hsubQ : {s : ℂ | c₀ < s.re} ⊆ {s : ℂ | 3 * κ / 2 / 2 < s.re} :=
    fun z (hz : c₀ < z.re) =>
      show 3 * κ / 2 / 2 < z.re from lt_of_le_of_lt (by rw [hc₀]; exact le_max_right _ _) hz
  have hzero : G (κ : ℂ) = 0 :=
    zero_of_minus_heavy he (hG.mono hsubG) hGeq (hQ.mono hsubQ) hc₀κ hκ1
      (κ' := (expo (plusSet e) + κ) / 2) (by linarith)
      (summableAt_of_expo_lt (by linarith))
      (fun σ hσ => summableAt_of_expo_lt (by rw [← hκdef]; exact hσ))
      (fun σ hσ => not_summableAt_of_lt_expo (by rw [← hκdef]; exact hκ0)
        (by rw [← hκdef]; exact hσ))
  -- `G` is analytic at `κ` and not identically zero
  have hUo : IsOpen {s : ℂ | β < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hκmem : (κ : ℂ) ∈ {s : ℂ | β < s.re} := by
    show β < (κ : ℂ).re
    rw [Complex.ofReal_re]; exact hκβ
  have hGan : AnalyticAt ℂ G (κ : ℂ) := hG.analyticAt (hUo.mem_nhds hκmem)
  have hlin := hasLinearCounting_of_count (B := editSystem e) (by linarith : β ≤ 1) hN
  have hnot : ¬ ∀ᶠ z in 𝓝 (κ : ℂ), G z = 0 := by
    intro hev
    have hglob := (hG.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt β).isPreconnected hκmem hev
    have h2mem : (2 : ℂ) ∈ {s : ℂ | β < s.re} := by
      show β < (2 : ℂ).re
      rw [show (2 : ℂ).re = 2 by norm_num]
      linarith
    have h2 : G 2 = 0 := hglob h2mem
    rw [hGeq 2 (by norm_num)] at h2
    have h3 := BeurlingSystem.zetaSeriesC_ne_zero (isDiscrete_editSystem e) hlin (s := 2)
      (by norm_num)
    rcases mul_eq_zero.mp h2 with h4 | h4
    · norm_num at h4
    · exact h3 h4
  obtain ⟨m, g, hgan, hg0, hgeq⟩ := hGan.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hself := hgeq.self_of_nhds
    rw [hm0', pow_zero, one_smul, hzero] at hself
    exact hg0 hself.symm
  -- the regular factor `(s − 1) ζ(s) · exp(D₊ + Q)` is analytic and nonzero at `κ`
  have hDp : AnalyticAt ℂ (gdSeries (wt (plusSet e)) freq) (κ : ℂ) :=
    (differentiableOn_gdSeries_wt (T := plusSet e) (c := (expo (plusSet e) + κ) / 2)
      (fun σ hσ => summableAt_of_expo_lt (by linarith))).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (expo (plusSet e) + κ) / 2 < (κ : ℂ).re by
          rw [Complex.ofReal_re]; linarith))
  have hQan : AnalyticAt ℂ (editRem e) (κ : ℂ) :=
    hQ.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 3 * κ / 2 / 2 < (κ : ℂ).re by rw [Complex.ofReal_re]; linarith))
  have hu0 : zetaResidueUnit (κ : ℂ) ≠ 0 := _root_.RHTower.zetaResidueUnit_ofReal_ne_zero hκ0
  have hden : AnalyticAt ℂ (fun s => zetaResidueUnit s *
      cexp (gdSeries (wt (plusSet e)) freq s + editRem e s)) (κ : ℂ) :=
    (analyticAt_zetaResidueUnit _).mul (hDp.add hQan).cexp
  have hden0 : zetaResidueUnit (κ : ℂ) *
      cexp (gdSeries (wt (plusSet e)) freq (κ : ℂ) + editRem e (κ : ℂ)) ≠ 0 :=
    mul_ne_zero hu0 (Complex.exp_ne_zero _)
  refine ⟨G, m, fun s => g s / (zetaResidueUnit s *
    cexp (gdSeries (wt (plusSet e)) freq s + editRem e s)), hG, hGeq, hzero, hm1,
    hgan.div hden hden0, div_ne_zero hg0 hden0, ?_⟩
  filter_upwards [hgeq, hden.continuousAt.eventually_ne hden0] with s hGs hne hre
  have hne' : zetaResidueUnit s * cexp (gdSeries (wt (plusSet e)) freq s + editRem e s) ≠ 0 :=
    hne
  have hcont := continuation_eq he (hG.mono hsubG) hGeq (hQ.mono hsubQ) hc₀κ.le hκ1
    (fun σ hσ => summableAt_of_expo_lt (lt_trans hκp hσ))
    (fun σ hσ => summableAt_of_expo_lt (by rw [← hκdef]; exact hσ)) hre
  have hsplit : cexp (gdSeries (wt (plusSet e)) freq s - gdSeries (wt (minusSet e)) freq s +
      editRem e s) = cexp (-gdSeries (wt (minusSet e)) freq s) *
        cexp (gdSeries (wt (plusSet e)) freq s + editRem e s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h5 : (s - (κ : ℂ)) ^ m * g s = G s := by rw [hGs, smul_eq_mul]
  rw [← mul_div_assoc, eq_div_iff hne', h5, hcont, hsplit]
  ring

/-- **A count below the exponent of the deleted primes is a real zero.**  If an edit has count
`A x + O(x^β)` and `max(κ₊, β) < κ₋`, the continuation of `(s − 1) ζ_B(s)` to `Re s > β` vanishes
at `κ₋`. -/
theorem zero_at_expo_minus_of_count {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (h : max (expo (plusSet e)) β < expo (minusSet e)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      G ((expo (minusSet e) : ℝ) : ℂ) = 0 := by
  obtain ⟨G, -, -, hG, hGeq, hzero, -⟩ := exists_order_of_count he hβ hN h
  exact ⟨G, hG, hGeq, hzero⟩

/-- **Thickness beaten by the count is balance or a real zero.**  If the count exponent `β` of
an edit is below `max(κ₊, κ₋)`, then `κ₊ = κ₋`, or `κ₊ < κ₋` and the continuation of
`(s − 1) ζ_B(s)` vanishes at `κ₋`. -/
theorem balance_or_zero_of_count {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hA : 0 ≤ A)
    (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hlt : β < max (expo (plusSet e)) (expo (minusSet e))) :
    expo (plusSet e) = expo (minusSet e) ∨
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        G ((expo (minusSet e) : ℝ) : ℂ) = 0 := by
  have hH := expo_plus_le_max he hA hβ hN
  rcases lt_trichotomy (expo (plusSet e)) (expo (minusSet e)) with hlt' | heq | hgt
  · right
    rw [max_eq_right hlt'.le] at hlt
    exact zero_at_expo_minus_of_count he hβ hN (max_lt hlt' hlt)
  · exact Or.inl heq
  · exfalso
    rw [max_eq_left hgt.le] at hlt
    have h1 : max β (expo (minusSet e)) < expo (plusSet e) := max_lt hlt hgt
    linarith

/-- The empty set of primes has exponent zero. -/
theorem expo_empty : expo (∅ : Set ℕ) = 0 := by
  refine le_antisymm (expo_le_of_summableAt le_rfl ?_) (expo_nonneg _)
  show Summable (gdTwistTerm (wt (∅ : Set ℕ)) freq 0 0)
  refine summable_zero.congr fun p => ?_
  rw [gdTwistTerm_wt, wt_of_notMem fun hmem => (Set.mem_empty_iff_false p).mp hmem, zero_mul]

/-- **Deletions are paid in full, or Landau's zero.**  A delete-only edit whose count exponent
is below the exponent of its deleted primes has a real zero of `ζ_B` at that exponent. -/
theorem zero_of_delete_only_of_count {e : ℕ → ℤ} (he : IsEdit e) (hp : plusSet e = ∅)
    {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hlt : β < expo (minusSet e)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      G ((expo (minusSet e) : ℝ) : ℂ) = 0 :=
  zero_at_expo_minus_of_count he hβ hN
    (by rw [hp, expo_empty]; exact max_lt (lt_of_le_of_lt hβ hlt) hlt)

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
