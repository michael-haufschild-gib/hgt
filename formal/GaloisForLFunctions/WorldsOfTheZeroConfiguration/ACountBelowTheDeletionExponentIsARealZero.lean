import GaloisForLFunctions.WorldsOfTheZeroConfiguration.AdditionsArePaidInFull

/-!
# A count below the exponent of the deleted primes is a real zero

The balance law of an edit was proved for a given continuation of `(s − 1) ζ_B(s)` to
`Re s > 1/2`.  The count supplies a continuation, at every height.

* **The count continues the zeta function** (`exists_continuation_of_count`).  For an
  integer-norm system with `N(x) = A x + O(x^β)`, `0 ≤ β ≤ 1`, the coefficients `a(n) − A` of
  `ζ_B − A ζ` have partial sums `O(x^β)`, so `(s − 1) ζ_B(s)` is holomorphic on `Re s > β`.
* **The prime-power remainder of a thin edit** (`differentiableOn_editRem_of_summable`).  If
  `Σ_p |e(p)| p^{−θ} < ∞`, `θ > 0`, then `Q(s) = Σ_p e(p) (−log(1 − p^{−s}) − p^{−s})` is
  holomorphic on `Re s > θ/2`.
* **Landau's zero from the count** (`zero_at_expo_minus_of_count`).  If
  `max(κ₊, β) < κ₋`, the continuation vanishes at `κ₋`: right of `κ₋` it is
  `(s − 1) ζ(s) · exp(D₊ − D₋ + Q)`, and `exp D₋` does not continue across `κ₋` unless the
  continuation vanishes there.

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

/-- **The count continues the zeta function.**  An integer-norm system with
`N(x) = A x + O(x^β)`, `0 ≤ β ≤ 1`, has a holomorphic continuation of `(s − 1) ζ_B(s)` to
`Re s > β`. -/
theorem exists_continuation_of_count {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have hc0 : countDefect B h A 0 = 0 := by simp [countDefect]
  have hgrow := norm_sum_countDefect_le h hd hβ hN
  have hlin : B.HasLinearCounting (|A| + C) := by
    intro X hX
    have h1 := (abs_le.mp (hN X hX)).2
    have h2 : X ^ β ≤ X := by
      have h5 := Real.rpow_le_rpow_of_exponent_le hX hβ1
      rwa [Real.rpow_one] at h5
    have h3 : A * X ≤ |A| * X := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
    have h4 : C * X ^ β ≤ C * X := mul_le_mul_of_nonneg_left h2 hC
    linarith
  refine ⟨fun s => (A : ℂ) * zetaResidueUnit s + (s - 1) * growthCont (countDefect B h A) β s,
    ?_, fun s hs => ?_⟩
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

/-- **A count below the exponent of the deleted primes is a real zero.**  If an edit has count
`A x + O(x^β)` and `max(κ₊, β) < κ₋`, the continuation of `(s − 1) ζ_B(s)` to `Re s > β` vanishes
at `κ₋`. -/
theorem zero_at_expo_minus_of_count {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (h : max (expo (plusSet e)) β < expo (minusSet e)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | β < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      G ((expo (minusSet e) : ℝ) : ℂ) = 0 := by
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
  refine ⟨G, hG, hGeq, ?_⟩
  exact zero_of_minus_heavy he (hG.mono hsubG) hGeq (hQ.mono hsubQ) hc₀κ hκ1
    (κ' := (expo (plusSet e) + κ) / 2) (by linarith)
    (summableAt_of_expo_lt (by linarith))
    (fun σ hσ => summableAt_of_expo_lt (by rw [← hκdef]; exact hσ))
    (fun σ hσ => not_summableAt_of_lt_expo (by rw [← hκdef]; exact hκ0)
      (by rw [← hκdef]; exact hσ))

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
