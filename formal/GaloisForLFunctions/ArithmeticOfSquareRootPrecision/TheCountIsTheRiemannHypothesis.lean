import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.PrecisionClassesAndTheCount
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.XiWardGlobalCapAndFiniteHeadArithmetic

/-!
# The count for `Λ` is the Riemann hypothesis, in each half; its exponent is the zero width

For the arithmetic weight `Λ` the partial sum is Chebyshev's `ψ`.

* **The count is RH** (`count_vonMangoldt_iff`): von Koch.
* **Each half is RH** (`upperCount_vonMangoldt_iff`, `lowerCount_vonMangoldt_iff`). A one-sided
  square-root bound on `ψ(x) − x`, in either direction, forces `Θ = sup Re ρ ≤ ½`: by Landau's
  argument both signs of `ψ(x) − x` reach `x^b` for every `b < Θ`, and `√x log² x = o(x^b)` for
  `b > ½`. One-sidedness costs no precision.
* **Precision exponent** (`precisionExponent`): the infimum of the `θ` with `A(x) − x = O(x^θ)`.
  It is never negative, since a step function stays `1/4` away from `x` at every integer scale
  (`zero_le_of_isBigO_rpow`). For `Λ` it is the zero width: `θ(Λ) = Θ`
  (`precisionExponent_vonMangoldt`); RH iff `θ(Λ) = ½` (`riemannHypothesis_iff_precisionExponent`).
  Every weight satisfying the count has exponent at most `½` (`precisionExponent_le_half_of_count`).
-/

noncomputable section

open Filter Asymptotics Real Finset RHTower

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The arithmetic weight `Λ`. -/
abbrev vonMangoldtWeight : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n

theorem partialSum_vonMangoldt (x : ℝ) : partialSum vonMangoldtWeight x = Chebyshev.psi x := rfl

/-- **The count for `Λ` is RH** (von Koch). -/
theorem count_vonMangoldt_iff : Count vonMangoldtWeight ↔ RiemannHypothesis :=
  riemannHypothesis_iff_chebyshevPsi_sub_isBigO.symm

/-- `√x log² x = o(x^b)` for every `b > ½`. -/
theorem sqrtScale_isLittleO_rpow_of_half_lt {b : ℝ} (hb : 1 / 2 < b) :
    sqrtScale =o[atTop] fun x => x ^ b := by
  have h := sqrtScale_isLittleO_rpow (η := 1 - b) (by linarith)
  simpa only [sub_sub_cancel] using h

/-- RH from `Θ ≤ ½`. -/
theorem riemannHypothesis_of_zeroReSup_le_half (h : zeroReSup ≤ 1 / 2) : RiemannHypothesis :=
  riemannHypothesis_iff_forall_xiZeroCopy_re_eq_half.mpr
    (xiZeroCopy_re_eq_half_of_forall_le fun q => (re_le_zeroReSup q).trans h)

/-- RH is `Θ = ½`. -/
theorem riemannHypothesis_iff_zeroReSup_eq_half : RiemannHypothesis ↔ zeroReSup = 1 / 2 := by
  refine ⟨fun h => le_antisymm ?_ half_le_zeroReSup, fun h => riemannHypothesis_of_zeroReSup_le_half
    h.le⟩
  haveI := nonempty_xiZeroCopy
  exact zeroReSup_le fun q => (riemannHypothesis_iff_forall_xiZeroCopy_re_eq_half.mp h q).le

/-- An eventual bound `f ≤ C √x log² x` and a frequent lower bound `f > x^b` with `b > ½` are
incompatible. -/
theorem not_eventually_le_sqrtScale_of_frequently {f : ℝ → ℝ} {b C : ℝ} (hb : 1 / 2 < b)
    (hfreq : ∃ᶠ x in atTop, x ^ b < f x) : ¬ ∀ᶠ x in atTop, f x ≤ C * sqrtScale x := by
  intro hev
  have ho := ((sqrtScale_isLittleO_rpow_of_half_lt hb).const_mul_left C).def one_half_pos
  obtain ⟨x, ⟨⟨h1, h2⟩, hx0⟩, h3⟩ :=
    (((hev.and ho).and (eventually_gt_atTop (0 : ℝ))).and_frequently hfreq).exists
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hxb.le] at h2
  linarith [le_abs_self (C * sqrtScale x)]

/-- **The upper half of the count is RH.** -/
theorem upperCount_vonMangoldt_iff : UpperCount vonMangoldtWeight ↔ RiemannHypothesis := by
  refine ⟨fun ⟨C, hC⟩ => riemannHypothesis_of_zeroReSup_le_half ?_,
    fun h => (count_iff_upperCount_and_lowerCount.mp (count_vonMangoldt_iff.mpr h)).1⟩
  by_contra hlt
  rw [not_le] at hlt
  exact not_eventually_le_sqrtScale_of_frequently (b := (1 / 2 + zeroReSup) / 2) (by linarith)
    (frequently_rpow_lt_chebyshevPsi_sub (by linarith)) hC

/-- **The lower half of the count is RH.** -/
theorem lowerCount_vonMangoldt_iff : LowerCount vonMangoldtWeight ↔ RiemannHypothesis := by
  refine ⟨fun ⟨C, hC⟩ => riemannHypothesis_of_zeroReSup_le_half ?_,
    fun h => (count_iff_upperCount_and_lowerCount.mp (count_vonMangoldt_iff.mpr h)).2⟩
  by_contra hlt
  rw [not_le] at hlt
  refine not_eventually_le_sqrtScale_of_frequently (f := fun x => -(Chebyshev.psi x - x))
    (b := (1 / 2 + zeroReSup) / 2) (C := C) (by linarith) ?_ (hC.mono fun x hx => by
      simp only [partialSum_vonMangoldt] at hx; linarith)
  exact (frequently_chebyshevPsi_sub_lt_neg_rpow (b := (1 / 2 + zeroReSup) / 2)
    (by linarith)).mono fun x hx => by linarith

/-! ### The precision exponent -/

/-- The **precision exponent** of a weight: the infimum of the `θ` with `A(x) − x = O(x^θ)`. -/
def precisionExponent (a : ℕ → ℝ) : ℝ :=
  sInf {θ : ℝ | (fun x => partialSum a x - x) =O[atTop] fun x => x ^ θ}

/-- **The step floor.** `A(x) − x` is never `O(x^θ)` with `θ < 0`: on `[n, n + 1)` the partial sum
is constant, so `|A(x) − x| ≥ 1/4` at `x = n` or `x = n + ½`. -/
theorem zero_le_of_isBigO_rpow {a : ℕ → ℝ} {θ : ℝ}
    (h : (fun x => partialSum a x - x) =O[atTop] fun x => x ^ θ) : 0 ≤ θ := by
  by_contra hθ
  rw [not_le] at hθ
  have ht : Tendsto (fun x : ℝ => x ^ θ) atTop (nhds 0) := tendsto_rpow_neg_atTop (y := -θ)
    (by linarith)
    |>.congr' (by filter_upwards with x; rw [neg_neg])
  have h0 := (h.trans_tendsto ht).eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨X, hX⟩ := eventually_atTop.mp h0
  set n : ℕ := ⌈max X 0⌉₊
  have hn : X ≤ n := (le_max_left X 0).trans (Nat.le_ceil _)
  have hfl1 : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  have hfl2 : ⌊(n : ℝ) + 1 / 2⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have h1 := hX n hn
  have h2 := hX ((n : ℝ) + 1 / 2) (by linarith)
  simp only [Real.dist_eq, sub_zero] at h1 h2
  have he : partialSum a ((n : ℝ) + 1 / 2) = partialSum a n := by
    unfold partialSum; rw [hfl1, hfl2]
  rw [he] at h2
  have h3 := abs_sub (partialSum a n - n) (partialSum a n - ((n : ℝ) + 1 / 2))
  rw [show partialSum a n - n - (partialSum a n - ((n : ℝ) + 1 / 2)) = 1 / 2 by ring,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
  linarith

theorem bddBelow_precisionSet (a : ℕ → ℝ) :
    BddBelow {θ : ℝ | (fun x => partialSum a x - x) =O[atTop] fun x => x ^ θ} :=
  ⟨0, fun _ hθ => zero_le_of_isBigO_rpow hθ⟩

/-- A bound at exponent `θ` bounds the precision exponent. -/
theorem precisionExponent_le {a : ℕ → ℝ} {θ : ℝ}
    (h : (fun x => partialSum a x - x) =O[atTop] fun x => x ^ θ) : precisionExponent a ≤ θ :=
  csInf_le (bddBelow_precisionSet a) h

/-- **Every weight satisfying the count has precision exponent at most `½`.** -/
theorem precisionExponent_le_half_of_count {a : ℕ → ℝ} (ha : Count a) :
    precisionExponent a ≤ 1 / 2 := by
  refine le_of_forall_gt fun w hw => ?_
  have hb : 1 / 2 < (1 / 2 + w) / 2 := by linarith
  exact lt_of_le_of_lt (precisionExponent_le
    ((ha : _ =O[atTop] sqrtScale).trans (sqrtScale_isLittleO_rpow_of_half_lt hb).isBigO))
    (by linarith)

/-- **The precision exponent of `Λ` is the zero width** `Θ = sup Re ρ`. -/
theorem precisionExponent_vonMangoldt : precisionExponent vonMangoldtWeight = zeroReSup := by
  have hmem : ∀ b, zeroReSup < b →
      (fun x => partialSum vonMangoldtWeight x - x) =O[atTop] fun x => x ^ b := by
    intro b hb
    obtain ⟨C, -, hC⟩ := exists_abs_chebyshevPsi_sub_le_rpow hb
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hC x hx
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨zeroReSup + 1, hmem _ (by linarith)⟩
    (fun b hb => ?_) (fun w hw => ⟨(zeroReSup + w) / 2, hmem _ (by linarith), by linarith⟩)
  by_contra hlt
  rw [not_le] at hlt
  set b' := (b + zeroReSup) / 2
  obtain ⟨C, hC⟩ := isBigO_iff.mp (hb : (fun x => partialSum vonMangoldtWeight x - x) =O[atTop]
    fun x => x ^ b)
  have hgrow : Tendsto (fun x : ℝ => x ^ (b' - b)) atTop atTop :=
    tendsto_rpow_atTop (by simp only [b']; linarith)
  obtain ⟨x, ⟨⟨h1, hx0⟩, h2⟩, h3⟩ := (((hC.and (eventually_gt_atTop (0 : ℝ))).and
    (hgrow.eventually_gt_atTop (|C| + 1))).and_frequently
    (frequently_rpow_lt_chebyshevPsi_sub (b := b') (by simp only [b']; linarith))).exists
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hsplit : x ^ b' = x ^ b * x ^ (b' - b) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hxb.le, partialSum_vonMangoldt] at h1
  have h4 : x ^ b * (|C| + 1) < x ^ b' := by rw [hsplit]; exact mul_lt_mul_of_pos_left h2 hxb
  nlinarith [le_abs_self (Chebyshev.psi x - x), le_abs_self C]

/-- **RH is the precision exponent `½` of `Λ`.** -/
theorem riemannHypothesis_iff_precisionExponent :
    RiemannHypothesis ↔ precisionExponent vonMangoldtWeight = 1 / 2 := by
  rw [precisionExponent_vonMangoldt, riemannHypothesis_iff_zeroReSup_eq_half]

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
