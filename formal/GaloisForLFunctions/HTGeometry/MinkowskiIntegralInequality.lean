import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Minkowski's integral inequality in the square case

The `L²` norm of a superposition is at most the superposition of the `L²` norms:

`‖∫ G(·, s) ds‖₂ ≤ ∫ ‖G(·, s)‖₂ ds`.

Mathlib has Minkowski only for a sum of two functions; the continuum version is proved here by the
standard duality-free argument.  Pairing the superposition with itself, Tonelli exchanges the two
integrations and Cauchy–Schwarz in the outer variable factors out one copy of the `L²` norm, giving
`A ≤ A^{1/2}B`.  The division by `A^{1/2}` is legitimate only when `A` is finite, so the argument is
run on the truncations `min(H, n)·1_{Sₙ}` — finite by construction — and monotone convergence
restores the full statement.

This is the step that converts a resolvent written as a Laplace transform into an operator bound:
each frequency slice is estimated separately by Plancherel and the slices are then summed in the
transform parameter.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

private theorem enn_sq_rpow (a : ℝ≥0∞) : a ^ (2 : ℝ) = a ^ 2 := by
  rw [← ENNReal.rpow_natCast a 2]
  norm_num

/-- **Cauchy–Schwarz in `ℝ≥0∞`.** -/
theorem lintegral_mul_le_sqrt_mul_sqrt {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ)
      ≤ (∫⁻ x, f x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (∫⁻ x, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hf hg
  simpa only [Pi.mul_apply, enn_sq_rpow] using hCS

/-- **Minkowski's integral inequality, square case.** -/
theorem lintegral_sq_lintegral_le [SigmaFinite μ] [SFinite ν] {G : α → β → ℝ≥0∞}
    (hG : Measurable (Function.uncurry G)) :
    (∫⁻ x, (∫⁻ s, G x s ∂ν) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ ∫⁻ s, (∫⁻ x, G x s ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ∂ν := by
  set H : α → ℝ≥0∞ := fun x => ∫⁻ s, G x s ∂ν with hHdef
  have hHmeas : Measurable H := hG.lintegral_prod_right'
  set B : ℝ≥0∞ := ∫⁻ s, (∫⁻ x, G x s ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ∂ν with hBdef
  -- the truncations
  set T : ℕ → α → ℝ≥0∞ :=
    fun n => (spanningSets μ n).indicator (fun x => min (H x) (n : ℝ≥0∞)) with hTdef
  have hSmeas : ∀ n, MeasurableSet (spanningSets μ n) := fun n => measurableSet_spanningSets μ n
  have hTmeas : ∀ n, Measurable (T n) := by
    intro n
    exact (hHmeas.min measurable_const).indicator (hSmeas n)
  have hTle : ∀ n x, T n x ≤ H x := by
    intro n x
    rw [hTdef]
    by_cases hx : x ∈ spanningSets μ n
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hTbound : ∀ n x, T n x ≤ (n : ℝ≥0∞) := by
    intro n x
    rw [hTdef]
    by_cases hx : x ∈ spanningSets μ n
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hTmono : Monotone T := by
    intro m n hmn x
    rw [hTdef]
    by_cases hx : x ∈ spanningSets μ m
    · have hx' : x ∈ spanningSets μ n := monotone_spanningSets μ hmn hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hmn)
    · simp [Set.indicator_of_notMem hx]
  have hTsup : ∀ x, ⨆ n, T n x = H x := by
    intro x
    refine le_antisymm (iSup_le fun n => hTle n x) ?_
    refine le_iSup_iff.mpr fun b hb => ?_
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨n₀, hn₀⟩ : ∃ n, x ∈ spanningSets μ n := by
      have hmem : x ∈ ⋃ n, spanningSets μ n := by
        rw [iUnion_spanningSets μ]
        exact Set.mem_univ x
      exact Set.mem_iUnion.mp hmem
    have hbtop : b ≠ ⊤ := by
      intro h
      rw [h] at hcon
      exact absurd (le_top : H x ≤ ⊤) (not_le.mpr hcon)
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hbtop
    set n := max n₀ k with hn
    have hxn : x ∈ spanningSets μ n := monotone_spanningSets μ (le_max_left n₀ k) hn₀
    have hcast : (k : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast Nat.cast_le.mpr (le_max_right n₀ k)
    have hTn : T n x = min (H x) (n : ℝ≥0∞) := by
      rw [hTdef]; simp [Set.indicator_of_mem hxn]
    have hlt : b < T n x := by
      rw [hTn]
      exact lt_min hcon (lt_of_lt_of_le hk hcast)
    exact absurd (hb n) (not_le.mpr hlt)
  -- each truncation has finite energy
  have hTfin : ∀ n, (∫⁻ x, T n x ^ 2 ∂μ) ≠ ⊤ := by
    intro n
    have hmaj : ∀ x, T n x ^ 2 ≤ (n : ℝ≥0∞) ^ 2 * (spanningSets μ n).indicator 1 x := by
      intro x
      by_cases hx : x ∈ spanningSets μ n
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact pow_le_pow_left' (hTbound n x) 2
      · simp [hTdef, Set.indicator_of_notMem hx]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hmaj)
    rw [lintegral_const_mul' _ _ (by simp : ((n : ℝ≥0∞) ^ 2) ≠ ⊤),
      lintegral_indicator_one (hSmeas n)]
    exact ENNReal.mul_ne_top (by simp) (measure_spanningSets_lt_top μ n).ne
  -- the key inequality on each truncation
  have hkey : ∀ n, (∫⁻ x, T n x ^ 2 ∂μ) ≤ (∫⁻ x, T n x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * B := by
    intro n
    have hswap : (∫⁻ x, ∫⁻ s, T n x * G x s ∂ν ∂μ) = ∫⁻ s, ∫⁻ x, T n x * G x s ∂μ ∂ν := by
      refine lintegral_lintegral_swap ?_
      exact (((hTmeas n).comp measurable_fst).mul hG).aemeasurable
    calc ∫⁻ x, T n x ^ 2 ∂μ
        = ∫⁻ x, T n x * T n x ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [sq]
      _ ≤ ∫⁻ x, T n x * H x ∂μ := lintegral_mono fun x => mul_le_mul' le_rfl (hTle n x)
      _ = ∫⁻ x, ∫⁻ s, T n x * G x s ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [hHdef]
          exact (lintegral_const_mul' _ _ (ne_top_of_le_ne_top (by simp) (hTbound n x))).symm
      _ = ∫⁻ s, ∫⁻ x, T n x * G x s ∂μ ∂ν := hswap
      _ ≤ ∫⁻ s, (∫⁻ x, T n x ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
            * (∫⁻ x, G x s ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ∂ν := by
          refine lintegral_mono fun s => ?_
          exact lintegral_mul_le_sqrt_mul_sqrt (hTmeas n).aemeasurable
            (hG.comp (measurable_id.prodMk measurable_const)).aemeasurable
      _ = (∫⁻ x, T n x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * B := by
          rw [lintegral_const_mul' _ _ ?_, hBdef]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hTfin n)
  -- transfer to a bound by `B ^ 2`
  have hsqle : ∀ n, (∫⁻ x, T n x ^ 2 ∂μ) ≤ B ^ 2 := by
    intro n
    set A := ∫⁻ x, T n x ^ 2 ∂μ with hA
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0]
      simp
    · have hAfin : A ≠ ⊤ := hTfin n
      have hAhalf : A ^ ((1 : ℝ) / 2) ≤ B := by
        have hpos : A ^ ((1 : ℝ) / 2) ≠ 0 := by
          intro hz
          rw [ENNReal.rpow_eq_zero_iff] at hz
          rcases hz with ⟨hz, _⟩ | ⟨_, hlt⟩
          · exact h0 hz
          · norm_num at hlt
        have hfin : A ^ ((1 : ℝ) / 2) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin
        have hsq : A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) = A := by
          rw [← ENNReal.rpow_add _ _ h0 hAfin]
          norm_num
        have hk : A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) ≤ A ^ ((1 : ℝ) / 2) * B := by
          rw [hsq]
          exact hkey n
        exact (ENNReal.mul_le_mul_iff_right hpos hfin).mp hk
      calc A = (A ^ ((1 : ℝ) / 2)) ^ 2 := by
            rw [← ENNReal.rpow_natCast (A ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
            norm_num
        _ ≤ B ^ 2 := pow_le_pow_left' hAhalf 2
  -- monotone convergence
  have hsup : (∫⁻ x, H x ^ 2 ∂μ) = ⨆ n, ∫⁻ x, T n x ^ 2 ∂μ := by
    have hmono : Monotone fun n => fun x => T n x ^ 2 := by
      intro m n hmn x
      exact pow_le_pow_left' (hTmono hmn x) 2
    have hmeas : ∀ n, Measurable fun x => T n x ^ 2 := fun n => (hTmeas n).pow_const 2
    rw [← lintegral_iSup hmeas hmono]
    refine lintegral_congr fun x => ?_
    rw [← hTsup x]
    exact ENNReal.iSup_pow (fun n => T n x) 2
  have hAle : (∫⁻ x, H x ^ 2 ∂μ) ≤ B ^ 2 := by
    rw [hsup]
    exact iSup_le hsqle
  calc (∫⁻ x, H x ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ (B ^ 2) ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hAle (by norm_num)
    _ = B := by
        rw [← ENNReal.rpow_natCast B 2, ← ENNReal.rpow_mul]
        norm_num

/-! ## The superposition estimate -/

variable {Y : Type*} [NormedAddCommGroup Y]

/-- **A superposition is bounded by the superposition of the bounds.**  If a profile is dominated
pointwise by the total mass of a two-parameter family, and each slice of that family has `L²` norm
at most `w s`, then the profile has `L²` norm at most `∫ w`.  This is the operator-free form of the
step that turns a resolvent written as a Laplace transform into an `L²` bound: each transform slice
is estimated separately and the slices are summed in the transform parameter. -/
theorem lintegral_sq_superposition_le [SigmaFinite μ] [SFinite ν]
    {Φ : α → Y} {Ψ : α → β → Y} {w : β → ℝ≥0∞}
    (hmeas : Measurable (Function.uncurry fun x s => ‖Ψ x s‖ₑ))
    (hΦ : ∀ x, ‖Φ x‖ₑ ≤ ∫⁻ s, ‖Ψ x s‖ₑ ∂ν)
    (hslice : ∀ s, (∫⁻ x, ‖Ψ x s‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤ w s) :
    (∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤ ∫⁻ s, w s ∂ν := by
  have hstep : (∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, (∫⁻ s, ‖Ψ x s‖ₑ ∂ν) ^ 2 ∂μ :=
    lintegral_mono fun x => pow_le_pow_left' (hΦ x) 2
  calc (∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ x, (∫⁻ s, ‖Ψ x s‖ₑ ∂ν) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hstep (by norm_num)
    _ ≤ ∫⁻ s, (∫⁻ x, ‖Ψ x s‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ∂ν :=
        lintegral_sq_lintegral_le hmeas
    _ ≤ ∫⁻ s, w s ∂ν := lintegral_mono hslice

end GaloisForLFunctions.HTGeometry
