import Zeta23.RvM.MainTerm
import Zeta23.GammaFacts.Complete
import Zeta23.Statement.SeamClosed
import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteCarriersAreRealAboveTheirHorizon

/-!
# The zeros of ζ have the sharp local density

The count input of the local camera. In every height interval `[x, y]` far enough up, the zeros of
`ζ` number at most `(y − x + 3)(log((y + 2)/2π) + 6/(x − 2))/2π + A log(y + 2) + 1`
(`exists_card_le_sharp`): the density is the Riemann–von Mangoldt density `(1/2π) log(t/2π)` with
its exact constant, and the error is `O(log y)`.

The proof is the argument principle on the rectangle between two good heights `T₁ ≤ x ≤ y ≤ T₂`
(`Zeta23.RvM.N_eq_halfContour_completedZeta`). The contour splits into a ζ-part and a `Γ_ℝ`-part
(`halfContour_completedZeta_split`). The ζ-part is `O(log T)` by Backlund's horizontal bound and the
vertical bound on `Re s = 2` (`backlund_horizontal`, `vertical_two`). The `Γ_ℝ`-part is the integral
of the density `μ(t) = (1/π) Re ψ_ℝ(½ + it)` (`gamma_side`). Pointwise
`μ(t) ≤ (log((t + 1)/2π) + 6/t)/2π` (`mu_le`), from the digamma asymptotics on the line
(`re_arch_line_le`).

* **Good-height count** (`ncount_le_of_goodHeight`). For good heights `T₀ ≤ T₁ < T₂`,
  `N(T₁, T₂) ≤ (T₂ − T₁)(log((T₂ + 1)/2π) + 6/T₁)/2π + |C_B|(log T₁ + log T₂) + 1`.
* **The sharp local count** (`exists_card_le_sharp`), for distinct zeros in a closed height
  interval, in the form consumed by the local camera.
* **Centred at a height** (`exists_card_le_sharp_centred`). The zeros at height distance `≤ R` from
  `X` inside `[x, y]` number at most `D (y − x) + C₀` with
  `D = (log((X + R + 2)/2π) + 6/(X − R − 2))/2π` and `C₀ = 3D + A log(X + R + 2) + 1`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 Zeta23.RvM

/-- **The density of the Γ-side.** `μ(t) ≤ (log((t + 1)/2π) + 6/t)/2π` for `t ≥ 4`. -/
theorem mu_le {τ : ℝ} (hτ : 4 ≤ τ) :
    mu τ ≤ (Real.log ((τ + 1) / (2 * Real.pi)) + 6 / τ) / (2 * Real.pi) := by
  have hτ0 : 0 < τ := by linarith
  have h := re_arch_line_le (τ := τ) (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h
  have e : linePt τ / 2 = 1 / 4 + Complex.I * τ / 2 := by
    rw [linePt]; push_cast; ring
  rw [e] at h
  have hre : (Complex.digamma (1 / 4 + Complex.I * τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re / 2 - Real.log Real.pi / 2 := by
    simp [Complex.sub_re]
  rw [hre] at h
  unfold mu
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [le_div_iff₀ hπ]
  have e2 : (1 / (2 * Real.pi) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re -
      Real.log Real.pi / (2 * Real.pi)) * (2 * Real.pi) =
      (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re - Real.log Real.pi := by
    field_simp
  rw [e2]
  linarith

theorem zeroMult_ge_one {ρ : ℂ} (h : IsNontrivialZero ρ) : 1 ≤ zeroMult ρ :=
  zetaSeam.one_le_mult ρ h

/-- Distinct zeros in a window are at most the count with multiplicity. -/
theorem card_le_ncount {T₁ T₂ : ℝ} (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ zerosIn T₁ T₂) :
    s.card ≤ Ncount T₁ T₂ := by
  classical
  have hfin := zerosIn_finite T₁ T₂
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc s.card = ∑ z ∈ s, 1 := (Finset.card_eq_sum_ones s)
    _ ≤ ∑ z ∈ s, zeroMult z := Finset.sum_le_sum fun z hz => zeroMult_ge_one (hs z hz).1
    _ ≤ ∑ z ∈ hfin.toFinset, zeroMult z := Finset.sum_le_sum_of_subset fun z hz =>
        (Set.Finite.mem_toFinset hfin).mpr (hs z hz)

/-- **Count between good heights.** -/
theorem ncount_le_of_goodHeight {CB TB : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    {T₁ T₂ : ℝ} (hT₁ : max TB 8 ≤ T₁) (h12 : T₁ < T₂) (hg1 : GoodHeight T₁)
    (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) ≤ (T₂ - T₁) * ((Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) /
      (2 * Real.pi)) + |CB| * (Real.log T₁ + Real.log T₂) + 1 := by
  have h8 : 8 ≤ T₁ := le_trans (le_max_right _ _) hT₁
  have hTB : TB ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have h1 : 1 ≤ T₁ := by linarith
  have hN := N_eq_halfContour_completedZeta h1 h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1 h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have h5 : (Ncount T₁ T₂ : ℝ) =
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im + ∫ t in T₁..T₂, mu t := by
    rw [hN, hsplit, Complex.add_im, mul_add, hgam]
  -- the ζ-part
  have hbk1 := hB T₁ hTB hg1
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := vertical_two T₁ T₂
  have hlog₁ : 0 ≤ Real.log T₁ := Real.log_nonneg h1
  have hlog₂ : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hζ : |(halfContour (logDeriv riemannZeta) T₁ T₂).im| ≤
      |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    unfold halfContour
    rw [Complex.sub_im, Complex.add_im]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im =
        (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    rw [hmulI]
    have e1 : CB * Real.log T₁ ≤ |CB| * Real.log T₁ :=
      mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁
    have e2 : CB * Real.log T₂ ≤ |CB| * Real.log T₂ :=
      mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂
    have t1 := abs_sub ((∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im +
      (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im)
      (∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
    have t2 := abs_add_le (∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
      (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im
    linarith
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hA : (1 / Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im ≤
      |CB| * (Real.log T₁ + Real.log T₂) + 1 := by
    have hle := (le_abs_self _).trans hζ
    have hπ0 : 0 < Real.pi := Real.pi_pos
    rw [one_div, inv_mul_le_iff₀ hπ0]
    have : 0 ≤ |CB| * (Real.log T₁ + Real.log T₂) := by positivity
    nlinarith
  -- the Γ-part
  have hB0 : ∀ τ ∈ Icc T₁ T₂, mu τ ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) /
      (2 * Real.pi) := fun τ hτ => by
    have hτ4 : 4 ≤ τ := by linarith [hτ.1]
    refine (mu_le hτ4).trans ?_
    have hpos : 0 < 2 * Real.pi := by positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((τ + 1) / (2 * Real.pi)) ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [hτ.2]) hpos.le)
    have h2' : 6 / τ ≤ 6 / T₁ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hτ.1
    linarith
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) h12.le
    ((mu_continuous gammaFacts).intervalIntegrable _ _) intervalIntegrable_const hB0
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  rw [h5]
  linarith

/-- **The sharp local count.** Far enough up, the distinct zeros of `ζ` with heights in `[x, y]`
number at most `(y − x + 3)(log((y + 2)/2π) + 6/(x − 2))/2π + A log(y + 2) + 1`. -/
theorem exists_card_le_sharp : ∃ T₀ A : ℝ, 8 ≤ T₀ ∧ 0 ≤ A ∧ ∀ x y : ℝ, T₀ ≤ x → x ≤ y →
    ∀ s : Finset ℂ, (∀ z ∈ s, IsNontrivialZero z ∧ z.im ∈ Icc x y) →
      (s.card : ℝ) ≤ (y - x + 3) * ((Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) /
        (2 * Real.pi)) + A * Real.log (y + 2) + 1 := by
  obtain ⟨CB, TB, hB⟩ := backlund_horizontal
  refine ⟨max TB 8 + 2, 2 * |CB|, by linarith [le_max_right TB 8], by positivity,
    fun x y hx hxy s hs => ?_⟩
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (x - 2)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight y
  have hT₁a : x - 2 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ x - 1 := by have := hT₁mem.2; linarith
  have hT₂a : y ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ y + 1 := hT₂mem.2
  have hT₁ : max TB 8 ≤ T₁ := by linarith
  have h8 : 8 ≤ T₁ := le_trans (le_max_right _ _) hT₁
  have h12 : T₁ < T₂ := by linarith
  have hcount := ncount_le_of_goodHeight hB hT₁ h12 hg1 hg2
  have hcard : (s.card : ℝ) ≤ Ncount T₁ T₂ := by
    exact_mod_cast card_le_ncount s fun z hz =>
      ⟨(hs z hz).1, by linarith [(hs z hz).2.1], by linarith [(hs z hz).2.2]⟩
  -- compare the constants
  have hpos : 0 < 2 * Real.pi := by positivity
  have hlogpos : 0 ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
  have hD1 : (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) ≤
      (Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((T₂ + 1) / (2 * Real.pi)) ≤ Real.log ((y + 2) / (2 * Real.pi)) :=
      Real.log_le_log (div_pos (by linarith) hpos)
        (div_le_div_of_nonneg_right (by linarith) hpos.le)
    have h2' : 6 / T₁ ≤ 6 / (x - 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hT₁a
    linarith
  have hD0 : 0 ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) := by
    have : 0 < 6 / T₁ := div_pos (by norm_num) (by linarith)
    exact div_nonneg (by linarith) hpos.le
  have hlen : T₂ - T₁ ≤ y - x + 3 := by linarith
  have hprod : (T₂ - T₁) * ((Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi)) ≤
      (y - x + 3) * ((Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) / (2 * Real.pi)) :=
    mul_le_mul hlen hD1 hD0 (by linarith)
  have hl1 : Real.log T₁ ≤ Real.log (y + 2) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log T₂ ≤ Real.log (y + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlogs : |CB| * (Real.log T₁ + Real.log T₂) ≤ 2 * |CB| * Real.log (y + 2) := by
    have := abs_nonneg CB
    nlinarith
  linarith

/-- **The sharp local count, centred at a height.** For `X − R ≥ T₀ + 0` with `R ≥ 0`, the
distinct zeros of `ζ` at height distance `≤ R` from `X` with heights in `[x, y]` number at most
`D (y − x) + C₀` with `D = (log((X + R + 2)/2π) + 6/(X − R − 2))/2π` and
`C₀ = 3D + A log(X + R + 2) + 1`. -/
theorem exists_card_le_sharp_centred : ∃ T₀ A : ℝ, 8 ≤ T₀ ∧ 0 ≤ A ∧
    ∀ X R : ℝ, 0 ≤ R → T₀ ≤ X - R → ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℂ,
      (∀ z ∈ s, IsNontrivialZero z ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ (Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) /
            (2 * Real.pi) * (y - x) +
          (3 * ((Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) / (2 * Real.pi)) +
            A * Real.log (X + R + 2) + 1) := by
  obtain ⟨T₀, A, hT₀, hA, hcount⟩ := exists_card_le_sharp
  refine ⟨T₀, A, hT₀, hA, fun X R hR hX x y hxy s hs => ?_⟩
  set D := (Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) / (2 * Real.pi) with hD
  have hpos : 0 < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D := by
    have hl : 0 ≤ Real.log ((X + R + 2) / (2 * Real.pi)) :=
      Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
    have : 0 < 6 / (X - R - 2) := div_pos (by norm_num) (by linarith)
    rw [hD]; exact div_nonneg (by linarith) hpos.le
  -- the effective interval `[x', y'] = [x, y] ∩ [X − R, X + R]`
  set x' := max x (X - R) with hx'
  set y' := min y (X + R) with hy'
  by_cases hne : x' ≤ y'
  · have hsub : ∀ z ∈ s, IsNontrivialZero z ∧ z.im ∈ Icc x' y' := fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := hs z hz
      rw [abs_le] at h2
      exact ⟨h1, max_le h3 (by linarith [h2.1]), le_min h4 (by linarith [h2.2])⟩
    have hx'T : T₀ ≤ x' := le_trans hX (le_max_right _ _)
    have hc := hcount x' y' hx'T hne s hsub
    have hDle : (Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) / (2 * Real.pi) ≤ D := by
      rw [hD]
      apply div_le_div_of_nonneg_right _ hpos.le
      have h1 : Real.log ((y' + 2) / (2 * Real.pi)) ≤ Real.log ((X + R + 2) / (2 * Real.pi)) :=
        Real.log_le_log (div_pos (by linarith) hpos)
          (div_le_div_of_nonneg_right (by linarith [min_le_right y (X + R)]) hpos.le)
      have h2 : 6 / (x' - 2) ≤ 6 / (X - R - 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith [le_max_right x (X - R)])
      linarith
    have hlen : y' - x' ≤ y - x := by
      linarith [min_le_left y (X + R), le_max_left x (X - R)]
    have hlog : Real.log (y' + 2) ≤ Real.log (X + R + 2) :=
      Real.log_le_log (by linarith) (by linarith [min_le_right y (X + R)])
    have hDy : 0 ≤ (Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) / (2 * Real.pi) := by
      have hl : 0 ≤ Real.log ((y' + 2) / (2 * Real.pi)) :=
        Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
      have : 0 < 6 / (x' - 2) := div_pos (by norm_num) (by linarith)
      exact div_nonneg (by linarith) hpos.le
    have hprod : (y' - x' + 3) * ((Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) /
        (2 * Real.pi)) ≤ D * (y - x) + 3 * D := by
      have := mul_le_mul (show y' - x' + 3 ≤ y - x + 3 by linarith) hDle hDy (by linarith)
      linarith
    have hAlog : A * Real.log (y' + 2) ≤ A * Real.log (X + R + 2) :=
      mul_le_mul_of_nonneg_left hlog hA
    linarith
  · -- the effective interval is empty, so is `s`
    have hempty : s = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => hne ?_
      obtain ⟨_, h2, h3, h4⟩ := hs z hz
      rw [abs_le] at h2
      exact (max_le h3 (by linarith [h2.1])).trans (le_min h4 (by linarith [h2.2]))
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hlogp : 0 ≤ Real.log (X + R + 2) := Real.log_nonneg (by linarith)
    have : 0 ≤ D * (y - x) := mul_nonneg hD0 (by linarith)
    have : 0 ≤ A * Real.log (X + R + 2) := mul_nonneg hA hlogp
    linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
