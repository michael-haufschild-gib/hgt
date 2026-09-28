import GaloisForLFunctions.RHTower.Sieve.MertensRiemannUniform
import GaloisForLFunctions.RHTower.Sieve.LipschitzBoundCalculus

/-!
# Prime sums against affine and affine-over-`(1-α)` envelopes

Special cases of the uniform Mertens–Riemann theorem used for the discarded Harman densities:
`∑_{y^a < p ≤ y^b} P(log p/log y)/p ≤ ∫_a^b P(α)/α dα + η` eventually, for `P(α) = A + Bα` and
`P(α) = (A + Bα)/(1-α)` (`b < 1`), and `∑_{y^a < p ≤ y^b} 1/p ≤ log(b/a) + η`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

theorem eventually_primeScaleSum_le_integral_add {a b M L η : ℝ} {P : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hη : 0 < η) (hL : 0 ≤ L) (hM : ∀ x ∈ Set.Icc a b, |P x| ≤ M)
    (hLip : LipschitzBound P (Set.Icc a b) L) :
    ∀ᶠ y : ℝ in atTop, primeScaleSum y a b P ≤ (∫ x in a..b, P x / x) + η := by
  filter_upwards [eventually_abs_primeScaleSum_sub_integral_le (a₀ := a) (b₀ := b) (M := M)
    (L := L) ha hη hL] with y hy
  have := hy a b le_rfl hab le_rfl P hM hLip
  linarith [(abs_le.mp this).2]

theorem eventually_primeScaleSum_affine_le {a b A B q η : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hη : 0 < η) (hq : ∫ x in a..b, (A + B * x) / x ≤ q) :
    ∀ᶠ y : ℝ in atTop, primeScaleSum y a b (fun x => A + B * x) ≤ q + η := by
  have hLip : LipschitzBound (fun x => A + B * x) (Set.Icc a b) |B| := lipschitzBound_affine A B _
  have hM : ∀ x ∈ Set.Icc a b, |A + B * x| ≤ |A| + |B| * b := by
    intro x hx
    have hx0 : 0 ≤ x := ha.le.trans hx.1
    calc |A + B * x| ≤ |A| + |B * x| := abs_add_le _ _
      _ = |A| + |B| * x := by rw [abs_mul, abs_of_nonneg hx0]
      _ ≤ |A| + |B| * b := by gcongr; exact hx.2
  filter_upwards [eventually_primeScaleSum_le_integral_add ha hab hη (abs_nonneg B) hM hLip]
    with y hy
  linarith

theorem eventually_primeScaleSum_affine_div_one_sub_le {a b A B q η : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hη : 0 < η) (hq : ∫ x in a..b, (A + B * x) / (1 - x) / x ≤ q) :
    ∀ᶠ y : ℝ in atTop, primeScaleSum y a b (fun x => (A + B * x) / (1 - x)) ≤ q + η := by
  have hb1 : 0 < 1 - b := by linarith
  have hsplit : ∀ x, x ≠ 1 → (A + B * x) / (1 - x) = -B + (A + B) * (1 / (1 + (-1) * x)) := by
    intro x hx
    have : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
    rw [show 1 + (-1) * x = 1 - x by ring]
    field_simp
    ring
  have hden : ∀ x ∈ Set.Icc a b, 1 - b ≤ 1 + (-1) * x := fun x hx => by linarith [hx.2]
  have hLip0 := (lipschitzBound_inv_affine (p := 1) (q := -1) hb1 hden).const_mul (A + B)
  have hLip : LipschitzBound (fun x => (A + B * x) / (1 - x)) (Set.Icc a b)
      (|A + B| * (|(-1 : ℝ)| / (1 - b) ^ 2)) := by
    intro x hx z hz
    simp only
    rw [hsplit x (by linarith [hx.2]), hsplit z (by linarith [hz.2])]
    have := hLip0 x hx z hz
    simp only at this
    rw [show -B + (A + B) * (1 / (1 + -1 * x)) - (-B + (A + B) * (1 / (1 + -1 * z)))
      = (A + B) * (1 / (1 + -1 * x)) - (A + B) * (1 / (1 + -1 * z)) by ring]
    exact this
  have hM : ∀ x ∈ Set.Icc a b, |(A + B * x) / (1 - x)| ≤ (|A| + |B| * b) / (1 - b) := by
    intro x hx
    have hx0 : 0 ≤ x := ha.le.trans hx.1
    have h1x : 1 - b ≤ 1 - x := by linarith [hx.2]
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - x)]
    have hnum : |A + B * x| ≤ |A| + |B| * b := by
      calc |A + B * x| ≤ |A| + |B * x| := abs_add_le _ _
        _ = |A| + |B| * x := by rw [abs_mul, abs_of_nonneg hx0]
        _ ≤ |A| + |B| * b := by gcongr; exact hx.2
    calc |A + B * x| / (1 - x) ≤ (|A| + |B| * b) / (1 - x) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ (|A| + |B| * b) / (1 - b) :=
          div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (by linarith))) hb1 h1x
  filter_upwards [eventually_primeScaleSum_le_integral_add ha hab hη
    (mul_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) (sq_nonneg _))) hM hLip] with y hy
  linarith

/-- Mertens' sum over `(y^a, y^b]` is eventually at most `log(b/a) + η`. -/
theorem eventually_sum_prime_inv_rpow_le {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop,
      ∑ p ∈ (Finset.Ioc ⌊y ^ a⌋₊ ⌊y ^ b⌋₊).filter Nat.Prime, 1 / (p : ℝ) ≤ log (b / a) + η := by
  have hlog : ∀ᶠ y : ℝ in atTop,
      (4 * mertensSecondErrorConst + 4) / (a * η) ≤ log y :=
    tendsto_log_atTop.eventually_ge_atTop _
  have h4 : ∀ᶠ y : ℝ in atTop, 4 ≤ y ^ a := (tendsto_rpow_atTop ha).eventually_ge_atTop 4
  filter_upwards [hlog, h4, eventually_gt_atTop (1 : ℝ)] with y hly hy4 hy1
  have hm := abs_sum_prime_inv_rpow_sub_log_le ha hy1 hy4 le_rfl hab
  have hly0 : 0 < log y := Real.log_pos hy1
  have hE : (4 * mertensSecondErrorConst + 4) / (a * log y) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hly
    nlinarith
  linarith [(abs_le.mp hm).2]

/-- The envelope form `P = (A + Bα)/(1-α)` given abstractly. -/
theorem eventually_primeScaleSum_le_of_affine_div_one_sub {a b q η : ℝ} {P : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hη : 0 < η)
    (hP : ∃ A B : ℝ, ∀ x, P x = (A + B * x) / (1 - x)) (hq : ∫ x in a..b, P x / x ≤ q) :
    ∀ᶠ y : ℝ in atTop, primeScaleSum y a b P ≤ q + η := by
  obtain ⟨A, B, hPAB⟩ := hP
  have hPeq : P = fun x => (A + B * x) / (1 - x) := funext hPAB
  subst hPeq
  exact eventually_primeScaleSum_affine_div_one_sub_le ha hab hb hη hq

/-- The affine envelope form given abstractly. -/
theorem eventually_primeScaleSum_le_of_affine {a b q η : ℝ} {P : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hη : 0 < η) (hP : ∃ A B : ℝ, ∀ x, P x = A + B * x)
    (hq : ∫ x in a..b, P x / x ≤ q) :
    ∀ᶠ y : ℝ in atTop, primeScaleSum y a b P ≤ q + η := by
  obtain ⟨A, B, hPAB⟩ := hP
  have hPeq : P = fun x => A + B * x := funext hPAB
  subst hPeq
  exact eventually_primeScaleSum_affine_le ha hab hη hq

/-- Mertens' sums over `(y^α, y^β]` are at most `log(β/α) + 1`, uniformly in
`a₀ ≤ α ≤ β`, eventually. -/
theorem eventually_sum_prime_inv_rpow_le_uniform {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ y : ℝ in atTop, ∀ α β : ℝ, a₀ ≤ α → α ≤ β →
      ∑ p ∈ (Finset.Ioc ⌊y ^ α⌋₊ ⌊y ^ β⌋₊).filter Nat.Prime, 1 / (p : ℝ) ≤ log (β / α) + 1 := by
  have hlog : ∀ᶠ y : ℝ in atTop, (4 * mertensSecondErrorConst + 4) / a₀ ≤ log y :=
    tendsto_log_atTop.eventually_ge_atTop _
  have h4 : ∀ᶠ y : ℝ in atTop, 4 ≤ y ^ a₀ := (tendsto_rpow_atTop ha₀).eventually_ge_atTop 4
  filter_upwards [hlog, h4, eventually_gt_atTop (1 : ℝ)] with y hly hy4 hy1
  intro α β hα hαβ
  have hm := abs_sum_prime_inv_rpow_sub_log_le ha₀ hy1 hy4 hα hαβ
  have hly0 : 0 < log y := Real.log_pos hy1
  have hE : (4 * mertensSecondErrorConst + 4) / (a₀ * log y) ≤ 1 := by
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ ha₀] at hly
    linarith
  linarith [(abs_le.mp hm).2]

end

end RHTower.Sieve
