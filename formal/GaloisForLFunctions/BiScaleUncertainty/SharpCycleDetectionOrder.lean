import GaloisForLFunctions.BiScaleUncertainty.StrictCopyCycleCharge
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The exact first order detecting a distant copy's sign

For a literal smooth seed with open unit correlation support and gap T > 2,
a closed product of length n distinguishes opposite nonzero copy amplitudes
exactly when n > T. One outer edge and n-1 equal inner edges attain the bound.
Exponentially attenuated copies give the same sharp order for a polar-distinct pair.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
open SeparatedCycle (rawProduct)
set_option autoImplicit false

/-- Exact value in the positive outer packet, parametrized by its open error interval. -/
theorem source_right (T : Ioi (2 : ℝ)) (a : ℝ) (e : Ioo (-1 : ℝ) 1) :
    autocorr (source T a) ((T : ℝ) + e) = -a * autocorr seed e := by
  have hz : autocorr seed ((T : ℝ) + e) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr
      ((by linarith only [show (2 : ℝ) < T from T.property, e.property.1] :
        1 ≤ (T : ℝ) + e).trans (le_abs_self _))
  have hr : autocorr seed ((T : ℝ) + e + T) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr
      ((by linarith only [show (2 : ℝ) < T from T.property, e.property.1] :
        1 ≤ (T : ℝ) + e + T).trans (le_abs_self _))
  rw [source_correlation, hz, hr, add_sub_cancel_left]
  ring

def detector (T : Ioi (2 : ℝ)) (k : ℕ) : List ℝ :=
  ((T : ℝ) - T / (k + 1)) :: List.replicate k (-(T : ℝ) / (k + 1))

theorem detector_length (T : Ioi (2 : ℝ)) (k : ℕ) : (detector T k).length = k + 1 := by
  simp [detector]

theorem detector_closed (T : Ioi (2 : ℝ)) (k : ℕ) : (detector T k).sum = 0 := by
  have hn : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [detector, List.sum_cons, List.sum_replicate, nsmul_eq_mul]
  field_simp [hn]
  ring

private theorem step_bounds (T : Ioi (2 : ℝ)) (k : ℕ) (h : (T : ℝ) < (k : ℝ) + 1) :
    0 < (T : ℝ) / (k + 1) ∧ (T : ℝ) / (k + 1) < 1 := by
  have hn : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  exact ⟨div_pos (by linarith only [show (2 : ℝ) < T from T.property]) hn,
    (div_lt_iff₀ hn).mpr (by simpa only [one_mul] using h)⟩

private theorem detector_charge (T : Ioi (2 : ℝ)) (k : ℕ) (h : (T : ℝ) < (k : ℝ) + 1) :
    packetCharge T (detector T k) = 1 := by
  obtain ⟨hp, hs⟩ := step_bounds T k h
  have hi : |-(T : ℝ) / (k + 1)| < 1 := by
    simpa only [neg_div, abs_neg, abs_of_pos hp] using hs
  have ho : ¬ |(T : ℝ) - T / (k + 1)| < 1 := by
    have hb : 1 < (T : ℝ) - T / (k + 1) := by
      linarith only [show (2 : ℝ) < T from T.property, hs]
    exact not_lt_of_ge (hb.le.trans (le_abs_self _))
  have he : |((T : ℝ) - T / (k + 1)) - T| < 1 := by
    rw [show ((T : ℝ) - T / (k + 1)) - T = -(T : ℝ) / (k + 1) by ring]
    exact hi
  have hzero : packetIndex T (-(T : ℝ) / (k + 1)) = 0 := by
    simp only [packetIndex, hi, if_true]
  have hone : packetIndex T ((T : ℝ) - T / (k + 1)) = 1 := by
    simp only [packetIndex, ho, if_false, he, if_true]
  simp [packetCharge, detector, hzero, hone]

private theorem detector_product_ne_zero (T : Ioi (2 : ℝ)) (a : ℝ) (ha : a ≠ 0)
    (k : ℕ) (h : (T : ℝ) < (k : ℝ) + 1) : rawProduct (source T a) (detector T k) ≠ 0 := by
  obtain ⟨hp, hs⟩ := step_bounds T k h
  have hi : |-(T : ℝ) / (k + 1)| < 1 := by
    simpa only [neg_div, abs_neg, abs_of_pos hp] using hs
  have hmem : -(T : ℝ) / (k + 1) ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hi
  have hn := (seed_correlation_ne_zero_iff (-(T : ℝ) / (k + 1))).mpr hi
  have hc := source_central T a ⟨-(T : ℝ) / (k + 1), hmem⟩
  have ho : autocorr (source T a) ((T : ℝ) - T / (k + 1)) =
      -a * autocorr seed (-(T : ℝ) / (k + 1)) := by
    simpa only [sub_eq_add_neg, neg_div] using source_right T a ⟨-(T : ℝ) / (k + 1), hmem⟩
  simp only [rawProduct, detector, List.map_cons, List.map_replicate,
    List.prod_cons, List.prod_replicate]
  rw [ho, hc]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hn)
    (pow_ne_zero k (mul_ne_zero (by positivity : (1 + a ^ 2 : ℝ) ≠ 0) hn))

def Detects (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) : Prop :=
  ∃ l : List ℝ, l.length = n ∧ l.sum = 0 ∧
    rawProduct (source T (-a)) l ≠ rawProduct (source T a) l

/-- The sharp detection classification includes zero amplitude and every boundary order. -/
theorem detects_iff (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) :
    Detects T a n ↔ a ≠ 0 ∧ (T : ℝ) < n := by
  constructor
  · rintro ⟨l, hl, hs, hd⟩
    refine ⟨?_, ?_⟩
    · intro ha
      subst a
      exact hd (by rw [neg_zero])
    · rcases closed_product_same_or_order T a ⟨l, hs⟩ with he | ho
      · exact False.elim (hd he)
      · simpa only [hl] using ho
  · rintro ⟨ha, ht⟩
    cases n with
    | zero =>
      have hz : (T : ℝ) < 0 := by simpa using ht
      linarith only [hz, show (2 : ℝ) < T from T.property]
    | succ k =>
      have h : (T : ℝ) < (k : ℝ) + 1 := by exact_mod_cast ht
      refine ⟨detector T k, detector_length T k, detector_closed T k, ?_⟩
      rw [rawProduct_sign, detector_charge T k h]
      simp only [zpow_one, neg_one_mul]
      intro he
      apply detector_product_ne_zero T a ha k h
      linarith

theorem detects_iff_floor (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) :
    Detects T a n ↔ a ≠ 0 ∧ ⌊(T : ℝ)⌋₊ < n := by
  rw [detects_iff,
    Nat.floor_lt (by linarith only [show (2 : ℝ) < T from T.property] : 0 ≤ (T : ℝ))]

def firstOrder (T : Ioi (2 : ℝ)) : ℕ := ⌊(T : ℝ)⌋₊ + 1

theorem firstOrder_detects_iff (T : Ioi (2 : ℝ)) (a : ℝ) :
    Detects T a (firstOrder T) ↔ a ≠ 0 := by
  rw [detects_iff_floor]
  simp [firstOrder]

theorem lower_orders_agree (T : Ioi (2 : ℝ)) (a : ℝ) (n : Fin (firstOrder T)) :
    ¬ Detects T a n := by
  rw [detects_iff_floor]
  intro h
  have hn := n.isLt
  dsimp [firstOrder] at hn
  omega

def polarAmplitude (T : Ioi (2 : ℝ)) : ℝ := Real.exp (-(T : ℝ) / 2)

theorem polarAmplitude_pos (T : Ioi (2 : ℝ)) : 0 < polarAmplitude T := Real.exp_pos _

theorem source_polar_zero (T : Ioi (2 : ℝ)) :
    normalizedPolarMoment (source T (polarAmplitude T)) = 0 :=
  normalizedPolarMoment_polarCopy seedBump.contDiff seed.hasCompactSupport T

theorem source_polar_plus (T : Ioi (2 : ℝ)) :
    normalizedPolarMoment (source T (-polarAmplitude T)) = 2 * normalizedPolarMoment seed := by
  have hf : ContDiff ℝ 2 (seed : ℝ → ℝ) := seedBump.contDiff
  have hs (x : ℝ) (hx : 1 < |x|) : autocorr seed x = 0 :=
    (seed_correlation_eq_zero_iff x).mpr hx.le
  have ht : (1 : ℝ) < T := by linarith only [show (2 : ℝ) < T from T.property]
  have hm := normalizedPolarMoment_subtractCopy hf seed.hasCompactSupport seed_mass_pos hs ht
    (polarAmplitude T)
  have hp := normalizedPolarMoment_subtractCopy hf seed.hasCompactSupport seed_mass_pos hs ht
    (-polarAmplitude T)
  change normalizedPolarMoment (source T (polarAmplitude T)) = _ at hm
  change normalizedPolarMoment (source T (-polarAmplitude T)) = _ at hp
  have hc : copyMixingCoefficient (-polarAmplitude T) = -copyMixingCoefficient (polarAmplitude T) := by
    simp only [copyMixingCoefficient, neg_sq, neg_div]
  rw [source_polar_zero] at hm
  rw [hc] at hp
  nlinarith only [hm, hp]

/-- Concrete smooth polar-distinct sources have the exact prescribed detection threshold. -/
theorem sharp_polar_pair (T : Ioi (2 : ℝ)) :
    ∃ f g : C_c(ℝ, ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (g : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ autocorr g 0 = autocorr f 0 ∧
      normalizedPolarMoment f = 0 ∧ 0 < normalizedPolarMoment g ∧
      ∀ n : ℕ, (∃ l : List ℝ, l.length = n ∧ l.sum = 0 ∧ rawProduct g l ≠ rawProduct f l) ↔
        (T : ℝ) < n := by
  refine ⟨source T (polarAmplitude T), source T (-polarAmplitude T),
    source_smooth _ _, source_smooth _ _, source_mass_pos _ _, ?_, source_polar_zero T, ?_, ?_⟩
  · simp only [source_mass, neg_sq]
  · rw [source_polar_plus]
    exact mul_pos (by positivity) seed_polar_pos
  · intro n
    change Detects T (polarAmplitude T) n ↔ (T : ℝ) < n
    constructor
    · intro h
      exact ((detects_iff T (polarAmplitude T) n).mp h).2
    · intro h
      exact (detects_iff T (polarAmplitude T) n).mpr ⟨(polarAmplitude_pos T).ne', h⟩

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle
