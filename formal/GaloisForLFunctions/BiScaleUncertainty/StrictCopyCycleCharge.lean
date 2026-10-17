import GaloisForLFunctions.BiScaleUncertainty.UnitCorrelationBump
import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopyCycleCharge

/-!
# Strict packet-charge bounds for a literal smooth source

The seed has exactly open unit correlation support. Opposite copies separated
by a gap greater than two differ only by packet parity. Every nonzero closed
product with nonzero packet charge has length strictly greater than the gap.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
open SeparatedCycle (rawProduct)
set_option autoImplicit false

def source (T : Ioi (2 : ℝ)) (a : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨subtractCopy seed a T, continuous_subtractCopy seed.continuous a T⟩,
    hasCompactSupport_subtractCopy seed.hasCompactSupport a T⟩

theorem source_smooth (T : Ioi (2 : ℝ)) (a : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (source T a : ℝ → ℝ) :=
  contDiff_subtractCopy seed_smooth a T

theorem source_mass (T : Ioi (2 : ℝ)) (a : ℝ) :
    autocorr (source T a) 0 = (1 + a ^ 2) * autocorr seed 0 :=
  autocorr_subtractCopy_zero (f := (seed : ℝ → ℝ)) seed.continuous seed.hasCompactSupport
    (D := 1) (fun x hx => (seed_correlation_eq_zero_iff x).mpr hx.le)
    (by linarith only [T.property]) a

theorem source_mass_pos (T : Ioi (2 : ℝ)) (a : ℝ) : 0 < autocorr (source T a) 0 := by
  rw [source_mass]
  exact mul_pos (by positivity) seed_mass_pos

theorem source_correlation (T : Ioi (2 : ℝ)) (a x : ℝ) :
    autocorr (source T a) x = (1 + a ^ 2) * autocorr seed x -
      a * (autocorr seed (x - T) + autocorr seed (x + T)) :=
  autocorr_subtractCopy (f := (seed : ℝ → ℝ)) seed.continuous seed.hasCompactSupport a T x

theorem source_central (T : Ioi (2 : ℝ)) (a : ℝ) (x : Ioo (-1 : ℝ) 1) :
    autocorr (source T a) x = (1 + a ^ 2) * autocorr seed x := by
  have hl : autocorr seed ((x : ℝ) - T) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr
      ((by linarith only [T.property, x.property.2] : 1 ≤ -((x : ℝ) - T)).trans (neg_le_abs _))
  have hr : autocorr seed ((x : ℝ) + T) = 0 :=
    (seed_correlation_eq_zero_iff _).mpr
      ((by linarith only [T.property, x.property.1] : 1 ≤ (x : ℝ) + T).trans (le_abs_self _))
  rw [source_correlation, hl, hr]
  ring

def packetIndex (T : Ioi (2 : ℝ)) (x : ℝ) : ℤ :=
  if |x| < 1 then 0 else if |x - T| < 1 then 1 else -1

theorem source_sign (T : Ioi (2 : ℝ)) (a x : ℝ) :
    autocorr (source T (-a)) x = (-1 : ℝ) ^ packetIndex T x * autocorr (source T a) x := by
  by_cases hx : |x| < 1
  · have hxc : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hx
    have hp := source_central T a ⟨x, hxc⟩
    have hn := source_central T (-a) ⟨x, hxc⟩
    simp only [packetIndex, hx, if_true, zpow_zero, one_mul]
    rw [hn, hp, neg_sq]
  · have hz := (seed_correlation_eq_zero_iff x).mpr (le_of_not_gt hx)
    rw [source_correlation, source_correlation]
    by_cases hy : |x - T| < 1 <;> simp [packetIndex, hx, hy, hz]

private theorem packet_distance (T : Ioi (2 : ℝ)) (a x : ℝ)
    (hn : autocorr (source T a) x ≠ 0) : |x - (packetIndex T x : ℝ) * T| < 1 := by
  by_cases hx : |x| < 1
  · simp [packetIndex, hx]
  · by_cases hy : |x - T| < 1
    · simp [packetIndex, hx, hy]
    · have hz : |x + T| < 1 := by
        by_contra hz
        apply hn
        rw [source_correlation,
          (seed_correlation_eq_zero_iff x).mpr (le_of_not_gt hx),
          (seed_correlation_eq_zero_iff (x - T)).mpr (le_of_not_gt hy),
          (seed_correlation_eq_zero_iff (x + T)).mpr (le_of_not_gt hz)]
        ring
      simpa [packetIndex, hx, hy] using hz

def packetCharge (T : Ioi (2 : ℝ)) (l : List ℝ) : ℤ := (l.map (packetIndex T)).sum

theorem rawProduct_sign (T : Ioi (2 : ℝ)) (a : ℝ) (l : List ℝ) :
    rawProduct (source T (-a)) l = (-1 : ℝ) ^ packetCharge T l * rawProduct (source T a) l := by
  induction l with
  | nil => simp [rawProduct, packetCharge]
  | cons x l ih =>
    change autocorr (source T (-a)) x * rawProduct (source T (-a)) l =
      (-1 : ℝ) ^ (packetIndex T x + packetCharge T l) *
        (autocorr (source T a) x * rawProduct (source T a) l)
    rw [source_sign, ih, zpow_add₀ (by norm_num)]
    ring

private theorem error_cons (T : Ioi (2 : ℝ)) (x : ℝ) (l : List ℝ) :
    (x :: l).sum - (packetCharge T (x :: l) : ℝ) * T =
      (x - (packetIndex T x : ℝ) * T) + (l.sum - (packetCharge T l : ℝ) * T) := by
  simp only [packetCharge, List.map_cons, List.sum_cons, Int.cast_add]
  ring

private theorem sum_error_le_length (T : Ioi (2 : ℝ)) (l : List ℝ)
    (h : ∀ x ∈ l, |x - (packetIndex T x : ℝ) * T| ≤ 1) :
    |l.sum - (packetCharge T l : ℝ) * T| ≤ (l.length : ℝ) := by
  induction l with
  | nil => simp [packetCharge]
  | cons x l ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    rw [error_cons]
    calc
      _ ≤ |x - (packetIndex T x : ℝ) * T| + |l.sum - (packetCharge T l : ℝ) * T| :=
        abs_add_le _ _
      _ ≤ 1 + (l.length : ℝ) := add_le_add hx hl
      _ = ((x :: l).length : ℝ) := by simp [add_comm]

private theorem sum_error_lt_length (T : Ioi (2 : ℝ)) (l : List ℝ) (hl : l ≠ [])
    (h : ∀ x ∈ l, |x - (packetIndex T x : ℝ) * T| < 1) :
    |l.sum - (packetCharge T l : ℝ) * T| < (l.length : ℝ) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons x l =>
    have hx := h x (by simp)
    have ht := sum_error_le_length T l (fun y hy => (h y (by simp [hy])).le)
    rw [error_cons]
    calc
      _ ≤ |x - (packetIndex T x : ℝ) * T| + |l.sum - (packetCharge T l : ℝ) * T| :=
        abs_add_le _ _
      _ < 1 + (l.length : ℝ) := add_lt_add_of_lt_of_le hx ht
      _ = ((x :: l).length : ℝ) := by simp [add_comm]

/-- Strict support gives a strict error bound for every nonempty nonzero product. -/
theorem packet_product_error (T : Ioi (2 : ℝ)) (a : ℝ) (l : List ℝ) :
    l = [] ∨ rawProduct (source T a) l = 0 ∨
      |l.sum - (packetCharge T l : ℝ) * T| < (l.length : ℝ) := by
  by_cases hl : l = []
  · exact Or.inl hl
  by_cases hp : rawProduct (source T a) l = 0
  · exact Or.inr (Or.inl hp)
  right
  right
  apply sum_error_lt_length T l hl
  intro x hx
  apply packet_distance T a x
  intro hz
  apply hp
  exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨x, hx, hz⟩)

/-- Any closed product that distinguishes the two signs has order strictly exceeding the gap. -/
theorem closed_product_same_or_order (T : Ioi (2 : ℝ)) (a : ℝ)
    (l : {l : List ℝ // l.sum = 0}) :
    rawProduct (source T (-a)) l.1 = rawProduct (source T a) l.1 ∨ (T : ℝ) < l.1.length := by
  by_cases he : rawProduct (source T (-a)) l.1 = rawProduct (source T a) l.1
  · exact Or.inl he
  right
  have hp : rawProduct (source T a) l.1 ≠ 0 := by
    intro hz
    apply he
    rw [rawProduct_sign, hz, mul_zero]
  have hq : packetCharge T l.1 ≠ 0 := by
    intro hz
    apply he
    rw [rawProduct_sign, hz, zpow_zero, one_mul]
  have hl : l.1 ≠ [] := by
    intro hz
    apply he
    simp [rawProduct, hz]
  have hb := ((packet_product_error T a l.1).resolve_left hl).resolve_left hp
  rw [l.2, zero_sub, abs_neg] at hb
  have hT0 : 0 ≤ (T : ℝ) := by linarith only [T.property]
  have hi : packetCharge T l.1 ≤ -1 ∨ 1 ≤ packetCharge T l.1 := by omega
  have ht : (T : ℝ) ≤ |(packetCharge T l.1 : ℝ) * T| := by
    rcases hi with hi | hi
    · have hi' : (packetCharge T l.1 : ℝ) ≤ -1 := by exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hi' hT0
      have ha := neg_le_abs ((packetCharge T l.1 : ℝ) * T)
      linarith
    · have hi' : (1 : ℝ) ≤ packetCharge T l.1 := by exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hi' hT0
      have ha := le_abs_self ((packetCharge T l.1 : ℝ) * T)
      linarith
  exact ht.trans_lt hb

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle
