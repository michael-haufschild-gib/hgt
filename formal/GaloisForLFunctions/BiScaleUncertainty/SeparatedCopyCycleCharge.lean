import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopySquareClassification
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Parity

/-!
# Packet charge of separated-copy correlation products

Changing the sign of the distant copy multiplies each correlation product by
the parity of its integer packet charge. Nonzero products satisfy an exact
geometric charge bound. Closed products below the separation order have zero
charge and cannot distinguish the two copy signs.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
open SeparatedSquare (radius radius_pos)
set_option autoImplicit false

def gap (f : C_c(ℝ, ℝ)) (m : ℕ) : ℝ := (m + 2) * radius f + 1

theorem order_mul_radius_lt_gap (f : C_c(ℝ, ℝ)) (m : ℕ) :
    (m : ℝ) * radius f < gap f m := by
  have hD := radius_pos f
  dsimp [gap]
  linarith

theorem twice_radius_lt_gap (f : C_c(ℝ, ℝ)) (m : ℕ) :
    2 * radius f < gap f m := by
  have hm : 0 ≤ (m : ℝ) * radius f := mul_nonneg (Nat.cast_nonneg m) (radius_pos f).le
  dsimp [gap]
  nlinarith only [hm]

theorem radius_lt_gap (f : C_c(ℝ, ℝ)) (m : ℕ) : radius f < gap f m := by
  linarith only [radius_pos f, twice_radius_lt_gap f m]

theorem gap_pos (f : C_c(ℝ, ℝ)) (m : ℕ) : 0 < gap f m :=
  (radius_pos f).trans (radius_lt_gap f m)

private theorem outside (f : C_c(ℝ, ℝ)) {x : ℝ} (hx : radius f < |x|) :
    autocorr f x = 0 :=
  (exists_pos_autocorr_support_radius f.hasCompactSupport).choose_spec.2 x hx

def source (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨subtractCopy f a (gap f m), continuous_subtractCopy f.continuous a (gap f m)⟩,
    hasCompactSupport_subtractCopy f.hasCompactSupport a (gap f m)⟩

theorem source_mass (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) :
    autocorr (source f m a) 0 = (1 + a ^ 2) * autocorr f 0 :=
  autocorr_subtractCopy_zero (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
    (fun _ hx => outside f hx) (radius_lt_gap f m) a

theorem source_correlation (f : C_c(ℝ, ℝ)) (m : ℕ) (a x : ℝ) :
    autocorr (source f m a) x = (1 + a ^ 2) * autocorr f x -
      a * (autocorr f (x - gap f m) + autocorr f (x + gap f m)) :=
  autocorr_subtractCopy (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport a (gap f m) x

/-- Integer center of the active packet; arbitrary inactive lags receive a harmless label. -/
def packetIndex (f : C_c(ℝ, ℝ)) (m : ℕ) (x : ℝ) : ℤ :=
  if |x| ≤ radius f then 0 else if |x - gap f m| ≤ radius f then 1 else -1

/-- The literal source correlations transform by the parity of their packet labels. -/
theorem source_sign (f : C_c(ℝ, ℝ)) (m : ℕ) (a x : ℝ) :
    autocorr (source f m (-a)) x =
      (-1 : ℝ) ^ packetIndex f m x * autocorr (source f m a) x := by
  rw [source_correlation, source_correlation]
  by_cases hx : |x| ≤ radius f
  · have hb := abs_le.mp hx
    have hT := twice_radius_lt_gap f m
    have hl := outside f (lt_of_lt_of_le (by linarith : radius f < -(x - gap f m))
      (neg_le_abs _))
    have hr := outside f (lt_of_lt_of_le (by linarith : radius f < x + gap f m)
      (le_abs_self _))
    simp [packetIndex, hx, hl, hr]
  · have hz := outside f (lt_of_not_ge hx)
    by_cases hy : |x - gap f m| ≤ radius f <;>
      simp [packetIndex, hx, hy, hz]

private theorem packet_distance (f : C_c(ℝ, ℝ)) (m : ℕ) (a x : ℝ)
    (hn : autocorr (source f m a) x ≠ 0) :
    |x - (packetIndex f m x : ℝ) * gap f m| ≤ radius f := by
  by_cases hx : |x| ≤ radius f
  · simp [packetIndex, hx]
  · by_cases hy : |x - gap f m| ≤ radius f
    · simp [packetIndex, hx, hy]
    · have hz : |x + gap f m| ≤ radius f := by
        by_contra hz
        apply hn
        rw [source_correlation, outside f (lt_of_not_ge hx),
          outside f (lt_of_not_ge hy), outside f (lt_of_not_ge hz)]
        ring
      simpa [packetIndex, hx, hy] using hz

def rawProduct (f : C_c(ℝ, ℝ)) (l : List ℝ) : ℝ := (l.map (autocorr f)).prod

def packetCharge (f : C_c(ℝ, ℝ)) (m : ℕ) (l : List ℝ) : ℤ :=
  (l.map (packetIndex f m)).sum

/-- Exact orientation law for arbitrary lag products, including vanishing factors. -/
theorem rawProduct_sign (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) (l : List ℝ) :
    rawProduct (source f m (-a)) l =
      (-1 : ℝ) ^ packetCharge f m l * rawProduct (source f m a) l := by
  induction l with
  | nil => simp [rawProduct, packetCharge]
  | cons x l ih =>
    change autocorr (source f m (-a)) x * rawProduct (source f m (-a)) l =
      (-1 : ℝ) ^ (packetIndex f m x + packetCharge f m l) *
        (autocorr (source f m a) x * rawProduct (source f m a) l)
    rw [source_sign, ih, zpow_add₀ (by norm_num)]
    ring

/-- Complete product ambiguity is exactly vanishing or even packet charge. -/
theorem rawProduct_eq_iff (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) (l : List ℝ) :
    rawProduct (source f m (-a)) l = rawProduct (source f m a) l ↔
      rawProduct (source f m a) l = 0 ∨ Even (packetCharge f m l) := by
  rw [rawProduct_sign, neg_one_zpow_eq_ite]
  by_cases h : Even (packetCharge f m l)
  · simp [h]
  · simp only [h, if_false, neg_one_mul, or_false]
    constructor
    · intro he
      linarith
    · intro he
      rw [he, neg_zero]

private theorem sum_error_bound (f : C_c(ℝ, ℝ)) (m : ℕ) (l : List ℝ)
    (h : ∀ x ∈ l, |x - (packetIndex f m x : ℝ) * gap f m| ≤ radius f) :
    |l.sum - (packetCharge f m l : ℝ) * gap f m| ≤ (l.length : ℝ) * radius f := by
  induction l with
  | nil => simp [packetCharge]
  | cons x l ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    have he : (x :: l).sum - (packetCharge f m (x :: l) : ℝ) * gap f m =
        (x - (packetIndex f m x : ℝ) * gap f m) +
          (l.sum - (packetCharge f m l : ℝ) * gap f m) := by
      simp only [packetCharge, List.map_cons, List.sum_cons, Int.cast_add]
      ring
    rw [he]
    calc
      _ ≤ |x - (packetIndex f m x : ℝ) * gap f m| +
          |l.sum - (packetCharge f m l : ℝ) * gap f m| := abs_add_le _ _
      _ ≤ radius f + (l.length : ℝ) * radius f := add_le_add hx hl
      _ = ((x :: l).length : ℝ) * radius f := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Every nonzero product bounds its integer packet charge by the total lag error. -/
theorem packetCharge_bound (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) (l : List ℝ) :
    rawProduct (source f m a) l = 0 ∨
      |l.sum - (packetCharge f m l : ℝ) * gap f m| ≤ (l.length : ℝ) * radius f := by
  by_cases hp : rawProduct (source f m a) l = 0
  · exact Or.inl hp
  · right
    apply sum_error_bound
    intro x hx
    apply packet_distance f m a x
    intro hz
    apply hp
    exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨x, hx, hz⟩)

private theorem short_charge_zero (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) (l : List ℝ)
    (hl : l.length ≤ m) (hs : l.sum = 0) (hp : rawProduct (source f m a) l ≠ 0) :
    packetCharge f m l = 0 := by
  have hb := (packetCharge_bound f m a l).resolve_left hp
  rw [hs, zero_sub, abs_neg] at hb
  have hlr : (l.length : ℝ) ≤ m := by exact_mod_cast hl
  have hb' : |(packetCharge f m l : ℝ) * gap f m| < gap f m :=
    lt_of_le_of_lt hb ((mul_le_mul_of_nonneg_right hlr (radius_pos f).le).trans_lt
      (order_mul_radius_lt_gap f m))
  have hbounds := abs_lt.mp hb'
  by_contra hq
  have hi : packetCharge f m l ≤ -1 ∨ 1 ≤ packetCharge f m l := by omega
  rcases hi with hi | hi
  · have hi' : (packetCharge f m l : ℝ) ≤ -1 := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hi' (gap_pos f m).le
    linarith
  · have hi' : (1 : ℝ) ≤ packetCharge f m l := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hi' (gap_pos f m).le
    linarith

/-- Closed lag products; nonclosed lists carry no closed-cycle datum. -/
def closedProduct (f : C_c(ℝ, ℝ)) (l : List ℝ) : ℝ :=
  if l.sum = 0 then rawProduct f l else 0

def shortData (f : C_c(ℝ, ℝ)) (m : ℕ) : {l : List ℝ // l.length ≤ m} → ℝ :=
  fun l => closedProduct f l.1

/-- Every closed product up to the prescribed order is invariant under copy-sign reversal. -/
theorem shortData_source_neg (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) :
    shortData (source f m (-a)) m = shortData (source f m a) m := by
  funext l
  dsimp only [shortData, closedProduct]
  split_ifs with hs
  · rw [rawProduct_sign]
    by_cases hp : rawProduct (source f m a) l.1 = 0
    · rw [hp, mul_zero]
    · rw [short_charge_zero f m a l.1 l.2 hs hp, zpow_zero, one_mul]
  · rfl

end GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
