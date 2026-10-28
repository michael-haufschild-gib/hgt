import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicCellSourceTransfer

/-!
# Balanced whole-cell sections remove successor prime interactions

A pair of adjacent logarithmic cells has a unique mean-zero profile with jump one.
Its actual translated pairing detects only multiplicative incidence of the odd
middle boundaries. Every other successor contribution cancels exactly.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

private def blockReading (lo hi n : ℕ) : ℝ := if lo ≤ n ∧ n < hi then 1 else 0

private theorem blockReading_adjacent {lo hi : ℕ} (h : lo ≤ hi) (n : ℕ) :
    blockReading lo hi n - blockReading lo hi (n + 1) =
      (if hi = n + 1 then 1 else 0) - (if lo = n + 1 then 1 else 0) := by
  unfold blockReading
  split_ifs <;> norm_num at * <;> omega

/-- A translated whole cell detects exactly its consecutive successor cells. -/
theorem inner_shift_cellAtom_entry {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) :
    inner ℂ (halfLineRightShift (Real.log m) (cellAtom a)) (cellAtom b) =
      if a * m ≤ b ∧ b < (a + 1) * m then (logCellWidth b : ℂ) else 0 := by
  classical
  rw [halfLineRightShift_cellAtom ha hm, sum_inner]
  have ht (r : ℕ) (_hr : r ∈ range m) :
      inner ℂ (cellAtom (a * m + r)) (cellAtom b) =
        if a * m + r = b then (logCellWidth b : ℂ) else 0 := by
    have hpos : 1 ≤ a * m + r := by
      have hp := Nat.mul_le_mul ha (show 1 ≤ m by omega)
      omega
    rw [inner_cellAtom hpos hb]
    split_ifs with he
    · rw [he]
    · rfl
  rw [sum_congr rfl ht]
  by_cases h : a * m ≤ b ∧ b < (a + 1) * m
  · rw [if_pos h, sum_eq_single (b - a * m)]
    · simp only [Nat.add_sub_of_le h.1, ite_true]
    · intro r hr hne
      apply if_neg
      intro he
      exact hne (by omega)
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      rw [Nat.add_mul, Nat.one_mul] at h
      omega
  · rw [if_neg h]
    apply sum_eq_zero
    intro r hr
    apply if_neg
    intro he
    apply h
    rw [Nat.add_mul, Nat.one_mul, ← he]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Finset.mem_range.mp hr) _⟩

private theorem inner_shift_cellAtom_re {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (cellAtom a)) (cellAtom b)).re =
      logCellWidth b * blockReading (a * m) ((a + 1) * m) b := by
  rw [inner_shift_cellAtom_entry ha hb hm]
  unfold blockReading
  split_ifs <;> simp

/-- Coefficients of the jump-one mean-zero profile on two consecutive cells. -/
def haarLeftCoeff (a : ℕ) : ℝ :=
  logCellWidth (2 * a + 1) / (logCellWidth (2 * a) + logCellWidth (2 * a + 1))

def haarRightCoeff (a : ℕ) : ℝ :=
  logCellWidth (2 * a) / (logCellWidth (2 * a) + logCellWidth (2 * a + 1))

/-- Square mass, also the unsigned integral on each half of the balanced pair. -/
def haarMass (a : ℕ) : ℝ :=
  logCellWidth (2 * a) * logCellWidth (2 * a + 1) /
    (logCellWidth (2 * a) + logCellWidth (2 * a + 1))

/-- The balanced section in the actual half-line Hilbert space. -/
def haarAtom (a : ℕ) : L²₊ :=
  (haarLeftCoeff a : ℂ) • cellAtom (2 * a) -
    (haarRightCoeff a : ℂ) • cellAtom (2 * a + 1)

theorem haarMass_pos {a : ℕ} (ha : 1 ≤ a) : 0 < haarMass a := by
  have hl := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  exact div_pos (mul_pos hl hr) (add_pos hl hr)

theorem haarCoeff_sum {a : ℕ} (ha : 1 ≤ a) :
    haarLeftCoeff a + haarRightCoeff a = 1 := by
  have hl := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  unfold haarLeftCoeff haarRightCoeff
  rw [← add_div, add_comm, div_self (add_pos hl hr).ne']

theorem haarCoeff_mass (a : ℕ) :
    haarLeftCoeff a * logCellWidth (2 * a) = haarMass a ∧
      haarRightCoeff a * logCellWidth (2 * a + 1) = haarMass a := by
  unfold haarLeftCoeff haarRightCoeff haarMass
  constructor <;> ring

private theorem re_inner_real_sub (A B C D : ℝ) (x y z w : L²₊) :
    (inner ℂ ((A : ℂ) • x - (B : ℂ) • y) ((C : ℂ) • z - (D : ℂ) • w)).re =
      A * C * (inner ℂ x z).re - A * D * (inner ℂ x w).re -
        B * C * (inner ℂ y z).re + B * D * (inner ℂ y w).re := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Only the odd middle boundary survives in the full translated pairing. -/
theorem inner_shift_haarAtom {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarAtom a)) (haarAtom b)).re =
      if (2 * a + 1) * m = 2 * b + 1 then haarMass b else 0 := by
  have ha0 : 1 ≤ 2 * a := by omega
  have ha1 : 1 ≤ 2 * a + 1 := by omega
  have hb0 : 1 ≤ 2 * b := by omega
  have hb1 : 1 ≤ 2 * b + 1 := by omega
  have hlo : (2 * a) * m ≠ 2 * b + 1 := by rw [Nat.mul_assoc]; omega
  have hhi : (2 * a + 1 + 1) * m ≠ 2 * b + 1 := by
    rw [show (2 * a + 1 + 1) * m = 2 * (a * m + m) by ring]
    omega
  have hleft := blockReading_adjacent
    (Nat.mul_le_mul_right m (show 2 * a ≤ 2 * a + 1 by omega)) (2 * b)
  have hright := blockReading_adjacent
    (Nat.mul_le_mul_right m (show 2 * a + 1 ≤ 2 * a + 1 + 1 by omega)) (2 * b)
  rw [if_neg hlo, sub_zero] at hleft
  rw [if_neg hhi, zero_sub] at hright
  rw [haarAtom, map_sub, map_smul, map_smul, haarAtom, re_inner_real_sub,
    inner_shift_cellAtom_re ha0 hb0 hm, inner_shift_cellAtom_re ha0 hb1 hm,
    inner_shift_cellAtom_re ha1 hb0 hm, inner_shift_cellAtom_re ha1 hb1 hm]
  have hfactor :
      haarLeftCoeff a * haarLeftCoeff b *
          (logCellWidth (2 * b) * blockReading (2 * a * m) ((2 * a + 1) * m) (2 * b)) -
        haarLeftCoeff a * haarRightCoeff b *
          (logCellWidth (2 * b + 1) * blockReading (2 * a * m) ((2 * a + 1) * m) (2 * b + 1)) -
        haarRightCoeff a * haarLeftCoeff b *
          (logCellWidth (2 * b) * blockReading ((2 * a + 1) * m) ((2 * a + 1 + 1) * m) (2 * b)) +
        haarRightCoeff a * haarRightCoeff b *
          (logCellWidth (2 * b + 1) * blockReading ((2 * a + 1) * m) ((2 * a + 1 + 1) * m) (2 * b + 1)) =
      haarMass b * (haarLeftCoeff a *
        (blockReading (2 * a * m) ((2 * a + 1) * m) (2 * b) -
          blockReading (2 * a * m) ((2 * a + 1) * m) (2 * b + 1)) -
        haarRightCoeff a *
        (blockReading ((2 * a + 1) * m) ((2 * a + 1 + 1) * m) (2 * b) -
          blockReading ((2 * a + 1) * m) ((2 * a + 1 + 1) * m) (2 * b + 1))) := by
    rw [← (haarCoeff_mass b).1]
    have he := (haarCoeff_mass b).2.trans (haarCoeff_mass b).1.symm
    linear_combination
      (-haarLeftCoeff a * blockReading (2*a*m) ((2*a+1)*m) (2*b+1) +
        haarRightCoeff a * blockReading ((2*a+1)*m) ((2*a+1+1)*m) (2*b+1)) * he
  rw [hfactor, hleft, hright]
  split_ifs with he
  · simp only [mul_one, mul_neg_one, sub_neg_eq_add, haarCoeff_sum ha, mul_one]
  · simp only [mul_zero, neg_zero, sub_zero]


theorem haarCoeff_nonneg {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ haarLeftCoeff a ∧ 0 ≤ haarRightCoeff a := by
  have hl := (logCellWidth_pos (show 1 ≤ 2 * a by omega)).le
  have hr := (logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)).le
  exact ⟨div_nonneg hr (add_nonneg hl hr), div_nonneg hl (add_nonneg hl hr)⟩

/-- Distinct balanced pairs are orthogonal; the diagonal is their harmonic cell width. -/
theorem re_inner_haarAtom {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (inner ℂ (haarAtom a) (haarAtom b)).re = if a = b then haarMass a else 0 := by
  have ha0 : 1 ≤ 2 * a := by omega
  have ha1 : 1 ≤ 2 * a + 1 := by omega
  have hb0 : 1 ≤ 2 * b := by omega
  have hb1 : 1 ≤ 2 * b + 1 := by omega
  have h01 : 2 * a ≠ 2 * b + 1 := by omega
  have h10 : 2 * a + 1 ≠ 2 * b := by omega
  rw [haarAtom, haarAtom, re_inner_real_sub,
    inner_cellAtom ha0 hb0, inner_cellAtom ha0 hb1,
    inner_cellAtom ha1 hb0, inner_cellAtom ha1 hb1,
    if_neg h01, if_neg h10]
  by_cases h : a = b
  · subst b
    simp only [ite_true, Complex.ofReal_re, Complex.zero_re, mul_zero, sub_zero]
    have hl := (haarCoeff_mass a).1
    have hr := (haarCoeff_mass a).2
    have hs := haarCoeff_sum ha
    linear_combination haarLeftCoeff a * hl + haarRightCoeff a * hr + haarMass a * hs
  · rw [if_neg (show 2 * a ≠ 2 * b by omega),
      if_neg (show 2 * a + 1 ≠ 2 * b + 1 by omega), if_neg h]
    simp only [Complex.zero_re, mul_zero, sub_zero, add_zero]

/-- The reciprocal right endpoint bounds a logarithmic cell from below. -/
theorem inv_add_one_le_logCellWidth {a : ℕ} (ha : 1 ≤ a) :
    1 / ((a : ℝ) + 1) ≤ logCellWidth a := by
  have hp : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hp1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hp hp1)
  rw [Real.log_div hp.ne' hp1.ne'] at h
  have he : (a : ℝ) / ((a : ℝ) + 1) - 1 = -(1 / ((a : ℝ) + 1)) := by
    field_simp
    ring
  rw [he] at h
  unfold logCellWidth
  linarith only [h]

private theorem parallelMass_mono {l r u v : ℝ} (hl : 0 < l) (hr : 0 < r)
    (hlu : l ≤ u) (hrv : r ≤ v) :
    l * r / (l + r) ≤ u * v / (u + v) := by
  have hu := hl.trans_le hlu
  have hv := hr.trans_le hrv
  apply (div_le_div_iff₀ (add_pos hl hr) (add_pos hu hv)).mpr
  calc
    l * r * (u + v) = (l * u) * r + (r * v) * l := by ring
    _ ≤ (l * u) * v + (r * v) * u :=
      add_le_add (mul_le_mul_of_nonneg_left hrv (mul_nonneg hl.le hu.le))
        (mul_le_mul_of_nonneg_left hlu (mul_nonneg hr.le hv.le))
    _ = u * v * (l + r) := by ring

/-- Balanced pair mass lies between the reciprocal sums of its endpoint indices. -/
theorem haarMass_bounds {a : ℕ} (ha : 1 ≤ a) :
    1 / (4 * (a : ℝ) + 3) ≤ haarMass a ∧
      haarMass a ≤ 1 / (4 * (a : ℝ) + 1) := by
  have ha0 : 1 ≤ 2 * a := by omega
  have ha1 : 1 ≤ 2 * a + 1 := by omega
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hl := logCellWidth_pos ha0
  have hr := logCellWidth_pos ha1
  have hlo := parallelMass_mono
    (by positivity : 0 < 1 / ((2 * a : ℕ) + (1 : ℝ)))
    (by positivity : 0 < 1 / ((2 * a + 1 : ℕ) + (1 : ℝ)))
    (inv_add_one_le_logCellWidth ha0) (inv_add_one_le_logCellWidth ha1)
  have hhi := parallelMass_mono hl hr (logCellWidth_le_inv ha0) (logCellWidth_le_inv ha1)
  unfold haarMass
  constructor
  · convert hlo using 1
    push_cast
    field_simp
    ring
  · convert hhi using 1
    push_cast
    field_simp
    ring

/-- Multiplicative incidence contracts balanced mass by the reciprocal multiplier. -/
theorem haarMass_mul_le {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) (he : (2 * a + 1) * m = 2 * b + 1) :
    (m : ℝ) * haarMass b ≤ 2 * haarMass a := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have heR : (2 * (a : ℝ) + 1) * (m : ℝ) = 2 * (b : ℝ) + 1 := by
    exact_mod_cast he
  calc
    (m : ℝ) * haarMass b ≤ (m : ℝ) * (1 / (4 * (b : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (haarMass_bounds hb).2 (Nat.cast_nonneg m)
    _ ≤ 2 * (1 / (4 * (a : ℝ) + 3)) := by
      rw [mul_one_div, mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hmR)]
    _ ≤ 2 * haarMass a := mul_le_mul_of_nonneg_left (haarMass_bounds ha).1 (by norm_num)

#print axioms re_inner_haarAtom
#print axioms haarMass_mul_le


/-- Arbitrary signed finite sections of balanced adjacent complete cells. -/
def haarSection (c : ℕ → ℝ) (X : ℕ) : L²₊ :=
  ∑ a ∈ Icc 1 X, (c a : ℂ) • haarAtom a

/-- The full prime series evaluated on the actual balanced source vector. -/
def haarPrimeEnergy (c : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑' m : ℕ, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection c X)).re

private theorem re_inner_real_smul (c d : ℝ) (u v : L²₊) :
    (inner ℂ ((c : ℂ) • u) ((d : ℂ) • v)).re = c * d * (inner ℂ u v).re := by
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The finite signed source retains precisely the odd-boundary divisor interactions. -/
theorem inner_shift_haarSection (c d : ℕ → ℝ) (X : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection d X)).re =
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        c a * d b * (if (2 * a + 1) * m = 2 * b + 1 then haarMass b else 0) := by
  classical
  unfold haarSection
  rw [map_sum, sum_inner, Complex.re_sum]
  apply sum_congr rfl
  intro a ha
  rw [inner_sum, Complex.re_sum]
  apply sum_congr rfl
  intro b hb
  rw [map_smul, re_inner_real_smul,
    inner_shift_haarAtom (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 hm]

/-- Square mass of a signed section is exactly its weighted coefficient norm. -/
theorem re_inner_haarSection_self (c : ℕ → ℝ) (X : ℕ) :
    (inner ℂ (haarSection c X) (haarSection c X)).re =
      ∑ a ∈ Icc 1 X, haarMass a * c a ^ 2 := by
  classical
  unfold haarSection
  rw [sum_inner, Complex.re_sum]
  apply sum_congr rfl
  intro a ha
  rw [inner_sum, Complex.re_sum]
  have he : ∀ b ∈ Icc 1 X,
      (inner ℂ ((c a : ℂ) • haarAtom a) ((c b : ℂ) • haarAtom b)).re =
        if a = b then haarMass a * c a ^ 2 else 0 := by
    intro b hb
    rw [re_inner_real_smul, re_inner_haarAtom (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
    split_ifs with h
    · subst b; ring
    · simp only [mul_zero]
  rw [sum_congr rfl he]
  simp only [sum_ite_eq, ha, ite_true]

theorem inner_shift_haarSection_eq_zero (c d : ℕ → ℝ) (X : ℕ) {m : ℕ}
    (hm : 2 * X + 1 < m) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection d X)).re = 0 := by
  rw [inner_shift_haarSection c d X (by omega : 2 ≤ m)]
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  have hbX := (mem_Icc.mp hb).2
  have hlo : m ≤ (2 * a + 1) * m := by
    simpa using Nat.mul_le_mul_right m (show 1 ≤ 2 * a + 1 by omega)
  rw [if_neg (by omega), mul_zero]

/-- A finite horizon follows from support; this identity keeps the entire prime series. -/
theorem haarPrimeEnergy_eq (c : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy c X = ∑ m ∈ Icc 2 (2 * X + 1),
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          c a * c b * (if (2 * a + 1) * m = 2 * b + 1 then haarMass b else 0) := by
  classical
  unfold haarPrimeEnergy
  rw [tsum_eq_sum (s := Icc 2 (2 * X + 1))]
  · apply sum_congr rfl
    intro m hm
    rw [inner_shift_haarSection c c X (mem_Icc.mp hm).1]
  · intro m hm
    by_cases hm2 : 2 ≤ m
    · have hmX : 2 * X + 1 < m := by simp only [mem_Icc] at hm; omega
      rw [inner_shift_haarSection_eq_zero c c X hmX, mul_zero]
    · have he : m = 0 ∨ m = 1 := by omega
      rcases he with rfl | rfl <;> simp

/-- Every even prime multiplier is annihilated on the balanced source space. -/
theorem inner_shift_haarSection_even (c d : ℕ → ℝ) (X : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (inner ℂ (halfLineRightShift (Real.log ((2 * k : ℕ) : ℝ)) (haarSection c X)) (haarSection d X)).re = 0 := by
  rw [inner_shift_haarSection c d X (by omega : 2 ≤ 2 * k)]
  apply sum_eq_zero
  intro a _ha
  apply sum_eq_zero
  intro b _hb
  have he : (2 * a + 1) * (2 * k) ≠ 2 * b + 1 := by
    rw [show (2 * a + 1) * (2 * k) = 2 * ((2 * a + 1) * k) by ring]
    omega
  rw [if_neg he, mul_zero]

#print axioms re_inner_haarSection_self
#print axioms haarPrimeEnergy_eq
#print axioms inner_shift_haarSection_even

#print axioms inner_shift_haarAtom

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
