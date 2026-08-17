import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The diagonal symbol of a bivariate polynomial

For a polynomial in one variable whose coefficients are again polynomials, the condition that the
`j`-th coefficient have inner degree at most `j / c` is stable under sums and products, and on the
weight-one class the extremal inner coefficients multiply by convolution.  This is the bookkeeping
that isolates, inside a product of series, the single factor responsible for the extremal degree at
each order: a factor of weight two contributes only at order zero.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The `j`-th outer coefficient has inner degree at most `j / c`. -/
def SubDiag (c : ℕ) (F : Polynomial (Polynomial R)) : Prop :=
  ∀ j d : ℕ, j < c * d → (F.coeff j).coeff d = 0

/-- The extremal inner coefficient at each outer order. -/
def diagSym (F : Polynomial (Polynomial R)) (j : ℕ) : R := (F.coeff j).coeff j

theorem SubDiag.mono {c c' : ℕ} {F : Polynomial (Polynomial R)} (hc : c ≤ c')
    (h : SubDiag c' F) : SubDiag c F :=
  fun j d hjd => h j d (lt_of_lt_of_le hjd (Nat.mul_le_mul_right d hc))

theorem natDegree_coeff_le_of_subDiag {F : Polynomial (Polynomial R)} (hF : SubDiag 1 F) (j : ℕ) :
    (F.coeff j).natDegree ≤ j :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun d hd => hF j d (by omega)

/-- A weight-two factor has no extremal coefficient beyond order zero. -/
theorem diagSym_eq_zero_of_subDiag_two {F : Polynomial (Polynomial R)} (h : SubDiag 2 F) {j : ℕ}
    (hj : 0 < j) : diagSym F j = 0 := h j j (by omega)

/-- A polynomial all of whose outer coefficients are inner constants is subdiagonal of every
weight. -/
theorem subDiag_of_coeff_C {F : Polynomial (Polynomial R)}
    (h : ∀ j, ∃ a : R, F.coeff j = Polynomial.C a) (c : ℕ) : SubDiag c F := by
  intro j d hjd
  obtain ⟨a, hja⟩ := h j
  have hd : d ≠ 0 := by
    rintro rfl
    omega
  rw [hja, Polynomial.coeff_C, if_neg hd]

theorem subDiag_zero (c : ℕ) : SubDiag c (0 : Polynomial (Polynomial R)) :=
  subDiag_of_coeff_C (fun _ => ⟨0, by simp⟩) c

theorem subDiag_one (c : ℕ) : SubDiag c (1 : Polynomial (Polynomial R)) :=
  subDiag_of_coeff_C (fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨1, by simp⟩
    · exact ⟨0, by rw [Polynomial.coeff_one, if_neg (by omega), Polynomial.C_0]⟩) c

theorem subDiag_CC (c : ℕ) (a : R) :
    SubDiag c (Polynomial.C (Polynomial.C a) : Polynomial (Polynomial R)) :=
  subDiag_of_coeff_C (fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨a, by simp⟩
    · exact ⟨0, by rw [Polynomial.coeff_C, if_neg (by omega), Polynomial.C_0]⟩) c

theorem subDiag_X_pow (c k : ℕ) :
    SubDiag c ((Polynomial.X : Polynomial (Polynomial R)) ^ k) :=
  subDiag_of_coeff_C (fun j => by
    rw [Polynomial.coeff_X_pow]
    by_cases h : j = k
    · exact ⟨1, by rw [if_pos h, Polynomial.C_1]⟩
    · exact ⟨0, by rw [if_neg h, Polynomial.C_0]⟩) c

theorem SubDiag.add {c : ℕ} {F G : Polynomial (Polynomial R)} (hF : SubDiag c F)
    (hG : SubDiag c G) : SubDiag c (F + G) := by
  intro j d hjd
  rw [Polynomial.coeff_add, Polynomial.coeff_add, hF j d hjd, hG j d hjd, add_zero]

theorem SubDiag.mul {c : ℕ} {F G : Polynomial (Polynomial R)} (hF : SubDiag c F)
    (hG : SubDiag c G) : SubDiag c (F * G) := by
  intro j d hjd
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  have huv : q.1 + q.2 = d := Finset.mem_antidiagonal.mp hq
  rcases lt_or_ge p.1 (c * q.1) with h1 | h1
  · rw [hF p.1 q.1 h1, zero_mul]
  · have h2 : p.2 < c * q.2 := by
      by_contra hcon
      push Not at hcon
      have : c * d ≤ j := by
        calc c * d = c * q.1 + c * q.2 := by rw [← Nat.mul_add, huv]
        _ ≤ p.1 + p.2 := Nat.add_le_add h1 hcon
        _ = j := hpq
      omega
    rw [hG p.2 q.2 h2, mul_zero]

theorem SubDiag.sum {ι : Type*} {c : ℕ} (s : Finset ι) {F : ι → Polynomial (Polynomial R)}
    (h : ∀ i ∈ s, SubDiag c (F i)) : SubDiag c (∑ i ∈ s, F i) := by
  classical
  revert h
  induction s using Finset.cons_induction with
  | empty => intro _; simpa using subDiag_zero c
  | cons a s ha ih =>
      intro h
      rw [Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem SubDiag.pow {c : ℕ} {F : Polynomial (Polynomial R)} (hF : SubDiag c F) :
    ∀ k : ℕ, SubDiag c (F ^ k)
  | 0 => by simpa using subDiag_one c
  | (k + 1) => by
      rw [pow_succ]
      exact (SubDiag.pow hF k).mul hF

@[simp] theorem diagSym_zero_poly (j : ℕ) : diagSym (0 : Polynomial (Polynomial R)) j = 0 := by
  simp [diagSym]

theorem diagSym_add (F G : Polynomial (Polynomial R)) (j : ℕ) :
    diagSym (F + G) j = diagSym F j + diagSym G j := by
  simp [diagSym]

theorem diagSym_sum {ι : Type*} (s : Finset ι) (F : ι → Polynomial (Polynomial R)) (j : ℕ) :
    diagSym (∑ i ∈ s, F i) j = ∑ i ∈ s, diagSym (F i) j := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, diagSym_add, ih, Finset.sum_cons]

theorem diagSym_CC (a : R) (j : ℕ) :
    diagSym (Polynomial.C (Polynomial.C a) : Polynomial (Polynomial R)) j
      = if j = 0 then a else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [diagSym]
  · rw [diagSym, Polynomial.coeff_C, if_neg (by omega), if_neg (by omega)]
    simp

/-- **On the weight-one class the extremal coefficients convolve.** -/
theorem diagSym_mul {F G : Polynomial (Polynomial R)} (hF : SubDiag 1 F) (hG : SubDiag 1 G)
    (j : ℕ) :
    diagSym (F * G) j = ∑ p ∈ Finset.antidiagonal j, diagSym F p.1 * diagSym G p.2 := by
  rw [diagSym, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpq : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
  rw [Polynomial.coeff_mul, Finset.sum_eq_single p]
  · rfl
  · intro q hq hqp
    have huv : q.1 + q.2 = j := Finset.mem_antidiagonal.mp hq
    rcases lt_or_ge p.1 q.1 with h1 | h1
    · rw [hF p.1 q.1 (by omega), zero_mul]
    · have h2 : p.2 < q.2 := by
        rcases lt_or_ge p.2 q.2 with h | h
        · exact h
        · exact absurd (Prod.ext (by omega : q.1 = p.1) (by omega : q.2 = p.2)) hqp
      rw [hG p.2 q.2 (by omega), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_antidiagonal.mpr hpq) hnot

/-- Multiplying by a weight-two factor multiplies the extremal coefficients by a constant. -/
theorem diagSym_mul_subDiag_two {F G : Polynomial (Polynomial R)} (hF : SubDiag 1 F)
    (hG : SubDiag 2 G) (j : ℕ) : diagSym (F * G) j = diagSym F j * diagSym G 0 := by
  rw [diagSym_mul hF (hG.mono (by omega)) j, Finset.sum_eq_single (j, 0)]
  · intro q hq hqj
    have huv : q.1 + q.2 = j := Finset.mem_antidiagonal.mp hq
    have hq2 : 0 < q.2 := by
      rcases Nat.eq_zero_or_pos q.2 with h | h
      · exact absurd (Prod.ext (by omega : q.1 = j) (by omega : q.2 = 0)) hqj
      · exact h
    rw [diagSym_eq_zero_of_subDiag_two hG hq2, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hnot

theorem diagSym_one (j : ℕ) :
    diagSym (1 : Polynomial (Polynomial R)) j = if j = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [diagSym]
  · rw [diagSym, Polynomial.coeff_one, if_neg (by omega), if_neg (by omega)]
    simp

theorem diagSym_mul_zero {F G : Polynomial (Polynomial R)} (hF : SubDiag 1 F) (hG : SubDiag 1 G) :
    diagSym (F * G) 0 = diagSym F 0 * diagSym G 0 := by
  rw [diagSym_mul hF hG 0,
    Finset.sum_eq_single_of_mem (0, 0) (Finset.mem_antidiagonal.mpr (by simp))]
  intro q hq hq0
  have huv : q.1 + q.2 = 0 := Finset.mem_antidiagonal.mp hq
  exact absurd (Prod.ext (by omega : q.1 = 0) (by omega : q.2 = 0)) hq0

/-- A left factor whose extremal symbol sits in order zero acts as a scalar. -/
theorem diagSym_mul_of_left_delta {F G : Polynomial (Polynomial R)} (hF : SubDiag 1 F)
    (hG : SubDiag 1 G) {c : R} (hFd : ∀ i, diagSym F i = if i = 0 then c else 0) (j : ℕ) :
    diagSym (F * G) j = c * diagSym G j := by
  rw [diagSym_mul hF hG j,
    Finset.sum_eq_single_of_mem (0, j) (Finset.mem_antidiagonal.mpr (by simp))]
  · rw [hFd 0, if_pos rfl]
  · intro q hq hq0
    have huv : q.1 + q.2 = j := Finset.mem_antidiagonal.mp hq
    have hq1 : q.1 ≠ 0 := fun h => hq0 (Prod.ext h (by omega))
    rw [hFd q.1, if_neg hq1, zero_mul]

theorem diagSym_X_pow_zero (k : ℕ) :
    diagSym ((Polynomial.X : Polynomial (Polynomial R)) ^ k) 0 = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [diagSym, pow_zero, if_pos rfl, Polynomial.coeff_one, if_pos rfl, Polynomial.coeff_one,
      if_pos rfl]
  · rw [diagSym, Polynomial.coeff_X_pow, if_neg (by omega), if_neg (by omega),
      Polynomial.coeff_zero]

/-- A constant factor scales the extremal coefficients. -/
theorem diagSym_CC_mul {G : Polynomial (Polynomial R)} (hG : SubDiag 1 G) (c : R) (j : ℕ) :
    diagSym (Polynomial.C (Polynomial.C c) * G) j = c * diagSym G j := by
  rw [diagSym_mul (subDiag_CC 1 c) hG j,
    Finset.sum_eq_single_of_mem (0, j) (Finset.mem_antidiagonal.mpr (by simp))]
  · rw [diagSym_CC, if_pos rfl]
  · intro q hq hq0
    have huv : q.1 + q.2 = j := Finset.mem_antidiagonal.mp hq
    have hq1 : q.1 ≠ 0 := by
      rintro h
      exact hq0 (Prod.ext h (by omega))
    rw [diagSym_CC, if_neg hq1, zero_mul]

/-- **Powers of a factor whose extremal symbol is concentrated in order one.** -/
theorem diagSym_pow_of_linear {F : Polynomial (Polynomial R)} (hF : SubDiag 1 F) {c : R}
    (hd : ∀ j, diagSym F j = if j = 1 then c else 0) (r : ℕ) :
    ∀ j, diagSym (F ^ r) j = if j = r then c ^ r else 0 := by
  induction r with
  | zero =>
      intro j
      rw [pow_zero, diagSym_one, pow_zero]
  | succ r ih =>
      intro j
      rw [pow_succ, diagSym_mul (hF.pow r) hF j]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Finset.sum_eq_single_of_mem (0, 0) (Finset.mem_antidiagonal.mpr (by simp))]
        · rw [hd 0, if_neg (by omega), mul_zero, if_neg (by omega)]
        · intro q hq hq0
          have huv : q.1 + q.2 = 0 := Finset.mem_antidiagonal.mp hq
          exact absurd (Prod.ext (by omega : q.1 = 0) (by omega : q.2 = 0)) hq0
      · rw [Finset.sum_eq_single_of_mem (j - 1, 1)
          (Finset.mem_antidiagonal.mpr (by omega))]
        · rw [ih (j - 1), hd 1, if_pos rfl]
          by_cases hjr : j = r + 1
          · rw [if_pos (by omega), if_pos hjr, pow_succ]
          · rw [if_neg (by omega), if_neg hjr, zero_mul]
        · intro q hq hq1
          have huv : q.1 + q.2 = j := Finset.mem_antidiagonal.mp hq
          have hq2 : q.2 ≠ 1 := by
            rintro h
            exact hq1 (Prod.ext (by omega) h)
          rw [hd q.2, if_neg hq2, mul_zero]

end

end GaloisForLFunctions.HTGeometry
