import GaloisForLFunctions.BezoutValuationIncidence.AllLevelPronicResidueGapCentering

/-!
# Shared-birth covariance of centered pronic residue cells

C12's local centering has an exact pronic tail formula at every cut. For unit
modulus gaps, two cells with lower moduli `p=g*l`, `r=g*k`, `k=l+offset`,
start together at `k*p=l*r`. Their covariance equals a positive piecewise
rational tent value, determined by the next jump of the smaller cell.

This classifies positivity exactly: a common factor `g>1` and an interior
jump are both necessary and sufficient. At the product start (`g=1`) the
covariance vanishes. An unconditional family of distinct ordered gaps has
positive covariance equal to the smaller cell's diagonal variance, so the
same-level nonpositive-covariance argument does not extend across levels.

The full arithmetic sum over differently placed cells is not estimated here.
All public statements use data parameters; no analytic premise is supplied.
-/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private theorem quotient_mod_cast {p n k : ℕ} (hl : k * p ≤ n) (hu : n < (k + 1) * p) :
    ((n % p : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) * p := by
  have hd : n / p = k := Nat.div_eq_of_lt_le hl hu
  have he := Nat.mod_add_div n p
  rw [hd] at he
  have heR : ((n % p : ℕ) : ℝ) + (p : ℝ) * k = n := by exact_mod_cast he
  nlinarith

private theorem reciprocal_cell_mass {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / (a : ℝ) - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have hb : (b : ℝ) ≠ 0 := by have : 0 < b := ha.trans_le hab; positivity
    have haR : (a : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private theorem centered_cell_tail (p k : ℕ+) (h T : ℕ)
    (hlo : (k : ℕ) * (p : ℕ) ≤ T) (hhi : T ≤ ((k : ℕ) + 1) * (p : ℕ)) :
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    (∑ n ∈ Ico T (((k : ℕ) + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ) - residueGapCellPronicMean p h k) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        if T ≤ s then
          (((k : ℝ) + 1) * p - s) * ((T : ℝ) - (k : ℝ) * p) /
            (((j : ℝ) + 1) * p * T)
        else
          ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - T) /
            (((j : ℝ) + 1) * p * T)
      else 0 := by
  let q := (p : ℕ) + h
  let j := (k : ℕ) * (p : ℕ) / q
  let s := (j + 1) * q
  let a := (k : ℕ) * (p : ℕ)
  let b := ((k : ℕ) + 1) * (p : ℕ)
  let W (n : ℕ) := ((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ) -
    residueGapCellPronicMean p h k
  change (∑ n ∈ Ico T b, W n / ((n : ℝ) * ((n : ℝ) + 1))) =
    if s < b then
      if T ≤ s then
        (((k : ℝ) + 1) * p - s) * ((T : ℝ) - (k : ℝ) * p) /
          (((j : ℝ) + 1) * p * T)
      else
        ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - T) /
          (((j : ℝ) + 1) * p * T)
    else 0
  have ha : 0 < a := by dsimp only [a]; positivity
  have hq : 0 < q := by dsimp only [q]; positivity
  have hlow : j * q ≤ a := Nat.div_mul_le_self a q
  have has : a < s := by simpa only [s, j, a, Nat.mul_comm] using Nat.lt_mul_div_succ a hq
  have hsb : b ≤ (j + 1 + 1) * q := by
    have hpq : (p : ℕ) ≤ q := by dsimp only [q]; omega
    dsimp only [a, b, s] at *
    nlinarith
  have hleft (n : ℕ) (hna : a ≤ n) (hnb : n < b) (hns : n < s) :
      W n = (j : ℝ) * q - (k : ℝ) * p - residueGapCellPronicMean p h k := by
    dsimp only [W]
    rw [quotient_mod_cast hna hnb, quotient_mod_cast (hlow.trans hna) hns]
    ring
  have hright (n : ℕ) (hna : a ≤ n) (hnb : n < b) (hsn : s ≤ n) :
      W n = ((j : ℝ) + 1) * q - (k : ℝ) * p - residueGapCellPronicMean p h k := by
    dsimp only [W]
    rw [quotient_mod_cast hna hnb, quotient_mod_cast hsn (hnb.trans_le hsb)]
    push_cast
    ring
  have hm := residueGapCellPronicMean_eq p k h
  change residueGapCellPronicMean p h k = if s < b then
    -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
    else (j : ℝ) * q - (k : ℝ) * p at hm
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hT0 : (T : ℝ) ≠ 0 := by have : 0 < T := ha.trans_le hlo; positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  by_cases hs : s < b
  · rw [if_pos hs]
    by_cases hTs : T ≤ s
    · rw [if_pos hTs]
      have hf : (∑ n ∈ Ico a T, W n / ((n : ℝ) * ((n : ℝ) + 1))) =
          ((j : ℝ) * q - (k : ℝ) * p - residueGapCellPronicMean p h k) *
            (1 / ((k : ℝ) * p) - 1 / (T : ℝ)) := by
        calc
          _ = ∑ n ∈ Ico a T,
              ((j : ℝ) * q - (k : ℝ) * p - residueGapCellPronicMean p h k) *
                (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
            apply sum_congr rfl
            intro n hn
            rw [hleft n (mem_Ico.mp hn).1 ((mem_Ico.mp hn).2.trans_le hhi)
              ((mem_Ico.mp hn).2.trans_le hTs), mul_one_div]
          _ = _ := by
            rw [← mul_sum, reciprocal_cell_mass ha hlo]
            simp only [a, Nat.cast_mul]
      have hz := (residueGapCellPronicMoments p k h).1
      change (∑ n ∈ Ico a b, W n / ((n : ℝ) * ((n : ℝ) + 1))) = 0 at hz
      rw [← sum_Ico_consecutive (fun n => W n / ((n : ℝ) * ((n : ℝ) + 1))) hlo hhi, hf] at hz
      have he : (∑ n ∈ Ico T b, W n / ((n : ℝ) * ((n : ℝ) + 1))) =
          -(((j : ℝ) * q - (k : ℝ) * p - residueGapCellPronicMean p h k) *
            (1 / ((k : ℝ) * p) - 1 / (T : ℝ))) := by linarith
      rw [he, hm, if_pos hs]
      dsimp only [s]
      push_cast
      field_simp
      ring
    · rw [if_neg hTs]
      calc
        _ = (((j : ℝ) + 1) * q - (k : ℝ) * p - residueGapCellPronicMean p h k) *
            (1 / (T : ℝ) - 1 / (b : ℝ)) := by
          rw [mul_sub, mul_one_div, mul_one_div]
          calc
            _ = ∑ n ∈ Ico T b,
                (((j : ℝ) + 1) * q - (k : ℝ) * p - residueGapCellPronicMean p h k) *
                  (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
              apply sum_congr rfl
              intro n hn
              rw [hright n (hlo.trans (mem_Ico.mp hn).1) (mem_Ico.mp hn).2
                ((not_le.mp hTs).le.trans (mem_Ico.mp hn).1), mul_one_div]
            _ = _ := by rw [← mul_sum, reciprocal_cell_mass (ha.trans_le hlo) hhi]; ring
        _ = _ := by
          rw [hm, if_pos hs]
          dsimp only [s, b]
          push_cast
          field_simp
          ring
  · rw [if_neg hs]
    apply sum_eq_zero
    intro n hn
    rw [hleft n (hlo.trans (mem_Ico.mp hn).1) (mem_Ico.mp hn).2
      ((mem_Ico.mp hn).2.trans_le (not_lt.mp hs)), hm, if_neg hs, sub_self, zero_div]


/-- Every cut of a locally centered residue cell has an explicit pronic tail. -/
theorem residueGapCellPronicTail_eq (p k : ℕ+) (h cut : ℕ) :
    let T := (k : ℕ) * (p : ℕ) + min cut (p : ℕ)
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    (∑ n ∈ Ico T (((k : ℕ) + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ) - residueGapCellPronicMean p h k) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        if T ≤ s then
          (((k : ℝ) + 1) * p - s) * ((T : ℝ) - (k : ℝ) * p) /
            (((j : ℝ) + 1) * p * T)
        else
          ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - T) /
            (((j : ℝ) + 1) * p * T)
      else 0 := by
  apply centered_cell_tail
  · omega
  · have hcut := min_le_right cut (p : ℕ)
    nlinarith


/-- At the product start, the larger unit-gap cell is constant on the smaller cell. -/
theorem residueGapProductBirth_centered_covariance_eq_zero (p : ℕ+) (offset : ℕ) :
    let r := (p : ℕ) + offset
    (∑ n ∈ Ico ((p : ℕ) * r) ((r + 1) * (p : ℕ)),
      ((((n % (p : ℕ) : ℕ) : ℝ) - ((n % ((p : ℕ) + 1) : ℕ) : ℝ) -
          residueGapCellPronicMean p 1 r) *
        (((n % r : ℕ) : ℝ) - ((n % (r + 1) : ℕ) : ℝ) -
          residueGapCellPronicMean r 1 p)) /
            ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
  let r := (p : ℕ) + offset
  have hp1 : 1 ≤ (p : ℕ) := p.pos
  have hpr : (p : ℕ) ≤ r := by dsimp only [r]; omega
  have hr : 0 < r := p.pos.trans_le hpr
  have hsub : (p : ℕ) - 1 + 1 = (p : ℕ) := Nat.sub_add_cancel hp1
  let C : ℝ := (((p : ℕ) - 1 : ℕ) : ℝ) * (r + 1 : ℕ) - (p : ℝ) * r -
    residueGapCellPronicMean r 1 p
  have hc (n : ℕ) (hn : n ∈ Ico ((p : ℕ) * r) ((r + 1) * (p : ℕ))) :
      ((n % r : ℕ) : ℝ) - ((n % (r + 1) : ℕ) : ℝ) -
        residueGapCellPronicMean r 1 p = C := by
    have hlo := (mem_Ico.mp hn).1
    have hhi := (mem_Ico.mp hn).2
    have hnr : n < ((p : ℕ) + 1) * r := by nlinarith
    have hlow : ((p : ℕ) - 1) * (r + 1) ≤ n := by
      calc
        _ = ((p : ℕ) - 1) * r + ((p : ℕ) - 1) := by ring
        _ ≤ ((p : ℕ) - 1) * r + r := Nat.add_le_add_left (by omega) _
        _ = ((p : ℕ) - 1 + 1) * r := by ring
        _ = (p : ℕ) * r := by rw [hsub]
        _ ≤ n := hlo
    have hhigh : n < ((p : ℕ) - 1 + 1) * (r + 1) := by
      rw [hsub, Nat.mul_comm]
      exact hhi
    rw [quotient_mod_cast hlo hnr, quotient_mod_cast hlow hhigh]
    dsimp only [C]
    ring
  have hm := (residueGapCellPronicMoments p ⟨r, hr⟩ 1).1
  change (∑ n ∈ Ico (r * (p : ℕ)) ((r + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % ((p : ℕ) + 1) : ℕ) : ℝ) -
        residueGapCellPronicMean p 1 r) / ((n : ℝ) * ((n : ℝ) + 1))) = 0 at hm
  have hm' : (∑ n ∈ Ico ((p : ℕ) * r) ((r + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % ((p : ℕ) + 1) : ℕ) : ℝ) -
        residueGapCellPronicMean p 1 r) / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
    simpa only [Nat.mul_comm] using hm
  change (∑ n ∈ Ico ((p : ℕ) * r) ((r + 1) * (p : ℕ)), _) = 0
  calc
    _ = (∑ n ∈ Ico ((p : ℕ) * r) ((r + 1) * (p : ℕ)),
        (((n % (p : ℕ) : ℕ) : ℝ) - ((n % ((p : ℕ) + 1) : ℕ) : ℝ) -
          residueGapCellPronicMean p 1 r) / ((n : ℝ) * ((n : ℝ) + 1))) * C := by
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [hc n hn]
      ring
    _ = 0 := by rw [hm', zero_mul]

/-- Exact covariance of two locally centered unit-gap cells with a common start. -/
def sharedBirthUnitGapCovariance (g l : ℕ+) (offset : ℕ) : ℝ :=
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  let r := (g : ℕ) * k
  ∑ n ∈ Ico (k * p) ((k + 1) * p),
    ((((n % p : ℕ) : ℝ) - ((n % (p + 1) : ℕ) : ℝ) - residueGapCellPronicMean p 1 k) *
      (((n % r : ℕ) : ℝ) - ((n % (r + 1) : ℕ) : ℝ) - residueGapCellPronicMean r 1 l)) /
        ((n : ℝ) * ((n : ℝ) + 1))

private theorem shared_birth_pairing_tail (g l : ℕ+) (offset : ℕ) :
    let k := (l : ℕ) + offset
    let p := (g : ℕ) * (l : ℕ)
    let r := (g : ℕ) * k
    sharedBirthUnitGapCovariance g l offset = ((r : ℝ) + 1) *
      ∑ n ∈ Ico (k * p + (l : ℕ)) ((k + 1) * p),
        (((n % p : ℕ) : ℝ) - ((n % (p + 1) : ℕ) : ℝ) - residueGapCellPronicMean p 1 k) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  let r := (g : ℕ) * k
  let a := k * p
  let b := (k + 1) * p
  let t := a + (l : ℕ)
  let W (n : ℕ) := ((n % p : ℕ) : ℝ) - ((n % (p + 1) : ℕ) : ℝ) -
    residueGapCellPronicMean p 1 k
  let V (n : ℕ) := ((n % r : ℕ) : ℝ) - ((n % (r + 1) : ℕ) : ℝ) -
    residueGapCellPronicMean r 1 l
  let C : ℝ := ((((l : ℕ) - 1 : ℕ) : ℝ) * (r + 1 : ℕ) - (l : ℝ) * r) -
    residueGapCellPronicMean r 1 l
  have hl1 : 1 ≤ (l : ℕ) := l.pos
  have hg1 : 1 ≤ (g : ℕ) := g.pos
  have hlk : (l : ℕ) ≤ k := by dsimp only [k]; omega
  have hk : 0 < k := l.pos.trans_le hlk
  have hp : 0 < p := by dsimp only [p]; positivity
  have hlp : (l : ℕ) ≤ p := by dsimp only [p]; nlinarith
  have hpr : p ≤ r := by dsimp only [p, r]; exact Nat.mul_le_mul_left _ hlk
  have hlr := hlp.trans hpr
  have ha : a = (l : ℕ) * r := by dsimp only [a, p, r]; ring
  have hat : a ≤ t := by dsimp only [t]; omega
  have htb : t ≤ b := by dsimp only [t, a, b]; nlinarith
  have hsub : (l : ℕ) - 1 + 1 = (l : ℕ) := Nat.sub_add_cancel hl1
  have ht : t = (l : ℕ) * (r + 1) := by dsimp only [t]; rw [ha]; ring
  have hrhi : b ≤ ((l : ℕ) + 1) * r := by dsimp only [b]; change k * p = (l : ℕ) * r at ha; nlinarith
  have hleft (n : ℕ) (hn : n ∈ Ico a t) : V n = C := by
    have hnlo := (mem_Ico.mp hn).1
    have hnhi := (mem_Ico.mp hn).2
    have hnrlo : (l : ℕ) * r ≤ n := by simpa only [ha] using hnlo
    have hnrhi : n < ((l : ℕ) + 1) * r := (hnhi.trans_le htb).trans_le hrhi
    have hnqlo : ((l : ℕ) - 1) * (r + 1) ≤ n := by
      calc
        _ = ((l : ℕ) - 1) * r + ((l : ℕ) - 1) := by ring
        _ ≤ ((l : ℕ) - 1) * r + r := Nat.add_le_add_left (by omega) _
        _ = ((l : ℕ) - 1 + 1) * r := by ring
        _ = (l : ℕ) * r := by rw [hsub]
        _ ≤ n := hnrlo
    have hnqhi : n < ((l : ℕ) - 1 + 1) * (r + 1) := by rw [hsub, ← ht]; exact hnhi
    dsimp only [V, C]
    rw [quotient_mod_cast hnrlo hnrhi, quotient_mod_cast hnqlo hnqhi]
    ring
  have hright (n : ℕ) (hn : n ∈ Ico t b) : V n = C + ((r : ℝ) + 1) := by
    have hnlo := (mem_Ico.mp hn).1
    have hnhi := (mem_Ico.mp hn).2
    have hnrlo : (l : ℕ) * r ≤ n := by rw [← ha]; exact hat.trans hnlo
    have hnrhi : n < ((l : ℕ) + 1) * r := hnhi.trans_le hrhi
    have hnqlo : (l : ℕ) * (r + 1) ≤ n := by simpa only [ht] using hnlo
    have hnqhi : n < ((l : ℕ) + 1) * (r + 1) := by nlinarith
    dsimp only [V, C]
    rw [quotient_mod_cast hnrlo hnrhi, quotient_mod_cast hnqlo hnqhi]
    rw [Nat.cast_sub hl1, Nat.cast_one]
    push_cast
    ring
  have hf : (∑ n ∈ Ico a t, W n * V n / ((n : ℝ) * ((n : ℝ) + 1))) =
      C * ∑ n ∈ Ico a t, W n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [hleft n hn]
    ring
  have ht' : (∑ n ∈ Ico t b, W n * V n / ((n : ℝ) * ((n : ℝ) + 1))) =
      (C + ((r : ℝ) + 1)) * ∑ n ∈ Ico t b, W n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [hright n hn]
    ring
  have hz := (residueGapCellPronicMoments ⟨p, hp⟩ ⟨k, hk⟩ 1).1
  change (∑ n ∈ Ico a b, W n / ((n : ℝ) * ((n : ℝ) + 1))) = 0 at hz
  rw [← sum_Ico_consecutive (fun n => W n / ((n : ℝ) * ((n : ℝ) + 1))) hat htb] at hz
  change (∑ n ∈ Ico a b, W n * V n / ((n : ℝ) * ((n : ℝ) + 1))) =
    ((r : ℝ) + 1) * ∑ n ∈ Ico t b, W n / ((n : ℝ) * ((n : ℝ) + 1))
  rw [← sum_Ico_consecutive (fun n => W n * V n / ((n : ℝ) * ((n : ℝ) + 1))) hat htb, hf, ht']
  linear_combination C * hz

/-- The exact shared-start covariance is the value of a positive pronic tent. -/
theorem sharedBirthUnitGapCovariance_eq (g l : ℕ+) (offset : ℕ) :
    let k := (l : ℕ) + offset
    let p := (g : ℕ) * (l : ℕ)
    let j := k * p / (p + 1)
    let s := (j + 1) * (p + 1)
    sharedBirthUnitGapCovariance g l offset =
      if s < (k + 1) * p then
        if k * p + (l : ℕ) ≤ s then
          (((k : ℝ) + 1) * p - s) / (((j : ℝ) + 1) * p)
        else
          ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) / (((j : ℝ) + 1) * p)
      else 0 := by
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  let r := (g : ℕ) * k
  let j := k * p / (p + 1)
  let s := (j + 1) * (p + 1)
  let t := k * p + (l : ℕ)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hg1 : 1 ≤ (g : ℕ) := g.pos
  have hlp : (l : ℕ) ≤ p := by dsimp only [p]; nlinarith
  have hthi : t ≤ (k + 1) * p := by dsimp only [t]; nlinarith
  have htlo : k * p ≤ t := by dsimp only [t]; omega
  have htail := centered_cell_tail ⟨p, hp⟩ ⟨k, hk⟩ 1 t htlo hthi
  change (∑ n ∈ Ico t ((k + 1) * p),
      (((n % p : ℕ) : ℝ) - ((n % (p + 1) : ℕ) : ℝ) - residueGapCellPronicMean p 1 k) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
    if s < (k + 1) * p then
      if t ≤ s then
        (((k : ℝ) + 1) * p - s) * ((t : ℝ) - (k : ℝ) * p) /
          (((j : ℝ) + 1) * p * t)
      else
        ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - t) /
          (((j : ℝ) + 1) * p * t)
    else 0 at htail
  change sharedBirthUnitGapCovariance g l offset =
    if s < (k + 1) * p then
      if t ≤ s then
        (((k : ℝ) + 1) * p - s) / (((j : ℝ) + 1) * p)
      else ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) / (((j : ℝ) + 1) * p)
    else 0
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have htcast : (t : ℝ) = (l : ℝ) * ((r : ℝ) + 1) := by
    dsimp only [t, p, r]
    push_cast
    ring
  have htleft : (t : ℝ) - (k : ℝ) * p = (l : ℝ) := by
    dsimp only [t]
    push_cast
    ring
  have htright : ((k : ℝ) + 1) * p - t = (l : ℝ) * ((g : ℝ) - 1) := by
    dsimp only [t, p]
    push_cast
    ring
  rw [shared_birth_pairing_tail]
  change ((r : ℝ) + 1) * (∑ n ∈ Ico t ((k + 1) * p),
      (((n % p : ℕ) : ℝ) - ((n % (p + 1) : ℕ) : ℝ) - residueGapCellPronicMean p 1 k) /
        ((n : ℝ) * ((n : ℝ) + 1))) = _
  rw [htail]
  by_cases hs : s < (k + 1) * p
  · simp only [if_pos hs]
    by_cases ht : t ≤ s
    · simp only [if_pos ht]
      rw [htleft, htcast]
      field_simp
    · simp only [if_neg ht]
      rw [htright, htcast]
      field_simp
  · simp only [if_neg hs, mul_zero]


/-- Shared-start centered unit-gap cells never have negative covariance. -/
theorem sharedBirthUnitGapCovariance_nonneg (g l : ℕ+) (offset : ℕ) :
    0 ≤ sharedBirthUnitGapCovariance g l offset := by
  rw [sharedBirthUnitGapCovariance_eq]
  split_ifs with hs ht
  · apply div_nonneg _ (by positivity)
    have hsR : (((((l : ℕ) + offset) * ((g : ℕ) * (l : ℕ)) /
        ((g : ℕ) * (l : ℕ) + 1) + 1) * ((g : ℕ) * (l : ℕ) + 1) : ℕ) : ℝ) <
        (((l : ℕ) + offset : ℕ) + 1 : ℝ) * ((g : ℕ) * (l : ℕ) : ℕ) := by
      exact_mod_cast hs
    exact sub_nonneg.mpr hsR.le
  · apply div_nonneg _ (by positivity)
    apply mul_nonneg
    · have h := Nat.lt_mul_div_succ (((l : ℕ) + offset) * ((g : ℕ) * (l : ℕ)))
        (by positivity : 0 < (g : ℕ) * (l : ℕ) + 1)
      have hR : (((l : ℕ) + offset : ℕ) : ℝ) * ((g : ℕ) * (l : ℕ) : ℕ) <
          (((((l : ℕ) + offset) * ((g : ℕ) * (l : ℕ)) /
          ((g : ℕ) * (l : ℕ) + 1) + 1) * ((g : ℕ) * (l : ℕ) + 1) : ℕ) : ℝ) := by
        have hnat : ((l : ℕ) + offset) * ((g : ℕ) * (l : ℕ)) <
            ((((l : ℕ) + offset) * ((g : ℕ) * (l : ℕ))) /
              ((g : ℕ) * (l : ℕ) + 1) + 1) * ((g : ℕ) * (l : ℕ) + 1) := by
          simpa only [Nat.mul_comm] using h
        exact_mod_cast hnat
      exact sub_nonneg.mpr hR.le
    · have hg : (1 : ℝ) ≤ g := by exact_mod_cast g.pos
      linarith
  · exact le_rfl

/-- The product-start channel vanishes, whether or not the two moduli are coprime. -/
theorem sharedBirthUnitGapCovariance_one (l : ℕ+) (offset : ℕ) :
    sharedBirthUnitGapCovariance 1 l offset = 0 := by
  have h1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  simpa only [sharedBirthUnitGapCovariance, h1, Nat.one_mul, Nat.mul_comm] using
    residueGapProductBirth_centered_covariance_eq_zero l offset

/-- Positive shared-start covariance is exactly the common-factor interior-jump case. -/
theorem sharedBirthUnitGapCovariance_pos_iff (g l : ℕ+) (offset : ℕ) :
    let k := (l : ℕ) + offset
    let p := (g : ℕ) * (l : ℕ)
    let s := (k * p / (p + 1) + 1) * (p + 1)
    0 < sharedBirthUnitGapCovariance g l offset ↔ 1 < (g : ℕ) ∧ s < (k + 1) * p := by
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  let j := k * p / (p + 1)
  let s := (j + 1) * (p + 1)
  change 0 < sharedBirthUnitGapCovariance g l offset ↔ 1 < (g : ℕ) ∧ s < (k + 1) * p
  have he := sharedBirthUnitGapCovariance_eq g l offset
  change sharedBirthUnitGapCovariance g l offset =
    if s < (k + 1) * p then
      if k * p + (l : ℕ) ≤ s then
        (((k : ℝ) + 1) * p - s) / (((j : ℝ) + 1) * p)
      else ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) / (((j : ℝ) + 1) * p)
    else 0 at he
  have hp : 0 < p := by dsimp only [p]; positivity
  constructor
  · intro hn
    constructor
    · by_contra hg
      have hgeq : g = 1 := by
        apply Subtype.ext
        have hgpos := g.pos
        change (g : ℕ) = 1
        omega
      rw [hgeq, sharedBirthUnitGapCovariance_one] at hn
      exact lt_irrefl _ hn
    · by_contra hs
      rw [he, if_neg hs] at hn
      exact lt_irrefl _ hn
  · rintro ⟨hg, hs⟩
    rw [he, if_pos hs]
    have hgR : (1 : ℝ) < g := by exact_mod_cast hg
    by_cases ht : k * p + (l : ℕ) ≤ s
    · rw [if_pos ht]
      have hsR : (s : ℝ) < ((k : ℝ) + 1) * p := by exact_mod_cast hs
      exact div_pos (sub_pos.mpr hsR) (by positivity)
    · rw [if_neg ht]
      have ha : k * p < s := by
        simpa only [s, j, Nat.mul_comm] using Nat.lt_mul_div_succ (k * p) (by positivity : 0 < p + 1)
      have haR : (k : ℝ) * p < (s : ℝ) := by exact_mod_cast ha
      exact div_pos (mul_pos (sub_pos.mpr haR) (sub_pos.mpr hgR)) (by positivity)

private theorem shared_birth_preoverlap (g l : ℕ+) (offset : ℕ)
    (hkp : (l : ℕ) + offset ≤ (g : ℕ) * (l : ℕ)) :
    sharedBirthUnitGapCovariance g l offset =
      1 / (((l : ℕ) + offset : ℕ) : ℝ) - 1 / (((g : ℕ) * (l : ℕ) : ℕ) : ℝ) := by
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  change k ≤ p at hkp
  have hk : 0 < k := by dsimp only [k]; positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hlk : (l : ℕ) ≤ k := by dsimp only [k]; omega
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hj : k * p / (p + 1) = k - 1 := by
    apply Nat.div_eq_of_lt_le
    · calc
        _ = (k - 1) * p + (k - 1) := by ring
        _ ≤ (k - 1) * p + p := Nat.add_le_add_left (by omega) _
        _ = (k - 1 + 1) * p := by ring
        _ = _ := by rw [hsub]
    · rw [hsub]
      nlinarith
  have he := sharedBirthUnitGapCovariance_eq g l offset
  change sharedBirthUnitGapCovariance g l offset =
    if (k * p / (p + 1) + 1) * (p + 1) < (k + 1) * p then
      if k * p + (l : ℕ) ≤ (k * p / (p + 1) + 1) * (p + 1) then
        (((k : ℝ) + 1) * p - ((k * p / (p + 1) + 1) * (p + 1) : ℕ)) /
          ((((k * p / (p + 1) : ℕ) : ℝ) + 1) * p)
      else (((k * p / (p + 1) + 1) * (p + 1) : ℕ) - (k : ℝ) * p) *
        ((g : ℝ) - 1) / ((((k * p / (p + 1) : ℕ) : ℝ) + 1) * p)
    else 0 at he
  rw [hj, hsub] at he
  have hjR : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hsub
  rw [hjR] at he
  have ht : k * p + (l : ℕ) ≤ k * (p + 1) := by nlinarith
  change sharedBirthUnitGapCovariance g l offset = 1 / (k : ℝ) - 1 / (p : ℝ)
  by_cases hstrict : k < p
  · have hs : k * (p + 1) < (k + 1) * p := by nlinarith
    rw [he, if_pos hs, if_pos ht]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hkeq : k = p := by omega
    have hs : ¬k * (p + 1) < (k + 1) * p := by nlinarith
    rw [he, if_neg hs, hkeq, sub_self]

/-- Distinct ordered gaps can have positive mixed-level covariance equal to a diagonal variance. -/
theorem sharedBirthUnitGapCovariance_coherent (l : ℕ+) (offset padding : ℕ) :
    let k := (l : ℕ) + (offset + 1)
    let g : ℕ+ := ⟨k + padding + 1, by positivity⟩
    let p := (g : ℕ) * (l : ℕ)
    sharedBirthUnitGapCovariance g l (offset + 1) = 1 / (k : ℝ) - 1 / (p : ℝ) ∧
      0 < sharedBirthUnitGapCovariance g l (offset + 1) := by
  let k := (l : ℕ) + (offset + 1)
  let g : ℕ+ := ⟨k + padding + 1, by positivity⟩
  let p := (g : ℕ) * (l : ℕ)
  have hl1 : 1 ≤ (l : ℕ) := l.pos
  have hk : 0 < k := by dsimp only [k]; positivity
  have hkp : k < p := by
    change k < (k + padding + 1) * (l : ℕ)
    nlinarith
  have he := shared_birth_preoverlap g l (offset + 1) hkp.le
  change sharedBirthUnitGapCovariance g l (offset + 1) = 1 / (k : ℝ) - 1 / (p : ℝ) at he
  change sharedBirthUnitGapCovariance g l (offset + 1) = 1 / (k : ℝ) - 1 / (p : ℝ) ∧ _
  refine ⟨he, ?_⟩
  rw [he]
  have hkpR : (k : ℝ) < p := by exact_mod_cast hkp
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (by positivity : 0 < (p : ℝ)) (by positivity : 0 < (k : ℝ))).mpr
  simpa only [one_mul] using hkpR


end
end GaloisForLFunctions.BezoutValuationIncidence
