import GaloisForLFunctions.RHTower.ThetaPowerFamily

/-!
# The theta series of the quadratic character modulo `8`

For the even primitive character `χ₈ = (2/·)` put `ϑ₈(τ) = ∑_{k ∈ ℤ} χ₈(k) e^{πiτk²/8}`.  Two exact
identities are proved on the upper half-plane:

* `θ₂(τ) θ₄(τ) = ϑ₈(τ)²/2`.  The map `(n, m) ↦ (2n+1+2m, 2n+1-2m)` is a bijection of `ℤ²` onto the
  odd pairs `(j, k)` with `j ≡ k (mod 4)`; it carries `(n+½)² + m²` to `(j² + k²)/8` and the sign
  `(-1)^m` to `χ₈(j)χ₈(k)`.  The odd pairs with `j ≡ -k (mod 4)` contribute the same amount by
  `k ↦ -k`.
* `ϑ₈(τ) = e^{-πi/8} θ₂((τ+1)/2)`, because `e^{πi(2n+1)²/8} = e^{πi/8} χ₈(2n+1)`.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-! ## The character -/

/-- `χ₈ = (2/·)` on the integers, as a real number. -/
def chiEight (k : ℤ) : ℝ := ((ZMod.χ₈ (k : ZMod 8) : ℤ) : ℝ)

theorem chiEight_eq (k : ℤ) :
    chiEight k = if k % 2 = 0 then 0 else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1 := by
  unfold chiEight; rw [ZMod.χ₈_int_eq_if_mod_eight]; split_ifs <;> simp

theorem chiEight_neg (k : ℤ) : chiEight (-k) = chiEight k := by
  rw [chiEight_eq, chiEight_eq]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem chiEight_of_even {k : ℤ} (h : k % 2 = 0) : chiEight k = 0 := by
  rw [chiEight_eq, if_pos h]

theorem odd_of_chiEight_ne_zero {k : ℤ} (h : chiEight k ≠ 0) : k % 2 = 1 := by
  by_contra h'
  exact h (chiEight_of_even (by omega))

theorem abs_chiEight_le (k : ℤ) : |chiEight k| ≤ 1 := by
  rw [chiEight_eq]; split_ifs <;> norm_num

theorem chiEight_add_eight_mul (q k : ℤ) : chiEight (8 * q + k) = chiEight k := by
  rw [chiEight_eq, chiEight_eq]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The sign `(-1)^m` as a real number. -/
def parSign (m : ℤ) : ℝ := if m % 2 = 0 then 1 else -1

theorem chiEight_line (n m : ℤ) :
    chiEight (2 * n + 1 + 2 * m) * chiEight (2 * n + 1 - 2 * m) = parSign m := by
  unfold parSign
  rw [chiEight_eq, chiEight_eq]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ## Gaussian summability -/

theorem jacobiTheta₂_term_zero_I_mul (k : ℤ) (c : ℝ) :
    jacobiTheta₂_term k 0 (I * (c : ℂ)) = (Real.exp (-(π * c * (k : ℝ) ^ 2)) : ℂ) := by
  rw [jacobiTheta₂_term, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem summable_gauss_int {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-(π * c * (k : ℝ) ^ 2))) := by
  have h := ((summable_jacobiTheta₂_term_iff 0 (I * (c : ℂ))).mpr (by simpa using hc)).norm
  refine h.congr (fun k => ?_)
  rw [jacobiTheta₂_term_zero_I_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_cexp_pi_I_mul (τ : ℂ) (c : ℝ) :
    ‖Complex.exp (π * I * τ * c)‖ = Real.exp (-(π * τ.im * c)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-! ## The character theta series -/

/-- `ϑ₈(τ) = ∑_{k ∈ ℤ} χ₈(k) e^{πiτk²/8}`. -/
def thetaChiEight (τ : ℂ) : ℂ :=
  ∑' k : ℤ, (chiEight k : ℂ) * Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 8))

theorem norm_thetaChiEight_term_le (τ : ℂ) (k : ℤ) :
    ‖(chiEight k : ℂ) * Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 8))‖ ≤
      Real.exp (-(π * (τ.im / 8) * (k : ℝ) ^ 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := norm_cexp_pi_I_mul τ ((k : ℝ) ^ 2 / 8)
  have e : ((((k : ℝ) ^ 2 / 8 : ℝ)) : ℂ) = (k : ℂ) ^ 2 / 8 := by push_cast; ring
  rw [e] at h
  rw [h]
  have := abs_chiEight_le k
  have e2 : -(π * τ.im * ((k : ℝ) ^ 2 / 8)) = -(π * (τ.im / 8) * (k : ℝ) ^ 2) := by ring
  rw [e2]
  calc |chiEight k| * Real.exp (-(π * (τ.im / 8) * (k : ℝ) ^ 2))
      ≤ 1 * Real.exp (-(π * (τ.im / 8) * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = _ := one_mul _

theorem summable_thetaChiEight_norm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun k : ℤ => ‖(chiEight k : ℂ) * Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 8))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaChiEight_term_le τ)
    (summable_gauss_int (by positivity))

/-! ## `θ₂` and `θ₄` as Jacobi series -/

theorem thetaTwo_eq_jacobi (τ : ℂ) :
    thetaTwo τ = ∑' n : ℤ, Complex.exp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  unfold thetaTwo
  rw [jacobiTheta₂, ← tsum_mul_left]

theorem thetaFour_eq_jacobi (τ : ℂ) : thetaFour τ = ∑' m : ℤ, jacobiTheta₂_term m (1 / 2) τ := rfl

theorem jacobi_two_term (τ : ℂ) (n : ℤ) :
    Complex.exp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ =
      Complex.exp (π * I * τ * (((n : ℂ) + 1 / 2) ^ 2)) := by
  rw [jacobiTheta₂_term, ← Complex.exp_add]; congr 1; ring

theorem jacobi_four_term (τ : ℂ) (m : ℤ) :
    jacobiTheta₂_term m (1 / 2) τ = (parSign m : ℂ) * Complex.exp (π * I * τ * (m : ℂ) ^ 2) := by
  rw [jacobiTheta₂_term]
  have e : 2 * π * I * (m : ℂ) * (1 / 2) + π * I * (m : ℂ) ^ 2 * τ =
      (m : ℂ) * (π * I) + π * I * τ * (m : ℂ) ^ 2 := by ring
  rw [e, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  unfold parSign
  split_ifs with h
  · have : Even m := Int.even_iff.mpr h
    simp [this.neg_one_zpow]
  · have : Odd m := Int.odd_iff.mpr (by omega)
    simp [this.neg_one_zpow]

/-! ## The product identity -/

/-- The summand of `ϑ₈²` on `ℤ²`. -/
def chiPairTerm (τ : ℂ) (p : ℤ × ℤ) : ℂ :=
  ((chiEight p.1 * chiEight p.2 : ℝ) : ℂ) *
    Complex.exp (π * I * τ * (((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) / 8))

/-- The pairing maps. -/
def chiPairMap (q : ℤ × ℤ) : ℤ × ℤ := (2 * q.1 + 1 + 2 * q.2, 2 * q.1 + 1 - 2 * q.2)

def chiPairMap' (q : ℤ × ℤ) : ℤ × ℤ := (2 * q.1 + 1 + 2 * q.2, -(2 * q.1 + 1 - 2 * q.2))

theorem chiPairMap_injective : Function.Injective chiPairMap := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [chiPairMap, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem chiPairMap'_injective : Function.Injective chiPairMap' := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [chiPairMap', Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem chiPairTerm_map (τ : ℂ) (q : ℤ × ℤ) :
    chiPairTerm τ (chiPairMap q) =
      (parSign q.2 : ℂ) * Complex.exp (π * I * τ * (((q.1 : ℂ) + 1 / 2) ^ 2 + (q.2 : ℂ) ^ 2)) := by
  unfold chiPairTerm chiPairMap
  simp only
  rw [chiEight_line]
  congr 2
  push_cast
  ring

theorem chiPairTerm_map' (τ : ℂ) (q : ℤ × ℤ) :
    chiPairTerm τ (chiPairMap' q) = chiPairTerm τ (chiPairMap q) := by
  unfold chiPairTerm chiPairMap chiPairMap'
  simp only
  rw [chiEight_neg]
  congr 2
  push_cast
  ring

theorem norm_chiPairTerm_le (τ : ℂ) (p : ℤ × ℤ) :
    ‖chiPairTerm τ p‖ ≤
      Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) * Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2)) := by
  unfold chiPairTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h := norm_cexp_pi_I_mul τ (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 8)
  have e : (((((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 8 : ℝ)) : ℂ) = ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) / 8 := by
    push_cast; ring
  rw [e] at h
  rw [h]
  have h1 := abs_chiEight_le p.1
  have h2 := abs_chiEight_le p.2
  have e2 : Real.exp (-(π * τ.im * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 8))) =
      Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) * Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e2]
  have hE : 0 ≤ Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) *
      Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2)) := by positivity
  calc |chiEight p.1| * |chiEight p.2| * (Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) *
        Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2)))
      ≤ 1 * 1 * (Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) *
        Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2))) := by
        gcongr
    _ = _ := by ring

theorem summable_chiPairTerm_norm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => ‖chiPairTerm τ p‖) := by
  have hg := summable_gauss_int (c := τ.im / 8) (by positivity)
  have hprod : Summable (fun p : ℤ × ℤ => Real.exp (-(π * (τ.im / 8) * (p.1 : ℝ) ^ 2)) *
      Real.exp (-(π * (τ.im / 8) * (p.2 : ℝ) ^ 2))) :=
    hg.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_chiPairTerm_le τ) hprod

theorem thetaChiEight_sq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaChiEight τ ^ 2 = ∑' p : ℤ × ℤ, chiPairTerm τ p := by
  have hs := summable_thetaChiEight_norm hτ
  rw [sq, thetaChiEight, tsum_mul_tsum_of_summable_norm hs hs]
  refine tsum_congr (fun p => ?_)
  unfold chiPairTerm
  push_cast
  rw [show (chiEight p.1 : ℂ) * Complex.exp (π * I * τ * ((p.1 : ℂ) ^ 2 / 8)) *
      ((chiEight p.2 : ℂ) * Complex.exp (π * I * τ * ((p.2 : ℂ) ^ 2 / 8))) =
      (chiEight p.1 : ℂ) * (chiEight p.2 : ℂ) *
        (Complex.exp (π * I * τ * ((p.1 : ℂ) ^ 2 / 8)) *
          Complex.exp (π * I * τ * ((p.2 : ℂ) ^ 2 / 8))) by ring, ← Complex.exp_add]
  congr 2
  ring

theorem thetaTwo_mul_thetaFour_eq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo τ * thetaFour τ =
      ∑' q : ℤ × ℤ, (parSign q.2 : ℂ) *
        Complex.exp (π * I * τ * (((q.1 : ℂ) + 1 / 2) ^ 2 + (q.2 : ℂ) ^ 2)) := by
  have h2 : Summable (fun n : ℤ => ‖Complex.exp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ‖) := by
    have := ((summable_jacobiTheta₂_term_iff (τ / 2) τ).mpr hτ).norm
    refine (this.mul_left ‖Complex.exp (π * I * τ / 4)‖).congr (fun n => ?_)
    rw [norm_mul]
  have h4 : Summable (fun m : ℤ => ‖jacobiTheta₂_term m (1 / 2) τ‖) :=
    ((summable_jacobiTheta₂_term_iff (1 / 2) τ).mpr hτ).norm
  rw [thetaTwo_eq_jacobi, thetaFour_eq_jacobi, tsum_mul_tsum_of_summable_norm h2 h4]
  refine tsum_congr (fun q => ?_)
  rw [jacobi_two_term, jacobi_four_term]
  rw [show Complex.exp (π * I * τ * (((q.1 : ℂ) + 1 / 2) ^ 2)) *
      ((parSign q.2 : ℂ) * Complex.exp (π * I * τ * (q.2 : ℂ) ^ 2)) =
      (parSign q.2 : ℂ) * (Complex.exp (π * I * τ * (((q.1 : ℂ) + 1 / 2) ^ 2)) *
        Complex.exp (π * I * τ * (q.2 : ℂ) ^ 2)) by ring, ← Complex.exp_add]
  congr 2
  ring

/-- **The product identity** `θ₂θ₄ = ϑ₈²/2`. -/
theorem thetaTwo_mul_thetaFour_eq_thetaChiEight_sq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo τ * thetaFour τ = thetaChiEight τ ^ 2 / 2 := by
  have hsum := summable_chiPairTerm_norm hτ
  have hS : Summable (chiPairTerm τ) := hsum.of_norm
  set f := chiPairTerm τ with hf
  set fA : ℤ × ℤ → ℂ := fun p => if (p.1 - p.2) % 4 = 0 then f p else 0 with hfA
  set fB : ℤ × ℤ → ℂ := fun p => if (p.1 - p.2) % 4 = 0 then 0 else f p with hfB
  have hsplit : ∀ p, f p = fA p + fB p := by
    intro p; simp only [hfA, hfB]; split_ifs <;> simp
  have hA : Summable fA := by
    refine Summable.of_norm_bounded hsum (fun p => ?_)
    simp only [hfA]; split_ifs <;> simp
  have hB : Summable fB := by
    refine Summable.of_norm_bounded hsum (fun p => ?_)
    simp only [hfB]; split_ifs <;> simp
  have hodd : ∀ p, f p ≠ 0 → p.1 % 2 = 1 ∧ p.2 % 2 = 1 := by
    intro p hp
    have hne : chiEight p.1 * chiEight p.2 ≠ 0 := by
      intro h0; apply hp; simp only [hf, chiPairTerm, h0, Complex.ofReal_zero, zero_mul]
    exact ⟨odd_of_chiEight_ne_zero (left_ne_zero_of_mul hne),
      odd_of_chiEight_ne_zero (right_ne_zero_of_mul hne)⟩
  have hsuppA : Function.support fA ⊆ Set.range chiPairMap := by
    intro p hp
    have hp' : fA p ≠ 0 := hp
    simp only [hfA] at hp'
    by_cases h4 : (p.1 - p.2) % 4 = 0
    · rw [if_pos h4] at hp'
      obtain ⟨h1, h2⟩ := hodd p hp'
      refine ⟨((p.1 + p.2 - 2) / 4, (p.1 - p.2) / 4), ?_⟩
      simp only [chiPairMap]
      ext <;> simp only <;> omega
    · rw [if_neg h4] at hp'; exact absurd rfl hp'
  have hsuppB : Function.support fB ⊆ Set.range chiPairMap' := by
    intro p hp
    have hp' : fB p ≠ 0 := hp
    simp only [hfB] at hp'
    by_cases h4 : (p.1 - p.2) % 4 = 0
    · rw [if_pos h4] at hp'; exact absurd rfl hp'
    · rw [if_neg h4] at hp'
      obtain ⟨h1, h2⟩ := hodd p hp'
      refine ⟨((p.1 - p.2 - 2) / 4, (p.1 + p.2) / 4), ?_⟩
      simp only [chiPairMap']
      ext <;> simp only <;> omega
  have hA' : ∑' p, fA p = ∑' q, f (chiPairMap q) := by
    rw [← chiPairMap_injective.tsum_eq (f := fA) hsuppA]
    refine tsum_congr (fun q => ?_)
    have hc : ((chiPairMap q).1 - (chiPairMap q).2) % 4 = 0 := by
      simp only [chiPairMap]; omega
    show (if ((chiPairMap q).1 - (chiPairMap q).2) % 4 = 0 then f (chiPairMap q) else 0) =
      f (chiPairMap q)
    rw [if_pos hc]
  have hB' : ∑' p, fB p = ∑' q, f (chiPairMap q) := by
    rw [← chiPairMap'_injective.tsum_eq (f := fB) hsuppB]
    refine tsum_congr (fun q => ?_)
    have hc : ¬ ((chiPairMap' q).1 - (chiPairMap' q).2) % 4 = 0 := by
      simp only [chiPairMap']; omega
    show (if ((chiPairMap' q).1 - (chiPairMap' q).2) % 4 = 0 then 0 else f (chiPairMap' q)) =
      f (chiPairMap q)
    rw [if_neg hc, hf, chiPairTerm_map']
  have htot : ∑' p, f p = 2 * ∑' q, f (chiPairMap q) := by
    rw [show (∑' p, f p) = ∑' p, (fA p + fB p) from tsum_congr hsplit, hA.tsum_add hB, hA', hB']
    ring
  rw [thetaChiEight_sq hτ, ← hf, htot, thetaTwo_mul_thetaFour_eq hτ]
  simp only [hf, chiPairTerm_map]
  ring

/-! ## `ϑ₈` through `θ₂` -/

theorem cexp_odd_sq_div_eight (n : ℤ) :
    Complex.exp (π * I * (((2 * n + 1 : ℤ) : ℂ) ^ 2 / 8)) =
      Complex.exp (π * I / 8) * (chiEight (2 * n + 1) : ℂ) := by
  obtain ⟨q, r, hr0, hr4, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, by omega, by omega, by omega⟩
  have hχ : chiEight (2 * (4 * q + r) + 1) = chiEight (2 * r + 1) := by
    rw [show 2 * (4 * q + r) + 1 = 8 * q + (2 * r + 1) by ring, chiEight_add_eight_mul]
  have e : (π : ℂ) * I * (((2 * (4 * q + r) + 1 : ℤ) : ℂ) ^ 2 / 8) =
      π * I * (((2 * r + 1 : ℤ) : ℂ) ^ 2 / 8) + ((4 * q ^ 2 + (2 * r + 1) * q : ℤ) : ℂ) *
        (2 * π * I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hχ]
  interval_cases r
  · rw [chiEight_eq]; norm_num; ring_nf
  · rw [chiEight_eq]
    have : (π : ℂ) * I * (((2 * 1 + 1 : ℤ) : ℂ) ^ 2 / 8) = π * I / 8 + π * I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; norm_num
  · rw [chiEight_eq]
    have : (π : ℂ) * I * (((2 * 2 + 1 : ℤ) : ℂ) ^ 2 / 8) = π * I / 8 + (1 : ℤ) * (2 * π * I) + π * I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      Complex.exp_pi_mul_I]; norm_num
  · rw [chiEight_eq]
    have : (π : ℂ) * I * (((2 * 3 + 1 : ℤ) : ℂ) ^ 2 / 8) = π * I / 8 + (3 : ℤ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]; norm_num

/-- **`ϑ₈(τ) = e^{-πi/8} θ₂((τ+1)/2)`.** -/
theorem thetaChiEight_eq_thetaTwo (τ : ℂ) :
    thetaChiEight τ = Complex.exp (-(π * I / 8)) * thetaTwo ((τ + 1) / 2) := by
  have hinj : Function.Injective (fun n : ℤ => 2 * n + 1) := by
    intro a b h; simp only at h; omega
  have hsupp : Function.support (fun k : ℤ => (chiEight k : ℂ) *
      Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 8))) ⊆ Set.range (fun n : ℤ => 2 * n + 1) := by
    intro k hk
    have hk' : chiEight k ≠ 0 := by
      intro h0; apply hk; simp [h0]
    have := odd_of_chiEight_ne_zero hk'
    exact ⟨(k - 1) / 2, by simp only; omega⟩
  unfold thetaChiEight
  rw [← hinj.tsum_eq hsupp, thetaTwo_eq_tsum, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  have e : (π : ℂ) * I * ((n : ℂ) + 1 / 2) ^ (2 : ℕ) * ((τ + 1) / 2) =
      π * I * (((2 * n + 1 : ℤ) : ℂ) ^ 2 / 8) + π * I * τ * ((((2 * n + 1 : ℤ) : ℂ)) ^ 2 / 8) := by
    push_cast; ring
  rw [e, Complex.exp_add, cexp_odd_sq_div_eight]
  have h1 : Complex.exp (-(π * I / 8)) * Complex.exp (π * I / 8) = 1 := by
    rw [← Complex.exp_add]; simp
  push_cast
  linear_combination (-(chiEight (2 * n + 1) : ℂ) *
    Complex.exp (π * I * τ * (((2 * (n : ℂ) + 1)) ^ 2 / 8))) * h1

end

end RHTower
