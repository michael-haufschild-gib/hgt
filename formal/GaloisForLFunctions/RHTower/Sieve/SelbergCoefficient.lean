import GaloisForLFunctions.RHTower.Sieve.SelbergError

/-!
# Closed form of the truncated Selberg coefficients

For a squarefree sifting modulus every divisor `l` of it factors as `d · (l/d)` into coprime
parts, so both the Möbius function and the Selberg terms split.  Two consequences:

`μ(l/d) · μ(l) = μ(d)`,   `g_l = g_d · g_{l/d}`   for `d ∣ l ∣ P`.

The first collapses the alternating sum defining the truncated Selberg weight into a *positive*
sum, giving the closed form

`w_d · ν_d · S_Y = μ(d) · U_d`,   `U_d = ∑_{l ∣ P, d ∣ l, l ≤ Y} g_l`,

so `|w_d| = U_d / (ν_d S_Y)`.  The coefficient bound `|w_d| ≤ 1` is therefore exactly the
inequality `U_d ≤ ν_d S_Y`, which the second consequence turns into a statement about a product
injection.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve
open scoped ArithmeticFunction.Moebius

/-- A divisor of a squarefree number is coprime to its cofactor. -/
theorem coprime_div_of_dvd_squarefree {l d : ℕ} (hl : Squarefree l) (hd : d ∣ l) :
    Nat.Coprime d (l / d) := by
  refine Nat.coprime_of_squarefree_mul ?_
  rwa [Nat.mul_div_cancel' hd]

/-- The Möbius factor of the Selberg inversion collapses to a single sign. -/
theorem moebius_div_mul_moebius {l d : ℕ} (hl : Squarefree l) (hd : d ∣ l) :
    (μ (l / d) : ℝ) * (μ l : ℝ) = (μ d : ℝ) := by
  have hcop : Nat.Coprime d (l / d) := coprime_div_of_dvd_squarefree hl hd
  have hsplit : (μ l : ℤ) = (μ d : ℤ) * (μ (l / d) : ℤ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hcast : (μ l : ℝ) = (μ d : ℝ) * (μ (l / d) : ℝ) := by exact_mod_cast hsplit
  have hsq : Squarefree (l / d) := hl.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
  have hmusq : (μ (l / d) : ℝ) ^ 2 = 1 := by
    have h : (μ (l / d) : ℤ) = (-1) ^ (ArithmeticFunction.cardFactors (l / d)) :=
      ArithmeticFunction.moebius_apply_of_squarefree hsq
    have hc : (μ (l / d) : ℝ) = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (l / d)) := by
      exact_mod_cast h
    rw [hc, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hcast, ← mul_assoc, mul_comm ((μ (l / d) : ℝ)) ((μ d : ℝ)), mul_assoc, ← sq, hmusq, mul_one]

/-- The Selberg terms split along a divisor of a squarefree modulus. -/
theorem selbergTerms_mul_div (s : BoundingSieve) {l d : ℕ} (hl : Squarefree l) (hd : d ∣ l) :
    s.selbergTerms l = s.selbergTerms d * s.selbergTerms (l / d) := by
  have hcop : Nat.Coprime d (l / d) := coprime_div_of_dvd_squarefree hl hd
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  exact selbergTerms_isMultiplicative.map_mul_of_coprime hcop

/-- The positive mass carried by the multiples of `d` inside the truncation. -/
noncomputable def selbergTruncU (s : BoundingSieve) (Y d : ℕ) : ℝ :=
  ∑ l ∈ {l ∈ s.prodPrimes.divisors | d ∣ l ∧ l ≤ Y}, s.selbergTerms l

theorem selbergTruncU_nonneg (s : BoundingSieve) (Y d : ℕ) : 0 ≤ selbergTruncU s Y d := by
  refine Finset.sum_nonneg ?_
  intro l hl
  exact (selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hl).1)).le

/-- **Closed form of the truncated Selberg coefficient.**  The alternating sum collapses to a
single sign times a positive mass. -/
theorem selbergTruncWeight_mul_nu_mul_mass (s : BoundingSieve) {Y d : ℕ}
    (hd : d ∣ s.prodPrimes) (hY : 1 ≤ Y) :
    selbergTruncWeight s Y d * s.nu d * selbergMassLE s Y
      = (μ d : ℝ) * selbergTruncU s Y d := by
  classical
  have hS := selbergMassLE_pos s hY
  have hnu : s.nu d ≠ 0 := nu_ne_zero hd
  unfold selbergTruncWeight selbergW
  rw [div_mul_cancel₀ _ hnu]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (if d ∣ l then (μ (l / d) : ℝ) * selbergTruncY s Y l else 0)
        = if d ∣ l ∧ l ≤ Y then (μ d : ℝ) * s.selbergTerms l / selbergMassLE s Y else 0 := by
    intro l hl
    have hlsq : Squarefree l :=
      s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
    by_cases hdl : d ∣ l
    · rw [if_pos hdl, selbergTruncY]
      by_cases hle : l ≤ Y
      · rw [if_pos hle, if_pos ⟨hdl, hle⟩]
        have hmu := moebius_div_mul_moebius hlsq hdl
        have hrw : (μ (l / d) : ℝ) * ((μ l : ℝ) * s.selbergTerms l / selbergMassLE s Y)
            = ((μ (l / d) : ℝ) * (μ l : ℝ)) * s.selbergTerms l / selbergMassLE s Y := by ring
        rw [hrw, hmu]
      · rw [if_neg hle, if_neg (fun hc => hle hc.2), mul_zero]
    · rw [if_neg hdl, if_neg (fun hc => hdl hc.1)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hpull : ∑ l ∈ {l ∈ s.prodPrimes.divisors | d ∣ l ∧ l ≤ Y},
        (μ d : ℝ) * s.selbergTerms l / selbergMassLE s Y
      = ((μ d : ℝ) / selbergMassLE s Y) * selbergTruncU s Y d := by
    rw [selbergTruncU, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    ring
  rw [hpull]
  field_simp

/-- The truncated Selberg coefficient in absolute value. -/
theorem abs_selbergTruncWeight_mul (s : BoundingSieve) {Y d : ℕ}
    (hd : d ∣ s.prodPrimes) (hY : 1 ≤ Y) :
    |selbergTruncWeight s Y d| * (s.nu d * selbergMassLE s Y) = selbergTruncU s Y d := by
  have hS := selbergMassLE_pos s hY
  have hnu : 0 < s.nu d := nu_pos_of_dvd_prodPrimes hd
  have hkey := selbergTruncWeight_mul_nu_mul_mass s hd hY
  have hmusq : |(μ d : ℝ)| = 1 := by
    have h := moebius_sq_eq_one_of_dvd (s := s) hd
    have : |(μ d : ℝ)| ^ 2 = 1 := by rw [sq_abs]; exact h
    nlinarith [abs_nonneg ((μ d : ℝ)), this]
  have habs : |selbergTruncWeight s Y d * s.nu d * selbergMassLE s Y|
      = |(μ d : ℝ)| * |selbergTruncU s Y d| := by
    rw [hkey, abs_mul]
  rw [abs_mul, abs_mul, abs_of_pos hnu, abs_of_pos hS] at habs
  rw [hmusq, one_mul, abs_of_nonneg (selbergTruncU_nonneg s Y d)] at habs
  rw [← habs]
  ring

/-- The sum of Selberg terms over the divisors of `d`. -/
theorem sum_divisors_selbergTerms (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    ∑ a ∈ d.divisors, s.selbergTerms a = s.selbergTerms d * (s.nu d)⁻¹ := by
  classical
  have h := sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  rw [← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd s.prodPrimes_squarefree.ne_zero hd] at h
  exact h

/-- **Key inequality.**  The mass carried by the multiples of `d` inside the truncation is at most
`ν_d` times the whole truncated mass. -/
theorem selbergTruncU_le (s : BoundingSieve) {Y d : ℕ} (hd : d ∣ s.prodPrimes) :
    selbergTruncU s Y d ≤ s.nu d * selbergMassLE s Y := by
  classical
  have hnu : 0 < s.nu d := nu_pos_of_dvd_prodPrimes hd
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  set F : Finset ℕ := {l ∈ s.prodPrimes.divisors | d ∣ l ∧ l ≤ Y} with hF
  set T : ℝ := ∑ l ∈ F, s.selbergTerms (l / d) with hT
  have hmemF : ∀ l ∈ F, l ∣ s.prodPrimes ∧ d ∣ l ∧ l ≤ Y := by
    intro l hl
    obtain ⟨hlmem, hdl, hle⟩ := Finset.mem_filter.1 hl
    exact ⟨Nat.dvd_of_mem_divisors hlmem, hdl, hle⟩
  have hU : selbergTruncU s Y d = s.selbergTerms d * T := by
    rw [selbergTruncU, hT, Finset.mul_sum, ← hF]
    refine Finset.sum_congr rfl ?_
    intro l hl
    obtain ⟨hlP, hdl, -⟩ := hmemF l hl
    exact selbergTerms_mul_div s (s.prodPrimes_squarefree.squarefree_of_dvd hlP) hdl
  set ι : ℕ × ℕ → ℕ := fun x => x.1 * (x.2 / d) with hι
  have hinjOn : ∀ x ∈ d.divisors ×ˢ F, ∀ y ∈ d.divisors ×ˢ F, ι x = ι y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.1 hy
    obtain ⟨hx1d, hd0⟩ := Nat.mem_divisors.1 hx1
    obtain ⟨hy1d, -⟩ := Nat.mem_divisors.1 hy1
    obtain ⟨hxP, hxdvd, -⟩ := hmemF x.2 hx2
    obtain ⟨hyP, hydvd, -⟩ := hmemF y.2 hy2
    have hcopx : Nat.Coprime (x.2 / d) d :=
      (coprime_div_of_dvd_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hxP)
        hxdvd).symm
    have hcopy : Nat.Coprime (y.2 / d) d :=
      (coprime_div_of_dvd_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hyP)
        hydvd).symm
    have hgx : Nat.gcd (ι x) d = x.1 := by
      rw [hι]
      simp only
      rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel _ hcopx, Nat.gcd_eq_left hx1d]
    have hgy : Nat.gcd (ι y) d = y.1 := by
      rw [hι]
      simp only
      rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel _ hcopy, Nat.gcd_eq_left hy1d]
    have h1 : x.1 = y.1 := by rw [← hgx, ← hgy, hxy]
    have hx1pos : 0 < x.1 := Nat.pos_of_mem_divisors hx1
    have h2 : x.2 / d = y.2 / d := by
      have := hxy
      rw [hι] at this
      simp only at this
      rw [h1] at this
      exact Nat.eq_of_mul_eq_mul_left (h1 ▸ hx1pos) this
    have h3 : x.2 = y.2 := by
      rw [← Nat.mul_div_cancel' hxdvd, ← Nat.mul_div_cancel' hydvd, h2]
    exact Prod.ext h1 h3
  have hmaps : ∀ x ∈ d.divisors ×ˢ F, ι x ∈ {l ∈ s.prodPrimes.divisors | l ≤ Y} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hx
    obtain ⟨hx1d, -⟩ := Nat.mem_divisors.1 hx1
    obtain ⟨hxP, hxdvd, hxle⟩ := hmemF x.2 hx2
    have hdvd : ι x ∣ x.2 := by
      rw [hι]
      simp only
      conv_rhs => rw [← Nat.mul_div_cancel' hxdvd]
      exact Nat.mul_dvd_mul hx1d dvd_rfl
    have hx2pos : 0 < x.2 := Nat.pos_of_mem_divisors (Finset.mem_filter.1 hx2).1
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd.trans hxP, hP0⟩, ?_⟩
    exact le_trans (Nat.le_of_dvd hx2pos hdvd) hxle
  have hvalue : ∀ x ∈ d.divisors ×ˢ F,
      s.selbergTerms x.1 * s.selbergTerms (x.2 / d) = s.selbergTerms (ι x) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hx
    obtain ⟨hx1d, -⟩ := Nat.mem_divisors.1 hx1
    obtain ⟨hxP, hxdvd, -⟩ := hmemF x.2 hx2
    have hcop : Nat.Coprime x.1 (x.2 / d) :=
      Nat.Coprime.coprime_dvd_left hx1d
        (coprime_div_of_dvd_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hxP) hxdvd)
    rw [hι]
    exact (selbergTerms_isMultiplicative.map_mul_of_coprime hcop).symm
  have hkey : (∑ a ∈ d.divisors, s.selbergTerms a) * T ≤ selbergMassLE s Y := by
    have hprod : (∑ a ∈ d.divisors, s.selbergTerms a) * T
        = ∑ x ∈ d.divisors ×ˢ F, s.selbergTerms x.1 * s.selbergTerms (x.2 / d) := by
      rw [hT, Finset.sum_mul_sum, Finset.sum_product]
    rw [hprod, Finset.sum_congr rfl hvalue,
      ← Finset.sum_image (f := fun n => s.selbergTerms n) hinjOn]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
      exact hmaps x hx
    · intro n hn _
      exact (selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hn).1)).le
  rw [sum_divisors_selbergTerms s hd] at hkey
  rw [hU]
  have hmul := mul_le_mul_of_nonneg_left hkey hnu.le
  have hsimp : s.nu d * (s.selbergTerms d * (s.nu d)⁻¹ * T) = s.selbergTerms d * T := by
    field_simp
  rw [hsimp] at hmul
  exact hmul

/-- **Coefficient bound.**  The truncated Selberg coefficients are bounded by one. -/
theorem abs_selbergTruncWeight_le_one (s : BoundingSieve) {Y d : ℕ}
    (hd : d ∣ s.prodPrimes) (hY : 1 ≤ Y) :
    |selbergTruncWeight s Y d| ≤ 1 := by
  have hnu : 0 < s.nu d := nu_pos_of_dvd_prodPrimes hd
  have hS := selbergMassLE_pos s hY
  have hpos : 0 < s.nu d * selbergMassLE s Y := mul_pos hnu hS
  have heq := abs_selbergTruncWeight_mul s hd hY
  have hle := selbergTruncU_le (s := s) (Y := Y) hd
  rw [← heq] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hpos

end RHTower.Sieve
