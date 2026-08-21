import GaloisForLFunctions.HTGeometry.KleinbockMargulis.CutInterval
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.PolynomialGood

/-!
# The one-dimensional case of Lemma 3.3

Let `F` be a derivative chain on an interval with `|F j| ≤ A₁` for `j ≤ k` and `|F k| ≥ A₂ > 0`.

Two estimates control the sublevel set `S = {|F 0| < ε}`.  First, any interval inside `S` is
short: interpolating at `k+1` equally spaced points inside it and comparing the top Lagrange
coefficient with `F k` bounds its length by `(k+2)((k+1)! ε / A₂)^{1/k}`.  Second, `‖F 0‖` on the
whole interval is controlled by interpolating at `k` points of such a subinterval and adding the
interpolation remainder.  Combining the two with the counting estimate of `CutInterval` gives the
`(C, 1/k)`-goodness of `F 0`.

## Main results

* `interval_length_le` — Sublemma 3.3.1 (a).
* `abs_le_of_interval` — Sublemma 3.3.1 (b).
-/

open Set MeasureTheory Polynomial
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

/-! ### Sublemma 3.3.1 (a) -/

/-- **An interval on which `|F 0| < ε` is short.** -/
theorem interval_length_le {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ}
    (hF : IsDerivChain F U) {k : ℕ} (hk : 1 ≤ k) {A₂ : ℝ} (hA₂ : 0 < A₂)
    (hlow : ∀ x ∈ U, A₂ ≤ |F k x|) {ε : ℝ} (hε : 0 < ε)
    {u v : ℝ} (huv : u < v) (hsub : Ioo u v ⊆ U) (hval : ∀ x ∈ Ioo u v, |F 0 x| < ε) :
    v - u ≤ ((k : ℝ) + 2) * (((k + 1).factorial : ℝ) * ε / A₂) ^ ((k : ℝ)⁻¹) := by
  classical
  set h : ℝ := (v - u) / ((k : ℝ) + 2) with hh
  have hhpos : 0 < h := by
    rw [hh]
    have : (0:ℝ) < (k : ℝ) + 2 := by positivity
    exact div_pos (by linarith) this
  set x : Fin (k + 1) → ℝ := fun i => u + ((i : ℕ) + 1 : ℝ) * h with hx
  have hxmem : ∀ i, x i ∈ Ioo u v := by
    intro i
    constructor
    · rw [hx]
      have : (0:ℝ) < (((i : ℕ) : ℝ) + 1) * h := by positivity
      linarith
    · rw [hx, hh]
      have hk2 : (0:ℝ) < (k : ℝ) + 2 := by positivity
      have hi : ((i : ℕ) : ℝ) + 1 < (k : ℝ) + 2 := by
        have : ((i : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
        linarith
      rw [← sub_pos]
      have : v - (u + (((i : ℕ) : ℝ) + 1) * ((v - u) / ((k : ℝ) + 2)))
          = (v - u) * (((k : ℝ) + 2 - (((i : ℕ) : ℝ) + 1)) / ((k : ℝ) + 2)) := by
        field_simp
        ring
      rw [this]
      have h1 : (0:ℝ) < v - u := by linarith
      have h2 : (0:ℝ) < (k : ℝ) + 2 - (((i : ℕ) : ℝ) + 1) := by linarith
      positivity
  have hxmono : StrictMono x := by
    intro i j hij
    rw [hx]
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    nlinarith
  obtain ⟨ξ, hξmem, hξ⟩ :=
    exists_chain_eq_factorial_mul_coeff hUc hF k x hxmono (fun i => hsub (hxmem i))
  have hξU : ξ ∈ U := hUc.out (hsub (hxmem 0)) (hsub (hxmem (Fin.last k))) hξmem
  set P : Polynomial ℝ := Lagrange.interpolate Finset.univ x fun i => F 0 (x i) with hP
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin (k + 1))) := hxmono.injective.injOn
  have hdeg : P.degree < ((Finset.univ : Finset (Fin (k + 1))).card : ℕ) :=
    Lagrange.degree_interpolate_lt _ hinj
  have hcoeff : P.coeff k = ∑ i, F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
    have h := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (k + 1)))) (v := x)
      (P := P) hinj hdeg
    have hc : (Finset.univ : Finset (Fin (k + 1))).card - 1 = k := by simp
    rw [hc] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)]
  -- bound the top coefficient
  have hprod : ∀ i : Fin (k + 1), h ^ k ≤ |∏ j ∈ Finset.univ.erase i, (x i - x j)| := by
    intro i
    rw [Finset.abs_prod]
    have hcard : (Finset.univ.erase i).card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    calc h ^ k = ∏ _j ∈ Finset.univ.erase i, h := by rw [Finset.prod_const, hcard]
      _ ≤ ∏ j ∈ Finset.univ.erase i, |x i - x j| := by
          refine Finset.prod_le_prod (fun j _ => hhpos.le) fun j hj => ?_
          have hne : (i : ℕ) ≠ (j : ℕ) := fun hc =>
            (Finset.ne_of_mem_erase hj) (Fin.ext hc).symm
          rw [hx]
          have : u + (((i : ℕ) : ℝ) + 1) * h - (u + (((j : ℕ) : ℝ) + 1) * h)
              = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h := by ring
          rw [this, abs_mul, abs_of_pos hhpos]
          have h1 : (1:ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
            have : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≠ 0 := by
              intro hc
              exact hne (by exact_mod_cast sub_eq_zero.mp hc)
            rcases lt_or_gt_of_ne this with hlt | hgt
            · rw [abs_of_neg hlt]
              have : ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) ≥ 1 := by
                have : (i : ℕ) < (j : ℕ) := by
                  by_contra hcon
                  push Not at hcon
                  have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hcon
                  linarith
                have : (i : ℕ) + 1 ≤ (j : ℕ) := this
                have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast this
                linarith
              linarith
            · rw [abs_of_pos hgt]
              have : (j : ℕ) < (i : ℕ) := by
                by_contra hcon
                push Not at hcon
                have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hcon
                linarith
              have : (j : ℕ) + 1 ≤ (i : ℕ) := this
              have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast this
              linarith
          nlinarith
  have hcbound : |P.coeff k| ≤ ((k : ℝ) + 1) * ε / h ^ k := by
    rw [hcoeff]
    calc |∑ i, F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)|
        ≤ ∑ i, |F 0 (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (k + 1), ε / h ^ k := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hp := hprod i
          have hppos : (0:ℝ) < |∏ j ∈ Finset.univ.erase i, (x i - x j)| :=
            lt_of_lt_of_le (by positivity) hp
          have hf := (hval _ (hxmem i)).le
          rw [abs_div]
          calc |F 0 (x i)| / |∏ j ∈ Finset.univ.erase i, (x i - x j)|
              ≤ ε / |∏ j ∈ Finset.univ.erase i, (x i - x j)| := by
                exact div_le_div_of_nonneg_right hf hppos.le
            _ ≤ ε / h ^ k := by
                exact div_le_div_of_nonneg_left hε.le (by positivity) hp
      _ = ((k : ℝ) + 1) * ε / h ^ k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  -- conclude
  have hfk : A₂ ≤ (k.factorial : ℝ) * |P.coeff k| := by
    have h1 := hlow ξ hξU
    rw [hξ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (k.factorial : ℝ))] at h1
    exact h1
  have hkey : h ^ k ≤ ((k + 1).factorial : ℝ) * ε / A₂ := by
    have h1 : A₂ * h ^ k ≤ (k.factorial : ℝ) * (((k : ℝ) + 1) * ε) := by
      have h2 : (k.factorial : ℝ) * |P.coeff k| ≤ (k.factorial : ℝ) * (((k : ℝ) + 1) * ε / h ^ k) :=
        mul_le_mul_of_nonneg_left hcbound (by positivity)
      have h3 : (0:ℝ) < h ^ k := by positivity
      rw [le_div_iff₀ h3] at *
      nlinarith
    rw [le_div_iff₀ hA₂]
    have hfac : ((k + 1).factorial : ℝ) = (k.factorial : ℝ) * ((k : ℝ) + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    nlinarith
  have hroot : h ≤ (((k + 1).factorial : ℝ) * ε / A₂) ^ ((k : ℝ)⁻¹) := by
    have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h2 : (h ^ (k : ℕ)) ^ ((k : ℝ)⁻¹) ≤ (((k + 1).factorial : ℝ) * ε / A₂) ^ ((k : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hkey (by positivity)
    rwa [← Real.rpow_natCast h k, ← Real.rpow_mul hhpos.le,
      mul_inv_cancel₀ (ne_of_gt hkR), Real.rpow_one] at h2
  have hvu : v - u = ((k : ℝ) + 2) * h := by
    rw [hh]
    field_simp
  rw [hvu]
  exact mul_le_mul_of_nonneg_left hroot (by positivity)


/-! ### Sublemma 3.3.1 (b) -/

/-- **The values of `F 0` on the whole interval are controlled by a short subinterval.**
Interpolating at `k` points of an interval on which `|F 0| < ε` and adding the interpolation
remainder bounds `|F 0|` everywhere. -/
theorem abs_le_of_interval {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ}
    (hF : IsDerivChain F U) {k : ℕ} (hk : 1 ≤ k) {A₁ : ℝ}
    (hup : ∀ x ∈ U, |F k x| ≤ A₁) {ε : ℝ} (_hε : 0 < ε)
    {u v : ℝ} (huv : u < v) (hsub : Ioo u v ⊆ U) (hval : ∀ x ∈ Ioo u v, |F 0 x| < ε)
    {a b : ℝ} (hab : Ioo a b ⊆ U) (hbb : ∀ y ∈ Ioo a b, ∀ w ∈ Ioo u v, |y - w| ≤ b - a)
    {y : ℝ} (hy : y ∈ Ioo a b) :
    |F 0 y| ≤ (k : ℝ) * ε * ((b - a) * ((k : ℝ) + 1) / (v - u)) ^ (k - 1)
      + A₁ * (b - a) ^ k / (k.factorial : ℝ) := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set h : ℝ := (v - u) / ((k' : ℝ) + 2) with hh
  have hhpos : 0 < h := by
    rw [hh]
    have : (0:ℝ) < (k' : ℝ) + 2 := by positivity
    exact div_pos (by linarith) this
  set x : Fin (k' + 1) → ℝ := fun i => u + ((i : ℕ) + 1 : ℝ) * h with hx
  have hxmem : ∀ i, x i ∈ Ioo u v := by
    intro i
    constructor
    · rw [hx]
      have : (0:ℝ) < (((i : ℕ) : ℝ) + 1) * h := by positivity
      linarith
    · rw [hx, hh]
      have hk2 : (0:ℝ) < (k' : ℝ) + 2 := by positivity
      have hi : ((i : ℕ) : ℝ) + 1 < (k' : ℝ) + 2 := by
        have : ((i : ℕ) : ℝ) ≤ (k' : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
        linarith
      rw [← sub_pos]
      have hrw : v - (u + (((i : ℕ) : ℝ) + 1) * ((v - u) / ((k' : ℝ) + 2)))
          = (v - u) * (((k' : ℝ) + 2 - (((i : ℕ) : ℝ) + 1)) / ((k' : ℝ) + 2)) := by
        field_simp
        ring
      rw [hrw]
      have h1 : (0:ℝ) < v - u := by linarith
      have h2 : (0:ℝ) < (k' : ℝ) + 2 - (((i : ℕ) : ℝ) + 1) := by linarith
      positivity
  have hxmono : StrictMono x := by
    intro i j hij
    rw [hx]
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    nlinarith
  set P : Polynomial ℝ := Lagrange.interpolate Finset.univ x fun i => F 0 (x i) with hP
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin (k' + 1))) := hxmono.injective.injOn
  have hnodes : ∀ i, P.eval (x i) = F 0 (x i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)
  have hdegP : P.natDegree ≤ k' := by
    have h1 : P.degree < ((Finset.univ : Finset (Fin (k' + 1))).card : ℕ) :=
      Lagrange.degree_interpolate_lt _ hinj
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    rcases eq_or_ne P 0 with hz | hne
    · rw [hz]; simp
    · rw [Polynomial.degree_eq_natDegree hne] at h1
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h1)
  -- the interpolant is small on the whole interval
  have hsep : ∀ i j : Fin (k' + 1), i ≠ j → h ≤ |x i - x j| := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
    rw [hx]
    have hrw : u + (((i : ℕ) : ℝ) + 1) * h - (u + (((j : ℕ) : ℝ) + 1) * h)
        = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h := by ring
    rw [hrw, abs_mul, abs_of_pos hhpos]
    have h1 : (1:ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne (fun hc : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) = 0 =>
        hne (by exact_mod_cast sub_eq_zero.mp hc)) with hlt | hgt
      · rw [abs_of_neg hlt]
        have hlt' : (i : ℕ) < (j : ℕ) := by
          by_contra hcon
          push Not at hcon
          have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hcon
          linarith
        have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt'
        linarith
      · rw [abs_of_pos hgt]
        have hgt' : (j : ℕ) < (i : ℕ) := by
          by_contra hcon
          push Not at hcon
          have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hcon
          linarith
        have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt'
        linarith
    nlinarith
  have hdist : ∀ i, |y - x i| ≤ b - a := fun i => hbb y hy _ (hxmem i)
  have hPbound : |P.eval y| ≤ ((k' : ℝ) + 1) * ε * ((b - a) / h) ^ (k' + 1 - 1) := by
    have hb0 : (0:ℝ) ≤ b - a := le_trans (abs_nonneg _) (hdist 0)
    have := abs_eval_le_of_lagrange (k := k') P hdegP x hxmono.injective hhpos hb0
      (fun i => by rw [hnodes i]; exact (hval _ (hxmem i)).le) hsep hdist
    simpa using this
  -- the interpolation remainder
  have hrem : |F 0 y - P.eval y| ≤ A₁ / ((k' + 1).factorial : ℝ) * ((b - a) ^ (k' + 1)) := by
    have hy' : y ∈ U := hab hy
    have h1 := abs_sub_interpolate_le hUc hF x hxmono (fun i => hsub (hxmem i))
      (M := A₁) (fun w hw => hup w hw) hy'
    refine le_trans h1 ?_
    have h2 : ∏ i : Fin (k' + 1), |y - x i| ≤ (b - a) ^ (k' + 1) := by
      calc ∏ i : Fin (k' + 1), |y - x i| ≤ ∏ _i : Fin (k' + 1), (b - a) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hdist i
        _ = (b - a) ^ (k' + 1) := by simp
    have hA₁0 : 0 ≤ A₁ := le_trans (abs_nonneg _) (hup y hy')
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- combine
  have hsplit : |F 0 y| ≤ |P.eval y| + |F 0 y - P.eval y| := by
    have h := abs_sub_abs_le_abs_sub (F 0 y) (P.eval y)
    linarith
  have hvune : v - u ≠ 0 := by
    intro hc
    linarith
  refine le_trans hsplit (add_le_add ?_ ?_)
  · refine le_trans hPbound (le_of_eq ?_)
    have hhe : (b - a) / h = (b - a) * (((k' + 1 : ℕ) : ℝ) + 1) / (v - u) := by
      rw [hh]
      have hk2 : ((k' : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [hhe]
    push_cast
    ring
  · refine le_trans hrem (le_of_eq ?_)
    ring


/-! ### Level sets are finite -/

theorem finite_level_set {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ}
    (hF : IsDerivChain F U) {k : ℕ} (hk : 1 ≤ k) (hne : ∀ x ∈ U, F k x ≠ 0) (c : ℝ) :
    {x | x ∈ U ∧ F 0 x = c}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq (k + 1)
  have := card_le_of_chain_ne_zero hUc hF hk hne c t fun x hx => hts hx
  omega

/-! ### The one-dimensional estimate -/

/-- **Lemma 3.3, one-dimensional case.**  A chain with `|F k| ≤ A₁` and `|F k| ≥ A₂ > 0` has
`F 0` `(C, 1/k)`-good on every subinterval, with `C` depending only on `k`, `A₁` and `A₂`. -/
theorem exists_good_const_one_dim (k : ℕ) (hk : 1 ≤ k) {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 < A₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set ℝ) (F : ℕ → ℝ → ℝ), U.OrdConnected → IsDerivChain F U →
      (∀ x ∈ U, |F k x| ≤ A₁) → (∀ x ∈ U, A₂ ≤ |F k x|) →
      ∀ a b : ℝ, a < b → Ioo a b ⊆ U → ∀ ε : ℝ, 0 < ε → ∀ z ∈ Ioo a b,
        (volume {x ∈ Ioo a b | |F 0 x| < ε}).toReal * |F 0 z| ^ ((k : ℝ)⁻¹)
          ≤ C * ε ^ ((k : ℝ)⁻¹) * (b - a) := by
  classical
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  set C₁ : ℝ := ((k : ℝ) + 1) * (2 * (k : ℝ) + 2) * (2 * (k : ℝ)) ^ ((k : ℝ)⁻¹) with hC₁
  set C₂ : ℝ := (2 * (k : ℝ) + 2) * ((k : ℝ) + 2)
    * (2 * ((k : ℝ) + 1) * A₁ / A₂) ^ ((k : ℝ)⁻¹) with hC₂
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    have : (0:ℝ) < (2 * (k : ℝ)) ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro U F hUc hF hup hlow a b hab hsubU ε hε z hz
  set S : Set ℝ := {x ∈ Ioo a b | |F 0 x| < ε} with hS
  set m : ℝ := (volume S).toReal with hm
  set bb : ℝ := b - a with hbb
  set s : ℝ := |F 0 z| with hsdef
  have hbbpos : 0 < bb := by rw [hbb]; linarith
  have hsnn : 0 ≤ s := abs_nonneg _
  have hmnn : 0 ≤ m := ENNReal.toReal_nonneg
  have hεnn : (0:ℝ) ≤ ε ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg hε.le _
  have hCnn : 0 ≤ max C₁ C₂ := le_of_lt (lt_of_lt_of_le hC₁pos (le_max_left _ _))
  have hRHSnn : 0 ≤ max C₁ C₂ * ε ^ ((k : ℝ)⁻¹) * bb := by positivity
  rcases eq_or_lt_of_le hsnn with hs0 | hspos
  · rw [← hs0, Real.zero_rpow (by positivity), mul_zero]
    exact hRHSnn
  rcases eq_or_lt_of_le hmnn with hm0 | hmpos
  · rw [← hm0, zero_mul]
    exact hRHSnn
  -- `m ≤ bb`
  have hSsub : S ⊆ Ioo a b := fun x hx => hx.1
  have hmbb : m ≤ bb := by
    have h1 : volume S ≤ volume (Ioo a b) := measure_mono hSsub
    have h2 : volume (Ioo a b) = ENNReal.ofReal bb := by rw [Real.volume_Ioo]
    rw [hm]
    calc (volume S).toReal ≤ (volume (Ioo a b)).toReal :=
          ENNReal.toReal_mono (by rw [h2]; exact ENNReal.ofReal_ne_top) h1
      _ = bb := by rw [h2, ENNReal.toReal_ofReal hbbpos.le]
  -- the cut set
  have hne : ∀ x ∈ U, F k x ≠ 0 := by
    intro x hx hc
    have := hlow x hx
    rw [hc, abs_zero] at this
    linarith
  have hfin : ∀ c : ℝ, {x | x ∈ Ioo a b ∧ F 0 x = c}.Finite := by
    intro c
    exact ((finite_level_set hUc hF hk hne c).subset fun x hx => ⟨hsubU hx.1, hx.2⟩)
  set Z : Finset ℝ := (hfin ε).toFinset ∪ (hfin (-ε)).toFinset with hZ
  have hZcard : Z.card ≤ 2 * k := by
    have h1 : ((hfin ε).toFinset).card ≤ k :=
      card_le_of_chain_ne_zero hUc hF hk hne ε _ fun x hx => by
        have := (Set.Finite.mem_toFinset _).mp hx
        exact ⟨hsubU this.1, this.2⟩
    have h2 : ((hfin (-ε)).toFinset).card ≤ k :=
      card_le_of_chain_ne_zero hUc hF hk hne (-ε) _ fun x hx => by
        have := (Set.Finite.mem_toFinset _).mp hx
        exact ⟨hsubU this.1, this.2⟩
    have := Finset.card_union_le ((hfin ε).toFinset) ((hfin (-ε)).toFinset)
    omega
  have hZmem : ∀ w ∈ Z, w ∈ Ioo a b ∧ |F 0 w| = ε := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · have := (Set.Finite.mem_toFinset _).mp h
      exact ⟨this.1, by rw [this.2, abs_of_pos hε]⟩
    · have := (Set.Finite.mem_toFinset _).mp h
      exact ⟨this.1, by rw [this.2, abs_neg, abs_of_pos hε]⟩
  have hZnotS : ∀ w ∈ Z, w ∉ S := by
    intro w hw hwS
    have := (hZmem w hw).2
    have := hwS.2
    linarith [(hZmem w hw).2]
  have hconv : ∀ x ∈ S, ∀ y ∈ S, x < y → (∀ w ∈ Ioo x y, w ∉ Z) → Ioo x y ⊆ S := by
    intro x hxS y hyS hxy hnoZ w hw
    have hwab : w ∈ Ioo a b := ⟨lt_trans hxS.1.1 hw.1, lt_trans hw.2 hyS.1.2⟩
    refine ⟨hwab, ?_⟩
    by_contra hcon
    push Not at hcon
    have hcont : ContinuousOn (fun t => |F 0 t|) (Icc x w) := by
      refine (hF.continuousOn 0 ?_).abs
      exact hUc.out (hsubU hxS.1) (hsubU hwab)
    have hmemIcc : ε ∈ Icc (|F 0 x|) (|F 0 w|) := ⟨hxS.2.le, hcon⟩
    obtain ⟨w', hw'mem, hw'val⟩ :=
      intermediate_value_Icc hw.1.le hcont hmemIcc
    have hw'ne : w' ≠ x := by
      intro hc
      rw [hc] at hw'val
      exact absurd hw'val (ne_of_lt hxS.2)
    have hw'Ioo : w' ∈ Ioo x y :=
      ⟨lt_of_le_of_ne hw'mem.1 (Ne.symm hw'ne), lt_of_le_of_lt hw'mem.2 hw.2⟩
    have hw'ab : w' ∈ Ioo a b := ⟨lt_trans hxS.1.1 hw'Ioo.1, lt_trans hw'Ioo.2 hyS.1.2⟩
    refine hnoZ w' hw'Ioo ?_
    rcases abs_eq hε.le |>.mp hw'val with h | h
    · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr ⟨hw'ab, h⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr ⟨hw'ab, h⟩)
  -- some interval inside `S` is long
  obtain ⟨u, v, huvS, huvlen⟩ :
      ∃ u v : ℝ, Ioo u v ⊆ S ∧ m / (2 * (k : ℝ) + 2) < v - u := by
    by_contra hcon
    push Not at hcon
    have hL : (0:ℝ) ≤ m / (2 * (k : ℝ) + 2) := by positivity
    have hbound := volume_le_of_cuts (2 * k) a b Z hZcard (fun w hw => (hZmem w hw).1) S
      (m / (2 * (k : ℝ) + 2)) hL hSsub hZnotS hconv (fun u v huv => hcon u v huv)
    have h1 : m ≤ ((Z.card : ℝ) + 1) * (m / (2 * (k : ℝ) + 2)) := by
      rw [hm]
      have h2 : volume S ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ (measure_mono hSsub)
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have h3 : ((Z.card : ℝ) + 1) ≤ 2 * (k : ℝ) + 1 := by
      have : (Z.card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hZcard
      linarith
    have h4 : (0:ℝ) < 2 * (k : ℝ) + 2 := by positivity
    rw [div_eq_mul_inv] at h1
    nlinarith [mul_pos hmpos (inv_pos.mpr h4)]
  have huv : u < v := by
    have : (0:ℝ) < m / (2 * (k : ℝ) + 2) := by positivity
    linarith
  have hIooU : Ioo u v ⊆ U := fun x hx => hsubU (huvS hx).1
  have hIooval : ∀ x ∈ Ioo u v, |F 0 x| < ε := fun x hx => (huvS hx).2
  -- Sublemma 3.3.1 (a)
  have hA := interval_length_le hUc hF hk hA₂ hlow hε huv hIooU hIooval
  -- Sublemma 3.3.1 (b)
  have hBB : ∀ y ∈ Ioo a b, ∀ w ∈ Ioo u v, |y - w| ≤ bb := by
    intro y hy w hw
    have hwab : w ∈ Ioo a b := (huvS hw).1
    rw [abs_le, hbb]
    constructor <;> [linarith [hy.1, hy.2, hwab.1, hwab.2]; linarith [hy.1, hy.2, hwab.1, hwab.2]]
  have hB := abs_le_of_interval hUc hF hk hup hε huv hIooU hIooval hsubU hBB hz
  rw [← hsdef] at hB
  sorry

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
