import GaloisForLFunctions.GrowingWindowsOfSpecZ.ADegenerateWindowIsACurve
import GaloisForLFunctions.GrowingWindowsOfSpecZ.RefiningTheLatticeLowersTheMargin

/-!
# A curve degenerates at its number of angles

The converse of `degenerate_window_is_curve`, and the function-field calibration of the lattice
canonical system. Let `S` be a finite set of Frobenius angles on the unit circle with multiplicities
`ρ_z > 0`, and let `κ(d) = Re Σ_{z∈S} ρ_z z^d` be the lattice data of the curve (`curveData`).

* **Sum of squares over the angles** (`toeplitzForm_curveData`): `T_N(x) = Σ_{z∈S} ρ_z|Σ_k x_kz^k|²`;
  the data are even (`curveData_isEven`).
* **Positive up to the number of angles** (`curveData_posDef`): a polynomial of degree `< |S|`
  vanishing on `S` is zero, so the window of size `N` is positive definite for every `N ≤ |S|`.
* **Degenerate at the number of angles** (`curveData_not_posDef`): if `S` is closed under conjugation,
  `∏_{z∈S}(X − z)` has real coefficients and is a zero mode of the window of size `|S| + 1`.
* **The first critical index is `|S|`** (`curve_first_critical`): the margins satisfy `E_k > 0` for
  `k < |S|` and `E_{|S|} = 0`.

With `degenerate_window_is_curve` this classifies first failures: a lattice evolution degenerates
for the first time at index `n + 1` exactly as a curve with `n + 1` angles does, and a curve of genus
`g` with `2g` distinct angles degenerates for the first time at index `2g`. The integer at which a
window first fails is its number of angles; Spec ℤ, with infinitely many, never fails under RH.
-/

noncomputable section

open Finset Polynomial Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

/-- The lattice data of a curve with Frobenius angles `S` and multiplicities `ρ`:
`κ(d) = Re Σ_{z∈S} ρ_z z^d`. -/
def curveData (S : Finset ℂ) (ρ : ℂ → ℝ) (d : ℤ) : ℝ := (∑ z ∈ S, (ρ z : ℂ) * z ^ d).re

variable {S : Finset ℂ} {ρ : ℂ → ℝ}

/-- On the unit circle `z^{i−j} = z^i\bar z^j`. -/
theorem zpow_sub_eq_mul_conj {z : ℂ} (hz : ‖z‖ = 1) (i j : ℕ) :
    z ^ ((i : ℤ) - j) = z ^ i * conj z ^ j := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, div_eq_mul_inv, ← inv_pow,
    Complex.inv_eq_conj hz]

/-- The data of a curve are even. -/
theorem curveData_isEven (hS : ∀ z ∈ S, ‖z‖ = 1) : IsEvenSeq (curveData S ρ) := fun d => by
  have h : ∑ z ∈ S, (ρ z : ℂ) * z ^ (-d) = conj (∑ z ∈ S, (ρ z : ℂ) * z ^ d) := by
    rw [map_sum]
    refine sum_congr rfl fun z hz => ?_
    have hzd : ‖z ^ d‖ = 1 := by rw [norm_zpow, hS z hz, one_zpow]
    rw [map_mul, Complex.conj_ofReal, zpow_neg, Complex.inv_eq_conj hzd, map_zpow₀]
  rw [curveData, curveData, h, Complex.conj_re]

/-- **The window of a curve is a sum of squares over its angles**:
`T_N(x) = Σ_{z∈S} ρ_z|Σ_k x_kz^k|²`. -/
theorem toeplitzForm_curveData (hS : ∀ z ∈ S, ‖z‖ = 1) (N : ℕ) (x : Fin N → ℝ) :
    toeplitzForm (curveData S ρ) N x =
      ∑ z ∈ S, ρ z * ‖∑ k : Fin N, (x k : ℂ) * z ^ (k : ℕ)‖ ^ 2 := by
  have key : ∀ z ∈ S, ((‖∑ k : Fin N, (x k : ℂ) * z ^ (k : ℕ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin N, ∑ j : Fin N, z ^ ((i : ℤ) - j) * x i * x j := fun z hz => by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [zpow_sub_eq_mul_conj (hS z hz), map_mul, Complex.conj_ofReal, map_pow]
    ring
  have hR : ∑ z ∈ S, ((ρ z * ‖∑ k : Fin N, (x k : ℂ) * z ^ (k : ℕ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ z ∈ S, (ρ z : ℂ) * ∑ i : Fin N, ∑ j : Fin N, z ^ ((i : ℤ) - j) * x i * x j :=
    sum_congr rfl fun z hz => by rw [Complex.ofReal_mul, key z hz]
  have hL : ∑ i : Fin N, ∑ j : Fin N, (∑ z ∈ S, (ρ z : ℂ) * z ^ ((i : ℤ) - j)) * x i * x j =
      ∑ z ∈ S, (ρ z : ℂ) * ∑ i : Fin N, ∑ j : Fin N, z ^ ((i : ℤ) - j) * x i * x j := by
    calc _ = ∑ i : Fin N, ∑ j : Fin N, ∑ z ∈ S, (ρ z : ℂ) * (z ^ ((i : ℤ) - j) * x i * x j) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          exact sum_congr rfl fun z _ => by ring
      _ = ∑ i : Fin N, ∑ z ∈ S, ∑ j : Fin N, (ρ z : ℂ) * (z ^ ((i : ℤ) - j) * x i * x j) :=
          sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ z ∈ S, ∑ i : Fin N, ∑ j : Fin N, (ρ z : ℂ) * (z ^ ((i : ℤ) - j) * x i * x j) :=
          Finset.sum_comm
      _ = _ := sum_congr rfl fun z _ => by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hre := congrArg Complex.re (hL.trans hR.symm)
  rw [← Complex.ofReal_sum, Complex.ofReal_re] at hre
  rw [← hre, toeplitzForm, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  simp [curveData, Complex.mul_re]

/-- **A curve is positive definite up to its number of angles.** -/
theorem curveData_posDef (hS : ∀ z ∈ S, ‖z‖ = 1) (hρ : ∀ z ∈ S, 0 < ρ z) {N : ℕ}
    (hN : N ≤ S.card) : ToeplitzPosDef (curveData S ρ) N := by
  intro x hx
  rw [toeplitzForm_curveData hS]
  have hnn : ∀ z ∈ S, 0 ≤ ρ z * ‖∑ k : Fin N, (x k : ℂ) * z ^ (k : ℕ)‖ ^ 2 :=
    fun z hz => mul_nonneg (hρ z hz).le (sq_nonneg _)
  refine lt_of_le_of_ne (sum_nonneg hnn) fun h0 => hx ?_
  have hzero := (sum_eq_zero_iff_of_nonneg hnn).mp h0.symm
  cases N with
  | zero => exact funext fun k => k.elim0
  | succ n =>
    -- the polynomial `Σ x_kX^k` vanishes on the `|S| > n` angles
    have heval : ∀ z ∈ S, (vecPoly x).eval z = 0 := fun z hz => by
      have := hzero z hz
      rw [mul_eq_zero, or_iff_right (hρ z hz).ne', sq_eq_zero_iff, norm_eq_zero] at this
      simpa [vecPoly, eval_finsetSum] using this
    have hp := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S heval
      ((natDegree_vecPoly_le x).trans_lt (by omega))
    funext k
    have hk := congrArg (fun q : ℂ[X] => q.coeff k) hp
    simp only [coeff_vecPoly, dif_pos k.isLt, coeff_zero] at hk
    exact_mod_cast hk

/-- The angle polynomial `∏_{z∈S}(X − z)` of a conjugation-closed set is fixed by conjugation. -/
theorem map_conj_anglePoly (hconj : ∀ z ∈ S, conj z ∈ S) :
    (∏ z ∈ S, (X - C z)).map (starRingEnd ℂ) = ∏ z ∈ S, (X - C z) := by
  have himage : S.image (starRingEnd ℂ) = S :=
    Finset.eq_of_subset_of_card_le (fun w hw => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact hconj z hz)
      (Finset.card_image_of_injective _ (starRingEnd ℂ).injective).ge
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C]
  conv_rhs => rw [← himage]
  rw [Finset.prod_image fun a _ b _ h => (starRingEnd ℂ).injective h]

/-- **A conjugation-closed curve degenerates at its number of angles**: the window of size `|S| + 1`
has the real zero mode `∏_{z∈S}(X − z)`. -/
theorem curveData_not_posDef (hS : ∀ z ∈ S, ‖z‖ = 1) (hconj : ∀ z ∈ S, conj z ∈ S) :
    ¬ ToeplitzPosDef (curveData S ρ) (S.card + 1) := by
  intro hpd
  set P : ℂ[X] := ∏ z ∈ S, (X - C z)
  have hdeg : P.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card S id
  have hmonic : P.Monic := monic_prod_X_sub_C id S
  -- the coefficients of `P` are real
  have hreal : ∀ k, ((P.coeff k).re : ℂ) = P.coeff k := fun k => by
    rw [← Complex.conj_eq_iff_re, ← Polynomial.coeff_map, map_conj_anglePoly hconj]
  set u : Fin (S.card + 1) → ℝ := fun k => (P.coeff k).re
  have hu : u ≠ 0 := fun h => by
    have := congrFun h (Fin.last _)
    simp only [u, Fin.val_last, Pi.zero_apply] at this
    rw [← hdeg, hmonic.coeff_natDegree, Complex.one_re] at this
    exact one_ne_zero this
  have hT := hpd u hu
  rw [toeplitzForm_curveData hS] at hT
  refine hT.ne' (sum_eq_zero fun z hz => ?_)
  have hPz : ∑ k : Fin (S.card + 1), (u k : ℂ) * z ^ (k : ℕ) = P.eval z := by
    rw [eval_eq_sum_range' (n := S.card + 1) (by omega), ← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun k _ => by rw [hreal]
  have h0 : P.eval z = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hz (by simp)
  rw [hPz, h0, norm_zero]
  ring

/-- **The first critical index of a curve is its number of angles**: `E_k > 0` for `k < |S|` and
`E_{|S|} = 0`. -/
theorem curve_first_critical (hS : ∀ z ∈ S, ‖z‖ = 1) (hρ : ∀ z ∈ S, 0 < ρ z)
    (hconj : ∀ z ∈ S, conj z ∈ S) :
    (∀ k < S.card, 0 < levinsonErr (curveData S ρ) k) ∧ levinsonErr (curveData S ρ) S.card = 0 := by
  have hκ := curveData_isEven (ρ := ρ) hS
  have hpos : ∀ k < S.card, 0 < levinsonErr (curveData S ρ) k := fun k hk => by
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    exact (toeplitzForm_posDef_iff hκ m).mp (hm ▸ curveData_posDef hS hρ le_rfl) k (by omega)
  refine ⟨hpos, le_antisymm ?_ ?_⟩
  · by_contra hlt
    exact curveData_not_posDef hS hconj ((toeplitzForm_posDef_iff hκ S.card).mpr fun k hk => by
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact hpos k hk
      · exact not_le.mp hlt)
  · rw [← toeplitzForm_levinsonVec hκ fun k hk => (hpos k hk).ne', toeplitzForm_curveData hS]
    exact sum_nonneg fun z hz => mul_nonneg (hρ z hz).le (sq_nonneg _)

end GaloisForLFunctions.GrowingWindowsOfSpecZ
