import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SpanContactLaw
import Mathlib.LinearAlgebra.Lagrange

/-!
# The window receivers of a curve

Over `𝔽_q` Weil's form on the window of `n` Frobenius graphs is the Toeplitz form of the power sums,
and the receivers of the window tower over `ℤ` can be read off exactly. Write `s = √q`, `R` for the
set of distinct normalized eigenvalues and `F_e(z) = Σ_{k<n} e_k z^k`.

* **One window decides purity** (`unitary_iff_toeplitz_nonneg_on_spectrum_window`). The datum is
  unitary iff the form is nonnegative on the single window of size `#R`. If `|z| ≠ 1` for some
  `z ∈ R`, a polynomial of degree `< #R` with `P(z) = 1`, `P(z*) = −1`, `z* = 1/z̄`, vanishing on the
  rest of `R`, has Hermitian energy `−#{i : β_i ∈ {z, z*}} < 0`.
* **The explicit formula** (`toeplitz_eq_curvePolar_sub_curvePrime`):
  `T(e) = H(e) − P(e)`, with polar part `H(e) = 2F_e(s)F_e(1/s) + (2g − 2)Σe_k²` and prime part
  `P(e) = Σ_{k≠l} e_k e_l N_{|k−l|} s^{−|k−l|}`.
* **The Hardy interval** `ℋ(n) = {t : H − tP ≥ 0 on the window n}`. The multiple `1` lies in every
  `ℋ(n)` iff the datum is unitary. For a unitary datum `ℋ(n) = {1}` exactly, for all large `n`
  (`eventually_curveHardyInterval_eq_singleton`): above the contact window the radical of `T` carries
  both signs of the rank-two polar plane, so a finite window pins the multiple exactly.
* **The chain ends at the number of angles** (`norm_eval_sq_le_mul_toeplitz`,
  `not_exists_evaluation_bound_of_lt`). On a unitary datum point evaluation is `T`-bounded on the
  window `n ≤ #R`, by the Lagrange constant, and is unbounded on every larger window: the reproducing
  kernel diverges at contact.

Over `ℤ` none of the three finite-window statements can hold: every bounded aperture is blind to every
width, and under RH the cone has positive margin at every aperture.
-/

open Complex Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem β_ne_zero' (i : ι) : D.β i ≠ 0 := by
  intro h
  have := D.β_fePerm i
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem β_fePerm_eq_inv (i : ι) : D.β (D.fePerm i) = (D.β i)⁻¹ :=
  eq_inv_of_mul_eq_one_left (D.β_fePerm i)

/-- The functional equation in the power sums. -/
theorem sum_inv_pow (j : ℕ) : ∑ i, ((D.β i)⁻¹) ^ j = D.powerSum j := by
  unfold powerSum
  simp_rw [← D.β_fePerm_eq_inv]
  exact Equiv.sum_comp D.fePerm (fun i => D.β i ^ j)

/-- `Σ_i β_i^k β_i^{−l}` is the power sum at the lag `|k − l|`. -/
theorem sum_pow_mul_inv_pow (k l : ℕ) :
    ∑ i, D.β i ^ k * ((D.β i)⁻¹) ^ l = D.powerSum (Nat.dist k l) := by
  rcases le_total k l with h | h
  · rw [Nat.dist_eq_sub_of_le h, ← D.sum_inv_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb := D.β_ne_zero' i
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hb),
      one_mul]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    unfold powerSum
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb := D.β_ne_zero' i
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (D.β i ^ l), mul_assoc, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hb), mul_one]

/-- The reflection `z ↦ 1/z̄` preserves the spectrum. -/
theorem star_mem_spectrum {z : ℂ} (hz : z ∈ D.spectrum) :
    (starRingEnd ℂ z)⁻¹ ∈ D.spectrum := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨D.fePerm (D.conjPerm i), Finset.mem_univ _, ?_⟩
  rw [D.β_fePerm_eq_inv, D.β_conjPerm]

/-- The Hermitian extension of the real Toeplitz form. -/
def toeplitzC (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ k ∈ S, ∑ l ∈ S, a k * starRingEnd ℂ (a l) * (D.trace (Nat.dist k l) : ℂ)

/-- **Reduction to real tests**: the Hermitian energy is the sum of the energies of the real and
imaginary parts. -/
theorem re_toeplitzC (S : Finset ℕ) (a : ℕ → ℂ) :
    (D.toeplitzC S a).re =
      D.toeplitz S (fun k => (a k).re) + D.toeplitz S (fun k => (a k).im) := by
  unfold toeplitzC toeplitz
  rw [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.re_mul_ofReal, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The Hermitian energy on the spectrum. -/
theorem toeplitzC_eq_sum (S : Finset ℕ) (a : ℕ → ℂ) :
    D.toeplitzC S a = ∑ i, (∑ k ∈ S, a k * D.β i ^ k) *
      starRingEnd ℂ (∑ l ∈ S, a l * (starRingEnd ℂ (D.β i))⁻¹ ^ l) := by
  unfold toeplitzC
  have hstar (i : ι) : starRingEnd ℂ (∑ l ∈ S, a l * (starRingEnd ℂ (D.β i))⁻¹ ^ l) =
      ∑ l ∈ S, starRingEnd ℂ (a l) * ((D.β i)⁻¹) ^ l := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, map_inv₀, Complex.conj_conj]
  have hentry (k l : ℕ) : a k * starRingEnd ℂ (a l) * (D.trace (Nat.dist k l) : ℂ) =
      ∑ i, a k * D.β i ^ k * (starRingEnd ℂ (a l) * ((D.β i)⁻¹) ^ l) := by
    rw [← D.powerSum_eq_trace, ← D.sum_pow_mul_inv_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hstar, Finset.sum_mul_sum, hentry]
  calc ∑ k ∈ S, ∑ l ∈ S, ∑ i, a k * D.β i ^ k * (starRingEnd ℂ (a l) * ((D.β i)⁻¹) ^ l)
      = ∑ k ∈ S, ∑ i, ∑ l ∈ S, a k * D.β i ^ k * (starRingEnd ℂ (a l) * ((D.β i)⁻¹) ^ l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-! ### One window decides purity -/

/-- A polynomial of degree `< #R` with values `1` at `z`, `−1` at `w`, vanishing on the rest of `R`. -/
theorem exists_two_point_poly {R : Finset ℂ} {z w : ℂ} (hz : z ∈ R) (hw : w ∈ R) (hzw : z ≠ w) :
    ∃ P : ℂ[X], P.natDegree < R.card ∧ P.eval z = 1 ∧ P.eval w = -1 ∧
      ∀ v ∈ R, v ≠ z → v ≠ w → P.eval v = 0 := by
  classical
  have hval : Set.InjOn (fun x : ℂ => x) R := fun _ _ _ _ h => h
  let r : ℂ → ℂ := fun v => if v = z then 1 else if v = w then -1 else 0
  refine ⟨Lagrange.interpolate R (fun x => x) r, ?_, ?_, ?_, ?_⟩
  · have hc : 0 < R.card := Finset.card_pos.mpr ⟨z, hz⟩
    by_cases h0 : Lagrange.interpolate R (fun x => x) r = 0
    · rw [h0, natDegree_zero]; exact hc
    · exact (natDegree_lt_iff_degree_lt h0).mpr (Lagrange.degree_interpolate_lt r hval)
  · rw [Lagrange.eval_interpolate_at_node r hval hz]
    simp [r]
  · rw [Lagrange.eval_interpolate_at_node r hval hw]
    simp [r, hzw.symm]
  · intro v hv hvz hvw
    rw [Lagrange.eval_interpolate_at_node r hval hv]
    simp [r, hvz, hvw]

/-- **One window decides purity.** Nonnegativity of Weil's form on the single window of size `#R`
forces every eigenvalue onto the unit circle. -/
theorem unitary_of_toeplitz_nonneg_on_spectrum_window
    (h : ∀ e : ℕ → ℝ, 0 ≤ D.toeplitz (range D.spectrum.card) e) : ∀ i, ‖D.β i‖ = 1 := by
  classical
  intro i₀
  by_contra hne
  set z := D.β i₀ with hzdef
  have hz0 : z ≠ 0 := D.β_ne_zero' i₀
  have hzm : z ∈ D.spectrum := Finset.mem_image_of_mem D.β (Finset.mem_univ i₀)
  set w := (starRingEnd ℂ z)⁻¹ with hwdef
  have hwm : w ∈ D.spectrum := D.star_mem_spectrum hzm
  have hnw : ‖w‖ = ‖z‖⁻¹ := by rw [hwdef, norm_inv, Complex.norm_conj]
  have hzw : z ≠ w := by
    intro heq
    apply hne
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have h1 : ‖z‖ * ‖z‖ = 1 := by
      have hn : ‖z‖ = ‖z‖⁻¹ := by rw [← hnw, ← heq]
      calc ‖z‖ * ‖z‖ = ‖z‖ * ‖z‖⁻¹ := by nth_rw 2 [hn]
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith only [h1, hpos]
  obtain ⟨P, hdeg, hPz, hPw, hP0⟩ := exists_two_point_poly hzm hwm hzw
  set n := D.spectrum.card with hn
  have heval (v : ℂ) : ∑ k ∈ range n, P.coeff k * v ^ k = P.eval v :=
    (Polynomial.eval_eq_sum_range' hdeg v).symm
  have hvalue (i : ι) : (∑ k ∈ range n, P.coeff k * D.β i ^ k) *
      starRingEnd ℂ (∑ l ∈ range n, P.coeff l * (starRingEnd ℂ (D.β i))⁻¹ ^ l) =
        if D.β i = z ∨ D.β i = w then -1 else 0 := by
    rw [heval, heval]
    have hmi : D.β i ∈ D.spectrum := Finset.mem_image_of_mem D.β (Finset.mem_univ i)
    by_cases h1 : D.β i = z
    · rw [if_pos (Or.inl h1), h1, hPz, ← hwdef, hPw]
      simp
    · by_cases h2 : D.β i = w
      · have hstar : (starRingEnd ℂ w)⁻¹ = z := by
          rw [hwdef, map_inv₀, Complex.conj_conj, inv_inv]
        rw [if_pos (Or.inr h2), h2, hPw, hstar, hPz]
        simp
      · rw [if_neg (by tauto), hP0 _ hmi h1 h2, zero_mul]
  have hsum : D.toeplitzC (range n) (fun k => P.coeff k) =
      ∑ i, if D.β i = z ∨ D.β i = w then (-1 : ℂ) else 0 := by
    rw [D.toeplitzC_eq_sum]
    exact Finset.sum_congr rfl fun i _ => hvalue i
  have hre : (D.toeplitzC (range n) (fun k => P.coeff k)).re ≤ -1 := by
    rw [hsum, Complex.re_sum]
    have hterm : ∀ i, ((if D.β i = z ∨ D.β i = w then (-1 : ℂ) else 0)).re ≤ 0 := fun i => by
      split_ifs <;> simp
    have hsingle := Finset.single_le_sum
      (f := fun i => -((if D.β i = z ∨ D.β i = w then (-1 : ℂ) else 0)).re)
      (fun i _ => neg_nonneg.mpr (hterm i)) (Finset.mem_univ i₀)
    have hi₀ : ((if D.β i₀ = z ∨ D.β i₀ = w then (-1 : ℂ) else 0)).re = -1 := by
      rw [if_pos (Or.inl rfl)]
      simp
    simp only [hi₀, Finset.sum_neg_distrib] at hsingle
    linarith only [hsingle]
  rw [D.re_toeplitzC] at hre
  have h1 := h fun k => (P.coeff k).re
  have h2 := h fun k => (P.coeff k).im
  linarith only [hre, h1, h2]

/-- **Purity is decided on one window**: the datum is unitary iff Weil's form is nonnegative on the
window of size `#R`. -/
theorem unitary_iff_toeplitz_nonneg_on_spectrum_window :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ e : ℕ → ℝ, 0 ≤ D.toeplitz (range D.spectrum.card) e := by
  refine ⟨fun hU e => ?_, D.unitary_of_toeplitz_nonneg_on_spectrum_window⟩
  rw [toeplitz_eq_sum_normSq D hU]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ### The explicit formula -/

/-- The polar part `H(e) = 2F_e(s)F_e(1/s) + (2g − 2)Σe_k²`. -/
def curvePolar (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  2 * (∑ k ∈ S, e k * D.sqrtq ^ k) * (∑ k ∈ S, e k * (D.sqrtq⁻¹) ^ k) +
    ((Fintype.card ι : ℝ) - 2) * ∑ k ∈ S, e k ^ 2

/-- The prime part `P(e) = Σ_{k≠l} e_k e_l N_{|k−l|} s^{−|k−l|}`. -/
def curvePrime (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ k ∈ S, ∑ l ∈ S, if k = l then 0 else
    e k * e l * (D.pointCount (Nat.dist k l) * (D.sqrtq⁻¹) ^ Nat.dist k l)

/-- A lag of the trace against the pole plane and the point count. -/
theorem trace_eq_polar_sub_prime (j : ℕ) :
    D.trace j = D.sqrtq ^ j + (D.sqrtq⁻¹) ^ j - D.pointCount j * (D.sqrtq⁻¹) ^ j := by
  have hs := D.sqrtq_pos
  have hq : D.q ^ j = D.sqrtq ^ j * D.sqrtq ^ j := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  have hj : D.sqrtq ^ j * (D.sqrtq⁻¹) ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
  rw [pointCount, hq]
  have h1 : (D.sqrtq ^ j * D.sqrtq ^ j + 1 - D.sqrtq ^ j * D.trace j) * (D.sqrtq⁻¹) ^ j =
      D.sqrtq ^ j * (D.sqrtq ^ j * (D.sqrtq⁻¹) ^ j) + (D.sqrtq⁻¹) ^ j -
        (D.sqrtq ^ j * (D.sqrtq⁻¹) ^ j) * D.trace j := by ring
  rw [h1, hj]
  ring

/-- `s^{|k−l|} + s^{−|k−l|} = s^k s^{−l} + s^l s^{−k}`. -/
theorem pow_dist_add (k l : ℕ) :
    D.sqrtq ^ Nat.dist k l + (D.sqrtq⁻¹) ^ Nat.dist k l =
      D.sqrtq ^ k * (D.sqrtq⁻¹) ^ l + D.sqrtq ^ l * (D.sqrtq⁻¹) ^ k := by
  have hs := D.sqrtq_pos.ne'
  have hc (a b : ℕ) : D.sqrtq ^ (a + b) * (D.sqrtq⁻¹) ^ a = D.sqrtq ^ b := by
    rw [pow_add, mul_comm (D.sqrtq ^ a), mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, mul_one]
  have hd (a b : ℕ) : D.sqrtq ^ a * (D.sqrtq⁻¹) ^ (a + b) = (D.sqrtq⁻¹) ^ b := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
  rcases le_total k l with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, hd, hc]
    ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, hd, hc]

/-- **The explicit formula over `𝔽_q`.** -/
theorem toeplitz_eq_curvePolar_sub_curvePrime (S : Finset ℕ) (e : ℕ → ℝ) :
    D.toeplitz S e = D.curvePolar S e - D.curvePrime S e := by
  have hentry (k l : ℕ) : e k * e l * D.trace (Nat.dist k l) =
      e k * e l * (D.sqrtq ^ k * (D.sqrtq⁻¹) ^ l + D.sqrtq ^ l * (D.sqrtq⁻¹) ^ k) +
        (if k = l then ((Fintype.card ι : ℝ) - 2) * (e k * e l) else 0) -
        (if k = l then 0 else
          e k * e l * (D.pointCount (Nat.dist k l) * (D.sqrtq⁻¹) ^ Nat.dist k l)) := by
    rw [← D.pow_dist_add]
    by_cases hkl : k = l
    · subst hkl
      simp [Nat.dist_self, trace_zero]
      ring
    · rw [if_neg hkl, if_neg hkl, D.trace_eq_polar_sub_prime]
      ring
  have hpolar : ∑ k ∈ S, ∑ l ∈ S, e k * e l *
      (D.sqrtq ^ k * (D.sqrtq⁻¹) ^ l + D.sqrtq ^ l * (D.sqrtq⁻¹) ^ k) =
      2 * (∑ k ∈ S, e k * D.sqrtq ^ k) * (∑ k ∈ S, e k * (D.sqrtq⁻¹) ^ k) := by
    have hA : (∑ k ∈ S, e k * D.sqrtq ^ k) * (∑ k ∈ S, e k * (D.sqrtq⁻¹) ^ k) =
        ∑ k ∈ S, ∑ l ∈ S, e k * D.sqrtq ^ k * (e l * (D.sqrtq⁻¹) ^ l) := Finset.sum_mul_sum _ _ _ _
    have hB : (∑ k ∈ S, e k * D.sqrtq ^ k) * (∑ k ∈ S, e k * (D.sqrtq⁻¹) ^ k) =
        ∑ k ∈ S, ∑ l ∈ S, e l * D.sqrtq ^ l * (e k * (D.sqrtq⁻¹) ^ k) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    have hsplit : ∑ k ∈ S, ∑ l ∈ S, e k * e l *
        (D.sqrtq ^ k * (D.sqrtq⁻¹) ^ l + D.sqrtq ^ l * (D.sqrtq⁻¹) ^ k) =
        ∑ k ∈ S, ∑ l ∈ S, e k * D.sqrtq ^ k * (e l * (D.sqrtq⁻¹) ^ l) +
          ∑ k ∈ S, ∑ l ∈ S, e l * D.sqrtq ^ l * (e k * (D.sqrtq⁻¹) ^ k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [hsplit, ← hA, ← hB]
    ring
  have hdiag : ∑ k ∈ S, ∑ l ∈ S, (if k = l then ((Fintype.card ι : ℝ) - 2) * (e k * e l) else 0) =
      ((Fintype.card ι : ℝ) - 2) * ∑ k ∈ S, e k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_ite_eq S k, if_pos hk]
    ring
  unfold toeplitz curvePolar curvePrime
  simp_rw [hentry, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hpolar, hdiag]

/-! ### The Hardy interval -/

/-- The pencil `H − tP` on a window. -/
def hardyPencil (S : Finset ℕ) (e : ℕ → ℝ) (t : ℝ) : ℝ :=
  D.curvePolar S e - t * D.curvePrime S e

/-- The **Hardy interval** of the window `n`. -/
def curveHardyInterval (n : ℕ) : Set ℝ := {t | ∀ e : ℕ → ℝ, 0 ≤ D.hardyPencil (range n) e t}

theorem hardyPencil_eq (S : Finset ℕ) (e : ℕ → ℝ) (t : ℝ) :
    D.hardyPencil S e t = (1 - t) * D.curvePolar S e + t * D.toeplitz S e := by
  rw [hardyPencil, toeplitz_eq_curvePolar_sub_curvePrime]
  ring

theorem hardyPencil_one (S : Finset ℕ) (e : ℕ → ℝ) : D.hardyPencil S e 1 = D.toeplitz S e := by
  rw [hardyPencil_eq]
  ring

/-- **The multiple `1` is admissible on every window iff the datum is unitary**, and already on the
window `#R`. -/
theorem unitary_iff_one_mem_curveHardyInterval :
    (∀ i, ‖D.β i‖ = 1) ↔ 1 ∈ D.curveHardyInterval D.spectrum.card := by
  rw [D.unitary_iff_toeplitz_nonneg_on_spectrum_window]
  simp only [curveHardyInterval, Set.mem_setOf_eq, hardyPencil_one]

theorem one_mem_curveHardyInterval (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) :
    1 ∈ D.curveHardyInterval n := fun e => by
  rw [hardyPencil_one, toeplitz_eq_sum_normSq D hU]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The real coefficients of the reduced characteristic polynomial. -/
def charCoeff (k : ℕ) : ℝ := (D.reducedCharPoly.coeff k).re

theorem charCoeff_eq_zero {k : ℕ} (hk : D.spectrum.card < k) : D.charCoeff k = 0 := by
  rw [charCoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_reducedCharPoly])]
  simp

/-- The reduced characteristic polynomial over `ℝ`. -/
def charPolyReal : ℝ[X] := ∑ k ∈ range (D.spectrum.card + 1), Polynomial.C (D.charCoeff k) * X ^ k

theorem coeff_charPolyReal (k : ℕ) : D.charPolyReal.coeff k = D.charCoeff k := by
  simp only [charPolyReal, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [D.charCoeff_eq_zero (by simpa using h)]

theorem map_charPolyReal : D.charPolyReal.map (algebraMap ℝ ℂ) = D.reducedCharPoly := by
  ext k
  rw [coeff_map, coeff_charPolyReal, charCoeff]
  exact D.coeff_reducedCharPoly_real k

theorem coe_eval_charPolyReal (x : ℝ) :
    ((D.charPolyReal.eval x : ℝ) : ℂ) = D.reducedCharPoly.eval (x : ℂ) := by
  rw [← D.map_charPolyReal]
  exact (Polynomial.eval_map_apply (p := D.charPolyReal) (algebraMap ℝ ℂ) x).symm

theorem natDegree_charPolyReal_le : D.charPolyReal.natDegree ≤ D.spectrum.card := by
  rw [← natDegree_reducedCharPoly, ← D.map_charPolyReal]
  exact le_of_eq (natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _).symm

/-- `B·(1 + σ X^j)`, with `B` the reduced characteristic polynomial. -/
def shiftedCharPoly (σ : ℝ) (j : ℕ) : ℝ[X] :=
  D.charPolyReal * (1 + Polynomial.C σ * X ^ j)

theorem natDegree_shiftedCharPoly_le (σ : ℝ) (j : ℕ) :
    (D.shiftedCharPoly σ j).natDegree ≤ D.spectrum.card + j := by
  refine natDegree_mul_le.trans (add_le_add D.natDegree_charPolyReal_le ?_)
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le _ _).trans (by simp)

theorem coeff_shiftedCharPoly (σ : ℝ) (j k : ℕ) :
    (D.shiftedCharPoly σ j).coeff k =
      D.charCoeff k + σ * (if j ≤ k then D.charCoeff (k - j) else 0) := by
  have hX : D.charPolyReal * (Polynomial.C σ * X ^ j) =
      Polynomial.C σ * (D.charPolyReal * X ^ j) := by ring
  rw [shiftedCharPoly, mul_add, mul_one, hX, coeff_add, coeff_C_mul, coeff_mul_X_pow',
    coeff_charPolyReal]
  split_ifs with h
  · rw [coeff_charPolyReal]
  · rfl

/-- On a window containing it, the test `B·(1 + σ X^j)` has transform `B(z)(1 + σ z^j)`. -/
theorem sum_shiftedCharPoly_eq {σ : ℝ} {j n : ℕ} (hj : D.spectrum.card + j < n) (z : ℂ) :
    ∑ k ∈ range n, (((D.shiftedCharPoly σ j).coeff k : ℝ) : ℂ) * z ^ k =
      D.reducedCharPoly.eval z * (1 + (σ : ℂ) * z ^ j) := by
  have hdeg : ((D.shiftedCharPoly σ j).map (algebraMap ℝ ℂ)).natDegree < n := by
    rw [natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact (D.natDegree_shiftedCharPoly_le σ j).trans_lt hj
  have h := Polynomial.eval_eq_sum_range' hdeg z
  simp only [coeff_map] at h
  have hmap : ∑ k ∈ range n, (algebraMap ℝ ℂ) ((D.shiftedCharPoly σ j).coeff k) * z ^ k =
      ∑ k ∈ range n, (((D.shiftedCharPoly σ j).coeff k : ℝ) : ℂ) * z ^ k := rfl
  rw [← hmap, ← h, shiftedCharPoly, Polynomial.map_mul, eval_mul, D.map_charPolyReal]
  simp

/-- The same on the real line. -/
theorem sum_shiftedCharPoly_real {σ : ℝ} {j n : ℕ} (hj : D.spectrum.card + j < n) (x : ℝ) :
    ∑ k ∈ range n, (D.shiftedCharPoly σ j).coeff k * x ^ k =
      D.charPolyReal.eval x * (1 + σ * x ^ j) := by
  have hdeg : (D.shiftedCharPoly σ j).natDegree < n :=
    (D.natDegree_shiftedCharPoly_le σ j).trans_lt hj
  rw [← Polynomial.eval_eq_sum_range' hdeg x, shiftedCharPoly]
  simp

/-- Every shifted test lies in the radical of the form of a unitary datum. -/
theorem toeplitz_shiftedCharPoly_eq_zero (hU : ∀ i, ‖D.β i‖ = 1) {σ : ℝ} {j n : ℕ}
    (hj : D.spectrum.card + j < n) :
    D.toeplitz (range n) (fun k => (D.shiftedCharPoly σ j).coeff k) = 0 := by
  rw [D.toeplitz_eq_zero_iff hU]
  intro i
  rw [eval_windowPoly, D.sum_shiftedCharPoly_eq hj, D.eval_reducedCharPoly, zero_mul]

/-- The energy of a shifted test is bounded independently of the shift. -/
theorem sum_sq_shiftedCharPoly_le {j n : ℕ} {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∑ k ∈ range n, ((D.shiftedCharPoly σ j).coeff k) ^ 2 ≤
      4 * ∑ k ∈ range (D.spectrum.card + 1), D.charCoeff k ^ 2 := by
  classical
  set m := D.spectrum.card + 1 with hm
  have hbase : ∑ k ∈ range n, D.charCoeff k ^ 2 ≤ ∑ k ∈ range m, D.charCoeff k ^ 2 := by
    rw [← Finset.sum_filter_of_ne (s := range n) (p := fun k => k < m)
      (f := fun k => D.charCoeff k ^ 2) (fun k _ hk => by
        by_contra hlt
        exact hk (by rw [D.charCoeff_eq_zero (by omega)]; norm_num))]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
    simpa using (Finset.mem_filter.mp hk).2
  have hshift : ∑ k ∈ range n, (if j ≤ k then D.charCoeff (k - j) else 0) ^ 2 ≤
      ∑ k ∈ range m, D.charCoeff k ^ 2 := by
    have hite : ∑ k ∈ range n, (if j ≤ k then D.charCoeff (k - j) else 0) ^ 2 =
        ∑ k ∈ (range n).filter (fun k => j ≤ k), D.charCoeff (k - j) ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    rw [hite]
    have hinj : Set.InjOn (fun k => k - j) ((range n).filter (fun k => j ≤ k) : Set ℕ) := by
      intro a ha b hb hab
      have h1 := (Finset.mem_filter.mp ha).2
      have h2 := (Finset.mem_filter.mp hb).2
      simp only at hab
      omega
    rw [← Finset.sum_image (f := fun i => D.charCoeff i ^ 2) hinj]
    rw [← Finset.sum_filter_of_ne (s := ((range n).filter (fun k => j ≤ k)).image (fun k => k - j))
      (p := fun k => k < m) (f := fun k => D.charCoeff k ^ 2) (fun k _ hk => by
        by_contra hlt
        exact hk (by rw [D.charCoeff_eq_zero (by omega)]; norm_num))]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
    simpa using (Finset.mem_filter.mp hk).2
  have hterm (k : ℕ) : ((D.shiftedCharPoly σ j).coeff k) ^ 2 ≤
      2 * D.charCoeff k ^ 2 + 2 * (if j ≤ k then D.charCoeff (k - j) else 0) ^ 2 := by
    rw [coeff_shiftedCharPoly]
    set a := D.charCoeff k
    set b := if j ≤ k then D.charCoeff (k - j) else 0
    have h : (a + σ * b) ^ 2 + (a - σ * b) ^ 2 = 2 * a ^ 2 + 2 * (σ ^ 2 * b ^ 2) := by ring
    rw [hσ, one_mul] at h
    nlinarith only [h, sq_nonneg (a - σ * b)]
  calc ∑ k ∈ range n, ((D.shiftedCharPoly σ j).coeff k) ^ 2
      ≤ ∑ k ∈ range n, (2 * D.charCoeff k ^ 2 +
          2 * (if j ≤ k then D.charCoeff (k - j) else 0) ^ 2) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * ∑ k ∈ range n, D.charCoeff k ^ 2 +
          2 * ∑ k ∈ range n, (if j ≤ k then D.charCoeff (k - j) else 0) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by linarith only [hbase, hshift]

/-- The reduced characteristic polynomial does not vanish off the unit circle on a unitary datum. -/
theorem eval_reducedCharPoly_ne_zero (hU : ∀ i, ‖D.β i‖ = 1) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    D.reducedCharPoly.eval z ≠ 0 := by
  rw [reducedCharPoly, eval_prod, Finset.prod_ne_zero_iff]
  intro w hw
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact hz (by rw [h, hU])

/-- **The Hardy interval collapses.** For a unitary datum there is a window beyond which
`ℋ(n) = {1}` exactly: the radical of the form contains tests on both sides of the polar plane. -/
theorem eventually_curveHardyInterval_eq_singleton (hU : ∀ i, ‖D.β i‖ = 1) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → D.curveHardyInterval n = {1} := by
  have hs1 : 1 < D.sqrtq := by
    have hq := D.one_lt_q
    have hsq := D.sqrtq_sq
    have hpos := D.sqrtq_pos
    nlinarith only [hq, hsq, hpos]
  have hspos := D.sqrtq_pos
  have hc1 : D.charPolyReal.eval D.sqrtq ≠ 0 := by
    intro h0
    have h := D.eval_reducedCharPoly_ne_zero hU (z := (D.sqrtq : ℂ)) (by
      rw [Complex.norm_real, Real.norm_of_nonneg hspos.le]
      exact hs1.ne')
    apply h
    rw [← D.coe_eval_charPolyReal, h0, Complex.ofReal_zero]
  have hc2 : D.charPolyReal.eval D.sqrtq⁻¹ ≠ 0 := by
    intro h0
    have h := D.eval_reducedCharPoly_ne_zero hU (z := ((D.sqrtq⁻¹ : ℝ) : ℂ)) (by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hspos).le]
      exact (inv_lt_one_of_one_lt₀ hs1).ne)
    apply h
    rw [← D.coe_eval_charPolyReal, h0, Complex.ofReal_zero]
  set c := D.charPolyReal.eval D.sqrtq * D.charPolyReal.eval D.sqrtq⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero hc1 hc2
  have hc0' : 0 < |c| := abs_pos.mpr hc0
  set B := 4 * ∑ k ∈ range (D.spectrum.card + 1), D.charCoeff k ^ 2 with hB
  set M := |(Fintype.card ι : ℝ) - 2| * B with hM
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have hM0 : 0 ≤ M := by positivity
  -- the shifted power `s^j` exceeds the budget
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 + M / (2 * |c|) + 1) hs1
  refine ⟨D.spectrum.card + j + 1, fun n hn => ?_⟩
  have hn' : D.spectrum.card + j < n := by omega
  have hinv : D.sqrtq ^ j * (D.sqrtq⁻¹) ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hspos.ne', one_pow]
  have hinv0 : 0 < (D.sqrtq⁻¹) ^ j := by positivity
  set Y := D.sqrtq ^ j + (D.sqrtq⁻¹) ^ j with hY
  have hYbig : 2 + M / (2 * |c|) < Y := by rw [hY]; linarith only [hj, hinv0]
  have hYpay : M < 2 * |c| * (Y - 2) := by
    have h : M / (2 * |c|) < Y - 2 := by linarith only [hYbig]
    rw [div_lt_iff₀ (by positivity)] at h
    linarith only [h]
  have hpolar (σ : ℝ) (hσ : σ ^ 2 = 1) :
      D.curvePolar (range n) (fun k => (D.shiftedCharPoly σ j).coeff k) =
        2 * c * (2 + σ * Y) + ((Fintype.card ι : ℝ) - 2) *
          ∑ k ∈ range n, ((D.shiftedCharPoly σ j).coeff k) ^ 2 := by
    rw [curvePolar, D.sum_shiftedCharPoly_real hn', D.sum_shiftedCharPoly_real hn']
    have hprod : (1 + σ * D.sqrtq ^ j) * (1 + σ * (D.sqrtq⁻¹) ^ j) = 2 + σ * Y := by
      have e : (1 + σ * D.sqrtq ^ j) * (1 + σ * (D.sqrtq⁻¹) ^ j) =
          1 + σ * Y + σ ^ 2 * (D.sqrtq ^ j * (D.sqrtq⁻¹) ^ j) := by rw [hY]; ring
      rw [e, hσ, hinv]
      ring
    rw [hc]
    linear_combination 2 * D.charPolyReal.eval D.sqrtq * D.charPolyReal.eval D.sqrtq⁻¹ * hprod
  have hextra (σ : ℝ) (hσ : σ ^ 2 = 1) :
      |((Fintype.card ι : ℝ) - 2) * ∑ k ∈ range n, ((D.shiftedCharPoly σ j).coeff k) ^ 2| ≤ M := by
    have hsum0 : 0 ≤ ∑ k ∈ range n, ((D.shiftedCharPoly σ j).coeff k) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [abs_mul, abs_of_nonneg hsum0]
    exact mul_le_mul_of_nonneg_left (D.sum_sq_shiftedCharPoly_le hσ) (abs_nonneg _)
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨D.one_mem_curveHardyInterval hU n, fun t ht => ?_⟩
  have hvalue (σ : ℝ) : 0 ≤ (1 - t) *
      D.curvePolar (range n) (fun k => (D.shiftedCharPoly σ j).coeff k) := by
    have h := ht fun k => (D.shiftedCharPoly σ j).coeff k
    rw [hardyPencil_eq, D.toeplitz_shiftedCharPoly_eq_zero hU hn', mul_zero, add_zero] at h
    exact h
  -- the two signs of the polar plane
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hpos, hneg⟩ : ∃ σ₁ σ₂ : ℝ, σ₁ ^ 2 = 1 ∧ σ₂ ^ 2 = 1 ∧
      0 < 2 * c * (2 + σ₁ * Y) - M ∧ 2 * c * (2 + σ₂ * Y) + M < 0 := by
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · rw [abs_of_neg hneg] at hYpay
      refine ⟨-1, 1, by norm_num, by norm_num, ?_, ?_⟩ <;> nlinarith only [hYpay, hneg]
    · rw [abs_of_pos hpos] at hYpay
      refine ⟨1, -1, by norm_num, by norm_num, ?_, ?_⟩ <;> nlinarith only [hYpay, hpos]
  have h1 := hvalue σ₁
  have h2 := hvalue σ₂
  rw [hpolar σ₁ hσ₁] at h1
  rw [hpolar σ₂ hσ₂] at h2
  have ha1 := abs_le.mp (hextra σ₁ hσ₁)
  have ha2 := abs_le.mp (hextra σ₂ hσ₂)
  have hP1 : 0 < 2 * c * (2 + σ₁ * Y) + ((Fintype.card ι : ℝ) - 2) *
      ∑ k ∈ range n, ((D.shiftedCharPoly σ₁ j).coeff k) ^ 2 := by linarith only [hpos, ha1.1]
  have hP2 : 2 * c * (2 + σ₂ * Y) + ((Fintype.card ι : ℝ) - 2) *
      ∑ k ∈ range n, ((D.shiftedCharPoly σ₂ j).coeff k) ^ 2 < 0 := by linarith only [hneg, ha2.2]
  have ht1 : 0 ≤ 1 - t := nonneg_of_mul_nonneg_left h1 hP1
  have ht2 : 1 - t ≤ 0 := nonpos_of_mul_nonneg_left h2 hP2
  linarith only [ht1, ht2]

/-! ### The chain ends at the number of angles -/

/-- **Bounded evaluation before contact**: on a unitary datum, for `n ≤ #R`, point evaluation is
bounded by Weil's form with the Lagrange constant `Σ_{z∈R} |ℓ_z(z₀)|²`. -/
theorem norm_eval_sq_le_mul_toeplitz (hU : ∀ i, ‖D.β i‖ = 1) {n : ℕ} (hn : n ≤ D.spectrum.card)
    (z₀ : ℂ) (e : ℕ → ℝ) :
    ‖(windowPoly n e).eval z₀‖ ^ 2 ≤
      (∑ z ∈ D.spectrum, ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖ ^ 2) *
        D.toeplitz (range n) e := by
  classical
  set E := windowPoly n e with hE
  have hval : Set.InjOn (fun x : ℂ => x) D.spectrum := fun _ _ _ _ h => h
  have hdeg : E.degree < (D.spectrum.card : WithBot ℕ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have h0 : E = 0 := by simp [hE, windowPoly]
      rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · by_cases h0 : E = 0
      · rw [h0, degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree h0]
        exact_mod_cast (natDegree_windowPoly_lt hn0 e).trans_le hn
  have hint : E = Lagrange.interpolate D.spectrum (fun x => x) (fun z => E.eval z) :=
    Lagrange.eq_interpolate hval hdeg
  have heval : E.eval z₀ = ∑ z ∈ D.spectrum,
      E.eval z * (Lagrange.basis D.spectrum (fun x => x) z).eval z₀ := by
    conv_lhs => rw [hint, Lagrange.interpolate_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [eval_mul, eval_C]
  -- Cauchy–Schwarz over the spectrum
  have hcs : ‖E.eval z₀‖ ^ 2 ≤ (∑ z ∈ D.spectrum, ‖E.eval z‖ ^ 2) *
      ∑ z ∈ D.spectrum, ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖ ^ 2 := by
    have htri : ‖E.eval z₀‖ ≤ ∑ z ∈ D.spectrum,
        ‖E.eval z‖ * ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖ := by
      rw [heval]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      rw [norm_mul]
    calc ‖E.eval z₀‖ ^ 2 ≤ (∑ z ∈ D.spectrum,
          ‖E.eval z‖ * ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- the spectrum is a subset of the eigenvalues with multiplicity
  have hspec : ∑ z ∈ D.spectrum, ‖E.eval z‖ ^ 2 ≤ D.toeplitz (range n) e := by
    rw [toeplitz_eq_sum_normSq D hU]
    have hmaps : ∀ i ∈ (Finset.univ : Finset ι), D.β i ∈ D.spectrum := fun i hi =>
      Finset.mem_image_of_mem D.β hi
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun z hz => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have hmem : i ∈ (Finset.univ : Finset ι).filter (fun i' => D.β i' = D.β i) := by simp
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i' =>
      ‖∑ k ∈ range n, (e k : ℂ) * D.β i' ^ k‖ ^ 2) (fun _ _ => sq_nonneg _) hmem)
    simp only [hE, eval_windowPoly]
  have hL : 0 ≤ ∑ z ∈ D.spectrum, ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖E.eval z₀‖ ^ 2 ≤ _ := hcs
    _ ≤ (D.toeplitz (range n) e) *
          ∑ z ∈ D.spectrum, ‖(Lagrange.basis D.spectrum (fun x => x) z).eval z₀‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hspec hL
    _ = _ := mul_comm _ _

/-- **The kernel diverges at contact**: on a unitary datum, for `n > #R` and `z₀` off the spectrum,
no bound of point evaluation by Weil's form holds. -/
theorem not_exists_evaluation_bound_of_lt (hU : ∀ i, ‖D.β i‖ = 1) {n : ℕ}
    (hn : D.spectrum.card < n) {z₀ : ℂ} (hz₀ : z₀ ∉ D.spectrum) :
    ¬ ∃ K : ℝ, ∀ e : ℕ → ℝ, ‖(windowPoly n e).eval z₀‖ ^ 2 ≤ K * D.toeplitz (range n) e := by
  rintro ⟨K, hK⟩
  have hj : D.spectrum.card + 0 < n := by omega
  -- the zero shift doubles `B`: its evaluation does not vanish
  have h0 := D.toeplitz_shiftedCharPoly_eq_zero hU (σ := 0) (j := 0) hj
  have hv := hK fun k => (D.shiftedCharPoly 0 0).coeff k
  rw [h0, mul_zero, eval_windowPoly, D.sum_shiftedCharPoly_eq hj] at hv
  have hne : D.reducedCharPoly.eval z₀ ≠ 0 := by
    rw [reducedCharPoly, eval_prod, Finset.prod_ne_zero_iff]
    intro w hw
    simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact fun h => hz₀ (h ▸ hw)
  have hval : ‖D.reducedCharPoly.eval z₀ * (1 + ((0 : ℝ) : ℂ) * z₀ ^ 0)‖ ^ 2 =
      ‖D.reducedCharPoly.eval z₀‖ ^ 2 := by simp
  rw [hval] at hv
  have hpos : 0 < ‖D.reducedCharPoly.eval z₀‖ ^ 2 := by positivity
  linarith only [hv, hpos]

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.unitary_iff_toeplitz_nonneg_on_spectrum_window
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.eventually_curveHardyInterval_eq_singleton
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.norm_eval_sq_le_mul_toeplitz
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.not_exists_evaluation_bound_of_lt
