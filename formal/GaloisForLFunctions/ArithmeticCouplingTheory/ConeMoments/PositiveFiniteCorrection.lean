import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Positive finite Fourier correction at arbitrary heights

For a finite set of positive frequencies and residuals of total norm at most `A/4`,
positive masses of total size `A` cancel every residual exactly. Their nodes can lie
above any prescribed height, with upper and lower weight bounds independent of it.

Convolving two-point half-period measures annihilates the frequencies, their sums,
and their nonzero differences. A real trigonometric density on the resulting atoms
then corrects the moments while retaining at least half the uniform mass.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def phase (u t : ℝ) : ℂ := Complex.exp ((u * t : ℝ) * Complex.I)

lemma phase_add (u x y : ℝ) : phase u (x + y) = phase u x * phase u y := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma phase_freq_add (u v t : ℝ) : phase (u + v) t = phase u t * phase v t := by
  simp only [phase, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma phase_neg (u t : ℝ) : phase (-u) t = star (phase u t) := by
  change phase (-u) t = (starRingEnd ℂ) (phase u t)
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    neg_mul, Complex.ofReal_neg, mul_neg]

lemma phase_norm (u t : ℝ) : ‖phase u t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma phase_zero (t : ℝ) : phase 0 t = 1 := by simp [phase]

lemma phase_halfPeriod {u : ℝ} (hu : u ≠ 0) : phase u (Real.pi / u) = -1 := by
  have h : u * (Real.pi / u) = Real.pi := by field_simp
  rw [phase, h, Complex.exp_pi_mul_I]

/-- Repeated half-period doubling gives equal positive masses annihilating any finite nonzero spectrum. -/
theorem exists_cancel (S : Finset ℝ) (hS : ∀ u ∈ S, u ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ x : Fin n → ℝ, ∀ u ∈ S, ∑ j, phase u (x j) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, Nat.zero_lt_one, fun _ => 0, by simp⟩
  | @insert u S hu ih =>
    obtain ⟨n, hn, x, hx⟩ := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv))
    refine ⟨n + n, by omega, Fin.append x (fun j => x j + Real.pi / u), ?_⟩
    intro v hv
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, phase_add]
    rw [← Finset.sum_mul]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [phase_halfPeriod (hS v (Finset.mem_insert_self _ _))]
      ring
    · rw [hx v hv]
      ring

/-- Translation preserves the vanishing moments and moves every atom above an arbitrary height. -/
theorem exists_cancel_above (S : Finset ℝ) (hS : ∀ u ∈ S, u ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : ℝ, ∃ x : Fin n → ℝ,
      (∀ j, H ≤ x j) ∧ (∀ u ∈ S, ∑ j, phase u (x j) = 0) := by
  classical
  obtain ⟨n, hn, x, hx⟩ := exists_cancel S hS
  refine ⟨n, hn, fun H => ⟨fun j => H + ∑ k, |x k| + x j, ?_, ?_⟩⟩
  · intro j
    have hj : |x j| ≤ ∑ k, |x k| := single_le_sum (fun k _ => abs_nonneg (x k)) (mem_univ j)
    linarith [neg_abs_le (x j)]
  · intro u hu
    simp_rw [phase_add]
    rw [← Finset.mul_sum, hx u hu, mul_zero]

/-- The frequencies needed to correct real positive masses include sums and differences. -/
def correctionSpectrum (S : Finset ℝ) : Finset ℝ :=
  (S ∪ (S.biUnion fun u => S.image fun v => u - v) ∪
    (S.biUnion fun u => S.image fun v => u + v)).erase 0

lemma mem_correctionSpectrum (S : Finset ℝ) {u : ℝ} (hu : u ∈ S) (hu0 : 0 < u) :
    u ∈ correctionSpectrum S := by
  classical
  simp only [correctionSpectrum, mem_erase, mem_union]
  exact ⟨hu0.ne', Or.inl (Or.inl hu)⟩

lemma sub_mem_correctionSpectrum (S : Finset ℝ) {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S)
    (hne : u ≠ v) : u - v ∈ correctionSpectrum S := by
  classical
  simp only [correctionSpectrum, mem_erase, mem_union]
  exact ⟨sub_ne_zero.mpr hne, Or.inl (Or.inr (mem_biUnion.mpr
    ⟨u, hu, mem_image.mpr ⟨v, hv, rfl⟩⟩))⟩

lemma add_mem_correctionSpectrum (S : Finset ℝ) {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S)
    (hu0 : 0 < u) (hv0 : 0 < v) : u + v ∈ correctionSpectrum S := by
  classical
  simp only [correctionSpectrum, mem_erase, mem_union]
  exact ⟨(add_pos hu0 hv0).ne', Or.inr (mem_biUnion.mpr
    ⟨u, hu, mem_image.mpr ⟨v, hv, rfl⟩⟩)⟩

def correctionSignal (S : Finset ℝ) (r : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ u ∈ S, r u * phase (-u) t

lemma correctionSignal_bound (S : Finset ℝ) (r : ℝ → ℂ) (t : ℝ) :
    |(correctionSignal S r t).re| ≤ ∑ u ∈ S, ‖r u‖ := by
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  simp only [norm_mul, phase_norm, mul_one, le_refl]

lemma sum_correctionSignal {n : ℕ} (S : Finset ℝ) (r : ℝ → ℂ) (x : Fin n → ℝ)
    (hx : ∀ u ∈ S, ∑ j, phase u (x j) = 0) :
    ∑ j, correctionSignal S r (x j) = 0 := by
  classical
  simp only [correctionSignal]
  rw [Finset.sum_comm]
  refine sum_eq_zero fun u hu => ?_
  simp_rw [phase_neg]
  rw [← Finset.mul_sum, ← star_sum, hx u hu, star_zero, mul_zero]

lemma sum_correctionSignal_phase {n : ℕ} (S : Finset ℝ) (r : ℝ → ℂ) (x : Fin n → ℝ)
    (hx : ∀ u ∈ correctionSpectrum S, ∑ j, phase u (x j) = 0)
    {u : ℝ} (hu : u ∈ S) :
    ∑ j, correctionSignal S r (x j) * phase u (x j) = (n : ℂ) * r u := by
  classical
  simp only [correctionSignal, Finset.sum_mul]
  rw [Finset.sum_comm]
  have heq : ∀ v ∈ S, ∑ j, r v * phase (-v) (x j) * phase u (x j) =
      if v = u then (n : ℂ) * r u else 0 := by
    intro v hv
    have hterm : ∀ j, r v * phase (-v) (x j) * phase u (x j) =
        r v * phase (u - v) (x j) := by
      intro j
      rw [sub_eq_add_neg, phase_freq_add]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    by_cases h : v = u
    · subst v
      simp [phase_zero, mul_comm]
    · rw [hx _ (sub_mem_correctionSpectrum S hu hv (Ne.symm h))]
      simp [h]
  rw [sum_congr rfl heq]
  simp [hu]

lemma sum_star_correctionSignal_phase {n : ℕ} (S : Finset ℝ) (r : ℝ → ℂ) (x : Fin n → ℝ)
    (hS : ∀ u ∈ S, 0 < u)
    (hx : ∀ u ∈ correctionSpectrum S, ∑ j, phase u (x j) = 0)
    {u : ℝ} (hu : u ∈ S) :
    ∑ j, star (correctionSignal S r (x j)) * phase u (x j) = 0 := by
  classical
  simp only [correctionSignal, star_sum, star_mul, ← phase_neg, neg_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_eq_zero fun v hv => ?_
  have hterm : ∀ j, phase v (x j) * star (r v) * phase u (x j) =
      star (r v) * phase (u + v) (x j) := by
    intro j
    rw [phase_freq_add]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hx _ (add_mem_correctionSpectrum S hu hv (hS u hu) (hS v hv)), mul_zero]

/-- Exact positive correction of finitely many positive Fourier moments, at any height. -/
theorem exists_positive_correction (S : Finset ℝ) (hS : ∀ u ∈ S, 0 < u)
    (r : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (hr : ∑ u ∈ S, ‖r u‖ ≤ A / 4) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : ℝ, ∃ (x w : Fin n → ℝ),
      (∀ j, H ≤ x j) ∧
      (∀ j, 0 < w j ∧ A / (2 * n) ≤ w j ∧ w j ≤ 3 * A / (2 * n)) ∧
      (∑ j, w j = A) ∧
      (∀ u ∈ S, ∑ j, (w j : ℂ) * phase u (x j) = -r u) := by
  classical
  obtain ⟨n, hn, hx⟩ := exists_cancel_above (correctionSpectrum S)
    (fun u hu => (mem_erase.mp hu).1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨n, hn, fun H => ?_⟩
  obtain ⟨x, hxH, hx⟩ := hx H
  let w : Fin n → ℝ := fun j => (A - 2 * (correctionSignal S r (x j)).re) / n
  have hxS : ∀ u ∈ S, ∑ j, phase u (x j) = 0 :=
    fun u hu => hx u (mem_correctionSpectrum S hu (hS u hu))
  have hg0 := sum_correctionSignal S r x hxS
  have hgreal : ∑ j, (correctionSignal S r (x j)).re = 0 := by
    rw [← Complex.re_sum, hg0]
    rfl
  refine ⟨x, w, hxH, ?_, ?_, ?_⟩
  · intro j
    have hb := (correctionSignal_bound S r (x j)).trans hr
    have hb' := abs_le.mp hb
    have hlo : A / (2 * n) ≤ w j := by
      rw [← div_div A 2 (n : ℝ)]
      exact div_le_div_of_nonneg_right (by linarith) hnR.le
    refine ⟨lt_of_lt_of_le (div_pos hA (mul_pos (by norm_num) hnR)) hlo, hlo, ?_⟩
    rw [← div_div (3 * A) 2 (n : ℝ)]
    exact div_le_div_of_nonneg_right (by linarith) hnR.le
  · calc ∑ j, w j = ((n : ℝ) * A - 2 * ∑ j, (correctionSignal S r (x j)).re) / n := by
          simp only [w, ← Finset.sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
        _ = A := by rw [hgreal]; field_simp; ring
  · intro u hu
    have hg := sum_correctionSignal_phase S r x hx hu
    have hgc := sum_star_correctionSignal_phase S r x hS hx hu
    have hre : ∑ j, ((correctionSignal S r (x j)).re : ℂ) * phase u (x j) =
        (n : ℂ) * r u / 2 := by
      have he : ∀ j, ((correctionSignal S r (x j)).re : ℂ) * phase u (x j) =
          (correctionSignal S r (x j) * phase u (x j) +
            star (correctionSignal S r (x j)) * phase u (x j)) / 2 := by
        intro j
        rw [Complex.re_eq_add_conj]
        change ((correctionSignal S r (x j) + star (correctionSignal S r (x j))) / 2) * _ = _
        ring
      simp_rw [he]
      rw [← Finset.sum_div, sum_add_distrib, hg, hgc, add_zero]
    have he : ∀ j, (w j : ℂ) * phase u (x j) =
        ((A : ℂ) * phase u (x j) -
          2 * ((correctionSignal S r (x j)).re : ℂ) * phase u (x j)) / n := by
      intro j
      simp only [w, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_natCast]
      ring
    simp_rw [he]
    rw [← Finset.sum_div, sum_sub_distrib, ← Finset.mul_sum]
    have he' : ∑ j, 2 * ((correctionSignal S r (x j)).re : ℂ) * phase u (x j) =
        2 * ∑ j, ((correctionSignal S r (x j)).re : ℂ) * phase u (x j) := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [he', hxS u hu, hre]
    field_simp
    ring

#print axioms exists_positive_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
