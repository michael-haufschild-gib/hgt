import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveAtomicConeNullseries

/-!
# Positive quartets with bounded cone coupling

Positive atomic nullseries give real even kernels with off-axis support and
unattained positive width. Reflection contributes at most four at each positive
cone time, so the mixed coupling is bounded by twenty. The support is distinct
and has linear height count; weights have a reciprocal lower bound.

These freely chosen masses exhibit a boundary of generic cone arguments.
They are not identified with the prescribed complex spline weights of zeta.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def laplaceSeries {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' i, (w i : ℂ) * Complex.exp ((t : ℂ) * z i)

/-- Reflection and conjugation attach the four points `z, conj z, -z, -conj z`. -/
def quartetKernel {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (t : ℝ) : ℂ :=
  laplaceSeries z w t + star (laplaceSeries z w t) +
    laplaceSeries z w (-t) + star (laplaceSeries z w (-t))

lemma quartetKernel_neg {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (t : ℝ) :
    quartetKernel z w (-t) = quartetKernel z w t := by
  simp only [quartetKernel, neg_neg]
  ring

lemma quartetKernel_hermitian {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (t : ℝ) :
    quartetKernel z w (-t) = star (quartetKernel z w t) := by
  simp only [quartetKernel, neg_neg, star_add, star_star]
  ring

lemma laplaceSeries_zero {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (hs : HasSum w 2) :
    laplaceSeries z w 0 = 2 := by
  simp only [laplaceSeries, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    ← Complex.ofReal_tsum, hs.tsum_eq, Complex.ofReal_ofNat]

lemma quartetKernel_zero {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (hs : HasSum w 2) :
    quartetKernel z w 0 = 8 := by
  simp only [quartetKernel, neg_zero, laplaceSeries_zero z w hs]
  norm_num

lemma norm_laplaceSeries_neg_le_two {ι : Type*} (z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 2) (hz : ∀ i, 0 ≤ (z i).re)
    {t : ℝ} (ht : 0 ≤ t) : ‖laplaceSeries z w (-t)‖ ≤ 2 := by
  apply tsum_of_norm_bounded hs
  intro i
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have he : Real.exp (-t * (z i).re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hz i))
  exact (mul_le_mul_of_nonneg_left he (hw i)).trans_eq (mul_one _)

lemma summable_laplaceSeries {ι : Type*} (z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) {D : ℝ}
    (hz0 : ∀ i, 0 ≤ (z i).re) (hzD : ∀ i, (z i).re ≤ D) (t : ℝ) :
    Summable fun i => (w i : ℂ) * Complex.exp ((t : ℂ) * z i) := by
  refine Summable.of_norm_bounded (hs.mul_right (Real.exp (|t| * D))) fun i => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw i)
  exact (mul_le_mul_of_nonneg_right (le_abs_self t) (hz0 i)).trans
    (mul_le_mul_of_nonneg_left (hzD i) (abs_nonneg t))

lemma norm_quartetKernel_le_four {ι : Type*} (z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 2) (hz : ∀ i, 0 ≤ (z i).re)
    {t : ℝ} (ht : 0 ≤ t)
    (hzero : HasSum (fun i => (w i : ℂ) * Complex.exp ((t : ℂ) * z i)) 0) :
    ‖quartetKernel z w t‖ ≤ 4 := by
  have he : laplaceSeries z w t = 0 := hzero.tsum_eq
  simp only [quartetKernel, he, star_zero, zero_add]
  have h := norm_add_le (laplaceSeries z w (-t)) (star (laplaceSeries z w (-t)))
  rw [norm_star] at h
  linarith [norm_laplaceSeries_neg_le_two z w hw hs hz ht]

/-- Vanishing cone moments leave only a uniformly bounded reflected contribution to the coupling. -/
theorem quartet_coupling_le_twenty {ι : Type*} (z : ι → ℂ) (w : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 2) (hz : ∀ i, 0 ≤ (z i).re)
    (hzero : ∀ t : PositiveCone a b,
      HasSum (fun i => (w i : ℂ) * Complex.exp ((t.val : ℂ) * z i)) 0)
    (m n : ℕ) :
    ‖quartetKernel z w (m * a + n * b) - quartetKernel z w (m * a) -
      quartetKernel z w (n * b) + quartetKernel z w 0‖ ≤ 20 := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_mul, zero_add]
    have he : quartetKernel z w (n * b) - quartetKernel z w 0 -
        quartetKernel z w (n * b) + quartetKernel z w 0 = 0 := by ring
    rw [he]
    norm_num
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have he : quartetKernel z w (m * a) - quartetKernel z w (m * a) -
        quartetKernel z w 0 + quartetKernel z w 0 = 0 := by ring
    rw [he]
    norm_num
  have hmpos : 0 < (m : ℝ) * a := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) ha
  have hnpos : 0 < (n : ℝ) * b := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hb
  let ta : PositiveCone a b := ⟨m * a, hmpos, ⟨(m, 0), by simp [coneFrequency]⟩⟩
  let tb : PositiveCone a b := ⟨n * b, hnpos, ⟨(0, n), by simp [coneFrequency]⟩⟩
  let tab : PositiveCone a b := ⟨m * a + n * b, add_pos hmpos hnpos, ⟨(m, n), rfl⟩⟩
  have hka := norm_quartetKernel_le_four z w hw hs hz hmpos.le (hzero ta)
  have hkb := norm_quartetKernel_le_four z w hw hs hz hnpos.le (hzero tb)
  have hkab := norm_quartetKernel_le_four z w hw hs hz (add_pos hmpos hnpos).le (hzero tab)
  have hk0 : ‖quartetKernel z w 0‖ = 8 := by rw [quartetKernel_zero z w hs]; norm_num
  have h1 := norm_add_le (quartetKernel z w (m * a + n * b) - quartetKernel z w (m * a) -
    quartetKernel z w (n * b)) (quartetKernel z w 0)
  have h2 := norm_sub_le (quartetKernel z w (m * a + n * b) - quartetKernel z w (m * a))
    (quartetKernel z w (n * b))
  have h3 := norm_sub_le (quartetKernel z w (m * a + n * b)) (quartetKernel z w (m * a))
  linarith only [h1, h2, h3, hka, hkb, hkab, hk0]

/-- Positive off-axis quartets with sparse heights and unattained width can have bounded cone coupling. -/
theorem exists_positive_quartet_cone_model {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ) (w : ι → ℝ),
      Function.Injective z ∧ (∀ i, 0 < w i) ∧ HasSum w 2 ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, 1 / (1 + |(z i).im|) ≤ w i) ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : ℝ, Summable (fun i => (w i : ℂ) * Complex.exp ((t : ℂ) * z i))) ∧
      (∀ m n : ℕ, ‖quartetKernel z w (m * a + n * b) - quartetKernel z w (m * a) -
        quartetKernel z w (n * b) + quartetKernel z w 0‖ ≤ 20) := by
  obtain ⟨ι, hι, z, w, hinj, hw, hs, hstrip, hwidth, hbound, hcount, hzero⟩ :=
    exists_two_clock_positive_atomic_nullseries ha hb hd hdD
  refine ⟨ι, hι, z, w, hinj, hw, hs, hstrip, hwidth, hbound, hcount, ?_, ?_⟩
  · exact summable_laplaceSeries z w (fun i => (hw i).le) hs.summable
      (fun i => hd.le.trans (hstrip i).1) (fun i => (hstrip i).2.le)
  · exact quartet_coupling_le_twenty z w ha hb (fun i => (hw i).le) hs
      (fun i => hd.le.trans (hstrip i).1) hzero

#print axioms exists_positive_quartet_cone_model
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
