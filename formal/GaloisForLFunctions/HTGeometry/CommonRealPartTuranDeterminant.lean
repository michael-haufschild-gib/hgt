import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The Turán determinant of a configuration with one common real part

For a finite family of complex points `w i` carrying nonnegative weights `m i`, put

`f n = sum_i m i * (w i) ^ n`.

The elementary variance identity `f 0 * f 2 - f 1 ^ (2 : ℕ) = (1/2) sum_(i,j) m i m j (w i - w j)^(2 : ℕ)`
becomes a sign statement as soon as all the points share one real part: then every difference
`w i - w j` is purely imaginary, its square is `-(Im w i - Im w j)^(2 : ℕ)`, and the determinant is
**nonpositive**, vanishing exactly when all weighted points have one common imaginary part.

A positive measure on the real line has nonnegative Turán determinant, so this is the exact
obstruction: a configuration confined to a vertical line reveals its nonreality already in the
first `2 x 2` Hankel minor.  This is what separates the second Hankel minor from the plain total
mass, which cannot see nonreality at all once a real atom of large weight is present.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- Moments of a weighted finite complex configuration. -/
def configMoment (s : Finset ι) (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ s, (m i : ℂ) * w i ^ n

/-- Second Hankel (Turán) determinant of a weighted finite complex configuration. -/
def configTuranDeterminant (s : Finset ι) (m : ι → ℝ) (w : ι → ℂ) : ℂ :=
  configMoment s m w 0 * configMoment s m w 2 - configMoment s m w 1 ^ (2 : ℕ)

/-- **The variance identity.**  The Turán determinant is half the weighted sum of all pairwise
squared differences. -/
theorem configTuranDeterminant_eq_pair_sum (s : Finset ι) (m : ι → ℝ) (w : ι → ℂ) :
    (2 : ℂ) * configTuranDeterminant s m w =
      ∑ i ∈ s, ∑ j ∈ s, (m i : ℂ) * (m j : ℂ) * (w i - w j) ^ (2 : ℕ) := by
  have hexpand : ∀ i ∈ s, ∑ j ∈ s, (m i : ℂ) * (m j : ℂ) * (w i - w j) ^ (2 : ℕ) =
      (m i : ℂ) * w i ^ (2 : ℕ) * configMoment s m w 0 -
        2 * ((m i : ℂ) * w i) * configMoment s m w 1 +
        (m i : ℂ) * configMoment s m w 2 := by
    intro i _
    rw [configMoment, configMoment, configMoment, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul]
  have h0 : ∑ i ∈ s, (m i : ℂ) = configMoment s m w 0 := by
    rw [configMoment]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : ∑ i ∈ s, 2 * ((m i : ℂ) * w i) = 2 * configMoment s m w 1 := by
    rw [configMoment, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ s, (m i : ℂ) * w i ^ (2 : ℕ) = configMoment s m w 2 := rfl
  rw [h0, h1, h2, configTuranDeterminant]
  ring

/-- One pair term of the variance identity, for two points of a common vertical line. -/
private theorem re_pair_term {m₁ m₂ : ℝ} {u v : ℂ} (huv : u.re = v.re) :
    ((m₁ : ℂ) * (m₂ : ℂ) * (u - v) ^ (2 : ℕ)).re = -(m₁ * m₂ * (u.im - v.im) ^ (2 : ℕ)) := by
  have hdiff : u - v = (((u.im - v.im : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, huv]
  have hsq : (u - v) ^ (2 : ℕ) = (((-((u.im - v.im) ^ (2 : ℕ))) : ℝ) : ℂ) := by
    rw [hdiff, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hsq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- On a common vertical line the Turán determinant is a nonpositive sum of squares. -/
theorem two_mul_re_configTuranDeterminant {s : Finset ι} {m : ι → ℝ} {w : ι → ℂ}
    {A : ℝ} (hre : ∀ i ∈ s, (w i).re = A) :
    (2 : ℝ) * (configTuranDeterminant s m w).re =
      ∑ i ∈ s, ∑ j ∈ s, -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) := by
  have h := congrArg Complex.re (configTuranDeterminant_eq_pair_sum s m w)
  rw [Complex.mul_re] at h
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun j hj => re_pair_term (by rw [hre i hi, hre j hj])

/-- **A weighted configuration on a vertical line has nonpositive Turán determinant.** -/
theorem configTuranDeterminant_re_nonpos_of_common_re {s : Finset ι} {m : ι → ℝ} {w : ι → ℂ}
    {A : ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (hre : ∀ i ∈ s, (w i).re = A) :
    (configTuranDeterminant s m w).re ≤ 0 := by
  have hkey := two_mul_re_configTuranDeterminant (m := m) hre
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) ≤ 0 := by
    intro i hi j hj
    have hnn : 0 ≤ m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ) := by
      have hmm := mul_nonneg (hm i hi) (hm j hj)
      positivity
    linarith
  have hsum : ∑ i ∈ s, ∑ j ∈ s, -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) ≤ 0 :=
    Finset.sum_nonpos fun i hi => Finset.sum_nonpos fun j hj => hterm i hi j hj
  linarith

/-- **Strict version.**  Two positively weighted points of the vertical line at different heights
make the Turán determinant strictly negative, whatever the rest of the configuration weighs. -/
theorem configTuranDeterminant_re_neg_of_common_re {s : Finset ι} {m : ι → ℝ} {w : ι → ℂ}
    {A : ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (hre : ∀ i ∈ s, (w i).re = A)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hma : 0 < m a) (hmb : 0 < m b)
    (hab : (w a).im ≠ (w b).im) :
    (configTuranDeterminant s m w).re < 0 := by
  classical
  have hkey := two_mul_re_configTuranDeterminant (m := m) hre
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) ≤ 0 := by
    intro i hi j hj
    have hnn : 0 ≤ m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ) := by
      have hmm := mul_nonneg (hm i hi) (hm j hj)
      positivity
    linarith
  have hstrict : -(m a * m b * ((w a).im - (w b).im) ^ (2 : ℕ)) < 0 := by
    have hne : (w a).im - (w b).im ≠ 0 := sub_ne_zero.mpr hab
    have hsq : 0 < ((w a).im - (w b).im) ^ (2 : ℕ) := by positivity
    nlinarith [mul_pos hma hmb]
  have hrow : ∑ j ∈ s, -(m a * m j * ((w a).im - (w j).im) ^ (2 : ℕ)) < 0 := by
    have hsplit := Finset.add_sum_erase s
      (fun j => -(m a * m j * ((w a).im - (w j).im) ^ (2 : ℕ))) hb
    have hrest : ∑ j ∈ s.erase b, -(m a * m j * ((w a).im - (w j).im) ^ (2 : ℕ)) ≤ 0 :=
      Finset.sum_nonpos fun j hj => hterm a ha j (Finset.mem_of_mem_erase hj)
    rw [← hsplit]
    linarith
  have hsum : ∑ i ∈ s, ∑ j ∈ s, -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) < 0 := by
    have hsplit := Finset.add_sum_erase s
      (fun i => ∑ j ∈ s, -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ))) ha
    have hrest : ∑ i ∈ s.erase a, ∑ j ∈ s,
        -(m i * m j * ((w i).im - (w j).im) ^ (2 : ℕ)) ≤ 0 :=
      Finset.sum_nonpos fun i hi =>
        Finset.sum_nonpos fun j hj => hterm i (Finset.mem_of_mem_erase hi) j hj
    rw [← hsplit]
    linarith
  linarith

end GaloisForLFunctions.HTGeometry

end
