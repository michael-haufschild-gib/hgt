import GaloisForLFunctions.HTGeometry.HausdorffDifferenceInertia
import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite

/-!
# A vanishing-weight outlier above the moving apex

Perturbing the Gauss quadrature of a positive moment functional by one small atom placed just above
the moving apex changes no fixed moment in the limit — every fixed moment of the perturbed
functional converges to the original one as the atom's weight vanishes and its position tends to
the apex — while the first Hausdorff-difference form of the perturbed functional is already
negative, witnessed by the orthogonal polynomial itself, which annihilates every quadrature node
and not the outlier.

Fixed-degree moment recession therefore cannot see an endpoint leak: the leak lives in a weight
that vanishes and a position that converges, exactly the two data a moment limit forgets.
-/

open Polynomial

noncomputable section

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The atomic pairing of a Gauss quadrature perturbed by one outlier atom of weight `ε` at `t`. -/
def outlierPairing (s : ℕ → ℝ) (n : ℕ) (ε t : ℝ) (p : Polynomial ℝ) : ℝ :=
  (1 - ε) * (∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x) + ε * p.eval t

/-- The moment sequence of the perturbed pairing. -/
def outlierMoments (s : ℕ → ℝ) (n : ℕ) (ε t : ℝ) (k : ℕ) : ℝ :=
  outlierPairing s n ε t (Polynomial.X ^ k)

/-- **(SAHI.25) The perturbed moments are the convex combination, up to the exactness degree.** -/
theorem outlierMoments_eq (h : PositiveMomentForm s) (n : ℕ) (ε t : ℝ) {k : ℕ}
    (hk : k ≤ 2 * n + 1) :
    outlierMoments s n ε t k = (1 - ε) * s k + ε * t ^ k := by
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hgauss := momentFunctional_eq_gaussSum h n (Polynomial.X ^ k) hdeg
  rw [momentFunctional_X_pow] at hgauss
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hgauss
  rw [outlierMoments, outlierPairing]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hgauss]

/-- **(SAHI.26) The perturbed pairing has a negative first Hausdorff difference.**  The orthogonal
polynomial annihilates every quadrature node, so only the outlier atom contributes, with the sign
of `1 - y t`. -/
theorem outlierPairing_hausdorff_neg (n : ℕ) {ε t y : ℝ}
    (hε : 0 < ε) (ht : 1 < y * t) (htne : (monicOrtho s (n + 1)).eval t ≠ 0) :
    outlierPairing s n ε t
      ((1 - Polynomial.C y * Polynomial.X) * (monicOrtho s (n + 1)) ^ 2) < 0 := by
  have hnodes : ∀ x ∈ gaussNodes s n,
      christoffel s n x *
        ((1 - Polynomial.C y * Polynomial.X) * (monicOrtho s (n + 1)) ^ 2).eval x = 0 := by
    intro x hx
    have hroot : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).1 hx
    simp [hroot]
  have hsum : (∑ x ∈ gaussNodes s n, christoffel s n x *
      ((1 - Polynomial.C y * Polynomial.X) * (monicOrtho s (n + 1)) ^ 2).eval x) = 0 :=
    Finset.sum_eq_zero hnodes
  rw [outlierPairing, hsum, mul_zero, zero_add]
  have heval : ((1 - Polynomial.C y * Polynomial.X) * (monicOrtho s (n + 1)) ^ 2).eval t
      = (1 - y * t) * (monicOrtho s (n + 1)).eval t ^ 2 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
  rw [heval]
  have hsq : 0 < (monicOrtho s (n + 1)).eval t ^ 2 := by positivity
  have hneg : 1 - y * t < 0 := by linarith
  have hprod : (1 - y * t) * (monicOrtho s (n + 1)).eval t ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hneg hsq
  exact mul_neg_of_pos_of_neg hε hprod

/-! ## Fixed-degree moment recession -/

open Filter Topology

/-- **Fixed-degree moment convergence of the perturbed family.**  As the outlier's weight vanishes
and its position tends to the apex, every fixed moment converges to the unperturbed one. -/
theorem tendsto_outlierMoments (h : PositiveMomentForm s) (k : ℕ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {E T : ℕ → ℝ} (hE : Tendsto E atTop (nhds 0)) (hT : Tendsto T atTop (nhds 1)) :
    Tendsto (fun j => outlierMoments s (N j) (E j) (T j) k) atTop (nhds (s k)) := by
  have heven : ∀ᶠ j in atTop, k ≤ 2 * N j + 1 := by
    have hev : ∀ᶠ j in atTop, k ≤ N j := hN.eventually_ge_atTop k
    filter_upwards [hev] with j hj
    omega
  have hform : ∀ᶠ j in atTop,
      outlierMoments s (N j) (E j) (T j) k = (1 - E j) * s k + E j * (T j) ^ k := by
    filter_upwards [heven] with j hj
    exact outlierMoments_eq h (N j) (E j) (T j) hj
  have hlim : Tendsto (fun j => (1 - E j) * s k + E j * (T j) ^ k) atTop
      (nhds ((1 - 0) * s k + 0 * (1 : ℝ) ^ k)) := by
    refine Tendsto.add (Tendsto.mul ?_ tendsto_const_nhds) (Tendsto.mul hE (hT.pow k))
    simpa using tendsto_const_nhds.sub hE
  rw [show ((1 - 0) * s k + 0 * (1 : ℝ) ^ k) = s k by ring] at hlim
  exact hlim.congr' (hform.mono fun j hj => hj.symm)


/-! ## The arcsine instance -/

/-- **(SAHI.25) The arcsine countermodel's moments recede to the arcsine moments.**  Every fixed
moment of the perturbed family converges to the corresponding arcsine moment, so every fixed Hankel
block has the positive-definite arcsine limit. -/
theorem tendsto_arcsine_outlierMoments (k : ℕ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {E T : ℕ → ℝ} (hE : Tendsto E atTop (nhds 0)) (hT : Tendsto T atTop (nhds 1)) :
    Tendsto (fun j =>
        outlierMoments GaloisForLFunctions.HTGeometry.normalizedCentralBinom (N j) (E j) (T j) k)
      atTop (nhds (GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) :=
  tendsto_outlierMoments GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm
    k hN hE hT

end HTGeometry

end
