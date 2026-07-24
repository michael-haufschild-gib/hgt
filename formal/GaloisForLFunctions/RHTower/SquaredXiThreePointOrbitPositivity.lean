import Mathlib
import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationLocal

/-!
# Squared-Xi log-derivative three-point orbit positivity

For a conjugate pair of squared Xi zeros with centred data `t = γ² − δ²` and `q = 4δ²γ²`, the
contribution of the pair to the squared-centred logarithmic derivative is a positive multiple of

```
H_{t,q}(y) = (t + y) / ((t + y)² + q).
```

The diameter-two point triple `{0, 1, 4}` produces the orbit matrix

```
G = ⎡ a b c ⎤     a = H(0),  b = H(1),  c = H(4).
    ⎢ b a b ⎥
    ⎣ c b a ⎦
```

This file proves that on the exact critical-strip chamber `t > 2`, `0 ≤ q ≤ t + 1/4` the orbit
matrix is positive definite unconditionally, so in particular `det G > 0`: the specific triple
cannot furnish a finite-kernel disproof of RH.  The determinant reduces to the factorisation
`det G = (a − c)(a(a + c) − 2b²)`, and the second factor is `2 P(t,q)` over a positive denominator,
where every non-constant coefficient of `P(·, q)` is negative for `t > 2` and `64 P(t, t + 1/4)`
has strictly positive coefficients in `u = t − 2`.  Positive definiteness itself is discharged
through the reusable `HilbertMetric.threePointCorrelationMatrix_posDef_iff`, whose matrix
`!![d, p, r; p, d, q; r, q, d]` is exactly `G` at `d = a, p = q = b, r = c`.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The paired-zero log-derivative response `H_{t,q}(y) = (t + y)/((t + y)² + q)`. -/
def orbitH (t q y : ℝ) : ℝ := (t + y) / ((t + y) ^ 2 + q)

/-- The exact numerator polynomial `P(t,q)` obtained after clearing denominators in
`a(a + c) − 2b²`, from the source's equation (12). -/
def orbitP (t q : ℝ) : ℝ :=
  (t + 1) ^ 2 * t ^ 2 * (t + 4) * (5 * t + 2)
    + (t + 1) ^ 2 * t * (2 - 11 * t) * q
    - (17 * t ^ 2 + 36 * t + 16) * q ^ 2 - q ^ 3

/-- The diameter-two orbit matrix `G = !![a,b,c; b,a,b; c,b,a]`. -/
def orbitMatrix (t q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![orbitH t q 0, orbitH t q 1, orbitH t q 4;
     orbitH t q 1, orbitH t q 0, orbitH t q 1;
     orbitH t q 4, orbitH t q 1, orbitH t q 0]

/-- The orbit matrix is the corpus three-point correlation matrix at `d = a, p = q = b, r = c`. -/
theorem orbitMatrix_eq (t q : ℝ) :
    orbitMatrix t q
      = HilbertMetric.threePointCorrelationMatrix
          (orbitH t q 0) (orbitH t q 1) (orbitH t q 1) (orbitH t q 4) := rfl

/-- `H_{t,q}(y) > 0` on the chamber. -/
theorem orbitH_pos {t q y : ℝ} (ht : 2 < t) (hq0 : 0 ≤ q) (hy : 0 ≤ y) : 0 < orbitH t q y := by
  unfold orbitH
  apply div_pos
  · linarith
  · have h1 : 0 < t + y := by linarith
    have h2 : 0 < (t + y) ^ 2 := pow_pos h1 2
    linarith

/-- Positivity of the exact numerator polynomial on the chamber: monotone decrease in `q` down to
`q = t + 1/4`, where the `u = t − 2` expansion has strictly positive coefficients. -/
theorem orbitP_pos {t q : ℝ} (ht : 2 < t) (hq0 : 0 ≤ q) (hq : q ≤ t + 1 / 4) : 0 < orbitP t q := by
  set b : ℝ := t + 1 / 4 with hb
  have hmono : orbitP t q - orbitP t b
      = (b - q) *
          ((t + 1) ^ 2 * t * (11 * t - 2)
            + (17 * t ^ 2 + 36 * t + 16) * (q + b)
            + (q ^ 2 + q * b + b ^ 2)) := by
    unfold orbitP; rw [hb]; ring
  have hfac : 0 ≤ (b - q) *
      ((t + 1) ^ 2 * t * (11 * t - 2)
        + (17 * t ^ 2 + 36 * t + 16) * (q + b)
        + (q ^ 2 + q * b + b ^ 2)) := by
    apply mul_nonneg
    · rw [hb]; linarith
    · have hbpos : 0 < b := by rw [hb]; linarith
      have t1 : 0 ≤ (t + 1) ^ 2 * t * (11 * t - 2) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
      have t2 : 0 ≤ (17 * t ^ 2 + 36 * t + 16) * (q + b) :=
        mul_nonneg (by positivity) (by linarith)
      have t3 : 0 ≤ q ^ 2 + q * b + b ^ 2 :=
        add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hq0 hbpos.le)) (sq_nonneg _)
      linarith
  have hge : orbitP t b ≤ orbitP t q := by linarith
  have hu : 0 < t - 2 := by linarith
  have hbase : 64 * orbitP t b
      = 320 * (t - 2) ^ 6 + 5184 * (t - 2) ^ 5 + 33744 * (t - 2) ^ 4 + 112544 * (t - 2) ^ 3
        + 201564 * (t - 2) ^ 2 + 181620 * (t - 2) + 62775 := by
    unfold orbitP; rw [hb]; ring
  have hbasepos : 0 < orbitP t b := by
    nlinarith [pow_pos hu 6, pow_pos hu 5, pow_pos hu 4, pow_pos hu 3, pow_pos hu 2, hu]
  linarith

/-- Denominator positivity. -/
private theorem orbit_den_pos {t : ℝ} (ht : 2 < t) {q : ℝ} (hq0 : 0 ≤ q) (y : ℝ) (hy : 0 ≤ y) :
    0 < (t + y) ^ 2 + q := by
  have h1 : 0 < t + y := by linarith
  have h2 : 0 < (t + y) ^ 2 := pow_pos h1 2
  linarith

/-- **Squared-Xi three-point orbit positivity.**  On the exact critical-strip chamber the orbit
matrix is positive definite. -/
theorem orbitMatrix_posDef {t q : ℝ} (ht : 2 < t) (hq0 : 0 ≤ q) (hq : q ≤ t + 1 / 4) :
    Matrix.PosDef (orbitMatrix t q) := by
  -- denominators
  have hd0 : 0 < t ^ 2 + q := by
    have := orbit_den_pos ht hq0 0 le_rfl; simpa using this
  have hd1 : 0 < (t + 1) ^ 2 + q := orbit_den_pos ht hq0 1 (by norm_num)
  have hd4 : 0 < (t + 4) ^ 2 + q := orbit_den_pos ht hq0 4 (by norm_num)
  -- entrywise positivity and ordering
  have ha_pos : 0 < orbitH t q 0 := orbitH_pos ht hq0 le_rfl
  have hb_nonneg : 0 ≤ orbitH t q 1 := (orbitH_pos ht hq0 (by norm_num)).le
  have hab : orbitH t q 1 < orbitH t q 0 := by
    have key : orbitH t q 0 - orbitH t q 1
        = (t * (t + 1) - q) / ((t ^ 2 + q) * ((t + 1) ^ 2 + q)) := by
      unfold orbitH; simp only [add_zero]; field_simp; ring
    have hnum : 0 < t * (t + 1) - q := by nlinarith [hq, ht]
    have : 0 < orbitH t q 0 - orbitH t q 1 := by
      rw [key]; exact div_pos hnum (mul_pos hd0 hd1)
    linarith
  have hca : orbitH t q 4 < orbitH t q 0 := by
    have key : orbitH t q 0 - orbitH t q 4
        = (4 * (t ^ 2 + 4 * t - q)) / ((t ^ 2 + q) * ((t + 4) ^ 2 + q)) := by
      unfold orbitH; simp only [add_zero]; field_simp; ring
    have hnum : 0 < 4 * (t ^ 2 + 4 * t - q) := by nlinarith [hq, ht]
    have : 0 < orbitH t q 0 - orbitH t q 4 := by
      rw [key]; exact div_pos hnum (mul_pos hd0 hd4)
    linarith
  -- second determinant factor via the exact P-identity
  have hDen : 0 < (t ^ 2 + q) ^ 2 * ((t + 1) ^ 2 + q) ^ 2 * ((t + 4) ^ 2 + q) :=
    mul_pos (mul_pos (pow_pos hd0 2) (pow_pos hd1 2)) hd4
  have hcrux : (orbitH t q 0 * (orbitH t q 0 + orbitH t q 4) - 2 * (orbitH t q 1) ^ 2)
      * ((t ^ 2 + q) ^ 2 * ((t + 1) ^ 2 + q) ^ 2 * ((t + 4) ^ 2 + q)) = 2 * orbitP t q := by
    unfold orbitH orbitP; simp only [add_zero]; field_simp; ring
  have hfactor : 0 < orbitH t q 0 * (orbitH t q 0 + orbitH t q 4) - 2 * (orbitH t q 1) ^ 2 := by
    have hP : 0 < orbitP t q := orbitP_pos ht hq0 hq
    have heq : orbitH t q 0 * (orbitH t q 0 + orbitH t q 4) - 2 * (orbitH t q 1) ^ 2
        = 2 * orbitP t q / ((t ^ 2 + q) ^ 2 * ((t + 1) ^ 2 + q) ^ 2 * ((t + 4) ^ 2 + q)) := by
      rw [eq_div_iff hDen.ne']; exact hcrux
    rw [heq]; exact div_pos (by linarith) hDen
  -- assemble the determinant and apply the reusable positive-definiteness criterion
  rw [orbitMatrix_eq, HilbertMetric.threePointCorrelationMatrix_posDef_iff ha_pos hb_nonneg hab]
  have hdetfac : HilbertMetric.threePointCorrelationDeterminant
      (orbitH t q 0) (orbitH t q 1) (orbitH t q 1) (orbitH t q 4)
      = (orbitH t q 0 - orbitH t q 4)
          * (orbitH t q 0 * (orbitH t q 0 + orbitH t q 4) - 2 * (orbitH t q 1) ^ 2) := by
    unfold HilbertMetric.threePointCorrelationDeterminant; ring
  rw [hdetfac]
  exact mul_pos (by linarith) hfactor

/-- The card's headline consequence: the orbit determinant is strictly positive, so the triple
cannot disprove RH. -/
theorem orbitMatrix_det_pos {t q : ℝ} (ht : 2 < t) (hq0 : 0 ≤ q) (hq : q ≤ t + 1 / 4) :
    0 < (orbitMatrix t q).det :=
  (orbitMatrix_posDef ht hq0 hq).det_pos

end

end RHTower
