import GaloisForLFunctions.RHTower.PrimeArchBernsteinPencil
import GaloisForLFunctions.HTGeometry.AntidiagonalRegrouping
import GaloisForLFunctions.HTGeometry.GutzmerPowerSeries
import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity

/-!
# The Bernstein Möbius-pullback law and its double Gutzmer susceptibility

For a moment sequence `m : ℕ → ℝ` the degree-`n` Bernstein pencil is

```
P_n(w) = ∑_i L_m(C(n,i) X^i (1-X)^{n-i}) w^i.
```

Two exact laws are proved here.

* **Binomial form.**  `P_n(w) = ∑_{k ≤ n} C(n,k) m_k (w-1)^k`, because
  `∑_i w^i B_{n,i}(X) = (1 + (w-1)X)^n`.
* **Möbius pullback.**  Wherever the moment germ `M(v) = ∑_k m_k v^k` converges absolutely at
  `v = s(w-1)/(1-s)` and `|s| < 1`,

  ```
  ∑_n P_n(w) s^n = (1-s)^{-1} M( s(w-1)/(1-s) ).
  ```

  The proof is the negative-binomial identity `∑_{n ≥ k} C(n,k) s^n = s^k/(1-s)^{k+1}` applied
  inside an absolutely convergent double sum, regrouped by antidiagonals.

The purity susceptibility `χ(t) = ∑_n Π_n t^n`, `Π_n = ∑_i b_{n,i}²`, is then the two-torus
Gutzmer norm of that single pullback: finite Parseval in the `w` circle gives `Π_n`, and Gutzmer in
the degree variable gives `χ(r²)`.

Finally the atom pole surface `1 - s(1-u+uw)` first reaches the `w` circle exactly at
`|s| = (|1-u|+|u|)^{-1}`, so the reflected susceptibility pinch sits at `t = (|1-u|+|u|)^{-2}`.
-/

open Polynomial Finset
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

open HTGeometry GaloisForLFunctions.HTGeometry

/-! ### The binomial form of the Bernstein pencil -/

theorem bernsteinPolynomial_map (n i : ℕ) :
    (bernsteinPolynomial ℝ n i).map (algebraMap ℝ ℂ) = bernsteinPolynomial ℂ n i := by
  simp [bernsteinPolynomial, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_natCast]

/-- **The Bernstein generating polynomial.**  `∑_i w^i B_{n,i}(X) = (1 + (w-1)X)^n`. -/
theorem bernstein_smul_sum (n : ℕ) (w : ℂ) :
    ∑ i ∈ Finset.range (n + 1), (Polynomial.C (w ^ i)) * (bernsteinPolynomial ℂ n i)
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C ((n.choose k : ℂ) * (w - 1) ^ k) * X ^ k := by
  have h1 : ((Polynomial.C w * X) + (1 - X)) ^ n
      = ∑ i ∈ Finset.range (n + 1), (Polynomial.C (w ^ i)) * (bernsteinPolynomial ℂ n i) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bernsteinPolynomial, mul_pow, ← Polynomial.C_pow]
    push_cast
    ring
  have h2 : ((Polynomial.C (w - 1) * X) + 1) ^ n
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C ((n.choose k : ℂ) * (w - 1) ^ k) * X ^ k := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← Polynomial.C_pow, one_pow, Polynomial.C_mul]
    simp only [Polynomial.C_eq_natCast]
    ring
  rw [← h1, ← h2]
  congr 1
  simp only [map_sub, map_one]
  ring

theorem natDegree_bernsteinPolynomial_le {R : Type*} [CommRing R] {n i : ℕ} (hi : i ≤ n) :
    (bernsteinPolynomial R n i).natDegree ≤ n := by
  have h : bernsteinPolynomial R n i
      = (Polynomial.C ((n.choose i : R))) * X ^ i * (1 - X) ^ (n - i) := by
    rw [bernsteinPolynomial]
    simp
  rw [h]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have hXle : (X : R[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
  have hX : (X ^ i : R[X]).natDegree ≤ i := by
    refine le_trans Polynomial.natDegree_pow_le ?_
    calc i * (X : R[X]).natDegree ≤ i * 1 := Nat.mul_le_mul_left i hXle
      _ = i := by ring
  have h1 : (Polynomial.C ((n.choose i : R)) * X ^ i).natDegree ≤ i := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    simpa using hX
  have h2 : ((1 - X : R[X]) ^ (n - i)).natDegree ≤ n - i := by
    refine le_trans (Polynomial.natDegree_pow_le) ?_
    have hone : (1 - X : R[X]).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simpa using hXle
    calc (n - i) * (1 - X : R[X]).natDegree ≤ (n - i) * 1 :=
          Nat.mul_le_mul_left _ hone
      _ = n - i := by ring
  omega

theorem coeff_bernstein_sum (n k : ℕ) (w : ℂ) :
    ∑ i ∈ Finset.range (n + 1), w ^ i * (bernsteinPolynomial ℂ n i).coeff k
      = if k ∈ Finset.range (n + 1) then (n.choose k : ℂ) * (w - 1) ^ k else 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff k) (bernstein_smul_sum n w)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
  rw [h]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) k (fun j => (n.choose j : ℂ) * (w - 1) ^ j)]

theorem momentFunctional_eq_range_sum (m : ℕ → ℝ) {p : Polynomial ℝ} {n : ℕ}
    (hp : p.natDegree ≤ n) :
    momentFunctional m p = ∑ k ∈ Finset.range (n + 1), p.coeff k * m k := by
  rw [momentFunctional_eq_support_sum]
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_range]
    have := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    omega
  · intro k _ hk
    rw [Polynomial.notMem_support_iff.mp hk]
    ring

/-- **(4)** The Bernstein pencil in binomial form. -/
theorem bernsteinCoefficientTransform_eq_binomial (m : ℕ → ℝ) (n : ℕ) (w : ℂ) :
    bernsteinCoefficientTransform m n w
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (m k : ℂ) * (w - 1) ^ k := by
  have hb : ∀ i ∈ Finset.range (n + 1), (bernsteinCoefficient m n i : ℂ) * w ^ i
      = ∑ k ∈ Finset.range (n + 1),
          (w ^ i * (bernsteinPolynomial ℂ n i).coeff k) * (m k : ℂ) := by
    intro i hi
    rw [bernsteinCoefficient, momentFunctional_eq_range_sum m
      (natDegree_bernsteinPolynomial_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmap : (bernsteinPolynomial ℂ n i).coeff k
        = (((bernsteinPolynomial ℝ n i).coeff k : ℝ) : ℂ) := by
      rw [← bernsteinPolynomial_map n i, Polynomial.coeff_map]
      simp
    rw [hmap]
    ring
  rw [bernsteinCoefficientTransform, Finset.sum_congr rfl hb, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_mul, coeff_bernstein_sum n k w, if_pos hk]
  ring

/-! ### The Möbius pullback of the moment germ -/

/-- The ordinary moment germ `M(v) = ∑_k m_k v^k`. -/
def bernsteinMomentGerm (m : ℕ → ℝ) (v : ℂ) : ℂ := ∑' k : ℕ, (m k : ℂ) * v ^ k

/-- The double-indexed family whose antidiagonal sums are the Bernstein pencils. -/
def pencilFamily (m : ℕ → ℝ) (s w : ℂ) (p : ℕ × ℕ) : ℂ :=
  ((p.1 + p.2).choose p.1 : ℂ) * (m p.1 : ℂ) * (w - 1) ^ p.1 * s ^ (p.1 + p.2)

theorem norm_pencilFamily (m : ℕ → ℝ) (s w : ℂ) (p : ℕ × ℕ) :
    ‖pencilFamily m s w p‖
      = ((p.1 + p.2).choose p.1 : ℝ) * |m p.1| * ‖w - 1‖ ^ p.1 * ‖s‖ ^ (p.1 + p.2) := by
  simp [pencilFamily, Real.norm_eq_abs]

theorem hasSum_pencilFamily_fiber (m : ℕ → ℝ) {s w : ℂ} (hs : ‖s‖ < 1) (i : ℕ) :
    HasSum (fun j : ℕ => pencilFamily m s w (i, j))
      ((m i : ℂ) * (w - 1) ^ i * s ^ i * (1 / (1 - s) ^ (i + 1))) := by
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) i hs
  have heq : (fun j : ℕ => pencilFamily m s w (i, j))
      = fun j : ℕ => ((m i : ℂ) * (w - 1) ^ i * s ^ i) * (((j + i).choose i : ℂ) * s ^ j) := by
    funext j
    simp only [pencilFamily]
    rw [show i + j = j + i from Nat.add_comm i j, pow_add]
    ring
  rw [heq]
  exact hgeo.mul_left _

theorem hasSum_norm_pencilFamily_fiber (m : ℕ → ℝ) {s w : ℂ} (hs : ‖s‖ < 1) (i : ℕ) :
    HasSum (fun j : ℕ => ‖pencilFamily m s w (i, j)‖)
      (|m i| * ‖w - 1‖ ^ i * ‖s‖ ^ i * (1 / (1 - ‖s‖) ^ (i + 1))) := by
  have hsr : ‖(‖s‖ : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg s)]
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) i hsr
  have heq : (fun j : ℕ => ‖pencilFamily m s w (i, j)‖)
      = fun j : ℕ => (|m i| * ‖w - 1‖ ^ i * ‖s‖ ^ i) * (((j + i).choose i : ℝ) * ‖s‖ ^ j) := by
    funext j
    rw [norm_pencilFamily]
    simp only
    rw [show i + j = j + i from Nat.add_comm i j, pow_add]
    ring
  rw [heq]
  exact hgeo.mul_left _

theorem summable_norm_pencilFamily (m : ℕ → ℝ) {s w : ℂ} (hs : ‖s‖ < 1)
    (hM : Summable fun k : ℕ => |m k| * (‖s‖ * ‖w - 1‖ / (1 - ‖s‖)) ^ k) :
    Summable fun p : ℕ × ℕ => ‖pencilFamily m s w p‖ := by
  have hpos : (0 : ℝ) < 1 - ‖s‖ := by linarith
  rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
  refine ⟨fun i => (hasSum_norm_pencilFamily_fiber m hs i).summable, ?_⟩
  refine ((hM.mul_left (1 / (1 - ‖s‖))).congr fun i => ?_)
  rw [(hasSum_norm_pencilFamily_fiber m hs i).tsum_eq]
  rw [div_pow, mul_pow]
  field_simp
  ring

theorem summable_pencilFamily (m : ℕ → ℝ) {s w : ℂ} (hs : ‖s‖ < 1)
    (hM : Summable fun k : ℕ => |m k| * (‖s‖ * ‖w - 1‖ / (1 - ‖s‖)) ^ k) :
    Summable (pencilFamily m s w) :=
  Summable.of_norm (summable_norm_pencilFamily m hs hM)

theorem sum_antidiagonal_pencilFamily (m : ℕ → ℝ) (s w : ℂ) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, pencilFamily m s w p
      = bernsteinCoefficientTransform m n w * s ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    bernsteinCoefficientTransform_eq_binomial, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [pencilFamily]
  rw [Nat.add_sub_cancel' hk']

/-- **(3) The Möbius-pullback law.**  The full degree-generating function of the Bernstein pencils
is a single Möbius pullback of the ordinary moment germ. -/
theorem tsum_bernsteinPencil_eq_mobiusPullback (m : ℕ → ℝ) {s w : ℂ} (hs : ‖s‖ < 1)
    (hM : Summable fun k : ℕ => |m k| * (‖s‖ * ‖w - 1‖ / (1 - ‖s‖)) ^ k) :
    ∑' n : ℕ, bernsteinCoefficientTransform m n w * s ^ n
      = (1 - s)⁻¹ * bernsteinMomentGerm m (s * (w - 1) / (1 - s)) := by
  have hsum := summable_pencilFamily m hs hM
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro hcon
    have : s = 1 := by linear_combination -hcon
    rw [this] at hs
    simp at hs
  have h1 : ∑' n : ℕ, bernsteinCoefficientTransform m n w * s ^ n
      = ∑' p : ℕ × ℕ, pencilFamily m s w p := by
    rw [← tsum_sum_antidiagonal hsum]
    exact (tsum_congr fun n => sum_antidiagonal_pencilFamily m s w n).symm
  have h2 : ∑' p : ℕ × ℕ, pencilFamily m s w p
      = ∑' i : ℕ, (m i : ℂ) * (w - 1) ^ i * s ^ i * (1 / (1 - s) ^ (i + 1)) := by
    rw [hsum.tsum_prod]
    exact tsum_congr fun i => (hasSum_pencilFamily_fiber m hs i).tsum_eq
  rw [h1, h2, bernsteinMomentGerm, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [div_pow, mul_pow]
  field_simp
  ring

/-! ### The atom pole surface and the reflected pinch -/

/-- `B_+(u) = |1-u| + |u|`, the maximum of `|1-u+uw|` on the `w` circle. -/
def poleSurfaceRadius (u : ℂ) : ℝ := ‖1 - u‖ + ‖u‖

theorem norm_affine_le_poleSurfaceRadius (u : ℂ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖1 - u + u * w‖ ≤ poleSurfaceRadius u := by
  refine le_trans (norm_add_le _ _) ?_
  rw [poleSurfaceRadius, norm_mul, hw, mul_one]

/-- **(12)** The maximum is attained. -/
theorem exists_norm_affine_eq_poleSurfaceRadius (u : ℂ) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ‖1 - u + u * w‖ = poleSurfaceRadius u := by
  rcases eq_or_ne u 0 with hu | hu
  · exact ⟨1, by simp, by simp [hu, poleSurfaceRadius]⟩
  rcases eq_or_ne (1 - u) 0 with ha | ha
  · refine ⟨1, by simp, ?_⟩
    rw [ha, poleSurfaceRadius, ha]
    simp
  refine ⟨(1 - u) * (‖u‖ : ℂ) / ((‖1 - u‖ : ℂ) * u), ?_, ?_⟩
  · rw [norm_div, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [mul_comm ‖1 - u‖ ‖u‖]
    exact div_self (by positivity)
  · have hane : ((‖1 - u‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr ha)
    have hval : 1 - u + u * ((1 - u) * (‖u‖ : ℂ) / ((‖1 - u‖ : ℂ) * u))
        = (1 - u) * (((‖1 - u‖ + ‖u‖ : ℝ) : ℂ) / (‖1 - u‖ : ℂ)) := by
      field_simp
      push_cast
      ring
    rw [hval, norm_mul, poleSurfaceRadius]
    rw [norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖1 - u‖ + ‖u‖),
      abs_of_nonneg (norm_nonneg (1 - u))]
    field_simp

/-- **(13)** The pole surface stays off the `w` circle strictly inside the reflected radius. -/
theorem pole_ne_zero_of_norm_lt (u : ℂ) {s : ℂ} (hs : ‖s‖ * poleSurfaceRadius u < 1)
    {w : ℂ} (hw : ‖w‖ = 1) : 1 - s * (1 - u + u * w) ≠ 0 := by
  intro hcon
  have h1 : s * (1 - u + u * w) = 1 := by linear_combination -hcon
  have h2 : ‖s‖ * ‖1 - u + u * w‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  have h3 : ‖s‖ * ‖1 - u + u * w‖ ≤ ‖s‖ * poleSurfaceRadius u :=
    mul_le_mul_of_nonneg_left (norm_affine_le_poleSurfaceRadius u hw) (norm_nonneg _)
  linarith

/-- **(13)** and the pole surface does reach the circle at the reflected radius. -/
theorem exists_pole_at_poleSurfaceRadius (u : ℂ) (hu : 0 < poleSurfaceRadius u) :
    ∃ s w : ℂ, ‖s‖ = (poleSurfaceRadius u)⁻¹ ∧ ‖w‖ = 1 ∧ 1 - s * (1 - u + u * w) = 0 := by
  obtain ⟨w, hw, hval⟩ := exists_norm_affine_eq_poleSurfaceRadius u
  have hne : (1 - u + u * w) ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hval
    linarith
  refine ⟨(1 - u + u * w)⁻¹, w, ?_, hw, ?_⟩
  · rw [norm_inv, hval]
  · rw [inv_mul_cancel₀ hne, sub_self]

/-! ### Finite Parseval on the `w` circle -/

/-- The degree-`n` pencil coefficient sequence, extended by zero. -/
def pencilCoeff (m : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℂ :=
  if i ∈ Finset.range (n + 1) then (bernsteinCoefficient m n i : ℂ) else 0

theorem summable_pencilCoeff (m : ℕ → ℝ) (n : ℕ) (ρ : ℝ) :
    Summable fun i => ‖pencilCoeff m n i‖ * ρ ^ i := by
  refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun i hi => ?_
  rw [pencilCoeff, if_neg hi]
  simp

theorem powerSeriesSum_pencilCoeff (m : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    GaloisForLFunctions.HTGeometry.powerSeriesSum (pencilCoeff m n) z
      = bernsteinCoefficientTransform m n z := by
  rw [GaloisForLFunctions.HTGeometry.powerSeriesSum, bernsteinCoefficientTransform,
    tsum_eq_sum (s := Finset.range (n + 1)) (fun i hi => by rw [pencilCoeff, if_neg hi]; ring)]
  exact Finset.sum_congr rfl fun i hi => by rw [pencilCoeff, if_pos hi]

theorem tsum_normSq_pencilCoeff (m : ℕ → ℝ) (n : ℕ) :
    ∑' i : ℕ, ‖pencilCoeff m n i‖ ^ 2 * (1 : ℝ) ^ (2 * i) = bernsteinCoefficientPurity m n := by
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun i hi => by rw [pencilCoeff, if_neg hi]; simp)]
  rw [bernsteinCoefficientPurity]
  exact Finset.sum_congr rfl fun i hi => by
    rw [pencilCoeff, if_pos hi]
    simp [sq_abs]

/-- **(7)** Finite Parseval: the coefficient purity is the circle mean of the pencil. -/
theorem bernsteinCoefficientPurity_eq_circleMean (m : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientPurity m n
      = (2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi),
          ‖bernsteinCoefficientTransform m n (circleMap 0 1 φ)‖ ^ 2 := by
  have hg := GaloisForLFunctions.HTGeometry.hasSum_gutzmer_of_summable_norm
    (a := pencilCoeff m n) (r := 1) (ρ := 2) (by norm_num) (by norm_num)
    (summable_pencilCoeff m n 2)
  have hrw : ∀ φ : ℝ, GaloisForLFunctions.HTGeometry.powerSeriesSum
      (pencilCoeff m n) (circleMap 0 1 φ)
      = bernsteinCoefficientTransform m n (circleMap 0 1 φ) :=
    fun φ => powerSeriesSum_pencilCoeff m n _
  simp only [hrw] at hg
  rw [← hg.tsum_eq, tsum_normSq_pencilCoeff]

/-! ### Uniform coefficient bounds on the `w` circle -/

/-- The crude coefficient majorant `B_n = ∑_{k ≤ n} C(n,k)|m_k| 2^k`. -/
def pencilBound (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * |m k| * 2 ^ k

theorem sum_antidiagonal_norm_pencilFamily (m : ℕ → ℝ) (s w : ℂ) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖pencilFamily m s w p‖
      = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * |m k| * ‖w - 1‖ ^ k) * ‖s‖ ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [norm_pencilFamily]
  simp only
  rw [Nat.add_sub_cancel' hk']

theorem summable_pencilBound (m : ℕ → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hM : Summable fun k : ℕ => |m k| * (2 * ρ / (1 - ρ)) ^ k) :
    Summable fun n : ℕ => pencilBound m n * ρ ^ n := by
  have hsnorm : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hwnorm : ‖(3 : ℂ) - 1‖ = 2 := by norm_num
  have hlt : ‖(ρ : ℂ)‖ < 1 := by rw [hsnorm]; exact hρ1
  have hM' : Summable fun k : ℕ => |m k| * (‖(ρ : ℂ)‖ * ‖(3 : ℂ) - 1‖ / (1 - ‖(ρ : ℂ)‖)) ^ k := by
    refine hM.congr fun k => ?_
    rw [hsnorm, hwnorm]
    ring_nf
  have hsum := GaloisForLFunctions.HTGeometry.summable_sum_antidiagonal
    (summable_norm_pencilFamily m hlt hM')
  refine hsum.congr fun n => ?_
  rw [sum_antidiagonal_norm_pencilFamily, hsnorm, hwnorm, pencilBound]

theorem norm_bernsteinCoefficientTransform_le_pencilBound (m : ℕ → ℝ) (n : ℕ) {w : ℂ}
    (hw : ‖w‖ = 1) : ‖bernsteinCoefficientTransform m n w‖ ≤ pencilBound m n := by
  rw [bernsteinCoefficientTransform_eq_binomial, pencilBound]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have hw1 : ‖w - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hw, norm_one]
    norm_num
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  gcongr

theorem summable_norm_bernsteinCoefficientTransform (m : ℕ → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hM : Summable fun k : ℕ => |m k| * (2 * ρ / (1 - ρ)) ^ k) {w : ℂ}
    (hw : ‖w‖ = 1) :
    Summable fun n : ℕ => ‖bernsteinCoefficientTransform m n w‖ * ρ ^ n := by
  refine (summable_pencilBound m hρ0 hρ1 hM).of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_)
  exact mul_le_mul_of_nonneg_right
    (norm_bernsteinCoefficientTransform_le_pencilBound m n hw) (by positivity)

/-! ### The double Gutzmer susceptibility -/

/-- The two-variable Möbius-pullback generating function `B(s,w) = ∑_n P_n(w) s^n`. -/
def bernsteinPencilGenerating (m : ℕ → ℝ) (s w : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.powerSeriesSum (fun n => bernsteinCoefficientTransform m n w) s

/-- **Inner Gutzmer**, in the degree variable. -/
theorem hasSum_inner_gutzmer (m : ℕ → ℝ) {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r < ρ) (hρ1 : ρ < 1)
    (hM : Summable fun k : ℕ => |m k| * (2 * ρ / (1 - ρ)) ^ k) {w : ℂ} (hw : ‖w‖ = 1) :
    HasSum (fun n => ‖bernsteinCoefficientTransform m n w‖ ^ 2 * r ^ (2 * n))
      ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖bernsteinPencilGenerating m (circleMap 0 r θ) w‖ ^ 2) :=
  GaloisForLFunctions.HTGeometry.hasSum_gutzmer_of_summable_norm hr0 hrρ
    (summable_norm_bernsteinCoefficientTransform m (le_trans hr0 hrρ.le) hρ1 hM hw)

theorem continuous_normSq_pencil (m : ℕ → ℝ) (n : ℕ) :
    Continuous fun φ : ℝ => ‖bernsteinCoefficientTransform m n (circleMap 0 1 φ)‖ ^ 2 := by
  have hc : Continuous fun φ : ℝ => bernsteinCoefficientTransform m n (circleMap 0 1 φ) := by
    rw [show (fun φ : ℝ => bernsteinCoefficientTransform m n (circleMap 0 1 φ))
        = fun φ : ℝ => ∑ i ∈ Finset.range (n + 1),
          (bernsteinCoefficient m n i : ℂ) * (circleMap 0 1 φ) ^ i from rfl]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_circleMap 0 1).pow i)
  exact hc.norm.pow 2

theorem circleMean_le_of_le {g : ℝ → ℝ} (hg : IntervalIntegrable g MeasureTheory.volume 0
    (2 * Real.pi)) {C : ℝ} (hC : ∀ θ, g θ ≤ C) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), g θ ≤ C := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmono : (∫ θ in (0:ℝ)..(2 * Real.pi), g θ) ≤ ∫ _θ in (0:ℝ)..(2 * Real.pi), C :=
    intervalIntegral.integral_mono_on hpi.le hg (intervalIntegrable_const)
      (fun x _ => hC x)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  calc (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), g θ
      ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * C) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = C := by field_simp

theorem bernsteinCoefficientPurity_le_sq (m : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientPurity m n ≤ (pencilBound m n) ^ 2 := by
  rw [bernsteinCoefficientPurity_eq_circleMean]
  refine circleMean_le_of_le ((continuous_normSq_pencil m n).intervalIntegrable _ _) fun θ => ?_
  have hcirc : ‖circleMap 0 1 θ‖ = 1 := by
    rw [norm_circleMap_zero]; norm_num
  have h := norm_bernsteinCoefficientTransform_le_pencilBound m n hcirc
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem summable_purity_mul_pow (m : ℕ → ℝ) {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r < ρ) (hρ1 : ρ < 1)
    (hM : Summable fun k : ℕ => |m k| * (2 * ρ / (1 - ρ)) ^ k) :
    Summable fun n : ℕ => bernsteinCoefficientPurity m n * r ^ (2 * n) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hr0 hrρ
  have hBsum := summable_pencilBound m hρ0.le hρ1 hM
  set C : ℝ := ∑' n : ℕ, pencilBound m n * ρ ^ n with hC
  have hnn : ∀ n : ℕ, 0 ≤ pencilBound m n * ρ ^ n := by
    intro n
    have : 0 ≤ pencilBound m n := by
      refine Finset.sum_nonneg fun k _ => by positivity
    positivity
  have hle : ∀ n : ℕ, pencilBound m n * ρ ^ n ≤ C := fun n =>
    hBsum.le_tsum n fun i _ => hnn i
  have hCnn : 0 ≤ C := le_trans (hnn 0) (hle 0)
  have hgeo : Summable fun n : ℕ => C ^ 2 * ((r / ρ) ^ 2) ^ n := by
    refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
    have : r / ρ < 1 := (div_lt_one hρ0).mpr hrρ
    nlinarith [div_nonneg hr0 hρ0.le]
  refine hgeo.of_nonneg_of_le (fun n => by
    have := bernsteinCoefficientPurity_nonneg m n
    positivity) (fun n => ?_)
  have hB : bernsteinCoefficientPurity m n * r ^ (2 * n) ≤ (pencilBound m n) ^ 2 * r ^ (2 * n) :=
    mul_le_mul_of_nonneg_right (bernsteinCoefficientPurity_le_sq m n) (by positivity)
  refine le_trans hB ?_
  have hρ2 : ((ρ : ℝ) ^ 2) ≠ 0 := by positivity
  have hkey : (pencilBound m n * ρ ^ n) ^ 2 * ((r / ρ) ^ 2) ^ n
      = (pencilBound m n) ^ 2 * r ^ (2 * n) := by
    have e1 : (ρ ^ n) ^ 2 = (ρ ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have e3 : (ρ ^ 2) * ((r ^ 2) / (ρ ^ 2)) = r ^ 2 := by field_simp
    calc (pencilBound m n * ρ ^ n) ^ 2 * ((r / ρ) ^ 2) ^ n
        = (pencilBound m n) ^ 2 * ((ρ ^ 2) ^ n * ((r ^ 2) / (ρ ^ 2)) ^ n) := by
          rw [mul_pow, e1, div_pow, mul_assoc]
      _ = (pencilBound m n) ^ 2 * ((ρ ^ 2) * ((r ^ 2) / (ρ ^ 2))) ^ n := by rw [mul_pow]
      _ = (pencilBound m n) ^ 2 * (r ^ 2) ^ n := by rw [e3]
      _ = (pencilBound m n) ^ 2 * r ^ (2 * n) := by rw [pow_mul]
  rw [← hkey]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hnn n) (hle n) 2) (by positivity)

theorem integral_normSq_pencil (m : ℕ → ℝ) (n : ℕ) :
    (∫ φ in (0:ℝ)..(2 * Real.pi), ‖bernsteinCoefficientTransform m n (circleMap 0 1 φ)‖ ^ 2)
      = (2 * Real.pi) * bernsteinCoefficientPurity m n := by
  have h := bernsteinCoefficientPurity_eq_circleMean m n
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith [h]

/-- **(8) The double Gutzmer susceptibility law.**  The positive Abel susceptibility is the exact
two-torus Gutzmer norm of the Möbius pullback. -/
theorem hasSum_purity_doubleCircleMean (m : ℕ → ℝ) {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r < ρ)
    (hρ1 : ρ < 1) (hM : Summable fun k : ℕ => |m k| * (2 * ρ / (1 - ρ)) ^ k) :
    HasSum (fun n => bernsteinCoefficientPurity m n * r ^ (2 * n))
      ((2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi),
        ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
          ‖bernsteinPencilGenerating m (circleMap 0 r θ) (circleMap 0 1 φ)‖ ^ 2)) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi)) with hμ
  set F : ℕ → ℝ → ℝ := fun n φ =>
    ‖bernsteinCoefficientTransform m n (circleMap 0 1 φ)‖ ^ 2 * r ^ (2 * n) with hF
  have hcirc : ∀ φ : ℝ, ‖circleMap 0 1 φ‖ = 1 := fun φ => by
    rw [norm_circleMap_zero]; norm_num
  have hinner : ∀ φ : ℝ,
      ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖bernsteinPencilGenerating m (circleMap 0 r θ) (circleMap 0 1 φ)‖ ^ 2)
      = ∑' n : ℕ, F n φ := fun φ =>
    (hasSum_inner_gutzmer m hr0 hrρ hρ1 hM (hcirc φ)).tsum_eq.symm
  have hFcont : ∀ n : ℕ, Continuous (F n) := fun n =>
    (continuous_normSq_pencil m n).mul continuous_const
  have hFnn : ∀ n φ, 0 ≤ F n φ := fun n φ => by
    rw [hF]; positivity
  have hFint : ∀ n : ℕ, (∫ φ, F n φ ∂μ) = (2 * Real.pi) * (bernsteinCoefficientPurity m n
      * r ^ (2 * n)) := by
    intro n
    have h1 : (∫ φ in (0:ℝ)..(2 * Real.pi), F n φ) = ∫ φ, F n φ ∂μ :=
      intervalIntegral.integral_of_le hpi.le
    rw [← h1, hF]
    simp only
    rw [intervalIntegral.integral_mul_const, integral_normSq_pencil]
    ring
  have hFintegrable : ∀ n : ℕ, MeasureTheory.Integrable (F n) μ := by
    intro n
    have hi := ((hFcont n).intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ)
      (2 * Real.pi))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le] at hi
    exact hi
  have hsummable := summable_purity_mul_pow m hr0 hrρ hρ1 hM
  have hlint : ∑' n : ℕ, ∫⁻ φ, ‖F n φ‖ₑ ∂μ ≠ ⊤ := by
    have hterm : ∀ n : ℕ, (∫⁻ φ, ‖F n φ‖ₑ ∂μ)
        = ENNReal.ofReal ((2 * Real.pi) * (bernsteinCoefficientPurity m n * r ^ (2 * n))) := by
      intro n
      have hnn : 0 ≤ᵐ[μ] F n := Filter.Eventually.of_forall (fun φ => hFnn n φ)
      have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hFintegrable n) hnn
      rw [hFint n] at h
      rw [h]
      refine MeasureTheory.lintegral_congr fun φ => ?_
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hFnn n φ)]
    rw [funext hterm]
    have hsum2 : Summable fun n : ℕ =>
        ((2 * Real.pi) * (bernsteinCoefficientPurity m n * r ^ (2 * n))).toNNReal := by
      rw [← NNReal.summable_coe]
      refine (hsummable.mul_left (2 * Real.pi)).congr fun n => ?_
      rw [Real.coe_toNNReal _ (by
        have := bernsteinCoefficientPurity_nonneg m n
        positivity)]
    rw [show (fun n : ℕ => ENNReal.ofReal ((2 * Real.pi)
        * (bernsteinCoefficientPurity m n * r ^ (2 * n))))
        = fun n : ℕ => ((((2 * Real.pi)
          * (bernsteinCoefficientPurity m n * r ^ (2 * n))).toNNReal : NNReal) : ℝ≥0∞) from rfl]
    rw [← ENNReal.coe_tsum hsum2]
    exact ENNReal.coe_ne_top
  have hswap := MeasureTheory.integral_tsum
    (fun n => (hFcont n).aestronglyMeasurable) hlint
  have hmain : ((2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi),
      ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖bernsteinPencilGenerating m (circleMap 0 r θ) (circleMap 0 1 φ)‖ ^ 2))
      = ∑' n : ℕ, bernsteinCoefficientPurity m n * r ^ (2 * n) := by
    simp only [hinner]
    rw [intervalIntegral.integral_of_le hpi.le, hswap]
    simp only [hFint]
    rw [tsum_mul_left]
    field_simp
  rw [hmain]
  exact hsummable.hasSum

end

end RHTower
