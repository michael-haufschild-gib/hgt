import Mathlib

/-!
# The reproducing kernel of quartic polynomials on an interval

For a polynomial `r` of degree at most four and every real `t`,

`r(t)² ≤ (1/12) J((t − 13)/12) ∫₁²⁵ r²`  (`sq_quartic_le_integral`),

with `J = Σ_{j ≤ 4} (j + ½) P_j²`, `P_j` the Legendre polynomials, and `J(s) ≤ 87 s⁸` for large `s`
(`legendreJ_le`). A quartic that is small on `[1, 25]` in `L²` therefore has an explicit polynomial
envelope everywhere, with no determinant of a Hankel matrix.

The proof is the Cauchy inequality in the Legendre basis, after an exact expansion of the
integral.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

/-- The integral of a polynomial of degree eight over `[−1, 1]`. -/
theorem integral_poly_eight (e0 e1 e2 e3 e4 e5 e6 e7 e8 : ℝ) :
    ∫ s in (-1 : ℝ)..1, (e0 + e1 * s + e2 * s ^ 2 + e3 * s ^ 3 + e4 * s ^ 4 + e5 * s ^ 5 +
        e6 * s ^ 6 + e7 * s ^ 7 + e8 * s ^ 8) =
      2 * e0 + 2 / 3 * e2 + 2 / 5 * e4 + 2 / 7 * e6 + 2 / 9 * e8 := by
  have hF : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s : ℝ => e0 * s + e1 * s ^ 2 / 2 + e2 * s ^ 3 / 3 + e3 * s ^ 4 / 4 + e4 * s ^ 5 / 5 +
        e5 * s ^ 6 / 6 + e6 * s ^ 7 / 7 + e7 * s ^ 8 / 8 + e8 * s ^ 9 / 9)
      (e0 + e1 * s + e2 * s ^ 2 + e3 * s ^ 3 + e4 * s ^ 4 + e5 * s ^ 5 + e6 * s ^ 6 + e7 * s ^ 7 +
        e8 * s ^ 8) s := by
    intro s _
    have h0 := (hasDerivAt_id s).const_mul e0
    have h1 := ((hasDerivAt_pow 2 s).const_mul e1).div_const 2
    have h2 := ((hasDerivAt_pow 3 s).const_mul e2).div_const 3
    have h3 := ((hasDerivAt_pow 4 s).const_mul e3).div_const 4
    have h4 := ((hasDerivAt_pow 5 s).const_mul e4).div_const 5
    have h5 := ((hasDerivAt_pow 6 s).const_mul e5).div_const 6
    have h6 := ((hasDerivAt_pow 7 s).const_mul e6).div_const 7
    have h7 := ((hasDerivAt_pow 8 s).const_mul e7).div_const 8
    have h8 := ((hasDerivAt_pow 9 s).const_mul e8).div_const 9
    refine (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8)).congr_deriv ?_
    push_cast
    ring
  rw [integral_eq_sub_of_hasDerivAt hF (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The integral of the square of a quartic over `[−1, 1]`. -/
theorem integral_quartic_sq (d0 d1 d2 d3 d4 : ℝ) :
    ∫ s in (-1 : ℝ)..1, (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4) ^ 2 =
      2 * d0 ^ 2 + 2 / 3 * (d1 ^ 2 + 2 * d0 * d2) + 2 / 5 * (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) +
        2 / 7 * (d3 ^ 2 + 2 * d2 * d4) + 2 / 9 * d4 ^ 2 := by
  have e : ∀ s : ℝ, (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4) ^ 2 =
      d0 ^ 2 + (2 * d0 * d1) * s + (d1 ^ 2 + 2 * d0 * d2) * s ^ 2 +
        (2 * d0 * d3 + 2 * d1 * d2) * s ^ 3 + (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) * s ^ 4 +
        (2 * d1 * d4 + 2 * d2 * d3) * s ^ 5 + (d3 ^ 2 + 2 * d2 * d4) * s ^ 6 +
        (2 * d3 * d4) * s ^ 7 + d4 ^ 2 * s ^ 8 := fun s => by ring
  simp_rw [e]
  rw [integral_poly_eight]

/-- The Legendre kernel of degree four on the diagonal. -/
def legendreJ (s : ℝ) : ℝ :=
  1 / 2 + 3 / 2 * s ^ 2 + 5 / 2 * ((3 * s ^ 2 - 1) / 2) ^ 2 + 7 / 2 * ((5 * s ^ 3 - 3 * s) / 2) ^ 2 +
    9 / 2 * ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) ^ 2

/-- The weighted Cauchy inequality for five terms. -/
theorem weighted_cauchy_five (b0 b1 b2 b3 b4 p0 p1 p2 p3 p4 : ℝ) :
    (b0 * p0 + b1 * p1 + b2 * p2 + b3 * p3 + b4 * p4) ^ 2 ≤
      (1 / 2 * p0 ^ 2 + 3 / 2 * p1 ^ 2 + 5 / 2 * p2 ^ 2 + 7 / 2 * p3 ^ 2 + 9 / 2 * p4 ^ 2) *
        (2 * b0 ^ 2 + 2 / 3 * b1 ^ 2 + 2 / 5 * b2 ^ 2 + 2 / 7 * b3 ^ 2 + 2 / 9 * b4 ^ 2) := by
  have key : (1 / 2 * p0 ^ 2 + 3 / 2 * p1 ^ 2 + 5 / 2 * p2 ^ 2 + 7 / 2 * p3 ^ 2 + 9 / 2 * p4 ^ 2) *
        (2 * b0 ^ 2 + 2 / 3 * b1 ^ 2 + 2 / 5 * b2 ^ 2 + 2 / 7 * b3 ^ 2 + 2 / 9 * b4 ^ 2) -
      (b0 * p0 + b1 * p1 + b2 * p2 + b3 * p3 + b4 * p4) ^ 2 =
      1 / 3 * (3 * b0 * p1 - b1 * p0) ^ 2 + 1 / 5 * (5 * b0 * p2 - b2 * p0) ^ 2 +
      1 / 7 * (7 * b0 * p3 - b3 * p0) ^ 2 + 1 / 9 * (9 * b0 * p4 - b4 * p0) ^ 2 +
      1 / 15 * (5 * b1 * p2 - 3 * b2 * p1) ^ 2 + 1 / 21 * (7 * b1 * p3 - 3 * b3 * p1) ^ 2 +
      1 / 27 * (9 * b1 * p4 - 3 * b4 * p1) ^ 2 + 1 / 35 * (7 * b2 * p3 - 5 * b3 * p2) ^ 2 +
      1 / 45 * (9 * b2 * p4 - 5 * b4 * p2) ^ 2 + 1 / 63 * (9 * b3 * p4 - 7 * b4 * p3) ^ 2 := by
    ring
  have hnn : 0 ≤ 1 / 3 * (3 * b0 * p1 - b1 * p0) ^ 2 + 1 / 5 * (5 * b0 * p2 - b2 * p0) ^ 2 +
      1 / 7 * (7 * b0 * p3 - b3 * p0) ^ 2 + 1 / 9 * (9 * b0 * p4 - b4 * p0) ^ 2 +
      1 / 15 * (5 * b1 * p2 - 3 * b2 * p1) ^ 2 + 1 / 21 * (7 * b1 * p3 - 3 * b3 * p1) ^ 2 +
      1 / 27 * (9 * b1 * p4 - 3 * b4 * p1) ^ 2 + 1 / 35 * (7 * b2 * p3 - 5 * b3 * p2) ^ 2 +
      1 / 45 * (9 * b2 * p4 - 5 * b4 * p2) ^ 2 + 1 / 63 * (9 * b3 * p4 - 7 * b4 * p3) ^ 2 := by
    positivity
  linarith only [key, hnn]

/-- **The kernel inequality on `[−1, 1]`.** -/
theorem sq_quartic_le_legendreJ_mul_integral (d0 d1 d2 d3 d4 s : ℝ) :
    (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4) ^ 2 ≤
      legendreJ s * ∫ x in (-1 : ℝ)..1, (d0 + d1 * x + d2 * x ^ 2 + d3 * x ^ 3 + d4 * x ^ 4) ^ 2 := by
  rw [integral_quartic_sq]
  obtain ⟨β4, h4⟩ : ∃ β4, β4 = 8 / 35 * d4 := ⟨_, rfl⟩
  obtain ⟨β3, h3⟩ : ∃ β3, β3 = 2 / 5 * d3 := ⟨_, rfl⟩
  obtain ⟨β2, h2⟩ : ∃ β2, β2 = 2 / 3 * (d2 + 15 / 4 * β4) := ⟨_, rfl⟩
  obtain ⟨β1, h1⟩ : ∃ β1, β1 = d1 + 3 / 2 * β3 := ⟨_, rfl⟩
  obtain ⟨β0, h0⟩ : ∃ β0, β0 = d0 + 1 / 2 * β2 - 3 / 8 * β4 := ⟨_, rfl⟩
  have hexp : d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 =
      β0 * 1 + β1 * s + β2 * ((3 * s ^ 2 - 1) / 2) + β3 * ((5 * s ^ 3 - 3 * s) / 2) +
        β4 * ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) := by
    rw [h0, h1, h2, h3, h4]
    ring
  have hI : 2 * d0 ^ 2 + 2 / 3 * (d1 ^ 2 + 2 * d0 * d2) +
      2 / 5 * (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) + 2 / 7 * (d3 ^ 2 + 2 * d2 * d4) + 2 / 9 * d4 ^ 2 =
      2 * β0 ^ 2 + 2 / 3 * β1 ^ 2 + 2 / 5 * β2 ^ 2 + 2 / 7 * β3 ^ 2 + 2 / 9 * β4 ^ 2 := by
    rw [h0, h1, h2, h3, h4]
    ring
  rw [hexp, hI]
  have h := weighted_cauchy_five β0 β1 β2 β3 β4 1 s ((3 * s ^ 2 - 1) / 2) ((5 * s ^ 3 - 3 * s) / 2)
    ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8)
  refine h.trans (le_of_eq ?_)
  unfold legendreJ
  ring

/-- A quartic in the variable `u`. -/
def quartic (c0 c1 c2 c3 c4 u : ℝ) : ℝ := c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4

theorem continuous_quartic (c0 c1 c2 c3 c4 : ℝ) : Continuous (quartic c0 c1 c2 c3 c4) := by
  unfold quartic
  fun_prop

/-- **The kernel inequality on `[1, 25]`.** -/
theorem sq_quartic_le_integral (c0 c1 c2 c3 c4 t : ℝ) :
    quartic c0 c1 c2 c3 c4 t ^ 2 ≤
      1 / 12 * legendreJ ((t - 13) / 12) * ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2 := by
  obtain ⟨d0, h0⟩ : ∃ d0, d0 = c0 + 13 * c1 + 169 * c2 + 2197 * c3 + 28561 * c4 := ⟨_, rfl⟩
  obtain ⟨d1, h1⟩ : ∃ d1, d1 = 12 * (c1 + 26 * c2 + 507 * c3 + 8788 * c4) := ⟨_, rfl⟩
  obtain ⟨d2, h2⟩ : ∃ d2, d2 = 144 * (c2 + 39 * c3 + 1014 * c4) := ⟨_, rfl⟩
  obtain ⟨d3, h3⟩ : ∃ d3, d3 = 1728 * (c3 + 52 * c4) := ⟨_, rfl⟩
  obtain ⟨d4, h4⟩ : ∃ d4, d4 = 20736 * c4 := ⟨_, rfl⟩
  have hsub : ∀ s : ℝ, quartic c0 c1 c2 c3 c4 (12 * s + 13) =
      d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 := fun s => by
    unfold quartic
    rw [h0, h1, h2, h3, h4]
    ring
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun u : ℝ => quartic c0 c1 c2 c3 c4 u ^ 2) (a := -1) (b := 1) (c := 12) (d := 13)
  norm_num at hcov
  rw [← hcov]
  simp_rw [hsub]
  have hk := sq_quartic_le_legendreJ_mul_integral d0 d1 d2 d3 d4 ((t - 13) / 12)
  have hval : quartic c0 c1 c2 c3 c4 t = d0 + d1 * ((t - 13) / 12) + d2 * ((t - 13) / 12) ^ 2 +
      d3 * ((t - 13) / 12) ^ 3 + d4 * ((t - 13) / 12) ^ 4 := by
    rw [← hsub]
    congr 1
    ring
  rw [hval]
  refine hk.trans (le_of_eq ?_)
  ring

/-- **The envelope of the kernel.** -/
theorem legendreJ_le {s : ℝ} (hs : 361 ≤ s) : legendreJ s ≤ 87 * s ^ 8 := by
  obtain ⟨u, hu⟩ : ∃ u, u = s ^ 2 := ⟨_, rfl⟩
  have hu1 : 130000 ≤ u := by rw [hu]; nlinarith only [hs]
  have hs0 : 0 ≤ s := by linarith only [hs]
  have h2 : ((3 * s ^ 2 - 1) / 2) ^ 2 ≤ 9 / 4 * u ^ 2 := by
    rw [hu]
    nlinarith only [hs, hs0, pow_nonneg hs0 2]
  have h3 : ((5 * s ^ 3 - 3 * s) / 2) ^ 2 ≤ 25 / 4 * u ^ 3 := by
    have e : ((5 * s ^ 3 - 3 * s) / 2) ^ 2 = u * ((5 * u - 3) / 2) ^ 2 := by
      rw [hu]
      ring
    rw [e]
    have : ((5 * u - 3) / 2) ^ 2 ≤ 25 / 4 * u ^ 2 := by nlinarith only [hu1]
    have h0 : 0 ≤ u := by linarith only [hu1]
    nlinarith only [mul_le_mul_of_nonneg_left this h0]
  have h4 : ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) ^ 2 ≤ (35 / 8) ^ 2 * u ^ 4 := by
    have e : (35 * s ^ 4 - 30 * s ^ 2 + 3) / 8 = (35 * u ^ 2 - 30 * u + 3) / 8 := by
      rw [hu]
      ring
    rw [e]
    have h1 : (35 * u ^ 2 - 30 * u + 3) / 8 ≤ 35 / 8 * u ^ 2 := by nlinarith only [hu1]
    have h0 : 0 ≤ (35 * u ^ 2 - 30 * u + 3) / 8 := by nlinarith only [hu1]
    have := pow_le_pow_left₀ h0 h1 2
    refine this.trans (le_of_eq ?_)
    ring
  have hs8 : s ^ 8 = u ^ 4 := by
    rw [hu]
    ring
  unfold legendreJ
  have h0 : 3 / 2 * s ^ 2 = 3 / 2 * u := by rw [hu]
  rw [hs8, h0]
  generalize ((3 * s ^ 2 - 1) / 2) ^ 2 = A at h2 ⊢
  generalize ((5 * s ^ 3 - 3 * s) / 2) ^ 2 = B at h3 ⊢
  generalize ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) ^ 2 = C at h4 ⊢
  have hu0 : 0 ≤ u := by linarith only [hu1]
  have h31 : u ^ 3 * 1000 ≤ u ^ 4 := by
    have := mul_le_mul_of_nonneg_left (by linarith only [hu1] : (1000 : ℝ) ≤ u) (pow_nonneg hu0 3)
    calc u ^ 3 * 1000 ≤ u ^ 3 * u := this
      _ = u ^ 4 := by ring
  have h21 : u ^ 2 * 1000 ≤ u ^ 3 := by
    have := mul_le_mul_of_nonneg_left (by linarith only [hu1] : (1000 : ℝ) ≤ u) (pow_nonneg hu0 2)
    calc u ^ 2 * 1000 ≤ u ^ 2 * u := this
      _ = u ^ 3 := by ring
  have h11 : u * 1000 ≤ u ^ 2 := by nlinarith only [hu1]
  norm_num at h4 ⊢
  linarith only [h2, h3, h4, h31, h21, h11, hu1]

/-- A quartic with vanishing energy has vanishing coefficients. -/
theorem quartic_coeffs_zero {c0 c1 c2 c3 c4 : ℝ}
    (h : ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have hz : ∀ t : ℝ, quartic c0 c1 c2 c3 c4 t = 0 := fun t => by
    have hk := sq_quartic_le_integral c0 c1 c2 c3 c4 t
    rw [h, mul_zero] at hk
    exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hk (sq_nonneg _))
  have e0 := hz 0
  have e1 := hz 1
  have e2 := hz (-1)
  have e3 := hz 2
  have e4 := hz (-2)
  unfold quartic at e0 e1 e2 e3 e4
  norm_num at e0 e1 e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [e0, e1, e2, e3, e4]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
