import GaloisForLFunctions.ThetaCuspSections.QuarticLegendreKernel

/-!
# The reproducing kernel of quintic polynomials on an interval

For a polynomial `r` of degree at most five and every real `t`,

`r(t)² ≤ (1/12) J₅((t − 13)/12) ∫₁²⁵ r²`  (`sq_quintic_le_integral`),

with `J₅ = Σ_{j ≤ 5} (j + ½) P_j²` and `J₅(s) ≤ 342 s¹⁰` for `s ≥ 361` (`legendreJ5_le`). The proof is
the Cauchy inequality in the Legendre basis, as for quartics.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

/-- The integral of a polynomial of degree ten over `[−1, 1]`. -/
theorem integral_poly_ten (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : ℝ) :
    ∫ s in (-1 : ℝ)..1, (e0 + e1 * s + e2 * s ^ 2 + e3 * s ^ 3 + e4 * s ^ 4 + e5 * s ^ 5 +
        e6 * s ^ 6 + e7 * s ^ 7 + e8 * s ^ 8 + e9 * s ^ 9 + e10 * s ^ 10) =
      2 * e0 + 2 / 3 * e2 + 2 / 5 * e4 + 2 / 7 * e6 + 2 / 9 * e8 + 2 / 11 * e10 := by
  have hF : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s : ℝ => e0 * s + e1 * s ^ 2 / 2 + e2 * s ^ 3 / 3 + e3 * s ^ 4 / 4 + e4 * s ^ 5 / 5 +
        e5 * s ^ 6 / 6 + e6 * s ^ 7 / 7 + e7 * s ^ 8 / 8 + e8 * s ^ 9 / 9 + e9 * s ^ 10 / 10 +
        e10 * s ^ 11 / 11)
      (e0 + e1 * s + e2 * s ^ 2 + e3 * s ^ 3 + e4 * s ^ 4 + e5 * s ^ 5 + e6 * s ^ 6 + e7 * s ^ 7 +
        e8 * s ^ 8 + e9 * s ^ 9 + e10 * s ^ 10) s := by
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
    have h9 := ((hasDerivAt_pow 10 s).const_mul e9).div_const 10
    have h10 := ((hasDerivAt_pow 11 s).const_mul e10).div_const 11
    refine (((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add
      h9).add h10)).congr_deriv ?_
    push_cast
    ring
  rw [integral_eq_sub_of_hasDerivAt hF (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The integral of the square of a quintic over `[−1, 1]`. -/
theorem integral_quintic_sq (d0 d1 d2 d3 d4 d5 : ℝ) :
    ∫ s in (-1 : ℝ)..1, (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 + d5 * s ^ 5) ^ 2 =
      2 * d0 ^ 2 + 2 / 3 * (d1 ^ 2 + 2 * d0 * d2) +
        2 / 5 * (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) +
        2 / 7 * (d3 ^ 2 + 2 * d2 * d4 + 2 * d1 * d5) + 2 / 9 * (d4 ^ 2 + 2 * d3 * d5) +
        2 / 11 * d5 ^ 2 := by
  have e : ∀ s : ℝ, (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 + d5 * s ^ 5) ^ 2 =
      d0 ^ 2 + (2 * d0 * d1) * s + (d1 ^ 2 + 2 * d0 * d2) * s ^ 2 +
        (2 * d0 * d3 + 2 * d1 * d2) * s ^ 3 + (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) * s ^ 4 +
        (2 * d0 * d5 + 2 * d1 * d4 + 2 * d2 * d3) * s ^ 5 +
        (d3 ^ 2 + 2 * d2 * d4 + 2 * d1 * d5) * s ^ 6 + (2 * d2 * d5 + 2 * d3 * d4) * s ^ 7 +
        (d4 ^ 2 + 2 * d3 * d5) * s ^ 8 + (2 * d4 * d5) * s ^ 9 + d5 ^ 2 * s ^ 10 := fun s => by
    ring
  simp_rw [e]
  rw [integral_poly_ten]

/-- The fifth Legendre polynomial. -/
def legendreP5 (s : ℝ) : ℝ := (63 * s ^ 5 - 70 * s ^ 3 + 15 * s) / 8

/-- The Legendre kernel of degree five on the diagonal. -/
def legendreJ5 (s : ℝ) : ℝ := legendreJ s + 11 / 2 * legendreP5 s ^ 2

/-- The weighted Cauchy inequality for six terms. -/
theorem weighted_cauchy_six (b0 b1 b2 b3 b4 b5 p0 p1 p2 p3 p4 p5 : ℝ) :
    (b0 * p0 + b1 * p1 + b2 * p2 + b3 * p3 + b4 * p4 + b5 * p5) ^ 2 ≤
      (1 / 2 * p0 ^ 2 + 3 / 2 * p1 ^ 2 + 5 / 2 * p2 ^ 2 + 7 / 2 * p3 ^ 2 + 9 / 2 * p4 ^ 2 +
          11 / 2 * p5 ^ 2) *
        (2 * b0 ^ 2 + 2 / 3 * b1 ^ 2 + 2 / 5 * b2 ^ 2 + 2 / 7 * b3 ^ 2 + 2 / 9 * b4 ^ 2 +
          2 / 11 * b5 ^ 2) := by
  have key : (1 / 2 * p0 ^ 2 + 3 / 2 * p1 ^ 2 + 5 / 2 * p2 ^ 2 + 7 / 2 * p3 ^ 2 + 9 / 2 * p4 ^ 2 +
          11 / 2 * p5 ^ 2) *
        (2 * b0 ^ 2 + 2 / 3 * b1 ^ 2 + 2 / 5 * b2 ^ 2 + 2 / 7 * b3 ^ 2 + 2 / 9 * b4 ^ 2 +
          2 / 11 * b5 ^ 2) -
      (b0 * p0 + b1 * p1 + b2 * p2 + b3 * p3 + b4 * p4 + b5 * p5) ^ 2 =
      1 / 3 * (3 * b0 * p1 - b1 * p0) ^ 2 + 1 / 5 * (5 * b0 * p2 - b2 * p0) ^ 2 +
      1 / 7 * (7 * b0 * p3 - b3 * p0) ^ 2 + 1 / 9 * (9 * b0 * p4 - b4 * p0) ^ 2 +
      1 / 11 * (11 * b0 * p5 - b5 * p0) ^ 2 +
      1 / 15 * (5 * b1 * p2 - 3 * b2 * p1) ^ 2 + 1 / 21 * (7 * b1 * p3 - 3 * b3 * p1) ^ 2 +
      1 / 27 * (9 * b1 * p4 - 3 * b4 * p1) ^ 2 + 1 / 33 * (11 * b1 * p5 - 3 * b5 * p1) ^ 2 +
      1 / 35 * (7 * b2 * p3 - 5 * b3 * p2) ^ 2 + 1 / 45 * (9 * b2 * p4 - 5 * b4 * p2) ^ 2 +
      1 / 55 * (11 * b2 * p5 - 5 * b5 * p2) ^ 2 + 1 / 63 * (9 * b3 * p4 - 7 * b4 * p3) ^ 2 +
      1 / 77 * (11 * b3 * p5 - 7 * b5 * p3) ^ 2 + 1 / 99 * (11 * b4 * p5 - 9 * b5 * p4) ^ 2 := by
    ring
  have hnn : 0 ≤ 1 / 3 * (3 * b0 * p1 - b1 * p0) ^ 2 + 1 / 5 * (5 * b0 * p2 - b2 * p0) ^ 2 +
      1 / 7 * (7 * b0 * p3 - b3 * p0) ^ 2 + 1 / 9 * (9 * b0 * p4 - b4 * p0) ^ 2 +
      1 / 11 * (11 * b0 * p5 - b5 * p0) ^ 2 +
      1 / 15 * (5 * b1 * p2 - 3 * b2 * p1) ^ 2 + 1 / 21 * (7 * b1 * p3 - 3 * b3 * p1) ^ 2 +
      1 / 27 * (9 * b1 * p4 - 3 * b4 * p1) ^ 2 + 1 / 33 * (11 * b1 * p5 - 3 * b5 * p1) ^ 2 +
      1 / 35 * (7 * b2 * p3 - 5 * b3 * p2) ^ 2 + 1 / 45 * (9 * b2 * p4 - 5 * b4 * p2) ^ 2 +
      1 / 55 * (11 * b2 * p5 - 5 * b5 * p2) ^ 2 + 1 / 63 * (9 * b3 * p4 - 7 * b4 * p3) ^ 2 +
      1 / 77 * (11 * b3 * p5 - 7 * b5 * p3) ^ 2 + 1 / 99 * (11 * b4 * p5 - 9 * b5 * p4) ^ 2 := by
    positivity
  linarith only [key, hnn]

/-- **The kernel inequality on `[−1, 1]`.** -/
theorem sq_quintic_le_legendreJ5_mul_integral (d0 d1 d2 d3 d4 d5 s : ℝ) :
    (d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 + d5 * s ^ 5) ^ 2 ≤
      legendreJ5 s * ∫ x in (-1 : ℝ)..1,
        (d0 + d1 * x + d2 * x ^ 2 + d3 * x ^ 3 + d4 * x ^ 4 + d5 * x ^ 5) ^ 2 := by
  rw [integral_quintic_sq]
  obtain ⟨β5, h5⟩ : ∃ β5, β5 = 8 / 63 * d5 := ⟨_, rfl⟩
  obtain ⟨β4, h4⟩ : ∃ β4, β4 = 8 / 35 * d4 := ⟨_, rfl⟩
  obtain ⟨β3, h3⟩ : ∃ β3, β3 = 2 / 5 * (d3 + 35 / 4 * β5) := ⟨_, rfl⟩
  obtain ⟨β2, h2⟩ : ∃ β2, β2 = 2 / 3 * (d2 + 15 / 4 * β4) := ⟨_, rfl⟩
  obtain ⟨β1, h1⟩ : ∃ β1, β1 = d1 + 3 / 2 * β3 - 15 / 8 * β5 := ⟨_, rfl⟩
  obtain ⟨β0, h0⟩ : ∃ β0, β0 = d0 + 1 / 2 * β2 - 3 / 8 * β4 := ⟨_, rfl⟩
  have hexp : d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 + d5 * s ^ 5 =
      β0 * 1 + β1 * s + β2 * ((3 * s ^ 2 - 1) / 2) + β3 * ((5 * s ^ 3 - 3 * s) / 2) +
        β4 * ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) + β5 * legendreP5 s := by
    rw [h0, h1, h2, h3, h4, h5, legendreP5]
    ring
  have hI : 2 * d0 ^ 2 + 2 / 3 * (d1 ^ 2 + 2 * d0 * d2) +
      2 / 5 * (d2 ^ 2 + 2 * d0 * d4 + 2 * d1 * d3) +
      2 / 7 * (d3 ^ 2 + 2 * d2 * d4 + 2 * d1 * d5) + 2 / 9 * (d4 ^ 2 + 2 * d3 * d5) +
      2 / 11 * d5 ^ 2 =
      2 * β0 ^ 2 + 2 / 3 * β1 ^ 2 + 2 / 5 * β2 ^ 2 + 2 / 7 * β3 ^ 2 + 2 / 9 * β4 ^ 2 +
        2 / 11 * β5 ^ 2 := by
    rw [h0, h1, h2, h3, h4, h5]
    ring
  rw [hexp, hI]
  have h := weighted_cauchy_six β0 β1 β2 β3 β4 β5 1 s ((3 * s ^ 2 - 1) / 2)
    ((5 * s ^ 3 - 3 * s) / 2) ((35 * s ^ 4 - 30 * s ^ 2 + 3) / 8) (legendreP5 s)
  refine h.trans (le_of_eq ?_)
  unfold legendreJ5 legendreJ
  ring

/-- A quintic in the variable `u`. -/
def quintic (c0 c1 c2 c3 c4 c5 u : ℝ) : ℝ :=
  c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5

theorem continuous_quintic (c0 c1 c2 c3 c4 c5 : ℝ) : Continuous (quintic c0 c1 c2 c3 c4 c5) := by
  unfold quintic
  fun_prop

/-- **The kernel inequality on `[1, 25]`.** -/
theorem sq_quintic_le_integral (c0 c1 c2 c3 c4 c5 t : ℝ) :
    quintic c0 c1 c2 c3 c4 c5 t ^ 2 ≤
      1 / 12 * legendreJ5 ((t - 13) / 12) * ∫ u in (1 : ℝ)..25, quintic c0 c1 c2 c3 c4 c5 u ^ 2 := by
  obtain ⟨d0, h0⟩ : ∃ d0, d0 = c0 + 13 * c1 + 169 * c2 + 2197 * c3 + 28561 * c4 + 371293 * c5 :=
    ⟨_, rfl⟩
  obtain ⟨d1, h1⟩ : ∃ d1, d1 = 12 * (c1 + 26 * c2 + 507 * c3 + 8788 * c4 + 142805 * c5) := ⟨_, rfl⟩
  obtain ⟨d2, h2⟩ : ∃ d2, d2 = 144 * (c2 + 39 * c3 + 1014 * c4 + 21970 * c5) := ⟨_, rfl⟩
  obtain ⟨d3, h3⟩ : ∃ d3, d3 = 1728 * (c3 + 52 * c4 + 1690 * c5) := ⟨_, rfl⟩
  obtain ⟨d4, h4⟩ : ∃ d4, d4 = 20736 * (c4 + 65 * c5) := ⟨_, rfl⟩
  obtain ⟨d5, h5⟩ : ∃ d5, d5 = 248832 * c5 := ⟨_, rfl⟩
  have hsub : ∀ s : ℝ, quintic c0 c1 c2 c3 c4 c5 (12 * s + 13) =
      d0 + d1 * s + d2 * s ^ 2 + d3 * s ^ 3 + d4 * s ^ 4 + d5 * s ^ 5 := fun s => by
    unfold quintic
    rw [h0, h1, h2, h3, h4, h5]
    ring
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun u : ℝ => quintic c0 c1 c2 c3 c4 c5 u ^ 2) (a := -1) (b := 1) (c := 12) (d := 13)
  norm_num at hcov
  rw [← hcov]
  simp_rw [hsub]
  have hk := sq_quintic_le_legendreJ5_mul_integral d0 d1 d2 d3 d4 d5 ((t - 13) / 12)
  have hval : quintic c0 c1 c2 c3 c4 c5 t = d0 + d1 * ((t - 13) / 12) +
      d2 * ((t - 13) / 12) ^ 2 + d3 * ((t - 13) / 12) ^ 3 + d4 * ((t - 13) / 12) ^ 4 +
      d5 * ((t - 13) / 12) ^ 5 := by
    rw [← hsub]
    congr 1
    ring
  rw [hval]
  refine hk.trans (le_of_eq ?_)
  ring

/-- **The envelope of the kernel.** -/
theorem legendreJ5_le {s : ℝ} (hs : 361 ≤ s) : legendreJ5 s ≤ 342 * s ^ 10 := by
  have hJ := legendreJ_le hs
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hP0 : 0 ≤ legendreP5 s := by
    unfold legendreP5
    have h3 : 70 * s ^ 3 ≤ 63 * s ^ 5 := by
      have : s ^ 3 * 70 ≤ s ^ 3 * (63 * s ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hs]) (by positivity)
      nlinarith only [this]
    have : 0 ≤ 15 * s := by linarith only [hs0]
    linarith only [h3, this]
  have hP1 : legendreP5 s ≤ 63 / 8 * s ^ 5 := by
    unfold legendreP5
    have h3 : 15 * s ≤ 70 * s ^ 3 := by
      have : s * 15 ≤ s * (70 * s ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith only [hs]) hs0
      nlinarith only [this]
    linarith only [h3]
  have hP2 : legendreP5 s ^ 2 ≤ (63 / 8) ^ 2 * s ^ 10 := by
    have := pow_le_pow_left₀ hP0 hP1 2
    refine this.trans (le_of_eq ?_)
    ring
  have h8 : 87 * s ^ 8 ≤ 1 / 1000 * s ^ 10 := by
    have : s ^ 8 * 87000 ≤ s ^ 8 * s ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hs]) (by positivity)
    nlinarith only [this]
  unfold legendreJ5
  nlinarith only [hJ, hP2, h8]

/-- A quintic with vanishing energy has vanishing coefficients. -/
theorem quintic_coeffs_zero {c0 c1 c2 c3 c4 c5 : ℝ}
    (h : ∫ u in (1 : ℝ)..25, quintic c0 c1 c2 c3 c4 c5 u ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 := by
  have hz : ∀ t : ℝ, quintic c0 c1 c2 c3 c4 c5 t = 0 := fun t => by
    have hk := sq_quintic_le_integral c0 c1 c2 c3 c4 c5 t
    rw [h, mul_zero] at hk
    exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hk (sq_nonneg _))
  have e0 := hz 0
  have e1 := hz 1
  have e2 := hz (-1)
  have e3 := hz 2
  have e4 := hz (-2)
  have e5 := hz 3
  unfold quintic at e0 e1 e2 e3 e4 e5
  norm_num at e0 e1 e2 e3 e4 e5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [e0, e1, e2, e3, e4, e5]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
