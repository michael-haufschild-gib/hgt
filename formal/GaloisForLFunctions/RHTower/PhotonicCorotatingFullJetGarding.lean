import GaloisForLFunctions.RHTower.PhotonicCorotatingInterfaceSymbol

/-!
# Full helical TE jet coercivity for the literal rotating cylinder

The source dielectric's exact angular derivative gives a first-order
commutator in the co-rotating TE operator. The paper's displayed parameters
make the resulting non-selfadjoint quadratic jet form coercive up to a
frequency-dependent zeroth-order cost for the inside-side formula at radius
ratio `0 ≤ ρ ≤ 11/10`, uniformly over all angular jets. The actual dielectric
occupies only `ρ ≤ 1`; the extra margin is a stability neighbourhood, not a
model of exterior air. This is a pointwise local Gårding premise; no Maxwell
trace domain, integrated estimate, or
distributional transmission regularity is asserted.
-/

namespace RHTower

private theorem real_jet_garding
    (A B N U V W : ℝ) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hmargin : 0 < A ^ 2 - 15 * B ^ 2) :
    A ^ 2 * (W ^ 2 + V ^ 2) -
        (15 * (B * V + N * U) ^ 2 +
          10 * B * U * (B * V + N * U)) ≥
      A ^ 2 * W ^ 2 + (A ^ 2 - 15 * B ^ 2) / 2 * V ^ 2 -
        (15 * N ^ 2 + 10 * B * N +
          (30 * B * N + 10 * B ^ 2) ^ 2 /
            (2 * (A ^ 2 - 15 * B ^ 2))) * U ^ 2 := by
  let m : ℝ := A ^ 2 - 15 * B ^ 2
  let L : ℝ := 30 * B * N + 10 * B ^ 2
  have hm : 0 < m := hmargin
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hyoung : L * U * V ≤ m / 2 * V ^ 2 + L ^ 2 / (2 * m) * U ^ 2 := by
    have hs := sq_nonneg (m * V - L * U)
    have hh : 2 * m * (L * U * V) ≤ m ^ 2 * V ^ 2 + L ^ 2 * U ^ 2 := by
      nlinarith only [hs]
    have heq : 2 * m * (m / 2 * V ^ 2 + L ^ 2 / (2 * m) * U ^ 2) =
        m ^ 2 * V ^ 2 + L ^ 2 * U ^ 2 := by
      field_simp
    have hh' : 2 * m * (L * U * V) ≤
        2 * m * (m / 2 * V ^ 2 + L ^ 2 / (2 * m) * U ^ 2) := by
      rw [heq]
      exact hh
    by_contra hnot
    have hgt : 0 < L * U * V -
        (m / 2 * V ^ 2 + L ^ 2 / (2 * m) * U ^ 2) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hmul := mul_pos (by positivity : 0 < 2 * m) hgt
    nlinarith only [hh', hmul]
  dsimp [m, L] at hyoung
  nlinarith only [hyoung]

private theorem complex_main (ε z : ℂ) :
    (ε * z * star z).re = ε.re * ‖z‖ ^ 2 := by
  have hnorm : z * star z = (‖z‖ : ℂ) ^ 2 := by
    simpa only [starRingEnd_apply] using Complex.mul_conj' z
  rw [mul_assoc, hnorm]
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem complex_cross (B σ : ℝ) (u z : ℂ) (hB : 0 ≤ B) :
    ((-Complex.I) * ((B * σ : ℝ) : ℂ) * u * star z).re ≤
      B * |σ| * ‖u‖ * ‖z‖ := by
  calc
    _ ≤ ‖(-Complex.I) * ((B * σ : ℝ) : ℂ) * u * star z‖ := Complex.re_le_norm _
    _ = B * |σ| * ‖u‖ * ‖z‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hB,
        mul_assoc, mul_comm, mul_left_comm]

private theorem complex_jet_garding
    (A B ν σ : ℝ) (ε u du dr : ℂ)
    (hB : 0 ≤ B) (hε : ε.re ≤ 15) (hσ : |σ| ≤ 10)
    (hmargin : 0 < A ^ 2 - 15 * B ^ 2) :
    let z : ℂ := (B : ℂ) * du + (ν : ℂ) * u
    A ^ 2 * (‖dr‖ ^ 2 + ‖du‖ ^ 2) -
        (ε * z * star z +
          (-Complex.I) * ((B * σ : ℝ) : ℂ) * u * star z).re ≥
      A ^ 2 * ‖dr‖ ^ 2 +
        (A ^ 2 - 15 * B ^ 2) / 2 * ‖du‖ ^ 2 -
        (15 * |ν| ^ 2 + 10 * B * |ν| +
          (30 * B * |ν| + 10 * B ^ 2) ^ 2 /
            (2 * (A ^ 2 - 15 * B ^ 2))) * ‖u‖ ^ 2 := by
  dsimp
  let z : ℂ := (B : ℂ) * du + (ν : ℂ) * u
  have hz : ‖z‖ ≤ B * ‖du‖ + |ν| * ‖u‖ := by
    dsimp [z]
    calc
      _ ≤ ‖(B : ℂ) * du‖ + ‖(ν : ℂ) * u‖ := norm_add_le _ _
      _ = B * ‖du‖ + |ν| * ‖u‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hB]
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hb0 : 0 ≤ B * ‖du‖ + |ν| * ‖u‖ := by positivity
  have hzsq : ‖z‖ ^ 2 ≤ (B * ‖du‖ + |ν| * ‖u‖) ^ 2 := by nlinarith
  have hmain : (ε * z * star z).re ≤ 15 * (B * ‖du‖ + |ν| * ‖u‖) ^ 2 := by
    rw [complex_main]
    have h1 : ε.re * ‖z‖ ^ 2 ≤ 15 * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hε (sq_nonneg _)
    have h2 : 15 * ‖z‖ ^ 2 ≤ 15 * (B * ‖du‖ + |ν| * ‖u‖) ^ 2 := by nlinarith
    linarith
  have hcross :
      ((-Complex.I) * ((B * σ : ℝ) : ℂ) * u * star z).re ≤
        10 * B * ‖u‖ * (B * ‖du‖ + |ν| * ‖u‖) := by
    calc
      _ ≤ B * |σ| * ‖u‖ * ‖z‖ := complex_cross B σ u z hB
      _ ≤ 10 * B * ‖u‖ * ‖z‖ := by
        calc
          _ = |σ| * (B * ‖u‖ * ‖z‖) := by ring
          _ ≤ 10 * (B * ‖u‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_right hσ (by positivity)
          _ = _ := by ring
      _ ≤ 10 * B * ‖u‖ * (B * ‖du‖ + |ν| * ‖u‖) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
  have hreal := real_jet_garding A B |ν| ‖u‖ ‖du‖ ‖dr‖ hB
    (abs_nonneg _) hmargin
  dsimp [z] at hmain hcross
  linarith

private theorem slope_bound (φ : ℝ) : |(-10 : ℝ) * Real.sin (4 * φ)| ≤ 10 := by
  have hs := Real.abs_sin_le_one (4 * φ)
  calc
    _ = 10 * |Real.sin (4 * φ)| := by simp [abs_mul]
    _ ≤ 10 * 1 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 10 := by ring

private theorem source_collar_margin (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 11 / 10) :
    0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      15 * (ρ * ((27 : ℝ) / 200 * Real.pi)) ^ 2 := by
  have hB0 : 0 ≤ (27 : ℝ) / 200 * Real.pi := by positivity
  have hB : (27 : ℝ) / 200 * Real.pi < 27 / 50 := by
    nlinarith [Real.pi_lt_four]
  have hprod : 0 ≤ ρ * ((27 : ℝ) / 200 * Real.pi) :=
    mul_nonneg hρ0 hB0
  have hupper : ρ * ((27 : ℝ) / 200 * Real.pi) ≤ 297 / 500 := by
    calc
      _ ≤ (11 / 10 : ℝ) * ((27 : ℝ) / 200 * Real.pi) :=
        mul_le_mul_of_nonneg_right hρ hB0
      _ ≤ (11 / 10 : ℝ) * (27 / 50) :=
        mul_le_mul_of_nonneg_left hB.le (by norm_num)
      _ = 297 / 500 := by ring
  have hA : (5 / 2 : ℝ) < (299792458 : ℝ) / 100000000 := by norm_num
  nlinarith [sq_nonneg (ρ * ((27 : ℝ) / 200 * Real.pi))]

/-- Full zeroth/first-order helical jet bound for the inside dielectric formula,
stable under a ten-percent radial extension beyond its physical wall. `du` and
`dr` are free complex jets; integration and Maxwell-domain membership remain open. -/
theorem ptr_paper_collar_full_jet_garding
    (ρ φ ν : ℝ) (u du dr : ℂ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 11 / 10) :
    let A : ℝ := (299792458 : ℝ) / 100000000
    let B : ℝ := ρ * ((27 : ℝ) / 200 * Real.pi)
    let z : ℂ := (B : ℂ) * du + (ν : ℂ) * u
    A ^ 2 * (‖dr‖ ^ 2 + ‖du‖ ^ 2) -
        (ptrPaperDielectricComplex φ * z * star z +
          (-Complex.I) * ((B * ((-10 : ℝ) * Real.sin (4 * φ)) : ℝ) : ℂ) *
            u * star z).re ≥
      A ^ 2 * ‖dr‖ ^ 2 +
        (A ^ 2 - 15 * B ^ 2) / 2 * ‖du‖ ^ 2 -
        (15 * |ν| ^ 2 + 10 * B * |ν| +
          (30 * B * |ν| + 10 * B ^ 2) ^ 2 /
            (2 * (A ^ 2 - 15 * B ^ 2))) * ‖u‖ ^ 2 := by
  dsimp
  exact complex_jet_garding
    ((299792458 : ℝ) / 100000000) (ρ * ((27 : ℝ) / 200 * Real.pi))
    ν ((-10 : ℝ) * Real.sin (4 * φ)) (ptrPaperDielectricComplex φ)
    u du dr
    (by positivity)
    (by simpa [ptrPaperDielectricComplex] using ptrPaperDielectricReal_le_fifteen φ)
    (slope_bound φ) (source_collar_margin ρ hρ0 hρ)

/-- Wall specialization of the collar coercivity theorem. -/
theorem ptr_paper_full_jet_garding (φ ν : ℝ) (u du dr : ℂ) :
    let A : ℝ := (299792458 : ℝ) / 100000000
    let B : ℝ := (27 : ℝ) / 200 * Real.pi
    let z : ℂ := (B : ℂ) * du + (ν : ℂ) * u
    A ^ 2 * (‖dr‖ ^ 2 + ‖du‖ ^ 2) -
        (ptrPaperDielectricComplex φ * z * star z +
          (-Complex.I) * ((B * ((-10 : ℝ) * Real.sin (4 * φ)) : ℝ) : ℂ) *
            u * star z).re ≥
      A ^ 2 * ‖dr‖ ^ 2 +
        (A ^ 2 - 15 * B ^ 2) / 2 * ‖du‖ ^ 2 -
        (15 * |ν| ^ 2 + 10 * B * |ν| +
          (30 * B * |ν| + 10 * B ^ 2) ^ 2 /
            (2 * (A ^ 2 - 15 * B ^ 2))) * ‖u‖ ^ 2 := by
  simpa only [one_mul] using
    ptr_paper_collar_full_jet_garding 1 φ ν u du dr (by norm_num) (by norm_num)

/-- Exact angular derivative of the literal lossy dielectric profile. -/
theorem ptr_paper_dielectric_hasDerivAt (φ : ℝ) :
    HasDerivAt ptrPaperDielectricComplex
      (((-10 : ℝ) * Real.sin (4 * φ) : ℝ) : ℂ) φ := by
  have harg : HasDerivAt (fun x : ℝ => 4 * x) 4 φ := by
    simpa using (hasDerivAt_id φ).const_mul 4
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (4 * x))
      (-Real.sin (4 * φ) * 4) φ := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (4 * φ)).comp φ harg
  have hreal : HasDerivAt ptrPaperDielectricReal
      ((-10 : ℝ) * Real.sin (4 * φ)) φ := by
    have h := ((hasDerivAt_const φ (1 : ℝ)).add
      (hcos.const_mul (1 / 5 : ℝ))).const_mul (25 / 2 : ℝ)
    have heq : (25 / 2 : ℝ) * (0 + (1 / 5 : ℝ) *
        (-Real.sin (4 * φ) * 4)) = (-10 : ℝ) * Real.sin (4 * φ) := by ring
    change HasDerivAt (fun x : ℝ => (25 / 2 : ℝ) *
      (1 + (1 / 5 : ℝ) * Real.cos (4 * x))) _ φ
    exact h.congr_deriv heq
  have hcomplex := hreal.ofReal_comp
  change HasDerivAt
    (fun x : ℝ => (ptrPaperDielectricReal x : ℂ) + Complex.I * (1 / 500 : ℂ)) _ φ
  exact (hasDerivAt_add_const_iff (Complex.I * (1 / 500 : ℂ))).mpr hcomplex

/-- The actual co-rotating frequency operator applied to `εu` differs from
`ε` times that operator on `u` by the displayed first-order commutator. -/
theorem ptr_paper_helical_commutator (φ ν B : ℝ) (u : ℝ → ℂ)
    (du : ℂ) (hu : HasDerivAt u du φ) :
    (ν : ℂ) * (ptrPaperDielectricComplex φ * u φ) -
      Complex.I * (B : ℂ) *
        deriv (fun x => ptrPaperDielectricComplex x * u x) φ =
      ptrPaperDielectricComplex φ *
        ((ν : ℂ) * u φ - Complex.I * (B : ℂ) * du) -
      Complex.I * (B : ℂ) *
        (((-10 : ℝ) * Real.sin (4 * φ) : ℝ) : ℂ) * u φ := by
  have hd := (ptr_paper_dielectric_hasDerivAt φ).mul hu
  have hde : deriv (fun x => ptrPaperDielectricComplex x * u x) φ =
      (((-10 : ℝ) * Real.sin (4 * φ) : ℝ) : ℂ) * u φ +
        ptrPaperDielectricComplex φ * du := by
    have hfun : (fun x => ptrPaperDielectricComplex x * u x) =
        ptrPaperDielectricComplex * u := rfl
    rw [hfun]
    exact hd.deriv
  rw [hde]
  ring

end RHTower
