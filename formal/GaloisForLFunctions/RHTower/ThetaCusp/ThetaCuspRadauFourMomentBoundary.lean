import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNormalizedShiftedGramStrict

/-!
# Four-moment Radau boundary for the theta source

Every offset of the normalized even theta moments has a strictly positive Hankel matrix.
The first four moments determine a quadratic whose two positive roots are the positive
nodes of the three-atom Radau endpoint law.  The zero-node mass is the ordinary size-three
Hankel determinant divided by the second shifted size-two determinant.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Every nonnegative offset of the raw even theta moments has a positive definite Hankel
matrix.  The offset is realized by selecting one parity class from the full theta moment matrix. -/
theorem thetaCuspRawEvenMoment_offsetHankel_posDef (k n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + k)) n).PosDef := by
  classical
  let N : ℕ := 2 * (n + k) + 1
  let e : Fin n → Fin N := fun i => ⟨2 * (i : ℕ) + k, by
    dsimp [N]
    omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp [e] at hval
    omega
  let H : Matrix (Fin N) (Fin N) ℝ :=
    HTGeometry.momentHankelMatrix (thetaTiltMoment 0) N
  have hH : H.PosDef :=
    HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
      (thetaTiltMoment 0) (fun j => thetaTiltMoment_eq_integral_measure j)
      (integrable_pow_thetaTiltMeasure_global 0)
      (thetaTiltMeasure_compl_finset_pos 0) N
  have hS : (H.submatrix e e).PosDef := hH.submatrix he
  have hEq : H.submatrix e e =
      HTGeometry.momentHankelMatrix
        (fun j => thetaCuspRawEvenMoment (j + k)) n := by
    ext i j
    change thetaTiltMoment 0 ((2 * (i : ℕ) + k) + (2 * (j : ℕ) + k)) =
      thetaCuspRawEvenMoment (((i : ℕ) + (j : ℕ)) + k)
    rw [show (2 * (i : ℕ) + k) + (2 * (j : ℕ) + k) =
      2 * (((i : ℕ) + (j : ℕ)) + k) by omega,
      thetaTiltMoment_zero_even_eq_raw]
  rwa [hEq] at hS

/-- Every offset normalized even-moment Hankel determinant is positive. -/
theorem thetaCuspNormalizedEvenMoment_offsetHankel_det_pos (k n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspNormalizedEvenMoment (j + k)) n).det := by
  let R : Matrix (Fin n) (Fin n) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + k)) n
  let T : Matrix (Fin n) (Fin n) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun j => thetaCuspNormalizedEvenMoment (j + k)) n
  have hR : 0 < R.det := (thetaCuspRawEvenMoment_offsetHankel_posDef k n).det_pos
  have hEq : T = (thetaCuspRawEvenMoment 0)⁻¹ • R := by
    ext i j
    change thetaCuspRawEvenMoment ((i : ℕ) + (j : ℕ) + k) /
        thetaCuspRawEvenMoment 0 =
      (thetaCuspRawEvenMoment 0)⁻¹ *
        thetaCuspRawEvenMoment ((i : ℕ) + (j : ℕ) + k)
    rw [div_eq_mul_inv]
    ring
  change 0 < T.det
  rw [hEq, Matrix.det_smul]
  exact mul_pos (pow_pos (inv_pos.mpr thetaCuspRawEvenMoment_zero_pos) _) hR

/-- The second shifted size-two minor, needed to recover the zero-node Radau mass. -/
theorem thetaCuspNormalizedEvenMoment_shifted_s_pos :
    0 < thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 4 -
      thetaCuspNormalizedEvenMoment 3 ^ 2 := by
  have h := thetaCuspNormalizedEvenMoment_offsetHankel_det_pos 2 2
  simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two, pow_two] using h

/-- The ordinary size-three theta moment determinant is strictly positive. -/
theorem thetaCuspNormalizedEvenMoment_ordinary_D_pos :
    0 < (thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 4 -
      thetaCuspNormalizedEvenMoment 3 ^ 2) -
      thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 4 +
      2 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 2 *
        thetaCuspNormalizedEvenMoment 3 -
      thetaCuspNormalizedEvenMoment 2 ^ 3 := by
  have h := thetaCuspNormalizedEvenMoment_offsetHankel_det_pos 0 3
  have hzero : thetaCuspNormalizedEvenMoment 0 = 1 := by
    simp [thetaCuspNormalizedEvenMoment, thetaCuspRawEvenMoment_zero_pos.ne']
  convert h using 1
  simp [HTGeometry.momentHankelMatrix, Matrix.det_fin_three, hzero]
  ring

/-- The Radau quadratic has two positive distinct real roots.  Its discriminant is a
square plus four times the strictly positive shifted size-two determinant. -/
theorem thetaCuspRadau_quadratic_data :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ 2
    let s := b * e - c ^ 2
    let alpha := (a * e - b * c) / q
    0 < a ∧ 0 < q ∧ 0 < s ∧ 0 < alpha ∧
      0 < alpha ^ 2 - 4 * s / q := by
  let q : ℝ := thetaCuspNormalizedEvenMoment 1 *
    thetaCuspNormalizedEvenMoment 3 - thetaCuspNormalizedEvenMoment 2 ^ 2
  let s : ℝ := thetaCuspNormalizedEvenMoment 2 *
    thetaCuspNormalizedEvenMoment 4 - thetaCuspNormalizedEvenMoment 3 ^ 2
  dsimp only
  have ha : 0 < thetaCuspNormalizedEvenMoment 1 := by
    exact div_pos (thetaCuspRawEvenMoment_pos 1) thetaCuspRawEvenMoment_zero_pos
  have hc : 0 < thetaCuspNormalizedEvenMoment 3 := by
    exact div_pos (thetaCuspRawEvenMoment_pos 3) thetaCuspRawEvenMoment_zero_pos
  have hq := thetaCuspNormalizedEvenMoment_shifted_q_pos
  have hs := thetaCuspNormalizedEvenMoment_shifted_s_pos
  have hcross : 0 < thetaCuspNormalizedEvenMoment 1 *
      thetaCuspNormalizedEvenMoment 4 -
      thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 := by
    have hident : thetaCuspNormalizedEvenMoment 2 *
        (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 -
          thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3) =
        thetaCuspNormalizedEvenMoment 1 *
          (thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 4 -
            thetaCuspNormalizedEvenMoment 3 ^ 2) +
        thetaCuspNormalizedEvenMoment 3 *
          (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
            thetaCuspNormalizedEvenMoment 2 ^ 2) := by ring
    have hb : 0 < thetaCuspNormalizedEvenMoment 2 := by
      exact div_pos (thetaCuspRawEvenMoment_pos 2) thetaCuspRawEvenMoment_zero_pos
    nlinarith [hident, mul_pos ha hs, mul_pos hc hq]
  have halpha : 0 < (thetaCuspNormalizedEvenMoment 1 *
      thetaCuspNormalizedEvenMoment 4 -
      thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3) /
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
        thetaCuspNormalizedEvenMoment 2 ^ 2) := div_pos hcross hq
  have hdisc :
      ((thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 -
        thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3) / q) ^ 2 -
      4 * s / q =
      (((thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 -
        thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3) / q) -
        2 * thetaCuspNormalizedEvenMoment 2 / thetaCuspNormalizedEvenMoment 1) ^ 2 +
      4 * q / thetaCuspNormalizedEvenMoment 1 ^ 2 := by
    dsimp only [q, s]
    field_simp [ha.ne', hq.ne']
    ring
  dsimp only [q, s] at hdisc
  refine ⟨ha, hq, hs, halpha, ?_⟩
  rw [hdisc]
  have hfrac : 0 < (thetaCuspNormalizedEvenMoment 1 *
      thetaCuspNormalizedEvenMoment 3 -
      thetaCuspNormalizedEvenMoment 2 ^ 2) /
        thetaCuspNormalizedEvenMoment 1 ^ 2 :=
    div_pos hq (sq_pos_of_pos ha)
  positivity

/-- The zero-node mass of the four-moment Radau law is a strictly positive fraction.
The formula uses only the first four actual theta moments. -/
theorem thetaCuspRadau_zero_mass_pos :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ 2
    let alpha := (a * e - b * c) / q
    let beta := (c ^ 2 - b * e) / q
    0 < 1 - (a * alpha - b) / (-beta) := by
  let a : ℝ := thetaCuspNormalizedEvenMoment 1
  let b : ℝ := thetaCuspNormalizedEvenMoment 2
  let c : ℝ := thetaCuspNormalizedEvenMoment 3
  let e : ℝ := thetaCuspNormalizedEvenMoment 4
  let q : ℝ := a * c - b ^ 2
  let s : ℝ := b * e - c ^ 2
  dsimp only
  have hq : 0 < q := thetaCuspNormalizedEvenMoment_shifted_q_pos
  have hs : 0 < s := thetaCuspNormalizedEvenMoment_shifted_s_pos
  have hD : 0 < s - a ^ 2 * e + 2 * a * b * c - b ^ 3 :=
    thetaCuspNormalizedEvenMoment_ordinary_D_pos
  have hden : -((c ^ 2 - b * e) / q) = s / q := by
    dsimp [s]
    ring
  have hident :
      1 - (a * ((a * e - b * c) / q) - b) /
        (-((c ^ 2 - b * e) / q)) =
      (s - a ^ 2 * e + 2 * a * b * c - b ^ 3) / s := by
    rw [hden]
    field_simp [hq.ne', hs.ne']
    ring
  change 0 < 1 - (a * ((a * e - b * c) / q) - b) /
      (-((c ^ 2 - b * e) / q))
  rw [hident]
  exact div_pos hD hs

/-- The quadratic fixed by the first four theta moments has two positive nodes, with the
size-biased mean strictly between them. -/
theorem thetaCuspRadau_positive_nodes :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ 2
    let s := b * e - c ^ 2
    let alpha := (a * e - b * c) / q
    ∃ r₁ r₂ : ℝ,
      0 < r₁ ∧ r₁ < b / a ∧ b / a < r₂ ∧
        r₁ + r₂ = alpha ∧ r₁ * r₂ = s / q := by
  let a : ℝ := thetaCuspNormalizedEvenMoment 1
  let b : ℝ := thetaCuspNormalizedEvenMoment 2
  let c : ℝ := thetaCuspNormalizedEvenMoment 3
  let e : ℝ := thetaCuspNormalizedEvenMoment 4
  let q : ℝ := a * c - b ^ 2
  let s : ℝ := b * e - c ^ 2
  let alpha : ℝ := (a * e - b * c) / q
  let delta : ℝ := alpha ^ 2 - 4 * s / q
  have hdata : 0 < a ∧ 0 < q ∧ 0 < s ∧ 0 < alpha ∧ 0 < delta :=
    thetaCuspRadau_quadratic_data
  rcases hdata with ⟨ha, hq, hs, halpha, hdelta⟩
  let r₁ : ℝ := (alpha - Real.sqrt delta) / 2
  let r₂ : ℝ := (alpha + Real.sqrt delta) / 2
  have hsdiv : 0 < s / q := div_pos hs hq
  have hsqrt_sq : (Real.sqrt delta) ^ 2 = delta := Real.sq_sqrt hdelta.le
  have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqrt_lt : Real.sqrt delta < alpha := by
    have hdlt : delta < alpha ^ 2 := by
      have hfour : 0 < 4 * s / q := div_pos (mul_pos (by positivity) hs) hq
      change alpha ^ 2 - 4 * s / q < alpha ^ 2
      exact sub_lt_self _ hfour
    nlinarith [hsqrt_sq, Real.sqrt_nonneg delta]
  have hr₁pos : 0 < r₁ := by dsimp [r₁]; linarith
  have hr₁₂ : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
  have hsum : r₁ + r₂ = alpha := by dsimp [r₁, r₂]; ring
  have hprod : r₁ * r₂ = s / q := by
    calc
      r₁ * r₂ = (alpha ^ 2 - (Real.sqrt delta) ^ 2) / 4 := by
        dsimp [r₁, r₂]
        ring
      _ = (alpha ^ 2 - delta) / 4 := by rw [hsqrt_sq]
      _ = s / q := by dsimp [delta]; ring
  have hQmean : (b / a) ^ 2 - alpha * (b / a) + s / q = -q / a ^ 2 := by
    dsimp [alpha, s]
    field_simp [ha.ne', hq.ne']
    dsimp [q]
    ring
  have hfactor : (b / a - r₁) * (b / a - r₂) = -q / a ^ 2 := by
    rw [← hsum, ← hprod] at hQmean
    nlinarith [hQmean]
  have hnegative : (b / a - r₁) * (b / a - r₂) < 0 := by
    rw [hfactor]
    have hqp : 0 < q / a ^ 2 := div_pos hq (sq_pos_of_pos ha)
    rw [neg_div]
    linarith only [hqp]
  have hleft : r₁ < b / a := by
    by_contra h
    have hmean : b / a ≤ r₁ := le_of_not_gt h
    have hother : b / a ≤ r₂ := hmean.trans hr₁₂.le
    have hproduct : 0 ≤ (b / a - r₁) * (b / a - r₂) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hmean) (sub_nonpos.mpr hother)
    linarith
  have hright : b / a < r₂ := by
    by_contra h
    have hmean : r₂ ≤ b / a := le_of_not_gt h
    have hother : r₁ ≤ b / a := hr₁₂.le.trans hmean
    have hproduct : 0 ≤ (b / a - r₁) * (b / a - r₂) :=
      mul_nonneg (sub_nonneg.mpr hother) (sub_nonneg.mpr hmean)
    linarith
  dsimp only
  exact ⟨r₁, r₂, hr₁pos, hleft, hright, hsum, hprod⟩

/-- Positive two-node quadrature weights reproduce the first four size-biased theta moments.
The remaining mass at zero is positive, so the corresponding three-atom law is positive. -/
theorem thetaCuspRadau_positive_weights :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ 2
    ∃ r₁ r₂ w₁ w₂ : ℝ,
      0 < r₁ ∧ r₁ < r₂ ∧ 0 < w₁ ∧ 0 < w₂ ∧
        w₁ + w₂ = a ∧
        w₁ * r₁ + w₂ * r₂ = b ∧
        w₁ * r₁ ^ 2 + w₂ * r₂ ^ 2 = c ∧
        w₁ * r₁ ^ 3 + w₂ * r₂ ^ 3 = e ∧
        w₁ * r₁ ^ 4 + w₂ * r₂ ^ 4 =
          (a * e ^ 2 - 2 * b * c * e + c ^ 3) / q ∧
        0 < 1 - w₁ / r₁ - w₂ / r₂ := by
  let a : ℝ := thetaCuspNormalizedEvenMoment 1
  let b : ℝ := thetaCuspNormalizedEvenMoment 2
  let c : ℝ := thetaCuspNormalizedEvenMoment 3
  let e : ℝ := thetaCuspNormalizedEvenMoment 4
  let q : ℝ := a * c - b ^ 2
  let s : ℝ := b * e - c ^ 2
  let alpha : ℝ := (a * e - b * c) / q
  have hdata : 0 < a ∧ 0 < q ∧ 0 < s ∧ 0 < alpha ∧
      0 < alpha ^ 2 - 4 * s / q := thetaCuspRadau_quadratic_data
  rcases hdata with ⟨ha, hq, hs, _, _⟩
  obtain ⟨r₁, r₂, hr₁, hleft, hright, hsum, hprod⟩ :=
    thetaCuspRadau_positive_nodes
  have hr₁₂ : r₁ < r₂ := hleft.trans hright
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hdiff : 0 < r₂ - r₁ := sub_pos.mpr hr₁₂
  let w₁ : ℝ := (a * r₂ - b) / (r₂ - r₁)
  let w₂ : ℝ := (b - a * r₁) / (r₂ - r₁)
  have hw₁ : 0 < w₁ := by
    have hn : b < r₂ * a := (div_lt_iff₀ ha).mp hright
    apply div_pos _ hdiff
    nlinarith
  have hw₂ : 0 < w₂ := by
    have hn : r₁ * a < b := (lt_div_iff₀ ha).mp hleft
    apply div_pos _ hdiff
    nlinarith
  have hw0 : w₁ + w₂ = a := by
    dsimp [w₁, w₂]
    field_simp [hdiff.ne']
    ring
  have hw1 : w₁ * r₁ + w₂ * r₂ = b := by
    dsimp [w₁, w₂]
    field_simp [hdiff.ne']
    ring
  have hrec2 : alpha * b - (s / q) * a = c := by
    dsimp [alpha, s]
    field_simp [hq.ne']
    dsimp [q]
    ring
  have hrec3 : alpha * c - (s / q) * b = e := by
    dsimp [alpha, s]
    field_simp [hq.ne']
    dsimp [q]
    ring
  have hw2 : w₁ * r₁ ^ 2 + w₂ * r₂ ^ 2 = c := by
    calc
      w₁ * r₁ ^ 2 + w₂ * r₂ ^ 2 =
          (r₁ + r₂) * (w₁ * r₁ + w₂ * r₂) -
            r₁ * r₂ * (w₁ + w₂) := by ring
      _ = alpha * b - (s / q) * a := by rw [hsum, hprod, hw1, hw0]
      _ = c := hrec2
  have hw3 : w₁ * r₁ ^ 3 + w₂ * r₂ ^ 3 = e := by
    calc
      w₁ * r₁ ^ 3 + w₂ * r₂ ^ 3 =
          (r₁ + r₂) * (w₁ * r₁ ^ 2 + w₂ * r₂ ^ 2) -
            r₁ * r₂ * (w₁ * r₁ + w₂ * r₂) := by ring
      _ = alpha * c - (s / q) * b := by rw [hsum, hprod, hw2, hw1]
      _ = e := hrec3
  have hrec4 : alpha * e - (s / q) * c =
      (a * e ^ 2 - 2 * b * c * e + c ^ 3) / q := by
    dsimp [alpha, s]
    field_simp [hq.ne']
    ring
  have hw4 : w₁ * r₁ ^ 4 + w₂ * r₂ ^ 4 =
      (a * e ^ 2 - 2 * b * c * e + c ^ 3) / q := by
    calc
      w₁ * r₁ ^ 4 + w₂ * r₂ ^ 4 =
          (r₁ + r₂) * (w₁ * r₁ ^ 3 + w₂ * r₂ ^ 3) -
            r₁ * r₂ * (w₁ * r₁ ^ 2 + w₂ * r₂ ^ 2) := by ring
      _ = alpha * e - (s / q) * c := by rw [hsum, hprod, hw3, hw2]
      _ = (a * e ^ 2 - 2 * b * c * e + c ^ 3) / q := hrec4
  have hquot : w₁ / r₁ + w₂ / r₂ = (a * alpha - b) / (s / q) := by
    have hfirst : w₁ / r₁ + w₂ / r₂ =
        (w₁ * r₂ + w₂ * r₁) / (r₁ * r₂) := by
      field_simp [hr₁.ne', hr₂.ne']
    have hnume : w₁ * r₂ + w₂ * r₁ = a * alpha - b := by
      calc
        w₁ * r₂ + w₂ * r₁ =
            (w₁ + w₂) * (r₁ + r₂) -
              (w₁ * r₁ + w₂ * r₂) := by ring
        _ = a * alpha - b := by rw [hw0, hsum, hw1]
    rw [hfirst, hnume, hprod]
  have hmass : 0 < 1 - (a * alpha - b) / (s / q) := by
    have h := thetaCuspRadau_zero_mass_pos
    change 0 < 1 - (a * alpha - b) / (-((c ^ 2 - b * e) / q)) at h
    have hden : -((c ^ 2 - b * e) / q) = s / q := by
      dsimp [s]
      ring
    rwa [hden] at h
  have hremain : 0 < 1 - w₁ / r₁ - w₂ / r₂ := by
    calc
      0 < 1 - (w₁ / r₁ + w₂ / r₂) := by rw [hquot]; exact hmass
      _ = 1 - w₁ / r₁ - w₂ / r₂ := by ring
  dsimp only
  exact ⟨r₁, r₂, w₁, w₂, hr₁, hr₁₂, hw₁, hw₂, hw0, hw1, hw2, hw3, hw4, hremain⟩

end

end RHTower
