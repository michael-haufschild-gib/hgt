import GaloisForLFunctions.HTGeometry.QuarticJensenDispersionTransfer
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex

/-!
# Degree-four Jensen polynomials of `Ξ` through the theta dispersions

Pólya's Jensen polynomials of `Ξ` are `J^{d,n}(X) = Σ_j C(d,j) γ(n+j) X^j` with
`γ(k) = k!·m(k)/(2k)!`, where `m(k) = 2∫₀^∞ x^{2k} Φ(x) dx` are the raw even moments of the
theta source (`iteratedDeriv_Xi_zero_eq_rawEvenMoment`). With `b = n + ½`, `t = m(n+1)/m(n)` and
the dispersions `D_l = m(n+l) m(n+l+2)/m(n+l+1)² − 1`, the degree-four polynomial is a positive
multiple of the abstract dispersion quartic at `z = tX/4`:

`J^{4,n}(X) = γ(n)/((b)(b+1)(b+2)(b+3)) · quartic b D₀ D₁ D₂ (tX/4)`.

Hence the dispersion certificate `hyperbolic_quarticPoly` applies to `Ξ` itself: whenever
`b ≥ 2000`, `D₀ b ≤ 1/2`, `|D₀ − D₁| b^{3/2} ≤ 1/8` and `|D₀ − 2D₁ + D₂| b² ≤ 1/5`, the quartic
Jensen polynomial `J^{4,n}` of `Ξ` is hyperbolic. The dispersions are nonnegative because the
even moments are log-convex (Cauchy–Schwarz).
-/

open Polynomial GaloisForLFunctions.SignAlternation HTGeometry.QuarticDispersionTransfer

namespace RHTower

noncomputable section

/-- Pólya's Jensen coefficients of `Ξ`: `γ(k) = k!·m(k)/(2k)!`. -/
def xiJensenCoeff (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * thetaCuspRawEvenMoment k / ((2 * k).factorial : ℝ)

theorem xiJensenCoeff_pos (k : ℕ) : 0 < xiJensenCoeff k := by
  unfold xiJensenCoeff
  have := thetaCuspRawEvenMoment_pos k
  positivity

/-- The `k`-th theta dispersion `m(k) m(k+2)/m(k+1)² − 1`. -/
def thetaDispersion (k : ℕ) : ℝ :=
  thetaCuspRawEvenMoment k * thetaCuspRawEvenMoment (k + 2) /
    thetaCuspRawEvenMoment (k + 1) ^ 2 - 1

/-- Dispersions are nonnegative: the even moments are log-convex. -/
theorem thetaDispersion_nonneg (k : ℕ) : 0 ≤ thetaDispersion k := by
  unfold thetaDispersion
  have h := thetaCuspRawEvenMoment_sq_le_adjacent (k + 1) (by omega)
  simp only [Nat.add_sub_cancel, show k + 1 + 1 = k + 2 from rfl] at h
  have h1 := thetaCuspRawEvenMoment_pos (k + 1)
  rw [sub_nonneg, one_le_div (by positivity)]
  exact h

/-- The moment ratio `t = m(n+1)/m(n)`. -/
def thetaMomentRatio (n : ℕ) : ℝ :=
  thetaCuspRawEvenMoment (n + 1) / thetaCuspRawEvenMoment n

theorem thetaMomentRatio_pos (n : ℕ) : 0 < thetaMomentRatio n :=
  div_pos (thetaCuspRawEvenMoment_pos _) (thetaCuspRawEvenMoment_pos _)

/-- One step of the Jensen coefficient chain:
`γ(k+1) = γ(k) · (m(k+1)/m(k)) / (4 (k + ½))`. -/
theorem xiJensenCoeff_succ (k : ℕ) :
    xiJensenCoeff (k + 1) =
      xiJensenCoeff k * (thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k) /
        (4 * ((k : ℝ) + 1 / 2)) := by
  unfold xiJensenCoeff
  have hf1 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hf2 : ((2 * (k + 1)).factorial : ℝ) =
      (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf1, hf2]
  have hm := thetaCuspRawEvenMoment_pos k
  have hk : (0 : ℝ) < k.factorial := by positivity
  have h2k : (0 : ℝ) < (2 * k).factorial := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have hk3 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
  have hkh : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  field_simp
  ring

/-- **The quartic Jensen polynomial of `Ξ` is the dispersion quartic.**
`J^{4,n}(X) = γ(n)/((b)(b+1)(b+2)(b+3)) · quartic b D₀ D₁ D₂ (tX/4)` with `b = n + ½`. -/
theorem eval_jensenPoly_xi_four (n : ℕ) (X : ℝ) :
    (jensenPoly xiJensenCoeff 4 n).eval X =
      xiJensenCoeff n /
          (((n : ℝ) + 1 / 2) * ((n : ℝ) + 3 / 2) * ((n : ℝ) + 5 / 2) * ((n : ℝ) + 7 / 2)) *
        quartic ((n : ℝ) + 1 / 2) (thetaDispersion n) (thetaDispersion (n + 1))
          (thetaDispersion (n + 2)) (thetaMomentRatio n * X / 4) := by
  have g1 := xiJensenCoeff_succ n
  have g2 := xiJensenCoeff_succ (n + 1)
  have g3 := xiJensenCoeff_succ (n + 2)
  have g4 := xiJensenCoeff_succ (n + 3)
  simp only [show n + 1 + 1 = n + 2 from rfl, show n + 2 + 1 = n + 3 from rfl,
    show n + 3 + 1 = n + 4 from rfl] at g2 g3 g4
  push_cast at g2 g3 g4
  simp only [jensenPoly, Finset.sum_range_succ, Finset.sum_range_zero, eval_add,
    eval_mul, eval_C, eval_pow, eval_X, zero_add, add_zero, pow_zero, mul_one,
    show (4 : ℕ).choose 0 = 1 from rfl, show (4 : ℕ).choose 1 = 4 from rfl,
    show (4 : ℕ).choose 2 = 6 from rfl, show (4 : ℕ).choose 3 = 4 from rfl,
    show (4 : ℕ).choose 4 = 1 from rfl, Nat.cast_one, Nat.cast_ofNat, one_mul]
  rw [g4, g3, g2, g1]
  unfold quartic thetaDispersion thetaMomentRatio
  simp only [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl,
    show n + 2 + 2 = n + 4 from rfl]
  have h0 := thetaCuspRawEvenMoment_pos n
  have h1 := thetaCuspRawEvenMoment_pos (n + 1)
  have h2 := thetaCuspRawEvenMoment_pos (n + 2)
  have h3 := thetaCuspRawEvenMoment_pos (n + 3)
  have hb0 : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hb1 : (0 : ℝ) < (n : ℝ) + 1 + 1 / 2 := by positivity
  have hb2 : (0 : ℝ) < (n : ℝ) + 2 + 1 / 2 := by positivity
  have hb3 : (0 : ℝ) < (n : ℝ) + 3 + 1 / 2 := by positivity
  have hb1' : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
  have hb2' : (0 : ℝ) < (n : ℝ) + 5 / 2 := by positivity
  have hb3' : (0 : ℝ) < (n : ℝ) + 7 / 2 := by positivity
  field_simp
  ring

/-- **Dispersion certificate for the quartic Jensen polynomial of `Ξ`.** If `b = n + ½ ≥ 2000`,
`D₀ b ≤ 1/2`, `|D₀ − D₁| b^{3/2} ≤ 1/8` and `|D₀ − 2D₁ + D₂| b² ≤ 1/5`, then `J^{4,n}` has four
distinct real roots. -/
theorem hyperbolic_jensenPoly_xi_four (n : ℕ) (hn : 2000 ≤ (n : ℝ) + 1 / 2)
    (hK : thetaDispersion n * ((n : ℝ) + 1 / 2) ≤ 1 / 2)
    (hε₁ : |thetaDispersion n - thetaDispersion (n + 1)| *
      (((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2)) ≤ 1 / 8)
    (hε₂ : |thetaDispersion n - 2 * thetaDispersion (n + 1) + thetaDispersion (n + 2)| *
      ((n : ℝ) + 1 / 2) ^ 2 ≤ 1 / 5) :
    Hyperbolic (jensenPoly xiJensenCoeff 4 n) := by
  obtain ⟨hspos, hs_lt, hA, hB, hC, hD, hE⟩ :=
    quartic_signs hn (thetaDispersion_nonneg n) (thetaDispersion_nonneg (n + 1))
      (thetaDispersion_nonneg (n + 2)) hK hε₁ hε₂
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (n : ℝ) + 1 / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (3 * (1 - thetaDispersion n * ((n : ℝ) + 1 / 2)) *
    ((n : ℝ) + 1 / 2)) := ⟨_, rfl⟩
  rw [← hb] at hn hspos hs_lt hA hB hC hD hE hs
  rw [← hs] at hspos hs_lt hB hD
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = thetaMomentRatio n := ⟨_, rfl⟩
  have ht : 0 < t := ht_def ▸ thetaMomentRatio_pos n
  have hc : 0 < xiJensenCoeff n /
      (((n : ℝ) + 1 / 2) * ((n : ℝ) + 3 / 2) * ((n : ℝ) + 5 / 2) * ((n : ℝ) + 7 / 2)) := by
    have := xiJensenCoeff_pos n
    positivity
  have hz : ∀ y : ℝ, t * (4 * y / t) / 4 = y := fun y => by field_simp
  have key : ∀ y y' : ℝ, y < y' → 4 * y / t < 4 * y' / t := fun y y' h => by
    apply div_lt_div_of_pos_right _ ht; linarith
  have heval : ∀ y : ℝ, (jensenPoly xiJensenCoeff 4 n).eval (4 * y / t) =
      xiJensenCoeff n /
          (((n : ℝ) + 1 / 2) * ((n : ℝ) + 3 / 2) * ((n : ℝ) + 5 / 2) * ((n : ℝ) + 7 / 2)) *
        quartic b (thetaDispersion n) (thetaDispersion (n + 1)) (thetaDispersion (n + 2)) y := by
    intro y
    rw [eval_jensenPoly_xi_four, ← ht_def, hz, hb]
  refine hyperbolic_of_alternating (d := 4) (y := fun i => 4 * altPoints b s i / t)
    (natDegree_jensenPoly_le _ _ _) ?_ ?_
  · intro i hi
    interval_cases i <;> apply key <;> simp only [altPoints] <;> linarith
  · intro i hi
    simp only [heval]
    interval_cases i
    · simp only [altPoints, pow_zero, one_mul]; exact mul_pos hc hA
    · simp only [altPoints, pow_one]
      have := mul_neg_of_pos_of_neg hc hB
      linarith
    · simp only [altPoints]; norm_num; exact mul_pos hc hC
    · simp only [altPoints]; norm_num
      have := mul_neg_of_pos_of_neg hc hD
      linarith
    · simp only [altPoints]; norm_num; exact mul_pos hc hE

end

end RHTower
