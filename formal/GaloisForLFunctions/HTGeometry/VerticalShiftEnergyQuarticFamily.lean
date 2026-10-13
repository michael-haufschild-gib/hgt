import Mathlib

/-!
# Imaginary energy of even fourth-order steps on a pair-plus-real-pair quartic

For `B ≥ 0` let `p_B = (X² + 1)(X² − B) = X⁴ + (1 − B)X² − B`: one non-real pair `±i` and the real
pair `±√B`. For real `S, P` let `T = 1 − S D² + P D⁴`, i.e. `T q = q − S q'' + P q⁗`. For a symmetric
random variable `X` with moments `m₂ = E X²`, `m₄ = E X⁴`, the vertical average `q ↦ E q(z + iX)`
acts on quartics as `T` with `S = m₂/2`, `P = m₄/24`; `X = ±a` gives `cos(aD)`.

`T p_B = Q(X²)` with `Q(u) = u² + (1 − B − 12S)u + (24P − B − 2S(1 − B))`, and

`Q(2S − 1) = 8S − 20S² + 24P`, for every `B`.

* `sq_add_two_mul_le_one_iff_of_evenStep_root`: when `Q(0) < 0` (exactly one non-real pair) and
  `2S < 1`, the root `iv` of `T p_B` obeys `v² + 2S ≤ 1` iff the margin `8S − 20S² + 24P` is
  `≥ 0`.
* `sq_add_moment_le_one_of_verticalShift_root`: for moments with `m₂² ≤ m₄` and `m₂ < 1` the
  margin is `4m₂ − 5m₂² + m₄ ≥ 4m₂(1 − m₂) ≥ 0`, so every vertical average obeys
  `v² + m₂ ≤ (Im i)² = 1`.
* `cosineStep_margin`: for `X = ±a` the margin is exactly `4a²(1 − a²)`; equality `m₄ = m₂²`
  characterises the cosine step, which is therefore extremal.
* `exists_laguerreStep_root_energy_gt`: the single Laguerre step `q − c q''` (`P = 0`) with
  `c = 9/20` has an imaginary root `iv` of `p₀ = X²(X² + 1)` with `v² + 2c > 1`.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quartic `(X² + 1)(X² − B)`. -/
def pairRealPairQuartic (B : ℝ) : ℝ[X] := X ^ 4 + C (1 - B) * X ^ 2 - C B

/-- The even fourth-order step `q ↦ q − S q'' + P q⁗`. -/
def evenQuarticStep (S P : ℝ) (q : ℝ[X]) : ℝ[X] :=
  q - C S * derivative (derivative q) + C P * derivative (derivative (derivative (derivative q)))

/-- The quadratic `Q` with `T p_B = Q(X²)`. -/
def evenStepQuadratic (B S P u : ℝ) : ℝ :=
  u ^ 2 + (1 - B - 12 * S) * u + (24 * P - B - 2 * S * (1 - B))

theorem evenQuarticStep_pairRealPairQuartic (B S P : ℝ) :
    evenQuarticStep S P (pairRealPairQuartic B) =
      X ^ 4 + C (1 - B - 12 * S) * X ^ 2 + C (24 * P - B - 2 * S * (1 - B)) := by
  apply Polynomial.funext; intro x
  simp [evenQuarticStep, pairRealPairQuartic, derivative_mul]
  ring

theorem evenQuarticStep_eval_mul_I (B S P v : ℝ) :
    ((evenQuarticStep S P (pairRealPairQuartic B)).map ofRealHom).eval ((v : ℂ) * I) =
      (evenStepQuadratic B S P (-v ^ 2) : ℂ) := by
  rw [evenQuarticStep_pairRealPairQuartic, evenStepQuadratic]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, eval_add,
    eval_mul, eval_pow, eval_X, eval_C, ofRealHom_eq_coe]
  push_cast
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  rw [mul_pow, mul_pow, hI4, I_sq]
  ring

/-- `Q(2S − 1) = 8S − 20S² + 24P`, independently of `B`. -/
theorem evenStepQuadratic_two_mul_sub_one (B S P : ℝ) :
    evenStepQuadratic B S P (2 * S - 1) = 8 * S - 20 * S ^ 2 + 24 * P := by
  unfold evenStepQuadratic; ring

/-- Splitting of `Q` at a known root `u₁`: `Q(u) = (u − u₁)(u − u₂)` with `u₂ = −(1 − B − 12S) − u₁`. -/
theorem evenStepQuadratic_eq_mul {B S P u₁ : ℝ} (h : evenStepQuadratic B S P u₁ = 0) (u : ℝ) :
    evenStepQuadratic B S P u = (u - u₁) * (u - (-(1 - B - 12 * S) - u₁)) := by
  unfold evenStepQuadratic at h ⊢; linear_combination h

/-- **Energy law on the family.** If `T p_B` has the imaginary root `iv`, `Q(0) < 0` and `2S < 1`,
then a nonnegative margin `8S − 20S² + 24P` gives `v² + 2S ≤ 1`. -/
theorem sq_add_two_mul_le_one_of_evenStep_root {B S P v : ℝ}
    (hroot : ((evenQuarticStep S P (pairRealPairQuartic B)).map ofRealHom).eval ((v : ℂ) * I) = 0)
    (hQ0 : evenStepQuadratic B S P 0 < 0) (hS : 2 * S < 1)
    (hmarg : 0 ≤ 8 * S - 20 * S ^ 2 + 24 * P) : v ^ 2 + 2 * S ≤ 1 := by
  rw [evenQuarticStep_eval_mul_I] at hroot
  have hr : evenStepQuadratic B S P (-v ^ 2) = 0 := by exact_mod_cast hroot
  have hsplit := evenStepQuadratic_eq_mul hr
  have h0 := hsplit 0
  have h1 := hsplit (2 * S - 1)
  rw [evenStepQuadratic_two_mul_sub_one] at h1
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hu2 : 0 < -(1 - B - 12 * S) - -v ^ 2 := by nlinarith
  have hfac : (2 * S - 1 - -v ^ 2) * (2 * S - 1 - (-(1 - B - 12 * S) - -v ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-- **Necessity.** A negative margin puts `2S − 1` strictly between the roots of `Q`, so the root
`iv` has `v² + 2S > 1`. -/
theorem one_lt_sq_add_two_mul_of_evenStep_root {B S P v : ℝ}
    (hroot : ((evenQuarticStep S P (pairRealPairQuartic B)).map ofRealHom).eval ((v : ℂ) * I) = 0)
    (hQ0 : evenStepQuadratic B S P 0 < 0) (hS : 2 * S < 1)
    (hmarg : 8 * S - 20 * S ^ 2 + 24 * P < 0) : 1 < v ^ 2 + 2 * S := by
  rw [evenQuarticStep_eval_mul_I] at hroot
  have hr : evenStepQuadratic B S P (-v ^ 2) = 0 := by exact_mod_cast hroot
  have hsplit := evenStepQuadratic_eq_mul hr
  have h0 := hsplit 0
  have h1 := hsplit (2 * S - 1)
  rw [evenStepQuadratic_two_mul_sub_one] at h1
  by_contra hcon
  replace hcon := le_of_not_gt hcon
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hu2 : 0 < -(1 - B - 12 * S) - -v ^ 2 := by nlinarith
  have hfac : 0 ≤ (2 * S - 1 - -v ^ 2) * (2 * S - 1 - (-(1 - B - 12 * S) - -v ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  linarith

/-- **Exact energy law on the family.** With one non-real pair and `2S < 1`, the imaginary root `iv`
of `T p_B` obeys `v² + 2S ≤ 1 = (Im i)²` iff `0 ≤ 8S − 20S² + 24P`. -/
theorem sq_add_two_mul_le_one_iff_of_evenStep_root {B S P v : ℝ}
    (hroot : ((evenQuarticStep S P (pairRealPairQuartic B)).map ofRealHom).eval ((v : ℂ) * I) = 0)
    (hQ0 : evenStepQuadratic B S P 0 < 0) (hS : 2 * S < 1) :
    v ^ 2 + 2 * S ≤ 1 ↔ 0 ≤ 8 * S - 20 * S ^ 2 + 24 * P :=
  ⟨fun h => le_of_not_gt fun hm => (one_lt_sq_add_two_mul_of_evenStep_root hroot hQ0 hS hm).not_ge h,
    sq_add_two_mul_le_one_of_evenStep_root hroot hQ0 hS⟩

/-- The margin of a vertical average with moments `m₂, m₄` (`S = m₂/2`, `P = m₄/24`). -/
theorem verticalShift_margin (m₂ m₄ : ℝ) :
    8 * (m₂ / 2) - 20 * (m₂ / 2) ^ 2 + 24 * (m₄ / 24) = 4 * m₂ - 5 * m₂ ^ 2 + m₄ := by ring

/-- **Every vertical average obeys the energy law on the family.** For moments with `m₂² ≤ m₄`
(Cauchy–Schwarz for a random shift) and `0 ≤ m₂ < 1`, an imaginary root `iv` of the averaged
quartic with one non-real pair satisfies `v² + m₂ ≤ 1`, where `1` is the energy of `p_B`. -/
theorem sq_add_moment_le_one_of_verticalShift_root {B m₂ m₄ v : ℝ} (hm₂ : 0 ≤ m₂) (hm₂1 : m₂ < 1)
    (hcs : m₂ ^ 2 ≤ m₄)
    (hroot : ((evenQuarticStep (m₂ / 2) (m₄ / 24) (pairRealPairQuartic B)).map ofRealHom).eval
      ((v : ℂ) * I) = 0)
    (hQ0 : evenStepQuadratic B (m₂ / 2) (m₄ / 24) 0 < 0) : v ^ 2 + m₂ ≤ 1 := by
  have h := sq_add_two_mul_le_one_of_evenStep_root hroot hQ0 (by linarith)
    (by rw [verticalShift_margin]; nlinarith)
  linarith

/-- **The cosine step is extremal.** For `X = ±a` (`m₂ = a²`, `m₄ = a⁴`, the equality case of
`m₂² ≤ m₄`) the margin is exactly `4a²(1 − a²)`, which vanishes when the pair dies at `a = 1`. -/
theorem cosineStep_margin (a : ℝ) :
    8 * (a ^ 2 / 2) - 20 * (a ^ 2 / 2) ^ 2 + 24 * (a ^ 4 / 24) = 4 * a ^ 2 * (1 - a ^ 2) := by ring

/-- **A single Laguerre step breaks the law.** For `p₀ = X²(X² + 1)` (energy `1`) and the step
`q ↦ q − (9/20) q''`, there is an imaginary root `iv` of the stepped quartic with
`v² + 2·(9/20) > 1`. -/
theorem exists_laguerreStep_root_energy_gt :
    ∃ v : ℝ, 0 < v ∧
      ((evenQuarticStep (9 / 20) 0 (pairRealPairQuartic 0)).map ofRealHom).eval ((v : ℂ) * I) = 0 ∧
      1 < v ^ 2 + 2 * (9 / 20) := by
  -- `Q(u) = u² − (22/5)u − 9/10`, negative root `u₁ = (22/5 − √D)/2`, `D = (22/5)² + 18/5`.
  set D : ℝ := (22 / 5) ^ 2 + 18 / 5 with hD
  have hDpos : 0 ≤ D := by positivity
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos
  have hs0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hgt : 22 / 5 < Real.sqrt D := by
    rw [show (22 / 5 : ℝ) = Real.sqrt ((22 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by rw [hD]; norm_num)
  set u₁ : ℝ := (22 / 5 - Real.sqrt D) / 2 with hu₁
  have hu₁neg : u₁ < 0 := by rw [hu₁]; linarith
  have hQ : evenStepQuadratic 0 (9 / 20) 0 u₁ = 0 := by
    have hsq' : Real.sqrt D ^ 2 = (22 / 5) ^ 2 + 18 / 5 := by rw [hsq, hD]
    unfold evenStepQuadratic; rw [hu₁]; linear_combination (1 / 4 : ℝ) * hsq'
  refine ⟨Real.sqrt (-u₁), Real.sqrt_pos.mpr (by linarith), ?_, ?_⟩
  · rw [evenQuarticStep_eval_mul_I, Real.sq_sqrt (by linarith), neg_neg, hQ]; simp
  · rw [Real.sq_sqrt (by linarith)]
    -- `Q(2c − 1) = 8c − 20c² < 0` puts `2c − 1` strictly between the roots.
    have hsplit := evenStepQuadratic_eq_mul hQ
    have h1 := hsplit (2 * (9 / 20) - 1)
    rw [evenStepQuadratic_two_mul_sub_one] at h1
    have h0 := hsplit 0
    have hQ0 : evenStepQuadratic 0 (9 / 20) 0 0 = -(9 / 10) := by unfold evenStepQuadratic; norm_num
    rw [hQ0] at h0
    by_contra hcon
    replace hcon := le_of_not_gt hcon
    have hu₂ : 0 < -(1 - 0 - 12 * (9 / 20)) - u₁ := by nlinarith
    have : 0 ≤ (2 * (9 / 20) - 1 - u₁) * (2 * (9 / 20) - 1 - (-(1 - 0 - 12 * (9 / 20)) - u₁)) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    norm_num at h1 this
    linarith

end

end GaloisForLFunctions.HTGeometry
