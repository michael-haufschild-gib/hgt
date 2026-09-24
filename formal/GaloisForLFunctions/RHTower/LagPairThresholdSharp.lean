import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz

/-!
# The exact threshold of the partner-pair positivity

`pairNumerator_nonneg` shows the partner-pair numerator is nonnegative for every ordinate offset `A`
once `4a⁴γ² ≤ X²(σ² − a²)`.  That condition is also necessary: the numerator is
`2σ(X(σ² − a² + A²) + 4a²γA)`, a quadratic in `A` whose vertex value is
`2σ(X²(σ² − a²) − 4a⁴γ²)/X`, so it goes negative at `A = −2a²γ/X` as soon as the condition fails.
The termwise method therefore has an exact wall, and no sharper estimate of the same pair can move
it.

At `σ = 1/2` the condition reads `4(¼ − b)²γ² ≤ (b + γ²)²b` with `b = β(1−β)`, and it follows from
the hyperbolic zero-free condition `β(1−β)γ² ≥ ¼`.  That condition is strictly weaker than RH —
under RH `b = ¼` and `γ² > 41/2` — and it is exactly what moves the unconditional threshold of
`re_lagPoleSeries_nonneg` from `13/25` down to `1/2`, the boundary of the method.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- The partner-pair numerator in vertex form. -/
theorem pairNumerator_eq (X a γ σ A : ℝ) :
    (X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ (2 : ℕ) + A ^ (2 : ℕ))
        + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ (2 : ℕ) + A ^ (2 : ℕ))
      = 2 * σ * (X * (σ ^ (2 : ℕ) - a ^ (2 : ℕ) + A ^ (2 : ℕ)) + 4 * a ^ (2 : ℕ) * γ * A) := by
  ring

/-- **Sharpness.**  If the pair condition fails, the numerator is negative at the vertex. -/
theorem exists_pairNumerator_neg {X a γ σ : ℝ} (hX : 0 < X) (hσ : 0 < σ)
    (hcond : X ^ (2 : ℕ) * (σ ^ (2 : ℕ) - a ^ (2 : ℕ)) < 4 * a ^ (4 : ℕ) * γ ^ (2 : ℕ)) :
    ∃ A : ℝ, (X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ (2 : ℕ) + A ^ (2 : ℕ))
        + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ (2 : ℕ) + A ^ (2 : ℕ)) < 0 := by
  refine ⟨-(2 * a ^ (2 : ℕ) * γ / X), ?_⟩
  rw [pairNumerator_eq]
  have hXne : X ≠ 0 := hX.ne'
  have hvertex : X * (σ ^ (2 : ℕ) - a ^ (2 : ℕ) + (-(2 * a ^ (2 : ℕ) * γ / X)) ^ (2 : ℕ))
        + 4 * a ^ (2 : ℕ) * γ * (-(2 * a ^ (2 : ℕ) * γ / X))
      = (X ^ (2 : ℕ) * (σ ^ (2 : ℕ) - a ^ (2 : ℕ)) - 4 * a ^ (4 : ℕ) * γ ^ (2 : ℕ)) / X := by
    field_simp
    ring
  rw [hvertex]
  refine mul_neg_of_pos_of_neg (by linarith) ?_
  exact div_neg_of_neg_of_pos (by linarith) hX

/-- **The exact pair threshold.**  For `X > 0` and `σ > 0` the partner-pair numerator is
nonnegative at every ordinate offset exactly when `4a⁴γ² ≤ X²(σ² − a²)`. -/
theorem pairNumerator_nonneg_forall_iff {X a γ σ : ℝ} (hX : 0 < X) (hσ : 0 < σ) :
    (∀ A : ℝ, 0 ≤ (X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ (2 : ℕ) + A ^ (2 : ℕ))
        + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ (2 : ℕ) + A ^ (2 : ℕ)))
      ↔ 4 * a ^ (4 : ℕ) * γ ^ (2 : ℕ) ≤ X ^ (2 : ℕ) * (σ ^ (2 : ℕ) - a ^ (2 : ℕ)) := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨A, hA⟩ := exists_pairNumerator_neg (X := X) (a := a) (γ := γ) (σ := σ) hX hσ
      (by linarith [not_le.mp hlt])
    linarith [h A]
  · intro hcond A
    exact pairNumerator_nonneg hX hσ.le hcond

/-- At `σ = 1/2` the pair condition follows from `β(1−β)γ² ≥ 1/4`. -/
theorem pairCondition_half_of_hyperbolic {u γ : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hhyp : 1 / 4 ≤ u * (1 - u) * γ ^ (2 : ℕ)) :
    4 * (u - 1 / 2) ^ (4 : ℕ) * γ ^ (2 : ℕ)
      ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ)
          * ((1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ)) := by
  have hb0 : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hb4 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hg0 : 0 ≤ γ ^ (2 : ℕ) := sq_nonneg γ
  have hsq : (1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ) = u * (1 - u) := by ring
  rw [hsq]
  have hquart : (u - 1 / 2) ^ (4 : ℕ) = (u * (1 - u) - 1 / 4) ^ (2 : ℕ) := by ring
  rw [hquart]
  have hlhs : 4 * (u * (1 - u) - 1 / 4) ^ (2 : ℕ) * γ ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) / 4 := by
    nlinarith [hg0, hb0, hb4]
  have hrhs : γ ^ (2 : ℕ) / 4 ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ) * (u * (1 - u)) := by
    nlinarith [hg0, hb0, hhyp, sq_nonneg (u * (1 - u))]
  linarith

/-- The hyperbolic zero-free condition: every zero copy satisfies `β(1−β)γ² ≥ 1/4`. -/
def HyperbolicZeroFree : Prop :=
  ∀ q : XiZeroCopy,
    1 / 4 ≤ (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) * (q.1 : ℂ).im ^ (2 : ℕ)

/-- The hyperbolic condition is strictly weaker than RH: it holds under RH. -/
theorem hyperbolicZeroFree_of_riemannHypothesis (hRH : RiemannHypothesis) :
    HyperbolicZeroFree := by
  intro q
  have hre := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hγ := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  rw [hre]
  nlinarith [hγ]

/-- **The `1/2` threshold from the hyperbolic condition.**  `Re G(s) ≥ 0` on `Re s > 1/2`. -/
theorem re_lagPoleSeries_nonneg_half_of_hyperbolic (h : HyperbolicZeroFree) {s : ℂ}
    (hs : 1 / 2 < s.re) : 0 ≤ (lagPoleSeries s).re := by
  refine re_lagPoleSeries_nonneg_of_pairs
    (summable_lagTerm_of_lt_re (c := 1 / 2) (fun q => (lagPole_re_lt_half q).le) hs)
    fun q => ?_
  have hu0 := xiZeroCopy_re_pos q
  have hu1 := xiZeroCopy_re_lt_one q
  set u : ℝ := (q.1 : ℂ).re with hu
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  set σ : ℝ := s.re with hσ
  have ha : |u - 1 / 2| < σ := by
    rw [abs_lt]; constructor <;> linarith
  refine re_lagTerm_add_partner_nonneg q ha ?_
  have hhalf := pairCondition_half_of_hyperbolic hu0 hu1 (h q)
  have hX0 : 0 < u * (1 - u) + γ ^ (2 : ℕ) := by
    have := mul_pos hu0 (by linarith : (0:ℝ) < 1 - u)
    positivity
  have hmono : (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ)
        * ((1 / 2 : ℝ) ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ))
      ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ) * (σ ^ (2 : ℕ) - (u - 1 / 2) ^ (2 : ℕ)) := by
    have hXsq : (0 : ℝ) ≤ (u * (1 - u) + γ ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
    have hss : (1 / 2 : ℝ) ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) := by nlinarith
    nlinarith [hXsq, hss]
  linarith

end

end RHTower
