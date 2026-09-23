import GaloisForLFunctions.RHTower.Sieve.CurvedPhaseBlockSum

/-!
# The difference of two near-diagonal phases

A Cauchy--Schwarz in the type-II half of Vaughan's identity replaces the phase
`F_{T,r}(d·m)` by the DIFFERENCE `F_{T,r}(d m₁) − F_{T,r}(d m₂)`, which by the dilation identity is
`F_{T,s₁}(d) − F_{T,s₂}(d)` with `s_i = r/m_i`.  The exact algebraic identity

`F''_{s₁}(u) − F''_{s₂}(u) = (T/2π)·(s₁−s₂)(2u+s₁+s₂)/((u+s₁)²(u+s₂)²)`

— the cross terms cancel because `s(2u+s) = (u+s)² − u²` — shows that the difference has exactly
the same reciprocal-cube curvature profile, at scale `T(s₁−s₂)`.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- The difference of two near-diagonal phases. -/
def diffPhase (T s₁ s₂ u : ℝ) : ℝ := nearDiagonalPhase T s₁ u - nearDiagonalPhase T s₂ u

/-- Its first derivative. -/
def diffPhaseD1 (T s₁ s₂ u : ℝ) : ℝ := nearDiagonalPhaseD1 T s₁ u - nearDiagonalPhaseD1 T s₂ u

/-- Its second derivative. -/
def diffPhaseD2 (T s₁ s₂ u : ℝ) : ℝ := nearDiagonalPhaseD2 T s₁ u - nearDiagonalPhaseD2 T s₂ u

theorem hasDerivAt_diffPhase (T : ℝ) {s₁ s₂ u : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hu : 0 < u) :
    HasDerivAt (diffPhase T s₁ s₂) (diffPhaseD1 T s₁ s₂ u) u :=
  (hasDerivAt_nearDiagonalPhase T hs₁ hu).sub (hasDerivAt_nearDiagonalPhase T hs₂ hu)

theorem hasDerivAt_diffPhaseD1 (T : ℝ) {s₁ s₂ u : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hu : 0 < u) :
    HasDerivAt (diffPhaseD1 T s₁ s₂) (diffPhaseD2 T s₁ s₂ u) u :=
  (hasDerivAt_nearDiagonalPhaseD1 T hs₁ hu).sub (hasDerivAt_nearDiagonalPhaseD1 T hs₂ hu)

/-- **The exact curvature identity.**  The cross terms cancel because `s(2u+s) = (u+s)² − u²`. -/
theorem diffPhaseD2_eq (T : ℝ) {s₁ s₂ u : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hu : 0 < u) :
    diffPhaseD2 T s₁ s₂ u
      = T / (2 * Real.pi)
          * ((s₁ - s₂) * (2 * u + s₁ + s₂) / ((u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ))) := by
  have hu1 : (0 : ℝ) < u + s₁ := by linarith
  have hu2 : (0 : ℝ) < u + s₂ := by linarith
  rw [diffPhaseD2, nearDiagonalPhaseD2, nearDiagonalPhaseD2]
  field_simp
  ring

/-- The curvature identity, as a single fraction. -/
theorem diffPhaseD2_eq' (T : ℝ) {s₁ s₂ u : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hu : 0 < u) :
    diffPhaseD2 T s₁ s₂ u
      = T * ((s₁ - s₂) * (2 * u + s₁ + s₂))
          / (2 * Real.pi * ((u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu1 : (0 : ℝ) < u + s₁ := by linarith
  have hu2 : (0 : ℝ) < u + s₂ := by linarith
  rw [diffPhaseD2_eq T hs₁ hs₂ hu]
  field_simp

/-- Lower curvature bound for the difference phase on a dyadic block. -/
theorem curvedLambda_le_diffPhaseD2 {T s₁ s₂ M u : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂)
    (hs : s₂ ≤ s₁) (hM : 4 * s₁ ≤ M) (hM0 : 0 < M) (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    curvedLambda (T * (s₁ - s₂)) M ≤ diffPhaseD2 T s₁ s₂ u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) ≤ s₁ := le_trans hs₂ hs
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM0 hu1
  have hus₁ : (0 : ℝ) < u + s₁ := by linarith
  have hus₂ : (0 : ℝ) < u + s₂ := by linarith
  have hΔ : (0 : ℝ) ≤ s₁ - s₂ := by linarith
  have hcoef : (0 : ℝ) ≤ T * (s₁ - s₂) * Real.pi :=
    mul_nonneg (mul_nonneg hT.le hΔ) hpi.le
  have hkey : 2 * ((u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ)) ≤ 36 * M ^ (3 : ℕ) * (2 * u + s₁ + s₂) := by
    have h1 : u + s₁ ≤ 9 / 4 * M := by linarith
    have h2 : u + s₂ ≤ 9 / 4 * M := by linarith
    have h3 : (2 : ℝ) * M ≤ 2 * u + s₁ + s₂ := by linarith
    have hA : (u + s₁) ^ (2 : ℕ) ≤ (9 / 4 * M) ^ (2 : ℕ) := by nlinarith
    have hB : (u + s₂) ^ (2 : ℕ) ≤ (9 / 4 * M) ^ (2 : ℕ) := by nlinarith
    have hC : (u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ) ≤ (9 / 4 * M) ^ (2 : ℕ) * (9 / 4 * M) ^ (2 : ℕ) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    have hD : 36 * M ^ (3 : ℕ) * (2 * M) ≤ 36 * M ^ (3 : ℕ) * (2 * u + s₁ + s₂) := by
      have hM3 : (0 : ℝ) ≤ 36 * M ^ (3 : ℕ) := by positivity
      nlinarith
    nlinarith [hC, hD]
  rw [diffPhaseD2_eq' T hs₁ hs₂ hu0, curvedLambda,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hkey hcoef]

/-- Upper curvature bound for the difference phase on a dyadic block. -/
theorem diffPhaseD2_le_curvedLambda {T s₁ s₂ M u : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂)
    (hs : s₂ ≤ s₁) (hM : 4 * s₁ ≤ M) (hM0 : 0 < M) (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    diffPhaseD2 T s₁ s₂ u ≤ 90 * curvedLambda (T * (s₁ - s₂)) M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) ≤ s₁ := le_trans hs₂ hs
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM0 hu1
  have hus₁ : (0 : ℝ) < u + s₁ := by linarith
  have hus₂ : (0 : ℝ) < u + s₂ := by linarith
  have hΔ : (0 : ℝ) ≤ s₁ - s₂ := by linarith
  have hcoef : (0 : ℝ) ≤ T * (s₁ - s₂) * Real.pi :=
    mul_nonneg (mul_nonneg hT.le hΔ) hpi.le
  have hkey : M ^ (3 : ℕ) * (2 * u + s₁ + s₂) ≤ 5 * ((u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ)) := by
    have h3 : 2 * u + s₁ + s₂ ≤ 9 / 2 * M := by linarith
    have hA : M ^ (2 : ℕ) ≤ (u + s₁) ^ (2 : ℕ) := by nlinarith
    have hB : M ^ (2 : ℕ) ≤ (u + s₂) ^ (2 : ℕ) := by nlinarith
    have hC : M ^ (2 : ℕ) * M ^ (2 : ℕ) ≤ (u + s₁) ^ (2 : ℕ) * (u + s₂) ^ (2 : ℕ) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    have hD : M ^ (3 : ℕ) * (2 * u + s₁ + s₂) ≤ M ^ (3 : ℕ) * (9 / 2 * M) := by
      have hM3 : (0 : ℝ) ≤ M ^ (3 : ℕ) := by positivity
      nlinarith
    nlinarith [hC, hD]
  have hrhs : 90 * curvedLambda (T * (s₁ - s₂)) M
      = 90 * (T * (s₁ - s₂)) / (36 * Real.pi * M ^ (3 : ℕ)) := by
    rw [curvedLambda]
    ring
  rw [diffPhaseD2_eq' T hs₁ hs₂ hu0, hrhs,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hkey hcoef]

/-- **The difference phase is a curved phase** at scale `T(s₁ − s₂)`, from `4 s₁` on. -/
theorem curvedPhase_diffPhase {T s₁ s₂ : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂) (hs : s₂ < s₁) :
    CurvedPhase (diffPhase T s₁ s₂) (diffPhaseD1 T s₁ s₂) (diffPhaseD2 T s₁ s₂)
      (T * (s₁ - s₂)) (4 * s₁) := by
  have hs₁ : (0 : ℝ) < s₁ := lt_of_le_of_lt hs₂ hs
  refine ⟨by linarith, mul_pos hT (by linarith), ?_, ?_, ?_, ?_⟩
  · exact fun u hu => hasDerivAt_diffPhase T hs₁.le hs₂ (by linarith)
  · exact fun u hu => hasDerivAt_diffPhaseD1 T hs₁.le hs₂ (by linarith)
  · exact fun M u hM hu1 hu2 =>
      curvedLambda_le_diffPhaseD2 hT hs₂ hs.le hM (by linarith) hu1 hu2
  · exact fun M u hM hu1 hu2 =>
      diffPhaseD2_le_curvedLambda hT hs₂ hs.le hM (by linarith) hu1 hu2

/-- **The near-diagonal phase is a curved phase** at scale `T r`, from `r` on. -/
theorem curvedPhase_nearDiagonalPhase {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    CurvedPhase (nearDiagonalPhase T r) (nearDiagonalPhaseD1 T r) (nearDiagonalPhaseD2 T r)
      (T * r) r := by
  refine ⟨hr, mul_pos hT hr, ?_, ?_, ?_, ?_⟩
  · exact fun u hu => hasDerivAt_nearDiagonalPhase T hr.le (lt_of_lt_of_le hr hu)
  · exact fun u hu => hasDerivAt_nearDiagonalPhaseD1 T hr.le (lt_of_lt_of_le hr hu)
  · intro M u hM hu1 hu2
    have h := nearDiagonalLambda_le_D2 hT hr (lt_of_lt_of_le hr hM) hM hu1 hu2
    rwa [nearDiagonalLambda] at h
  · intro M u hM hu1 hu2
    have h := D2_le_nearDiagonalLambda hT hr (lt_of_lt_of_le hr hM) hM hu1 hu2
    rwa [nearDiagonalLambda] at h

end

end RHTower.Sieve
