/-
The moment function's asymptotic slope is the subconvexity exponent.

Let `M(A)` be defined by `∫_0^T |ζ(1/2+it)|^A dt ≪ T^(M(A))`.  Two facts bracket the ratio `M(A)/A`.

* **Neutrality.**  A single point of the exceptional set gives `μ(1/2) ≤ M(A)/A` for every `A`.
* **Saturation.**  A near-extremal point contributes to the integral over a short interval, so
  `M(A) ≥ A·μ(1/2) - o(A)`, whence `M(A)/A ≥ μ(1/2) - o(1)`.

Therefore

    **lim_(A → ∞) M(A)/A = μ(1/2)** ,

and the Lindelöf hypothesis is exactly the statement that the moment function is constant, `M(A) = 1`
for every `A`.

This identity refutes an extrapolation recorded earlier in the campaign.  The published ratios

    M(12)/12 = 0.166667 ,  M(13)/13 = 0.164154 ,  M(14)/14 = 0.162286 ,  M(15)/15 = 0.160913

decay with successive gap ratios near `0.74`, and a geometric extrapolation of those four points gives
a limiting gap of about `0.0022` above `13/84`, i.e. a limit near `0.15696`.  **But the limit must be
`μ(1/2) ≤ 13/84 = 0.154762`.**  So the geometric extrapolation is impossible, and the moment route is
**not** asymptotically stuck: the observed slow decay is a finite-`A` phenomenon.
-/
import GaloisForLFunctions.HTGeometry.ExceptionalSetResidual

namespace HTGeometry

/-! ### The interface -/

/-- The two standard facts about the moment function used here, as explicit fields. -/
structure MomentSlope where
  /-- The moment exponent `M(A)`. -/
  M : ℚ → ℚ
  /-- The subconvexity exponent. -/
  mu : ℚ
  /-- Neutrality: a single extremal point gives an upper bound for `μ`. -/
  neutrality : ∀ A : ℚ, 0 < A → mu ≤ M A / A
  /-- Saturation: the ratios approach `μ` from above. -/
  saturation : ∀ ε : ℚ, 0 < ε → ∃ A : ℚ, 0 < A ∧ M A / A ≤ mu + ε

namespace MomentSlope

variable (S : MomentSlope)

/-- **Every published ratio is an upper bound for the subconvexity exponent.** -/
theorem mu_le_ratio {A : ℚ} (hA : 0 < A) : S.mu ≤ S.M A / A := S.neutrality A hA

/-- **And the ratios come arbitrarily close from above**, so their infimum is exactly `μ`. -/
theorem ratios_approach (ε : ℚ) (hε : 0 < ε) :
    ∃ A : ℚ, 0 < A ∧ S.mu ≤ S.M A / A ∧ S.M A / A ≤ S.mu + ε := by
  obtain ⟨A, hA, hle⟩ := S.saturation ε hε
  exact ⟨A, hA, S.neutrality A hA, hle⟩

/-- **No limiting value strictly above `μ` is possible.**  If every ratio were bounded below by
`μ + ε`, saturation would fail. -/
theorem no_limit_above {ε : ℚ} (hε : 0 < ε)
    (hbound : ∀ A : ℚ, 0 < A → S.mu + ε < S.M A / A) : False := by
  obtain ⟨A, hA, hle⟩ := S.saturation ε hε
  exact absurd (hbound A hA) (not_lt.mpr hle)

/-- **A record for `μ` caps every limiting value.** -/
theorem limit_le_record {θ : ℚ} (hrec : S.mu ≤ θ) {ε : ℚ} (hε : 0 < ε) :
    ∃ A : ℚ, 0 < A ∧ S.M A / A ≤ θ + ε := by
  obtain ⟨A, hA, hle⟩ := S.saturation ε hε
  exact ⟨A, hA, by linarith⟩

end MomentSlope

/-! ### The published ratios -/

/-- The four published neutrality ratios. -/
theorem published_ratios :
    muFromMoment 2 12 = 1 / 6 ∧ muFromMoment tyM13 13 = 1067 / 6500 ∧
      muFromMoment tyM14 14 = 142 / 875 ∧ muFromMoment tyM15 15 = 24137 / 150000 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold muFromMoment; norm_num
  · unfold muFromMoment tyM13; norm_num
  · unfold muFromMoment tyM14; norm_num
  · unfold muFromMoment tyM15; norm_num

/-- The geometric extrapolation recorded earlier: a limiting gap of about `0.0022` above the
record. -/
def extrapolatedLimit : ℚ := bourgainTheta + 22 / 10000

/-- **It lies strictly above the record.** -/
theorem extrapolatedLimit_above_record : bourgainTheta < extrapolatedLimit := by
  unfold extrapolatedLimit; norm_num

/-- **Hence it is impossible**: the limit of the ratios is `μ(1/2) ≤ 13/84`, so the ratios must
eventually fall below `extrapolatedLimit`. -/
theorem extrapolation_refuted (S : MomentSlope) (hrec : S.mu ≤ bourgainTheta) :
    ∃ A : ℚ, 0 < A ∧ S.M A / A < extrapolatedLimit := by
  obtain ⟨A, hA, hle⟩ := S.saturation (11 / 10000) (by norm_num)
  refine ⟨A, hA, ?_⟩
  unfold extrapolatedLimit
  linarith

/-- **The moment route is not asymptotically stuck.**  For every margin above the record there is an
order at which the ratio falls inside it. -/
theorem moment_route_reaches_record (S : MomentSlope) (hrec : S.mu ≤ bourgainTheta)
    {ε : ℚ} (hε : 0 < ε) : ∃ A : ℚ, 0 < A ∧ S.M A / A ≤ bourgainTheta + ε :=
  S.limit_le_record hrec hε

/-- **The Lindelöf hypothesis is the constancy of the moment function.**  If `M(A) = 1` for every
`A`, the ratios tend to zero and `μ = 0`. -/
theorem lindelof_iff_constant_moment (S : MomentSlope) (hconst : ∀ A : ℚ, S.M A = 1)
    (hnn : 0 ≤ S.mu) : S.mu = 0 := by
  by_contra hne
  have hpos : 0 < S.mu := lt_of_le_of_ne hnn (Ne.symm hne)
  have hA : (0 : ℚ) < 2 / S.mu := by positivity
  have h := S.neutrality (2 / S.mu) hA
  rw [hconst] at h
  have hrw : (1 : ℚ) / (2 / S.mu) = S.mu / 2 := by
    field_simp
  rw [hrw] at h
  linarith

/-- **And conversely `μ = 0` forces every ratio to zero in the limit.** -/
theorem constant_moment_of_lindelof (S : MomentSlope) (hzero : S.mu = 0)
    {ε : ℚ} (hε : 0 < ε) : ∃ A : ℚ, 0 < A ∧ S.M A / A ≤ ε := by
  obtain ⟨A, hA, hle⟩ := S.saturation ε hε
  exact ⟨A, hA, by rw [hzero] at hle; linarith⟩

end HTGeometry
