import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FiniteTiltResponse

/-!
# Four-organ first-response conservation for an arbitrary finite source law

For a finite probability weight `μ`, an intervention score `r` and statistics `f, g`, put
`A = Cov_e(f,f)`, `B = Cov_e(f,g)`, `M = C = Cov_e(g,g)`, `H = AC - B²` and
`Q = 4π²(A - B²/C)` along the affine tilt `μ_e ∝ μ (1 + e r)`.  Wherever `C ≠ 0`,
`Q M = 4π² H`.  If `C(0) ≠ 0`, differentiating at `e = 0` gives

`Q₁ M₀ + Q₀ M₁ = 4π² H₁`,  `H₁ = A₁C₀ + A₀C₁ - 2B₀B₁`,  `Q₁ = (4π² H₁ - Q₀ M₁)/M₀`,

with every first response a covariance with `r` (the exact affine-tilt response law).
-/

namespace HTGeometry.ConstraintFrameRelativity

noncomputable section

variable {Ω : Type*} [Fintype Ω] (μ r f g : Ω → ℝ)

/-- The four organs along the tilt. -/
def tiltIncidence (e : ℝ) : ℝ := tiltCov μ r e f f
def tiltCross (e : ℝ) : ℝ := tiltCov μ r e f g
def tiltMass (e : ℝ) : ℝ := tiltCov μ r e g g
def tiltHankel (e : ℝ) : ℝ :=
  tiltIncidence μ r f e * tiltMass μ r g e - tiltCross μ r f g e ^ 2
def tiltQFI (e : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * (tiltIncidence μ r f e - tiltCross μ r f g e ^ 2 / tiltMass μ r g e)

/-- The centred first response of a tilted covariance, `Cov_μ(r, (u - Eu)(v - Ev))`. -/
def tiltResponse (u v : Ω → ℝ) : ℝ := wcov μ r (fun ω => (u ω - wexp μ u) * (v ω - wexp μ v))

/-- **(LJP.12)** `Q M = 4π² H` wherever the Mass port is nonzero. -/
theorem tiltQFI_mul_tiltMass {e : ℝ} (hM : tiltMass μ r g e ≠ 0) :
    tiltQFI μ r f g e * tiltMass μ r g e = 4 * Real.pi ^ 2 * tiltHankel μ r f g e := by
  unfold tiltQFI tiltHankel
  field_simp

/-- The QFI response, from the quotient rule. -/
def tiltQFIResponse : ℝ :=
  4 * Real.pi ^ 2 * (tiltResponse μ r f f -
    (2 * wcov μ f g * tiltResponse μ r f g * wcov μ g g -
      wcov μ f g ^ 2 * tiltResponse μ r g g) / wcov μ g g ^ 2)

variable {μ}

/-- **(LJP.13)** Every organ responds by a covariance with the intervention score. -/
theorem hasDerivAt_tiltOrgans (hμ : ∑ ω, μ ω = 1) :
    HasDerivAt (tiltIncidence μ r f) (tiltResponse μ r f f) 0 ∧
      HasDerivAt (tiltCross μ r f g) (tiltResponse μ r f g) 0 ∧
      HasDerivAt (tiltMass μ r g) (tiltResponse μ r g g) 0 :=
  ⟨hasDerivAt_tiltCov hμ r f f, hasDerivAt_tiltCov hμ r f g, hasDerivAt_tiltCov hμ r g g⟩

/-- **(LJP.15)** The Hankel response `H₁ = A₁C₀ + A₀C₁ - 2B₀B₁`. -/
theorem hasDerivAt_tiltHankel (hμ : ∑ ω, μ ω = 1) :
    HasDerivAt (tiltHankel μ r f g)
      (tiltResponse μ r f f * wcov μ g g + wcov μ f f * tiltResponse μ r g g -
        2 * wcov μ f g * tiltResponse μ r f g) 0 := by
  obtain ⟨hA, hB, hC⟩ := hasDerivAt_tiltOrgans r f g hμ
  have h := (hA.mul hC).sub (hB.pow 2)
  simp only [tiltIncidence, tiltCross, tiltMass, tiltCov_zero hμ] at h
  refine h.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_tiltQFI (hμ : ∑ ω, μ ω = 1) (hC : wcov μ g g ≠ 0) :
    HasDerivAt (tiltQFI μ r f g) (tiltQFIResponse μ r f g) 0 := by
  obtain ⟨hA, hB, hCd⟩ := hasDerivAt_tiltOrgans r f g hμ
  have hC0 : tiltMass μ r g 0 ≠ 0 := by
    simp only [tiltMass, tiltCov_zero hμ]; exact hC
  have h := ((hA.sub ((hB.pow 2).div hCd hC0)).const_mul (4 * Real.pi ^ 2))
  simp only [Pi.pow_apply, tiltCross, tiltMass, tiltCov_zero hμ] at h
  refine h.congr_deriv ?_
  unfold tiltQFIResponse
  push_cast
  ring

/-- **Theorem 5.1 (LJP.14)** Four-organ first-response conservation
`Q₁ M₀ + Q₀ M₁ = 4π² H₁`. -/
theorem tilt_fourOrgan_firstResponse_conservation (hμ : ∑ ω, μ ω = 1) (hC : wcov μ g g ≠ 0) :
    tiltQFIResponse μ r f g * wcov μ g g + tiltQFI μ r f g 0 * tiltResponse μ r g g =
      4 * Real.pi ^ 2 * (tiltResponse μ r f f * wcov μ g g + wcov μ f f * tiltResponse μ r g g -
        2 * wcov μ f g * tiltResponse μ r f g) := by
  simp only [tiltQFIResponse, tiltQFI, tiltIncidence, tiltCross, tiltMass, tiltCov_zero hμ]
  field_simp
  ring

/-- **(LJP.16)** The withheld QFI response is forced by incidence, Mass, and Hankel responses. -/
theorem tiltQFIResponse_eq (hμ : ∑ ω, μ ω = 1) (hC : wcov μ g g ≠ 0) :
    tiltQFIResponse μ r f g =
      (4 * Real.pi ^ 2 * (tiltResponse μ r f f * wcov μ g g +
          wcov μ f f * tiltResponse μ r g g - 2 * wcov μ f g * tiltResponse μ r f g) -
        tiltQFI μ r f g 0 * tiltResponse μ r g g) / wcov μ g g := by
  rw [eq_div_iff hC, ← tilt_fourOrgan_firstResponse_conservation r f g hμ hC]
  ring

end

end HTGeometry.ConstraintFrameRelativity
