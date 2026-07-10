import Mathlib

/-!
# Scalar FE/Schwarz germ gluing has no invariant beyond orbit shape

The local two-torsion extension is invariant under reflection, so the remaining proposed datum was
the **ordered pair** of functional-equation and Schwarz identifications between divisor germs.  This
file classifies the rank-one scalar part of that descent datum without constructing a carrier.

At a nonreal critical-line zero, FE and Schwarz both map the germ to the same partner.  Their
relative composite is an anti-linear involution of one complex line, hence has the form
`z |-> a * conj z` with `a * conj a = 1`.  Rank-one Hilbert 90 is explicit: if `a != -1`, the gauge
`b = 1 + a` kills `a`; if `a = -1`, the gauge `b = I` kills it.  Thus both arrows can be normalized
to coefficient one.  In particular the apparent leading-jet phase `(-1)^m` is not a complex-gauge
invariant.

At a free four-point orbit, the two FE arrows and two anti-linear Schwarz arrows form a square.  The
exact FE/Schwarz commutation relation is precisely flatness of that square.  Choosing bases along a
spanning tree normalizes three arrows, and flatness normalizes the fourth.  Hence every flat scalar
square is vertexwise gauge-equivalent to the all-one square.

The capstone makes the no-go exact: every scalar detector invariant under the natural germ-basis
gauges factors through a Boolean recording only fixed versus free orbit shape.  Comparing the two
identifications therefore yields no refinement of orbit cardinality.  Any surviving completed
invariant must use higher-rank or genuinely arithmetic global gluing data, not scalar germ phases or
a projective multiplier inserted into an exactly commuting square.
-/

noncomputable section

namespace RHTower

open Complex

/-! ## Anti-linear reflection coefficients -/

/-- The anti-linear endomorphism of a complex line with scalar coefficient `a`. -/
def antiLinearLineCoeff (a z : ℂ) : ℂ := a * starRingEnd ℂ z

/-- The coefficient equation saying `z |-> a * conj z` squares to the identity. -/
def IsAntiLinearInvolutionCoeff (a : ℂ) : Prop := a * starRingEnd ℂ a = 1

/-- Change the basis of the complex line by a nonzero scalar `b`. -/
def antiLinearCoeffGauge (a b : ℂ) : ℂ := b⁻¹ * a * starRingEnd ℂ b

/-- The coefficient equation is exactly involutivity of the anti-linear line map. -/
theorem antiLinearLineCoeff_sq_iff (a : ℂ) :
    (∀ z : ℂ, antiLinearLineCoeff a (antiLinearLineCoeff a z) = z) ↔
      IsAntiLinearInvolutionCoeff a := by
  constructor
  · intro h
    have h₁ := h 1
    simpa [antiLinearLineCoeff, IsAntiLinearInvolutionCoeff] using h₁
  · intro ha z
    simp only [antiLinearLineCoeff, map_mul, starRingEnd_self_apply]
    rw [← mul_assoc, ha, one_mul]

/-- **Rank-one anti-linear Hilbert 90, explicitly.**  Every anti-linear involution coefficient is
removed by a nonzero complex change of basis. -/
theorem exists_antiLinearCoeffGauge_eq_one (a : ℂ) (ha : IsAntiLinearInvolutionCoeff a) :
    ∃ b : ℂ, b ≠ 0 ∧ antiLinearCoeffGauge a b = 1 := by
  by_cases hminus : a = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    simp [antiLinearCoeffGauge, hminus]
  · have hb : 1 + a ≠ 0 := by
      intro h
      apply hminus
      have h' := congrArg (fun z : ℂ => z - 1) h
      simpa only [add_sub_cancel_left, zero_sub] using h'
    refine ⟨1 + a, hb, ?_⟩
    have hrel : a * (1 + starRingEnd ℂ a) = 1 + a := by
      rw [mul_add, ha]
      ring
    rw [antiLinearCoeffGauge, map_add, map_one]
    rw [mul_assoc, hrel]
    exact inv_mul_cancel₀ hb

/-- The multiplicity phase `(-1)^m` of a reflected leading germ is gauge-trivial for every order
`m`; parity alone does not orient a complex germ line. -/
theorem germParityCoeff_gauge_trivial (m : ℕ) :
    ∃ b : ℂ, b ≠ 0 ∧ antiLinearCoeffGauge ((-1 : ℂ) ^ m) b = 1 := by
  apply exists_antiLinearCoeffGauge_eq_one
  rw [IsAntiLinearInvolutionCoeff, map_pow, map_neg, map_one]
  rw [← pow_two, ← pow_mul]
  simp

/-! ## Critical-line two-point orbits -/

/-- Scalar FE/Schwarz gluing on a nonreal orbit fixed by their composite.  Both arrows go from one
germ line to its partner.  Their relative coefficient is the anti-linear stabilizer. -/
structure FixedOrbitFESchwarzGluing where
  fe : ℂ
  schwarz : ℂ
  fe_ne : fe ≠ 0
  schwarz_ne : schwarz ≠ 0
  relative_involutive : IsAntiLinearInvolutionCoeff (fe⁻¹ * schwarz)

/-- FE-arrow coefficient after independent basis changes at the two germs. -/
def fixedFEGaugeCoeff (G : FixedOrbitFESchwarzGluing) (g₀ g₁ : ℂ) : ℂ :=
  g₁⁻¹ * G.fe * g₀

/-- Schwarz-arrow coefficient after independent basis changes at the two germs. -/
def fixedSchwarzGaugeCoeff (G : FixedOrbitFESchwarzGluing) (g₀ g₁ : ℂ) : ℂ :=
  g₁⁻¹ * G.schwarz * starRingEnd ℂ g₀

/-- **Fixed-orbit normalization.**  Both ordered identifications can simultaneously be made one. -/
theorem FixedOrbitFESchwarzGluing.exists_normalizingGauge
    (G : FixedOrbitFESchwarzGluing) :
    ∃ g₀ g₁ : ℂ, g₀ ≠ 0 ∧ g₁ ≠ 0 ∧
      fixedFEGaugeCoeff G g₀ g₁ = 1 ∧ fixedSchwarzGaugeCoeff G g₀ g₁ = 1 := by
  obtain ⟨b, hb, hnorm⟩ :=
    exists_antiLinearCoeffGauge_eq_one (G.fe⁻¹ * G.schwarz) G.relative_involutive
  refine ⟨b, G.fe * b, hb, mul_ne_zero G.fe_ne hb, ?_, ?_⟩
  · simp [fixedFEGaugeCoeff, G.fe_ne, hb]
  · simpa [fixedSchwarzGaugeCoeff, antiLinearCoeffGauge, mul_inv_rev, mul_assoc] using hnorm

/-! ## Free four-point orbits -/

/-- Scalar descent data on a free FE/Schwarz orbit.  FE is complex-linear, Schwarz is anti-linear,
and `flat` is the exact commutation square. -/
structure FreeOrbitFESchwarzGluing where
  feBottom : ℂ
  feTop : ℂ
  schwarzLeft : ℂ
  schwarzRight : ℂ
  feBottom_ne : feBottom ≠ 0
  feTop_ne : feTop ≠ 0
  schwarzLeft_ne : schwarzLeft ≠ 0
  schwarzRight_ne : schwarzRight ≠ 0
  flat : feTop * schwarzLeft = schwarzRight * starRingEnd ℂ feBottom

/-- The central multiplier one would read by traversing the FE/Schwarz square in the two orders. -/
def freeOrbitProjectiveMultiplier (G : FreeOrbitFESchwarzGluing) : ℂ :=
  (G.schwarzRight * starRingEnd ℂ G.feBottom)⁻¹ * (G.feTop * G.schwarzLeft)

/-- **No projective residue.**  Exact FE/Schwarz commutation forces the would-be central multiplier
to be one.  A nontrivial multiplier would be extra projective data, not an invariant of the
completed scalar functional equations. -/
theorem FreeOrbitFESchwarzGluing.projectiveMultiplier_eq_one
    (G : FreeOrbitFESchwarzGluing) :
    freeOrbitProjectiveMultiplier G = 1 := by
  rw [freeOrbitProjectiveMultiplier, G.flat]
  exact inv_mul_cancel₀
    (mul_ne_zero G.schwarzRight_ne ((map_ne_zero (starRingEnd ℂ)).2 G.feBottom_ne))

def freeFEBottomGaugeCoeff (G : FreeOrbitFESchwarzGluing) (g₀₀ g₁₀ : ℂ) : ℂ :=
  g₁₀⁻¹ * G.feBottom * g₀₀

def freeFETopGaugeCoeff (G : FreeOrbitFESchwarzGluing) (g₀₁ g₁₁ : ℂ) : ℂ :=
  g₁₁⁻¹ * G.feTop * g₀₁

def freeSchwarzLeftGaugeCoeff (G : FreeOrbitFESchwarzGluing) (g₀₀ g₀₁ : ℂ) : ℂ :=
  g₀₁⁻¹ * G.schwarzLeft * starRingEnd ℂ g₀₀

def freeSchwarzRightGaugeCoeff (G : FreeOrbitFESchwarzGluing) (g₁₀ g₁₁ : ℂ) : ℂ :=
  g₁₁⁻¹ * G.schwarzRight * starRingEnd ℂ g₁₀

/-- **Free-orbit normalization.**  A flat scalar FE/Schwarz square is vertexwise gauge-equivalent
to the all-one square. -/
theorem FreeOrbitFESchwarzGluing.exists_normalizingVertexGauge
    (G : FreeOrbitFESchwarzGluing) :
    ∃ g₀₀ g₁₀ g₀₁ g₁₁ : ℂ,
      g₀₀ ≠ 0 ∧ g₁₀ ≠ 0 ∧ g₀₁ ≠ 0 ∧ g₁₁ ≠ 0 ∧
      freeFEBottomGaugeCoeff G g₀₀ g₁₀ = 1 ∧
      freeFETopGaugeCoeff G g₀₁ g₁₁ = 1 ∧
      freeSchwarzLeftGaugeCoeff G g₀₀ g₀₁ = 1 ∧
      freeSchwarzRightGaugeCoeff G g₁₀ g₁₁ = 1 := by
  refine ⟨1, G.feBottom, G.schwarzLeft, G.feTop * G.schwarzLeft,
    one_ne_zero, G.feBottom_ne, G.schwarzLeft_ne,
    mul_ne_zero G.feTop_ne G.schwarzLeft_ne, ?_, ?_, ?_, ?_⟩
  · simp [freeFEBottomGaugeCoeff, G.feBottom_ne]
  · simp [freeFETopGaugeCoeff, G.feTop_ne, G.schwarzLeft_ne]
  · simp [freeSchwarzLeftGaugeCoeff, G.schwarzLeft_ne]
  · change (G.feTop * G.schwarzLeft)⁻¹ * G.schwarzRight *
      starRingEnd ℂ G.feBottom = 1
    rw [mul_assoc, ← G.flat]
    exact inv_mul_cancel₀ (mul_ne_zero G.feTop_ne G.schwarzLeft_ne)

/-! ## Exhaustion of scalar gauge-invariant detectors -/

/-- A detector of fixed-orbit arrow coefficients which is invariant under every nonzero germ-basis
change. -/
def FixedOrbitDetectorGaugeInvariant {A : Type*} (D : ℂ → ℂ → A) : Prop :=
  ∀ (G : FixedOrbitFESchwarzGluing) (g₀ g₁ : ℂ), g₀ ≠ 0 → g₁ ≠ 0 →
    D (fixedFEGaugeCoeff G g₀ g₁) (fixedSchwarzGaugeCoeff G g₀ g₁) = D G.fe G.schwarz

/-- Every gauge-invariant scalar detector is constant on fixed-orbit gluing data. -/
theorem fixedOrbitDetector_eq_trivial {A : Type*} (D : ℂ → ℂ → A)
    (hD : FixedOrbitDetectorGaugeInvariant D) (G : FixedOrbitFESchwarzGluing) :
    D G.fe G.schwarz = D 1 1 := by
  obtain ⟨g₀, g₁, hg₀, hg₁, hfe, hschwarz⟩ := G.exists_normalizingGauge
  calc
    D G.fe G.schwarz =
        D (fixedFEGaugeCoeff G g₀ g₁) (fixedSchwarzGaugeCoeff G g₀ g₁) :=
      (hD G g₀ g₁ hg₀ hg₁).symm
    _ = D 1 1 := by rw [hfe, hschwarz]

/-- A detector of free-square arrow coefficients invariant under independent nonzero basis changes
at all four orbit germs. -/
def FreeOrbitDetectorGaugeInvariant {A : Type*}
    (D : ℂ → ℂ → ℂ → ℂ → A) : Prop :=
  ∀ (G : FreeOrbitFESchwarzGluing) (g₀₀ g₁₀ g₀₁ g₁₁ : ℂ),
    g₀₀ ≠ 0 → g₁₀ ≠ 0 → g₀₁ ≠ 0 → g₁₁ ≠ 0 →
    D (freeFEBottomGaugeCoeff G g₀₀ g₁₀) (freeFETopGaugeCoeff G g₀₁ g₁₁)
        (freeSchwarzLeftGaugeCoeff G g₀₀ g₀₁)
        (freeSchwarzRightGaugeCoeff G g₁₀ g₁₁) =
      D G.feBottom G.feTop G.schwarzLeft G.schwarzRight

/-- Every gauge-invariant scalar detector is constant on flat free-orbit gluing squares. -/
theorem freeOrbitDetector_eq_trivial {A : Type*} (D : ℂ → ℂ → ℂ → ℂ → A)
    (hD : FreeOrbitDetectorGaugeInvariant D) (G : FreeOrbitFESchwarzGluing) :
    D G.feBottom G.feTop G.schwarzLeft G.schwarzRight = D 1 1 1 1 := by
  obtain ⟨g₀₀, g₁₀, g₀₁, g₁₁, hg₀₀, hg₁₀, hg₀₁, hg₁₁, hfb, hft, hcl, hcr⟩ :=
    G.exists_normalizingVertexGauge
  calc
    D G.feBottom G.feTop G.schwarzLeft G.schwarzRight =
        D (freeFEBottomGaugeCoeff G g₀₀ g₁₀) (freeFETopGaugeCoeff G g₀₁ g₁₁)
          (freeSchwarzLeftGaugeCoeff G g₀₀ g₀₁)
          (freeSchwarzRightGaugeCoeff G g₁₀ g₁₁) :=
      (hD G g₀₀ g₁₀ g₀₁ g₁₁ hg₀₀ hg₁₀ hg₀₁ hg₁₁).symm
    _ = D 1 1 1 1 := by rw [hfb, hft, hcl, hcr]

/-- **Scalar ordered-gluing no-go.**  Any detector of the separate FE and Schwarz scalar
identifications which respects germ-basis gauge factors through the Boolean fixed/free orbit shape.
There is no further scalar compatibility invariant inside either orbit type. -/
theorem scalarGluingDetector_factors_through_orbitShape {A : Type*}
    (Dfixed : ℂ → ℂ → A) (Dfree : ℂ → ℂ → ℂ → ℂ → A)
    (hfixed : FixedOrbitDetectorGaugeInvariant Dfixed)
    (hfree : FreeOrbitDetectorGaugeInvariant Dfree) :
    ∃ d : Bool → A,
      (∀ G : FixedOrbitFESchwarzGluing, Dfixed G.fe G.schwarz = d true) ∧
      (∀ G : FreeOrbitFESchwarzGluing,
        Dfree G.feBottom G.feTop G.schwarzLeft G.schwarzRight = d false) := by
  refine ⟨fun fixed => if fixed then Dfixed 1 1 else Dfree 1 1 1 1, ?_, ?_⟩
  · intro G
    simpa using fixedOrbitDetector_eq_trivial Dfixed hfixed G
  · intro G
    simpa using freeOrbitDetector_eq_trivial Dfree hfree G

end RHTower
