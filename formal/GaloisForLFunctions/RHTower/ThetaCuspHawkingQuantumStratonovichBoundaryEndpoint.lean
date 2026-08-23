import GaloisForLFunctions.RHTower.ThetaCuspHawkingUnitWindingSelectionNoGo

/-!
# Quantum-Stratonovich boundary completion of theta-cusp Hawking scattering

The canonical Cayley block now has a dynamical origin rather than being merely an algebraic
unitarization.  Quantum Wong--Zakai limits promote regular open-system Hamiltonians to
Hudson--Parthasarathy scattering evolutions; their singular Hamiltonians are equivalently
symmetric Schrödinger boundary-value problems.  See Gough, arXiv:math-ph/0511046, and
Chebotarev--Gregoratti, arXiv:funct-an/9706006.

For one exterior/horizon pair, let the skew exchange coordinate be

`A_g(x,h) = (-conj(g) h, g x)`.

The symmetric singular-interaction jump law is

`out - in = A_g (out + in) / 2`.

This file solves that law exactly and uniquely.  Its solution is the Cayley scattering matrix

`S_g = (1 + A_g/2) (1 - A_g/2)⁻¹`,

with retention `(1-|g|²/4)/(1+|g|²/4)` and transition `g/(1+|g|²/4)`.  Substituting the genuine
theta-cusp Hawking Born shell `g = lambda F_theta(a,omega)` recovers, entry for entry, the existing
source-faithful KMS/Cayley collision.  Hence the preceding Hawking Gibbs reduction is the reduced
dynamics of the unique singular-Hamiltonian boundary scattering block, and all-sector mixing is
again equivalent to RH.

Scope matters.  This is the full nonperturbative S-matrix of the quantum-Markov/white-noise
scattering limit; it is not the raw Davies--Fulling moving-mirror Bogoliubov matrix.  The latter
identification is already formally false because the exact mirror has even coupling jets.

The final countermodel is decisive: the same exact boundary selection, losslessness, KMS detailed
balance, and mixing at every nonzero coupling allow `g(lambda)=lambda²`, whose coupling winding is
two.  Thus deriving the Cayley boundary law from actual Hawking scattering closes completion
provenance but does not prove RH.  Remaining producer is theta-specific first-order transversality:
the physical singular coupling must inherit the unsquared Born coefficient without a dark sector
or delayed onset.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

def quantumStratonovichCayleyLoad (g : ℂ) : ℝ :=
  Complex.normSq g / 4

def quantumStratonovichCayleyRetention (g : ℂ) : ℝ :=
  (1 - quantumStratonovichCayleyLoad g) /
    (1 + quantumStratonovichCayleyLoad g)

def quantumStratonovichCayleyTransition (g : ℂ) : ℂ :=
  g / (((1 + quantumStratonovichCayleyLoad g : ℝ) : ℂ))

def quantumStratonovichCayleyExteriorOutput (g x h : ℂ) : ℂ :=
  (quantumStratonovichCayleyRetention g : ℂ) * x -
    conj (quantumStratonovichCayleyTransition g) * h

def quantumStratonovichCayleyHorizonOutput (g x h : ℂ) : ℂ :=
  quantumStratonovichCayleyTransition g * x +
    (quantumStratonovichCayleyRetention g : ℂ) * h

def QuantumStratonovichTwoPortBoundary
    (g x h y k : ℂ) : Prop :=
  y - x = -conj g * ((k + h) / 2) ∧
    k - h = g * ((y + x) / 2)

theorem quantumStratonovichCayleyLoad_nonneg (g : ℂ) :
    0 ≤ quantumStratonovichCayleyLoad g := by
  exact div_nonneg (Complex.normSq_nonneg g) (by norm_num)

theorem quantumStratonovichCayley_denominator_ne_zero (g : ℂ) :
    1 + quantumStratonovichCayleyLoad g ≠ 0 := by
  linarith [quantumStratonovichCayleyLoad_nonneg g]

theorem quantumStratonovichCayley_outputs_satisfy_boundary
    (g x h : ℂ) :
    QuantumStratonovichTwoPortBoundary g x h
      (quantumStratonovichCayleyExteriorOutput g x h)
      (quantumStratonovichCayleyHorizonOutput g x h) := by
  have hdenR : 1 + quantumStratonovichCayleyLoad g ≠ 0 :=
    quantumStratonovichCayley_denominator_ne_zero g
  have hdenC :
      (((1 + quantumStratonovichCayleyLoad g : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdenR
  have hj :
      ((quantumStratonovichCayleyLoad g : ℝ) : ℂ) = conj g * g / 4 := by
    rw [quantumStratonovichCayleyLoad]
    rw [Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
    norm_num
  have hdenG : (1 : ℂ) + conj g * g / 4 ≠ 0 := by
    rw [Complex.ofReal_add, Complex.ofReal_one] at hdenC
    rw [← hj]
    exact hdenC
  have hden4 : (4 : ℂ) + conj g * g ≠ 0 := by
    intro hzero
    apply hdenG
    linear_combination hzero / 4
  have hden4' : (4 : ℂ) + g * conj g ≠ 0 := by
    simpa [mul_comm] using hden4
  have hret :
      (quantumStratonovichCayleyRetention g : ℂ) =
        ((4 : ℂ) - conj g * g) / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyRetention]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  have htrans :
      quantumStratonovichCayleyTransition g =
        4 * g / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyTransition]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  have hconjtrans :
      conj (quantumStratonovichCayleyTransition g) =
        4 * conj g / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyTransition, map_div₀]
    rw [conj_ofReal]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  rw [QuantumStratonovichTwoPortBoundary]
  constructor <;>
    simp only [quantumStratonovichCayleyExteriorOutput,
      quantumStratonovichCayleyHorizonOutput]
  · rw [hret, hconjtrans, htrans]
    field_simp [hden4, hden4']
    ring
  · rw [hret, hconjtrans, htrans]
    field_simp [hden4]
    ring

theorem quantumStratonovichCayley_boundary_unique
    {g x h y k : ℂ}
    (hboundary : QuantumStratonovichTwoPortBoundary g x h y k) :
    y = quantumStratonovichCayleyExteriorOutput g x h ∧
      k = quantumStratonovichCayleyHorizonOutput g x h := by
  have hdenR : 1 + quantumStratonovichCayleyLoad g ≠ 0 :=
    quantumStratonovichCayley_denominator_ne_zero g
  have hdenC :
      (((1 + quantumStratonovichCayleyLoad g : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdenR
  have hj :
      ((quantumStratonovichCayleyLoad g : ℝ) : ℂ) = conj g * g / 4 := by
    rw [quantumStratonovichCayleyLoad]
    rw [Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
    norm_num
  have hdenG : (1 : ℂ) + conj g * g / 4 ≠ 0 := by
    rw [Complex.ofReal_add, Complex.ofReal_one] at hdenC
    rw [← hj]
    exact hdenC
  have hden4 : (4 : ℂ) + conj g * g ≠ 0 := by
    intro hzero
    apply hdenG
    linear_combination hzero / 4
  have hden4' : (4 : ℂ) + g * conj g ≠ 0 := by
    simpa [mul_comm] using hden4
  have hret :
      (quantumStratonovichCayleyRetention g : ℂ) =
        ((4 : ℂ) - conj g * g) / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyRetention]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  have htrans :
      quantumStratonovichCayleyTransition g =
        4 * g / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyTransition]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  have hconjtrans :
      conj (quantumStratonovichCayleyTransition g) =
        4 * conj g / (4 + conj g * g) := by
    rw [quantumStratonovichCayleyTransition, map_div₀]
    rw [conj_ofReal]
    push_cast
    rw [hj]
    field_simp [hdenG, hden4]
  rcases hboundary with ⟨hy, hk⟩
  have hyNum :
      (4 + conj g * g) * y =
        (4 - conj g * g) * x - 4 * conj g * h := by
    linear_combination 4 * hy - 2 * conj g * hk
  have hkNum :
      (4 + conj g * g) * k =
        4 * g * x + (4 - conj g * g) * h := by
    linear_combination 4 * hk + 2 * g * hy
  constructor
  · simp only [quantumStratonovichCayleyExteriorOutput,
      hret, hconjtrans]
    field_simp [hden4]
    simpa [mul_comm] using hyNum
  · simp only [quantumStratonovichCayleyHorizonOutput,
      hret, htrans]
    field_simp [hden4, hden4']
    simpa [mul_comm] using hkNum

theorem quantumStratonovichCayley_boundary_iff
    (g x h y k : ℂ) :
    QuantumStratonovichTwoPortBoundary g x h y k ↔
      y = quantumStratonovichCayleyExteriorOutput g x h ∧
      k = quantumStratonovichCayleyHorizonOutput g x h := by
  constructor
  · exact quantumStratonovichCayley_boundary_unique
  · rintro ⟨rfl, rfl⟩
    exact quantumStratonovichCayley_outputs_satisfy_boundary g x h

/-! ### Source-faithful theta/Hawking specialization -/

/-- Singular Stratonovich exchange coefficient supplied by the genuine theta-cusp Hawking
Born shell. -/
def thetaCuspHawkingQuantumStratonovichCoupling
    (lambda a omega : ℝ) : ℂ :=
  (lambda : ℂ) * thetaCuspHawkingFriedrichsShellFormFactor a omega

theorem quantumStratonovichCayleyLoad_theta_eq
    (lambda a omega : ℝ) :
    quantumStratonovichCayleyLoad
        (thetaCuspHawkingQuantumStratonovichCoupling lambda a omega) =
      thetaCuspHawkingCayleyLoad lambda a omega := by
  rw [quantumStratonovichCayleyLoad,
    thetaCuspHawkingQuantumStratonovichCoupling,
    thetaCuspHawkingCayleyLoad, Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring

theorem quantumStratonovichCayleyRetention_theta_eq
    (lambda a omega : ℝ) :
    quantumStratonovichCayleyRetention
        (thetaCuspHawkingQuantumStratonovichCoupling lambda a omega) =
      thetaCuspHawkingCayleyRetention lambda a omega := by
  rw [quantumStratonovichCayleyRetention,
    thetaCuspHawkingCayleyRetention,
    quantumStratonovichCayleyLoad_theta_eq]

theorem quantumStratonovichCayleyTransition_theta_eq
    (lambda a omega : ℝ) :
    quantumStratonovichCayleyTransition
        (thetaCuspHawkingQuantumStratonovichCoupling lambda a omega) =
      thetaCuspHawkingCayleyTransition lambda a omega := by
  rw [quantumStratonovichCayleyTransition,
    thetaCuspHawkingCayleyTransition,
    quantumStratonovichCayleyLoad_theta_eq,
    thetaCuspHawkingQuantumStratonovichCoupling]

/-- Actual theta/Hawking singular-Hamiltonian jump law.  This is the symmetric boundary
condition underlying the Hudson--Parthasarathy scattering limit. -/
def ThetaCuspHawkingQuantumStratonovichBoundary
    (lambda a omega : ℝ) (x h y k : ℂ) : Prop :=
  QuantumStratonovichTwoPortBoundary
    (thetaCuspHawkingQuantumStratonovichCoupling lambda a omega)
    x h y k

/-- **Canonical Cayley completion.**  The source-faithful theta/Hawking Cayley block is the
unique solution of the symmetric singular-Hamiltonian boundary equation. -/
theorem thetaCuspHawkingQuantumStratonovichBoundary_iff_cayley
    (lambda a omega : ℝ) (x h y k : ℂ) :
    ThetaCuspHawkingQuantumStratonovichBoundary
        lambda a omega x h y k ↔
      y = thetaCuspHawkingCayleyExteriorOutput lambda a omega x h ∧
      k = thetaCuspHawkingCayleyHorizonOutput lambda a omega x h := by
  rw [ThetaCuspHawkingQuantumStratonovichBoundary,
    quantumStratonovichCayley_boundary_iff]
  simp only [quantumStratonovichCayleyExteriorOutput,
    quantumStratonovichCayleyHorizonOutput,
    quantumStratonovichCayleyRetention_theta_eq,
    quantumStratonovichCayleyTransition_theta_eq,
    thetaCuspHawkingCayleyExteriorOutput,
    thetaCuspHawkingCayleyHorizonOutput]

/-! ### Full boundary-scattering endpoint -/

/-- Every physical tilted sector has one unique singular-Hamiltonian two-port output, and its
Hawking Gibbs reduction mixes.  Uniqueness encodes canonical Cayley selection; mixing is the
nondegeneracy not supplied by boundary self-adjointness alone. -/
def ThetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing : Prop :=
  ∀ (kappa a omega : ℝ), 0 < kappa → 0 < omega → |a| < 1 → a ≠ 0 →
    (∀ x h : ℂ,
      ∃! output : ℂ × ℂ,
        ThetaCuspHawkingQuantumStratonovichBoundary
          1 a omega x h output.1 output.2) ∧
    ThetaCuspHawkingKMSCayleySectorMixes kappa a omega

theorem thetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing_iff_KMSCayley :
    ThetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing ↔
      ThetaCuspHawkingKMSCayleyScatteringMixing := by
  constructor
  · intro h kappa a omega hkappa homega ha hane
    exact (h kappa a omega hkappa homega ha hane).2
  · intro h kappa a omega hkappa homega ha hane
    refine ⟨?_, h kappa a omega hkappa homega ha hane⟩
    intro x hport
    let output : ℂ × ℂ :=
      (thetaCuspHawkingCayleyExteriorOutput 1 a omega x hport,
        thetaCuspHawkingCayleyHorizonOutput 1 a omega x hport)
    refine ⟨output, ?_, ?_⟩
    · exact (thetaCuspHawkingQuantumStratonovichBoundary_iff_cayley
        1 a omega x hport output.1 output.2).2 ⟨rfl, rfl⟩
    · intro candidate hcandidate
      have hcay :=
        (thetaCuspHawkingQuantumStratonovichBoundary_iff_cayley
          1 a omega x hport candidate.1 candidate.2).1 hcandidate
      apply Prod.ext
      · exact hcay.1
      · exact hcay.2

/-- **Hawking quantum-boundary endpoint.**  RH is equivalent to mixing of every noncentral
theta sector after the genuine Born shell is promoted to the unique symmetric-boundary Cayley
scattering block and reduced against a Hawking KMS mode. -/
theorem riemannHypothesis_iff_thetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing :
    RiemannHypothesis ↔
      ThetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing :=
  riemannHypothesis_iff_thetaCuspHawkingKMSCayleyScatteringMixing.trans
    thetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing_iff_KMSCayley.symm

/-! ### Delayed-onset obstruction -/

theorem quantumStratonovichCayleyLoad_delayed_eq
    (m : ℕ) (lambda : ℝ) :
    quantumStratonovichCayleyLoad (((lambda ^ m : ℝ) : ℂ)) =
      delayedHawkingCayleyLoad m lambda := by
  rw [quantumStratonovichCayleyLoad, delayedHawkingCayleyLoad,
    Complex.normSq_ofReal]
  congr 1
  rw [← pow_add]
  congr 1
  omega

theorem quantumStratonovichCayleyRetention_delayed_eq
    (m : ℕ) (lambda : ℝ) :
    quantumStratonovichCayleyRetention (((lambda ^ m : ℝ) : ℂ)) =
      delayedHawkingCayleyRetention m lambda := by
  rw [quantumStratonovichCayleyRetention,
    delayedHawkingCayleyRetention,
    quantumStratonovichCayleyLoad_delayed_eq]

theorem quantumStratonovichCayleyTransition_delayed_eq
    (m : ℕ) (lambda : ℝ) :
    quantumStratonovichCayleyTransition (((lambda ^ m : ℝ) : ℂ)) =
      delayedHawkingCayleyTransition m lambda := by
  rw [quantumStratonovichCayleyTransition,
    delayedHawkingCayleyTransition,
    quantumStratonovichCayleyLoad_delayed_eq]

theorem delayedHawkingCayley_satisfies_quantumStratonovichBoundary
    (m : ℕ) (lambda : ℝ) (x h : ℂ) :
    QuantumStratonovichTwoPortBoundary (((lambda ^ m : ℝ) : ℂ)) x h
      (delayedHawkingCayleyExteriorOutput m lambda x h)
      (delayedHawkingCayleyHorizonOutput m lambda x h) := by
  rw [quantumStratonovichCayley_boundary_iff]
  simp only [quantumStratonovichCayleyExteriorOutput,
    quantumStratonovichCayleyHorizonOutput,
    quantumStratonovichCayleyRetention_delayed_eq,
    quantumStratonovichCayleyTransition_delayed_eq,
    delayedHawkingCayleyExteriorOutput,
    delayedHawkingCayleyHorizonOutput]
  exact ⟨True.intro, True.intro⟩

/-- **[NO-GO]** Even exact quantum-Stratonovich boundary selection, losslessness, Hawking KMS
detailed balance, and mixing at every nonzero coupling permit quadratic onset and winding two.
Canonical Cayley selection therefore does not prove the source coefficient is first-order bright. -/
theorem quantumStratonovich_lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding :
    (∀ lambda x h,
      QuantumStratonovichTwoPortBoundary (((lambda ^ 2 : ℝ) : ℂ)) x h
        (delayedHawkingCayleyExteriorOutput 2 lambda x h)
        (delayedHawkingCayleyHorizonOutput 2 lambda x h)) ∧
    (∀ lambda x h,
      conj (delayedHawkingCayleyExteriorOutput 2 lambda x h) *
            delayedHawkingCayleyExteriorOutput 2 lambda x h +
          conj (delayedHawkingCayleyHorizonOutput 2 lambda x h) *
            delayedHawkingCayleyHorizonOutput 2 lambda x h =
        conj x * x + conj h * h) ∧
    (∀ lambda : ℝ, lambda ≠ 0 →
      delayedHawkingCayleyRetention 2 lambda ^ 2 < 1) ∧
    (∀ lambda kappa omega,
      delayedHawkingKMSCayleyUpProbability 2 lambda kappa omega =
        thetaCuspHawkingKMSBoltzmannRatio kappa omega *
          delayedHawkingKMSCayleyDownProbability 2 lambda kappa omega) ∧
    (∀ r : ℝ, 0 < r →
      windingNumber
          (fun theta : ℝ =>
            (((r : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ 2))
          0 (2 * Real.pi) = 2) := by
  rcases lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding with
    ⟨hlossless, hmix, hKMS, hwinding⟩
  exact ⟨delayedHawkingCayley_satisfies_quantumStratonovichBoundary 2,
    hlossless, hmix, hKMS, hwinding⟩

end RHTower
