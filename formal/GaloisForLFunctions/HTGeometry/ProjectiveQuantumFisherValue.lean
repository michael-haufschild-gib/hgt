import Mathlib

/-!
# Projective quantum-Fisher tangent values

For an unnormalised pure-state tangent, retain only the three real values

```text
mass      = <psi,psi>,
overlap   = <psi,dpsi>,
speedSq   = <dpsi,dpsi>.
```

Removing an arbitrary scalar-phase tangent replaces `speedSq` by

```text
speedSq - 2*c*overlap + c^2*mass.
```

The exact quotient-free square completion is

```text
mass * shiftedSpeedSq(c)
  = (mass*speedSq-overlap^2) + (mass*c-overlap)^2.
```

Thus the projective tangent value `mass*speedSq-overlap^2` is invariant under scalar-phase
gauge, is the minimum after normalization, and is the two-vector Gram determinant.  Dividing it
by `mass^2` gives the pure-state Fubini--Study value; four times that value is the conventional
pure-state quantum Fisher information.

This file records only static value identities.  No Hamiltonian evolution or flow premise is
introduced.

Physics provenance: J. P. Provost and G. Vallee, *Riemannian structure on manifolds of quantum
states*, Commun. Math. Phys. 76 (1980), 289--301, DOI 10.1007/BF02193559; J. Anandan and
Y. Aharonov, *Geometry of quantum evolution*, Phys. Rev. Lett. 65 (1990), 1697--1700,
DOI 10.1103/PhysRevLett.65.1697; S. L. Braunstein and C. M. Caves, *Statistical distance and the
geometry of quantum states*, Phys. Rev. Lett. 72 (1994), 3439--3443,
DOI 10.1103/PhysRevLett.72.3439.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

/-- Quotient-free projective tangent value.  It is the determinant of the real two-channel Gram
value with vacuum mass `mass`, mixed value `overlap`, and tangent energy `speedSq`. -/
def projectiveQuantumTangentValue (mass overlap speedSq : ℝ) : ℝ :=
  mass * speedSq - overlap ^ 2

/-- A two-channel Robertson/Cauchy--Schwarz bound is exactly nonnegativity of the projective
tangent value. -/
theorem projectiveQuantumTangentValue_nonneg
    {mass overlap speedSq : ℝ}
    (h : overlap ^ 2 ≤ mass * speedSq) :
    0 ≤ projectiveQuantumTangentValue mass overlap speedSq := by
  unfold projectiveQuantumTangentValue
  linarith

/-- Squared tangent value after subtracting the scalar-phase direction `c`. -/
def scalarShiftedQuantumTangentValue
    (mass overlap speedSq c : ℝ) : ℝ :=
  speedSq - 2 * c * overlap + c ^ 2 * mass

/-- **Projective/Fubini--Study square completion.**  The shifted tangent splits into the
gauge-invariant projective value and one positive scalar-phase square. -/
theorem mass_mul_scalarShiftedQuantumTangentValue
    (mass overlap speedSq c : ℝ) :
    mass * scalarShiftedQuantumTangentValue mass overlap speedSq c =
      projectiveQuantumTangentValue mass overlap speedSq +
        (mass * c - overlap) ^ 2 := by
  unfold scalarShiftedQuantumTangentValue projectiveQuantumTangentValue
  ring

/-- The quotient-free projective value is invariant after changing the tangent by any real
multiple of the vacuum/state direction. -/
theorem projectiveQuantumTangentValue_scalarShift_invariant
    (mass overlap speedSq c : ℝ) :
    projectiveQuantumTangentValue mass (overlap - c * mass)
        (scalarShiftedQuantumTangentValue mass overlap speedSq c) =
      projectiveQuantumTangentValue mass overlap speedSq := by
  unfold scalarShiftedQuantumTangentValue projectiveQuantumTangentValue
  ring

/-- Every scalar recentering has mass-weighted energy at least the projective tangent value. -/
theorem projectiveQuantumTangentValue_le_mass_mul_shifted
    (mass overlap speedSq c : ℝ) :
    projectiveQuantumTangentValue mass overlap speedSq ≤
      mass * scalarShiftedQuantumTangentValue mass overlap speedSq c := by
  rw [mass_mul_scalarShiftedQuantumTangentValue]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- For positive mass, the normalized projective tangent is a lower bound for every scalar-shifted
tangent value. -/
theorem projectiveQuantumTangentValue_div_le_shifted
    {mass : ℝ} (hmass : 0 < mass) (overlap speedSq c : ℝ) :
    projectiveQuantumTangentValue mass overlap speedSq / mass ≤
      scalarShiftedQuantumTangentValue mass overlap speedSq c := by
  exact (div_le_iff₀ hmass).2
    (by simpa [mul_comm] using
      projectiveQuantumTangentValue_le_mass_mul_shifted mass overlap speedSq c)

/-- The canonical scalar connection `overlap/mass` attains the projective minimum exactly. -/
theorem scalarShiftedQuantumTangentValue_canonical
    {mass : ℝ} (hmass : mass ≠ 0) (overlap speedSq : ℝ) :
    scalarShiftedQuantumTangentValue mass overlap speedSq (overlap / mass) =
      projectiveQuantumTangentValue mass overlap speedSq / mass := by
  unfold scalarShiftedQuantumTangentValue projectiveQuantumTangentValue
  field_simp [hmass]
  ring

/-- Pure-state quantum Fisher value in the conventional normalization `4 ds_FS^2`. -/
def pureStateQuantumFisherValue (mass overlap speedSq : ℝ) : ℝ :=
  4 * projectiveQuantumTangentValue mass overlap speedSq / mass ^ 2

/-- Nonnegative projective tangent value gives nonnegative pure-state quantum Fisher value. -/
theorem pureStateQuantumFisherValue_nonneg
    {mass overlap speedSq : ℝ}
    (h : 0 ≤ projectiveQuantumTangentValue mass overlap speedSq) :
    0 ≤ pureStateQuantumFisherValue mass overlap speedSq := by
  exact div_nonneg (mul_nonneg (by norm_num) h) (sq_nonneg _)

/-- Quantum Fisher value is scalar-phase gauge invariant. -/
theorem pureStateQuantumFisherValue_scalarShift_invariant
    (mass overlap speedSq c : ℝ) :
    pureStateQuantumFisherValue mass (overlap - c * mass)
        (scalarShiftedQuantumTangentValue mass overlap speedSq c) =
      pureStateQuantumFisherValue mass overlap speedSq := by
  rw [pureStateQuantumFisherValue, pureStateQuantumFisherValue,
    projectiveQuantumTangentValue_scalarShift_invariant]

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The intrinsic two-vector projective tangent energy.  This is the unnormalised Fubini--Study
metric numerator and the determinant of the two-vector Gram matrix. -/
def projectiveGramTangentEnergy (v w : E) : ℝ :=
  ‖v‖ ^ 2 * ‖w‖ ^ 2 - ‖inner 𝕜 v w‖ ^ 2

/-- Every projective Gram tangent energy is nonnegative by Cauchy--Schwarz. -/
theorem projectiveGramTangentEnergy_nonneg (v w : E) :
    0 ≤ projectiveGramTangentEnergy (𝕜 := 𝕜) v w := by
  have hinner : ‖inner 𝕜 v w‖ ≤ ‖v‖ * ‖w‖ :=
    norm_inner_le_norm v w
  have hinner0 : 0 ≤ ‖inner 𝕜 v w‖ := norm_nonneg _
  have hprod0 : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  unfold projectiveGramTangentEnergy
  nlinarith [sq_nonneg (‖v‖ * ‖w‖ - ‖inner 𝕜 v w‖)]

/-- Vector projective energy is the scalar projective value of its three Gram coordinates. -/
theorem projectiveGramTangentEnergy_eq_value (v w : E) :
    projectiveGramTangentEnergy (𝕜 := 𝕜) v w =
      projectiveQuantumTangentValue (‖v‖ ^ 2) (‖inner 𝕜 v w‖) (‖w‖ ^ 2) := by
  rfl

/-- For unit vectors, projective Gram energy is exactly the squared projective-angle defect used
by Rayleigh-gap estimates.  This is the normalization-free value specialized to unit mass. -/
theorem projectiveGramTangentEnergy_eq_unit_projectiveDefect
    {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    projectiveGramTangentEnergy (𝕜 := 𝕜) v w = 1 - ‖inner 𝕜 v w‖ ^ 2 := by
  simp [projectiveGramTangentEnergy, hv, hw]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- In any complex moment/Krylov realization, the projective energy of the first two columns is
the first nontrivial `2 x 2` Hankel determinant `m₀ m₂ - m₁²`.  This is the direct value bridge
from pure-state quantum Fisher geometry to first-step Krylov nontermination. -/
theorem projectiveGramTangentEnergy_eq_firstKrylovDeterminant
    (m : ℕ → ℝ) (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ)) :
    projectiveGramTangentEnergy (𝕜 := ℂ) (v 0) (v 1) =
      m 0 * m 2 - m 1 ^ 2 := by
  have h00 := hgram 0 0
  have h11 := hgram 1 1
  have h01 : inner ℂ (v 0) (v 1) = (m 1 : ℂ) := by
    simpa using hgram 0 1
  rw [inner_self_eq_norm_sq_to_K] at h00 h11
  have hv0 : ‖v 0‖ ^ 2 = m 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, zero_add] using! h00
  have hv1 : ‖v 1‖ ^ 2 = m 2 := by
    apply Complex.ofReal_injective
    norm_num at h11 ⊢
    exact h11
  unfold projectiveGramTangentEnergy
  rw [hv0, hv1, h01, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end

end HTGeometry
