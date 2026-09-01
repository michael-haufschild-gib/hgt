import Mathlib

/-!
# Algebra of a topological Page--Wootters clock readout

This module formalizes the unconditional algebraic identities used by arXiv:2608.27650:

* the Rice--Mele Bloch-vector norm identity and even dispersion;
* a concrete radius-`1/2`, unit-coupling pump loop with a uniform positive gap;
* exact forward/backward cancellation of common dynamical phase;
* factorization of the two-path amplitude and its cosine coincidence fringe.

No adiabatic approximation, numerical estimate, or added axiom occurs here.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Rice--Mele algebra -/

/-- `σₓ` coefficient of the Rice--Mele Bloch Hamiltonian. -/
def riceMeleDx (J delta k : ℝ) : ℝ :=
  J * ((1 + delta) + (1 - delta) * Real.cos k)

/-- `σᵧ` coefficient of the Rice--Mele Bloch Hamiltonian. -/
def riceMeleDy (J delta k : ℝ) : ℝ :=
  J * (1 - delta) * Real.sin k

/-- `σ_z` coefficient of the Rice--Mele Bloch Hamiltonian. -/
def riceMeleDz (Delta : ℝ) : ℝ := Delta

/-- Squared length of the Rice--Mele Bloch vector. -/
def riceMeleNormSq (J delta Delta k : ℝ) : ℝ :=
  riceMeleDx J delta k ^ 2 + riceMeleDy J delta k ^ 2 + riceMeleDz Delta ^ 2

/-- Closed radicand formula, equation (6) of the paper. -/
theorem riceMeleNormSq_closedForm (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta k =
      Delta ^ 2 + 2 * J ^ 2 *
        (1 + delta ^ 2 + (1 - delta ^ 2) * Real.cos k) := by
  unfold riceMeleNormSq riceMeleDx riceMeleDy riceMeleDz
  calc
    (J * (1 + delta + (1 - delta) * Real.cos k)) ^ 2 +
          (J * (1 - delta) * Real.sin k) ^ 2 + Delta ^ 2 =
        Delta ^ 2 + J ^ 2 * ((1 + delta) ^ 2 +
          2 * (1 + delta) * (1 - delta) * Real.cos k +
          (1 - delta) ^ 2 * (Real.sin k ^ 2 + Real.cos k ^ 2)) := by ring
    _ = Delta ^ 2 + 2 * J ^ 2 *
        (1 + delta ^ 2 + (1 - delta ^ 2) * Real.cos k) := by
      rw [Real.sin_sq_add_cos_sq]
      ring

/-- Bloch-vector norm is even in crystal momentum. -/
theorem riceMeleNormSq_neg (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta (-k) = riceMeleNormSq J delta Delta k := by
  rw [riceMeleNormSq_closedForm, riceMeleNormSq_closedForm]
  simp

/-- Lower-band Rice--Mele dispersion. -/
def riceMeleLowerDispersion (omega0 J delta Delta k : ℝ) : ℝ :=
  omega0 - Real.sqrt (riceMeleNormSq J delta Delta k)

/-- Lower-band dispersion is exactly even in momentum. -/
theorem riceMeleLowerDispersion_neg (omega0 J delta Delta k : ℝ) :
    riceMeleLowerDispersion omega0 J delta Delta (-k) =
      riceMeleLowerDispersion omega0 J delta Delta k := by
  rw [riceMeleLowerDispersion, riceMeleLowerDispersion, riceMeleNormSq_neg]

/-- Dimensionless dimerization on the concrete radius-`1/2` pump loop. -/
def referenceRiceMeleDelta (tau : ℝ) : ℝ := (1 / 2 : ℝ) * Real.cos tau

/-- Staggered detuning on the concrete unit-coupling, radius-`1/2` pump loop. -/
def referenceRiceMeleDetuning (tau : ℝ) : ℝ := (1 / 2 : ℝ) * Real.sin tau

/-- Squared Bloch-vector norm on the concrete pump loop. -/
def referenceRiceMeleNormSq (k tau : ℝ) : ℝ :=
  riceMeleNormSq 1 (referenceRiceMeleDelta tau) (referenceRiceMeleDetuning tau) k

/-- The concrete pump loop remains uniformly gapped: `|d|² ≥ 1/4` at every momentum and time. -/
theorem referenceRiceMeleNormSq_ge_quarter (k tau : ℝ) :
    (1 / 4 : ℝ) ≤ referenceRiceMeleNormSq k tau := by
  rw [referenceRiceMeleNormSq, riceMeleNormSq_closedForm]
  unfold referenceRiceMeleDelta referenceRiceMeleDetuning
  have hsinSq := sq_nonneg (Real.sin tau)
  have hcosSq := sq_nonneg (Real.cos tau)
  have htrig := Real.sin_sq_add_cos_sq tau
  have hkLower := Real.neg_one_le_cos k
  have hkUpper := Real.cos_le_one k
  nlinarith [sq_nonneg (1 + Real.cos k), sq_nonneg (1 - Real.cos k)]

/-- At the zone edge and quarter-cycle, the squared norm attains the lower bound `1/4`. -/
theorem referenceRiceMeleNormSq_pi_piDivTwo :
    referenceRiceMeleNormSq Real.pi (Real.pi / 2) = 1 / 4 := by
  rw [referenceRiceMeleNormSq, riceMeleNormSq_closedForm]
  simp [referenceRiceMeleDelta, referenceRiceMeleDetuning]
  norm_num

/-- Spectral gap of the concrete two-level Rice--Mele Hamiltonian. -/
def referenceRiceMeleGap (k tau : ℝ) : ℝ :=
  2 * Real.sqrt (referenceRiceMeleNormSq k tau)

/-- The concrete reference cycle has spectral gap at least one. -/
theorem referenceRiceMeleGap_ge_one (k tau : ℝ) :
    1 ≤ referenceRiceMeleGap k tau := by
  have hsqNonneg : 0 ≤ referenceRiceMeleNormSq k tau := by
    linarith [referenceRiceMeleNormSq_ge_quarter k tau]
  have hsqrtSq := Real.sq_sqrt hsqNonneg
  have hsqrtNonneg := Real.sqrt_nonneg (referenceRiceMeleNormSq k tau)
  unfold referenceRiceMeleGap
  nlinarith [referenceRiceMeleNormSq_ge_quarter k tau]

/-- The minimum gap is attained at the zone edge and quarter-cycle. -/
theorem referenceRiceMeleGap_pi_piDivTwo :
    referenceRiceMeleGap Real.pi (Real.pi / 2) = 1 := by
  rw [referenceRiceMeleGap, referenceRiceMeleNormSq_pi_piDivTwo]
  norm_num

/-! ## Forward/backward phase algebra -/

/-- Total phase of the forward traversal. -/
def forwardTraversalPhase (dynamic geometric : ℝ) : ℝ := dynamic + geometric

/-- Total phase of the backward traversal. -/
def backwardTraversalPhase (dynamic geometric : ℝ) : ℝ := dynamic - geometric

/-- Reversing the loop cancels dynamical phase and isolates twice geometric phase. -/
theorem forwardTraversalPhase_sub_backwardTraversalPhase (dynamic geometric : ℝ) :
    forwardTraversalPhase dynamic geometric - backwardTraversalPhase dynamic geometric =
      2 * geometric := by
  unfold forwardTraversalPhase backwardTraversalPhase
  ring

/-- A common phase added to both arms disappears from their phase difference. -/
theorem forwardBackward_commonPhase_cancels (dynamic geometric common : ℝ) :
    (forwardTraversalPhase dynamic geometric + common) -
        (backwardTraversalPhase dynamic geometric + common) =
      2 * geometric := by
  unfold forwardTraversalPhase backwardTraversalPhase
  ring

/-- Pair amplitude of forward and backward traversal arms. -/
def twoTraversalAmplitude
    (dynamic geometric common reference : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((forwardTraversalPhase dynamic geometric + common : ℝ) : ℂ)) +
    Complex.exp (Complex.I *
      ((backwardTraversalPhase dynamic geometric + common + reference : ℝ) : ℂ))

/-- Relative fringe amplitude after stripping the common dynamical and path phase. -/
def relativeTraversalAmplitude (geometric reference : ℝ) : ℂ :=
  Complex.exp (Complex.I * (geometric : ℂ)) +
    Complex.exp (Complex.I * ((-geometric + reference : ℝ) : ℂ))

/-- Exact common-mode factorization of the two-path amplitude. -/
theorem twoTraversalAmplitude_factor (dynamic geometric common reference : ℝ) :
    twoTraversalAmplitude dynamic geometric common reference =
      Complex.exp (Complex.I * ((dynamic + common : ℝ) : ℂ)) *
        relativeTraversalAmplitude geometric reference := by
  rw [twoTraversalAmplitude, relativeTraversalAmplitude,
    forwardTraversalPhase, backwardTraversalPhase, mul_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> push_cast <;> ring

/-- Exact cosine fringe: squared amplitude depends only on `2γ - θ_ref`. -/
theorem normSq_relativeTraversalAmplitude (geometric reference : ℝ) :
    Complex.normSq (relativeTraversalAmplitude geometric reference) =
      2 + 2 * Real.cos (2 * geometric - reference) := by
  let h : ℝ := -geometric + reference
  have hFirst :
      Complex.exp (Complex.I * (geometric : ℂ)) =
        (Real.cos geometric : ℂ) + (Real.sin geometric : ℂ) * Complex.I := by
    rw [show Complex.I * (geometric : ℂ) = (geometric : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I]
  have hSecond :
      Complex.exp (Complex.I * ((-geometric + reference : ℝ) : ℂ)) =
        (Real.cos h : ℂ) + (Real.sin h : ℂ) * Complex.I := by
    rw [show Complex.I * ((-geometric + reference : ℝ) : ℂ) =
        ((h : ℝ) : ℂ) * Complex.I by dsimp [h]; push_cast; ring,
      Complex.exp_ofReal_mul_I]
  have hUnitFirst := Real.sin_sq_add_cos_sq geometric
  have hUnitSecond := Real.sin_sq_add_cos_sq h
  have hCross :
      Real.cos geometric * Real.cos h + Real.sin geometric * Real.sin h =
        Real.cos (2 * geometric - reference) := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [h]
    ring
  rw [relativeTraversalAmplitude, Complex.normSq_add, hFirst, hSecond]
  simp only [Complex.normSq_add_mul_I, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_zero, add_re, add_im, neg_re, neg_im]
  norm_num
  rw [hCross]

/-- The full coincidence intensity is independent of dynamical and common path phase. -/
theorem normSq_twoTraversalAmplitude (dynamic geometric common reference : ℝ) :
    Complex.normSq (twoTraversalAmplitude dynamic geometric common reference) =
      2 + 2 * Real.cos (2 * geometric - reference) := by
  rw [twoTraversalAmplitude_factor, Complex.normSq_mul,
    normSq_relativeTraversalAmplitude]
  have hNorm :
      Complex.normSq (Complex.exp (Complex.I * ((dynamic + common : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hRewrite : Complex.I * ((dynamic + common : ℝ) : ℂ) =
        (((dynamic + common : ℝ) : ℂ)) * Complex.I := by ring
    rw [hRewrite, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hNorm, one_mul]

/-- Normalized coincidence rate, matching `1 + cos(2γ - θ_ref)`. -/
def normalizedCoincidenceRate
    (dynamic geometric common reference : ℝ) : ℝ :=
  Complex.normSq (twoTraversalAmplitude dynamic geometric common reference) / 2

/-- Operational fringe law, equation (54) of the paper. -/
theorem normalizedCoincidenceRate_eq (dynamic geometric common reference : ℝ) :
    normalizedCoincidenceRate dynamic geometric common reference =
      1 + Real.cos (2 * geometric - reference) := by
  rw [normalizedCoincidenceRate, normSq_twoTraversalAmplitude]
  ring

end GaloisForLFunctions.HTGeometry

end
