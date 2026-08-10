import GaloisForLFunctions.HTGeometry.StaticOrbitNetBellmanLaw
import GaloisForLFunctions.HTGeometry.DiagonalProjectorClockPackingLaw

/-!
# Static-ensemble parameter--time--coverage barrier

At a fixed time, an `m`-parameter coefficient-sphere Hamiltonian ensemble has an endpoint net of
size at most `(1 + 2 |t| sqrt(m) / ε)^m`.  If that endpoint image is `ε`-dense in a target, the same
net covers the target at radius `2ε`.  Any lower metric-entropy bound for the target therefore gives
an unconditional parameter--time obstruction to global coverage.

The concrete fixed-resolution corollary uses the Boolean reflection carrier.  Its covering number
is at least `2^d`, so dense coverage forces

`2^d ≤ (1 + 8 |t| sqrt(m))^m`.

This is a route-killing theorem for global-Haar explanations of Brown complexity, not a circuit
complexity lower bound.  The positive survivor is directional avoidance of the short-circuit set.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

namespace HTGeometry

variable {m : ℕ} {A : Type*} [CStarAlgebra A]

local notation "E" => EuclideanSpace ℝ (Fin m)

/- Mathlib exposes all constituent matrix instances under the operator-norm scope, but does not
assemble the bundled `CStarAlgebra` instance automatically. -/
noncomputable local instance matrixCStarAlgebra (d : ℕ) :
    CStarAlgebra (GaloisForLFunctions.HTGeometry.FiniteComplexMatrix d) where

/-- **Static target-entropy bound.**  If the coefficient-sphere endpoint image is `ε`-dense in a
target whose external `2ε`-covering number is at least `N`, then `N` cannot exceed the volumetric
size of the static orbit net. -/
theorem staticOrbit_targetEntropy_le [Nontrivial E] {P : Fin m → A}
    (hP : ∀ a, IsSelfAdjoint (P a)) (hPnorm : ∀ a, ‖P a‖ ≤ 1)
    {t eps : ℝ} (ht : t ≠ 0) (heps : 0 < eps) (hm : 0 < m)
    {S : Set A}
    (hdense : ∀ y ∈ S, ∃ theta ∈ Metric.sphere (0 : E) 1,
      ‖y - NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta))‖ ≤ eps)
    {N : ℕ}
    (hN : (N : ℕ∞) ≤
      Metric.externalCoveringNumber (Real.toNNReal (2 * eps)) S) :
    (N : ℝ) ≤ (1 + 2 * (|t| * Real.sqrt m) / eps) ^ m := by
  obtain ⟨Z, hZcard, _, hZnet⟩ :=
    exists_staticOrbit_net hP hPnorm ht heps hm
  have hcover : Metric.IsCover (Real.toNNReal (2 * eps)) S (Z : Set A) := by
    intro y hy
    obtain ⟨theta, htheta, hytheta⟩ := hdense y hy
    obtain ⟨z, hz, hthetaz⟩ := hZnet theta htheta
    refine ⟨z, hz, ?_⟩
    have hydist : dist y z ≤ 2 * eps := by
      calc
        dist y z ≤
            dist y (NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta))) +
              dist (NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta))) z :=
          dist_triangle _ _ _
        _ ≤ eps + eps := by simpa [dist_eq_norm] using add_le_add hytheta hthetaz
        _ = 2 * eps := by ring
    show edist y z ≤ ((Real.toNNReal (2 * eps) : ℝ≥0) : ℝ≥0∞)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hydist
  have hcovernum :
      Metric.externalCoveringNumber (Real.toNNReal (2 * eps)) S ≤ (Z.card : ℕ∞) := by
    simpa using hcover.externalCoveringNumber_le_encard
  have hNZ : N ≤ Z.card := by
    exact_mod_cast hN.trans hcovernum
  have hNZreal : (N : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hNZ
  exact hNZreal.trans hZcard

/-- **Concrete fixed-resolution coverage-time barrier.**  Dense coverage of all Boolean reflection
endpoints by an `m`-parameter static coefficient-sphere ensemble forces the endpoint-net capacity
to dominate `2^d`. -/
theorem staticOrbit_booleanReflection_coverage_time [Nontrivial E]
    {d : ℕ} [Nonempty (Fin d)]
    {P : Fin m → GaloisForLFunctions.HTGeometry.FiniteComplexMatrix d}
    (hP : ∀ a, IsSelfAdjoint (P a)) (hPnorm : ∀ a, ‖P a‖ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) (hm : 0 < m)
    (hdense : ∀ y ∈ GaloisForLFunctions.HTGeometry.booleanReflectionCarrier d,
      ∃ theta ∈ Metric.sphere (0 : E) 1,
        ‖y - NormedSpace.exp (t • ((-Complex.I) • coefficientHamiltonian P theta))‖ ≤ 1 / 4) :
    ((2 ^ d : ℕ) : ℝ) ≤ (1 + 8 * (|t| * Real.sqrt m)) ^ m := by
  have hN : ((2 ^ d : ℕ) : ℕ∞) ≤
      Metric.externalCoveringNumber (Real.toNNReal (2 * (1 / 4 : ℝ)))
        (GaloisForLFunctions.HTGeometry.booleanReflectionCarrier d) := by
    have hrad : Real.toNNReal (2 * (1 / 4 : ℝ)) = (1 / 2 : ℝ≥0) := by
      ext
      norm_num
    rw [hrad]
    exact
      GaloisForLFunctions.HTGeometry.two_pow_le_externalCoveringNumber_booleanReflectionCarrier d
  have h := staticOrbit_targetEntropy_le hP hPnorm ht
    (by norm_num : (0 : ℝ) < 1 / 4) hm hdense hN
  convert h using 1
  all_goals ring

end HTGeometry
