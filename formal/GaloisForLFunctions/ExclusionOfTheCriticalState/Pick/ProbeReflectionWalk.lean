import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelIsAKreinForm
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic
import GaloisForLFunctions.HilbertMetric.QuantumWalk.Compression
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The reflection walk of the actual Weil probe space

On the square-summable zeta-zero coordinates, let `R` reflect a zero across
the critical line and let `Q` project onto a finite span of actual probe
vectors. The operator `W=R(2Q-1)` is a surjective linear isometry and
`Q W^n Q = T_n(Q R Q) Q` at every order. The matrix coefficients of `Q R Q`
on the probe vectors are exactly the bare Weil probe kernel. Polynomial
evaluation is on the compressed operator, without treating the generally
nonorthogonal probe vectors as an orthonormal basis.
-/

noncomputable section
open scoped lp
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri HTGeometry Zeta23
open _root_.Polynomial

abbrev ZeroSpace := ℓ²(zetaZeroConfig.carrier, ℂ)

/-- The actual reflection of zeta-zero coordinates, as a bounded operator. -/
def zeroReflection : ZeroSpace →L[ℂ] ZeroSpace :=
  (reflectLin zetaZeroConfig).mkContinuous 1 (fun x => by
    change ‖reflectVec zetaZeroConfig x‖ ≤ 1 * ‖x‖
    rw [norm_reflectVec, one_mul])

theorem zeroReflection_apply (x : ZeroSpace) :
    zeroReflection x = reflectVec zetaZeroConfig x := rfl

theorem zeroReflection_involutive (x : ZeroSpace) : zeroReflection (zeroReflection x) = x := by
  ext τ
  simp only [zeroReflection_apply, reflectVec_apply, reflectCarrier_reflectCarrier]

theorem zeroReflection_sq : zeroReflection * zeroReflection = 1 := by
  apply ContinuousLinearMap.ext
  exact zeroReflection_involutive

theorem norm_zeroReflection (x : ZeroSpace) : ‖zeroReflection x‖ = ‖x‖ :=
  norm_reflectVec zetaZeroConfig x

/-- A finite family of real probes in their established domain `p ≥ 1`. -/
def probeSpace {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : Submodule ℂ ZeroSpace :=
  Submodule.span ℂ (Set.range fun i => probeVec (p i).property)

instance probeSpace_finiteDimensional {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    FiniteDimensional ℂ (probeSpace p) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- Orthogonal projection onto the actual finite probe span. -/
def probeProjection {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : ZeroSpace →L[ℂ] ZeroSpace :=
  (probeSpace p).starProjection

theorem probeProjection_vec {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (i : Fin N) :
    probeProjection p (probeVec (p i).property) = probeVec (p i).property :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨i, rfl⟩)

/-- The zero reflection followed after reflection in the finite probe span. -/
def walk {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : ZeroSpace →L[ℂ] ZeroSpace :=
  zeroReflection * _root_.HTGeometry.projectionReflection (probeProjection p)

private def reverseWalk {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : ZeroSpace →L[ℂ] ZeroSpace :=
  _root_.HTGeometry.projectionReflection (probeProjection p) * zeroReflection

private theorem reverseWalk_mul {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    reverseWalk p * walk p = 1 := by
  have hQ := _root_.HTGeometry.projectionReflection_sq_eq_one
    (probeProjection p) (probeSpace p).isIdempotentElem_starProjection
  calc
    _ = _root_.HTGeometry.projectionReflection (probeProjection p) *
        (zeroReflection * zeroReflection) *
        _root_.HTGeometry.projectionReflection (probeProjection p) := by
      simp only [reverseWalk, walk, mul_assoc]
    _ = 1 := by rw [zeroReflection_sq, mul_one, hQ]

private theorem walk_mul_reverseWalk {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    walk p * reverseWalk p = 1 := by
  have hQ := _root_.HTGeometry.projectionReflection_sq_eq_one
    (probeProjection p) (probeSpace p).isIdempotentElem_starProjection
  calc
    _ = zeroReflection *
        (_root_.HTGeometry.projectionReflection (probeProjection p) *
          _root_.HTGeometry.projectionReflection (probeProjection p)) * zeroReflection := by
      simp only [reverseWalk, walk, mul_assoc]
    _ = 1 := by rw [hQ, mul_one, zeroReflection_sq]

/-- The constructed walk preserves the norm of every zero-coordinate vector. -/
theorem norm_walk {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (x : ZeroSpace) :
    ‖walk p x‖ = ‖x‖ := by
  change ‖zeroReflection (probeProjection p x + probeProjection p x - x)‖ = ‖x‖
  rw [norm_zeroReflection]
  simpa only [Submodule.reflection_apply, two_smul, probeProjection] using
    (probeSpace p).reflection.norm_map x

/-- The actual walk is a surjective linear isometry, with the reflections reversed as inverse. -/
def walkEquiv {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : ZeroSpace ≃ₗᵢ[ℂ] ZeroSpace where
  toLinearEquiv :=
    { toLinearMap := (walk p).toLinearMap
      invFun := reverseWalk p
      left_inv := fun x => congrArg (fun A : ZeroSpace →L[ℂ] ZeroSpace => A x) (reverseWalk_mul p)
      right_inv := fun x => congrArg (fun A : ZeroSpace →L[ℂ] ZeroSpace => A x) (walk_mul_reverseWalk p) }
  norm_map' := norm_walk p

private def positiveProjector : ZeroSpace →L[ℂ] ZeroSpace :=
  (1 / 2 : ℂ) • (1 + zeroReflection)

private theorem positiveProjector_idempotent : positiveProjector * positiveProjector = positiveProjector := by
  apply ContinuousLinearMap.ext
  intro x
  change (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x + zeroReflection x) +
      zeroReflection ((1 / 2 : ℂ) • (x + zeroReflection x))) =
    (1 / 2 : ℂ) • (x + zeroReflection x)
  rw [map_smul, map_add, zeroReflection_involutive]
  module

private theorem positiveProjector_reflection : positiveProjector + positiveProjector - 1 = zeroReflection := by
  apply ContinuousLinearMap.ext
  intro x
  change (1 / 2 : ℂ) • (x + zeroReflection x) +
    (1 / 2 : ℂ) • (x + zeroReflection x) - x = zeroReflection x
  module

/-- Compression of the actual zero reflection to the finite probe span. -/
def signal {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : ZeroSpace →L[ℂ] ZeroSpace :=
  probeProjection p * zeroReflection * probeProjection p

/-- Every compressed walk power is exactly the Chebyshev polynomial of the probe signal. -/
theorem walk_compression {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (n : ℕ) :
    probeProjection p * walk p ^ n * probeProjection p =
      aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) * probeProjection p := by
  have h := HilbertMetric.QuantumWalk.compressed_reflection_pow (𝕜 := ℂ)
    positiveProjector (probeProjection p) positiveProjector_idempotent
    (probeSpace p).isIdempotentElem_starProjection n
  rw [positiveProjector_reflection] at h
  exact h

/-- The compressed signal has the literal bare Weil kernel as its probe matrix coefficients. -/
theorem signal_inner_probe {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (i j : Fin N) :
    inner ℂ (signal p (probeVec (p j).property)) (probeVec (p i).property) =
      (bareMixedEnergy (probe (p i).val) (probe (p j).val) : ℂ) := by
  change inner ℂ (probeProjection p (zeroReflection
    (probeProjection p (probeVec (p j).property)))) (probeVec (p i).property) = _
  rw [probeProjection_vec]
  change inner ℂ ((probeSpace p).starProjection
    (zeroReflection (probeVec (p j).property))) (probeVec (p i).property) = _
  rw [(probeSpace p).inner_starProjection_left_eq_right]
  rw [show (probeSpace p).starProjection (probeVec (p i).property) =
    probeVec (p i).property from probeProjection_vec p i]
  exact (bareMixedEnergy_probe_eq_inner (p i).property (p j).property).symm

#print axioms walkEquiv
#print axioms walk_compression
#print axioms signal_inner_probe

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
