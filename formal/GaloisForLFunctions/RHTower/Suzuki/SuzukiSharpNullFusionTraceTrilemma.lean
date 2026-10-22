import GaloisForLFunctions.HTGeometry.ColorGramNullFusion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentSharpSourceDomainNoGo

/-!
# Sharp Suzuki source: null-fusion trace and orientation trilemma

Encode each depth-zero sharp Suzuki prime amplitude as one Lorentz-null `2`-spinor root.  Nullity
does remove its Lorentz self-mass, and an independent companion even makes the fused colour Gram
strictly positive definite.  It does not put the all-prime source into an ordinary trace-class
positive carrier: the fused Gram trace is exactly the sharp source square plus the two nonnegative
companion squares, hence is never summable.  Moreover the entire fused Gram, not only its
determinant, is invariant under reflection of the sharp root.

Thus a lightlike encoding cannot simultaneously supply ordinary positive trace class and retain
source orientation.  A surviving null/Krein construction must use a renormalized or semifinite
trace and carry orientation outside the positive Gram quotient, for example in a cross term or
determinant line.  No RH premise, Xi-zero data, asymptotic estimate, or numerical input is used.
-/

open Matrix
open scoped ComplexOrder Matrix

namespace RHTower

noncomputable section

/-- Depth-zero sharp Suzuki amplitude placed on one two-spinor coordinate. -/
def suzukiSharpNullRoot (p : Nat.Primes) : Fin 2 → ℂ :=
  fun j => if j = 0 then (suzukiCriticalEntryWallBareAmplitude p 0 : ℂ) else 0

/-- Split-signature Hermitian pairing: both coordinate axes are null and pair with each other. -/
def suzukiSharpNullKreinPairing (u v : Fin 2 → ℂ) : ℂ :=
  star (u 0) * v 1 + star (u 1) * v 0

/-- Sharp source has exactly zero self-charge in the split Krein form. -/
theorem suzukiSharpNullRoot_kreinSelf_eq_zero (p : Nat.Primes) :
    suzukiSharpNullKreinPairing (suzukiSharpNullRoot p) (suzukiSharpNullRoot p) = 0 := by
  simp [suzukiSharpNullKreinPairing, suzukiSharpNullRoot]

/-- Unlike the positive Gram, split Krein cross-charge remembers sharp-source orientation. -/
theorem suzukiSharpNullKreinPairing_neg_left
    (u v : Fin 2 → ℂ) :
    suzukiSharpNullKreinPairing (-u) v = -suzukiSharpNullKreinPairing u v := by
  simp [suzukiSharpNullKreinPairing]
  ring

/-- Colour event obtained by fusing the sharp null root with an arbitrary prime-dependent root. -/
def suzukiSharpNullFusionEvent
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.ColorEventMatrix :=
  GaloisForLFunctions.HTGeometry.twoNullRootEvent
    (suzukiSharpNullRoot p) (companion p)

/-- Positive trace energy of the fused Gram, written as twice its Lorentz time coordinate. -/
def suzukiSharpNullFusionTraceEnergy
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) : ℝ :=
  2 * GaloisForLFunctions.HTGeometry.colorGramTime
    (suzukiSharpNullFusionEvent companion p)

private theorem colorColumnNormSq_twoNullRootEvent
    (u v : Fin 2 → ℂ) (j : Fin 2) :
    GaloisForLFunctions.HTGeometry.colorColumnNormSq
        (GaloisForLFunctions.HTGeometry.twoNullRootEvent u v) j =
      Complex.normSq (u j) + Complex.normSq (v j) := by
  change Complex.normSq (u j) + Complex.normSq (v j) + Complex.normSq 0 = _
  simp

/-- Exact trace decomposition: nullity does not erase Euclidean source energy. -/
theorem suzukiSharpNullFusionTraceEnergy_eq
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) :
    suzukiSharpNullFusionTraceEnergy companion p =
      suzukiCriticalEntryWallBareAmplitude p 0 ^ (2 : ℕ) +
        Complex.normSq (companion p 0) + Complex.normSq (companion p 1) := by
  rw [suzukiSharpNullFusionTraceEnergy,
    GaloisForLFunctions.HTGeometry.colorGramTime,
    suzukiSharpNullFusionEvent,
    colorColumnNormSq_twoNullRootEvent,
    colorColumnNormSq_twoNullRootEvent]
  simp [suzukiSharpNullRoot, Complex.normSq_ofReal]
  ring

/-- Trace energy is literally the real trace of the positive colour Gram matrix. -/
theorem suzukiSharpNullFusionTraceEnergy_eq_gramTrace
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) :
    suzukiSharpNullFusionTraceEnergy companion p =
      (Matrix.trace (GaloisForLFunctions.HTGeometry.colorGramMatrix
        (suzukiSharpNullFusionEvent companion p))).re := by
  rw [suzukiSharpNullFusionTraceEnergy, Matrix.trace_fin_two,
    GaloisForLFunctions.HTGeometry.colorGramMatrix_apply_zero_zero,
    GaloisForLFunctions.HTGeometry.colorGramMatrix_apply_one_one]
  simp [GaloisForLFunctions.HTGeometry.colorGramTime]
  ring

/-- Every individual sharp source packet is exactly Lorentz-null. -/
theorem suzukiSharpNullRoot_lorentz_null (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.colorGramLorentzMassSq
      (GaloisForLFunctions.HTGeometry.singleColorEvent (suzukiSharpNullRoot p)) = 0 :=
  GaloisForLFunctions.HTGeometry.singleColorEvent_lorentz_null _

/-- Every companion leaves at least the full sharp source square in positive trace energy. -/
theorem suzukiSharpNullFusionTraceEnergy_ge_source_sq
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) :
    suzukiCriticalEntryWallBareAmplitude p 0 ^ (2 : ℕ) ≤
      suzukiSharpNullFusionTraceEnergy companion p := by
  rw [suzukiSharpNullFusionTraceEnergy_eq]
  nlinarith [Complex.normSq_nonneg (companion p 0),
    Complex.normSq_nonneg (companion p 1)]

/-- No arbitrary prime-dependent companion makes the fused positive trace energy summable. -/
theorem no_summable_suzukiSharpNullFusionTraceEnergy
    (companion : Nat.Primes → Fin 2 → ℂ) :
    ¬ Summable (suzukiSharpNullFusionTraceEnergy companion) := by
  intro hsum
  apply not_summable_sq_suzukiCriticalEntryWallBareAmplitude_zero
  exact Summable.of_nonneg_of_le (fun p => sq_nonneg _)
    (suzukiSharpNullFusionTraceEnergy_ge_source_sq companion) hsum

/-- **Trace-class no-go.**  The literal fused Gram traces are nonsummable for every companion. -/
theorem no_summable_suzukiSharpNullFusion_gramTrace
    (companion : Nat.Primes → Fin 2 → ℂ) :
    ¬ Summable (fun p : Nat.Primes =>
      (Matrix.trace (GaloisForLFunctions.HTGeometry.colorGramMatrix
        (suzukiSharpNullFusionEvent companion p))).re) := by
  intro hsum
  apply no_summable_suzukiSharpNullFusionTraceEnergy companion
  exact hsum.congr fun p =>
    (suzukiSharpNullFusionTraceEnergy_eq_gramTrace companion p).symm

/-- **Orientation no-go.**  Sharp-root reflection leaves the entire fused positive Gram fixed. -/
theorem suzukiSharpNullFusionGram_reflection_invariant
    (companion : Nat.Primes → Fin 2 → ℂ) (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.colorGramMatrix
        (GaloisForLFunctions.HTGeometry.twoNullRootEvent
          (-suzukiSharpNullRoot p) (companion p)) =
      GaloisForLFunctions.HTGeometry.colorGramMatrix
        (suzukiSharpNullFusionEvent companion p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiSharpNullFusionEvent, suzukiSharpNullRoot,
      GaloisForLFunctions.HTGeometry.colorGramMatrix,
      GaloisForLFunctions.HTGeometry.twoNullRootEvent,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Fixed independent null companion used to rule out rank degeneracy as the obstruction. -/
def suzukiSharpNullCanonicalCompanion (_p : Nat.Primes) : Fin 2 → ℂ :=
  fun j => if j = 1 then 1 else 0

/-- Pairing with the dual null root recovers the exact signed sharp amplitude. -/
theorem suzukiSharpNullRoot_kreinPair_canonical_eq (p : Nat.Primes) :
    suzukiSharpNullKreinPairing
        (suzukiSharpNullRoot p) (suzukiSharpNullCanonicalCompanion p) =
      (suzukiCriticalEntryWallBareAmplitude p 0 : ℂ) := by
  simp [suzukiSharpNullKreinPairing, suzukiSharpNullRoot,
    suzukiSharpNullCanonicalCompanion]

/-- Dual-null cross-charge is nonzero at every prime. -/
theorem suzukiSharpNullRoot_kreinPair_canonical_ne_zero (p : Nat.Primes) :
    suzukiSharpNullKreinPairing
        (suzukiSharpNullRoot p) (suzukiSharpNullCanonicalCompanion p) ≠ 0 := by
  rw [suzukiSharpNullRoot_kreinPair_canonical_eq]
  exact_mod_cast ne_of_gt (suzukiCriticalEntryWallBareAmplitude_zero_pos p)

/--
**Positive survivor.**  Split Krein geometry gives the sharp packet zero self-cost while its mixed
dual-null charge recovers the exact amplitude and reverses sign under source reflection.
-/
theorem suzukiSharpNullKreinOrientationSurvivor (p : Nat.Primes) :
    suzukiSharpNullKreinPairing (suzukiSharpNullRoot p) (suzukiSharpNullRoot p) = 0 ∧
    suzukiSharpNullKreinPairing
        (suzukiSharpNullRoot p) (suzukiSharpNullCanonicalCompanion p) =
      (suzukiCriticalEntryWallBareAmplitude p 0 : ℂ) ∧
    suzukiSharpNullKreinPairing
        (-suzukiSharpNullRoot p) (suzukiSharpNullCanonicalCompanion p) =
      -(suzukiCriticalEntryWallBareAmplitude p 0 : ℂ) := by
  rw [suzukiSharpNullRoot_kreinSelf_eq_zero,
    suzukiSharpNullRoot_kreinPair_canonical_eq,
    suzukiSharpNullKreinPairing_neg_left,
    suzukiSharpNullRoot_kreinPair_canonical_eq]
  simp

/-- Sharp root plus canonical companion has positive-definite Gram at every prime. -/
theorem suzukiSharpNullCanonicalFusion_gram_posDef (p : Nat.Primes) :
    (GaloisForLFunctions.HTGeometry.colorGramMatrix
        (GaloisForLFunctions.HTGeometry.singleColorEvent (suzukiSharpNullRoot p)) +
      GaloisForLFunctions.HTGeometry.colorGramMatrix
        (GaloisForLFunctions.HTGeometry.singleColorEvent
          (suzukiSharpNullCanonicalCompanion p))).PosDef := by
  apply GaloisForLFunctions.HTGeometry.independent_nullRoot_gram_add_posDef
  simp [suzukiSharpNullRoot, suzukiSharpNullCanonicalCompanion]
  exact_mod_cast ne_of_gt (suzukiCriticalEntryWallBareAmplitude_zero_pos p)

/--
**Sharp null-fusion trilemma.**  Source packets are individually lightlike; an explicit independent
companion makes every local fusion strictly positive definite; nevertheless no choice of companions
makes the global positive Gram trace summable.
-/
theorem suzukiSharpNullFusionTraceTrilemma :
    (∀ p : Nat.Primes,
      GaloisForLFunctions.HTGeometry.colorGramLorentzMassSq
        (GaloisForLFunctions.HTGeometry.singleColorEvent (suzukiSharpNullRoot p)) = 0) ∧
    (∀ p : Nat.Primes,
      (GaloisForLFunctions.HTGeometry.colorGramMatrix
          (GaloisForLFunctions.HTGeometry.singleColorEvent (suzukiSharpNullRoot p)) +
        GaloisForLFunctions.HTGeometry.colorGramMatrix
          (GaloisForLFunctions.HTGeometry.singleColorEvent
            (suzukiSharpNullCanonicalCompanion p))).PosDef) ∧
    (∀ companion : Nat.Primes → Fin 2 → ℂ,
      ¬ Summable (fun p : Nat.Primes =>
        (Matrix.trace (GaloisForLFunctions.HTGeometry.colorGramMatrix
          (suzukiSharpNullFusionEvent companion p))).re)) := by
  exact ⟨suzukiSharpNullRoot_lorentz_null,
    suzukiSharpNullCanonicalFusion_gram_posDef,
    no_summable_suzukiSharpNullFusion_gramTrace⟩

end

end RHTower
