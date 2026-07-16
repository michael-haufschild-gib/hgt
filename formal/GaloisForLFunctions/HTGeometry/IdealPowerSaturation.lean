import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Operations

/-!
# Saturation by powers of an ideal

The saturation of `I` by powers of `m` is the directed union of the colon ideals
`I : m^n`.  Multiplying `I` by any fixed power of `m` does not change this saturation.

For a homogeneous coordinate ring and its irrelevant ideal, this is the exact algebraic reason
that a finite irrelevant-power factor changes only the affine cone vertex and not the associated
projective ideal sheaf.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Saturation of `I` by all powers of `m`, expressed as a supremum of colon ideals. -/
def idealPowerSaturation (m I : Ideal R) : Ideal R :=
  ⨆ n : ℕ, I.colon ((m ^ n : Ideal R) : Set R)

/-- Saturation by powers is monotone in the ideal being saturated. -/
theorem idealPowerSaturation_mono_right
    (m : Ideal R) {I J : Ideal R} (hIJ : I ≤ J) :
    idealPowerSaturation m I ≤ idealPowerSaturation m J := by
  apply iSup_le
  intro n
  exact (Submodule.colon_mono hIJ (Set.Subset.rfl)).trans (le_iSup (fun k : ℕ =>
    J.colon ((m ^ k : Ideal R) : Set R)) n)

/-- **Irrelevant-thickening removal.**  Multiplying an ideal by a finite power of the saturating
ideal leaves its power saturation unchanged. -/
theorem idealPowerSaturation_pow_mul
    (m I : Ideal R) (T : ℕ) :
    idealPowerSaturation m (m ^ T * I) = idealPowerSaturation m I := by
  apply le_antisymm
  · exact idealPowerSaturation_mono_right m Ideal.mul_le_left
  · apply iSup_le
    intro n
    refine (show I.colon ((m ^ n : Ideal R) : Set R) ≤
        (m ^ T * I).colon ((m ^ (n + T) : Ideal R) : Set R) from ?_).trans
      (le_iSup (fun k : ℕ =>
        (m ^ T * I).colon ((m ^ k : Ideal R) : Set R)) (n + T))
    intro r hr
    rw [Submodule.mem_colon] at hr ⊢
    intro s hs
    have hrmul : Ideal.span {r} * m ^ n ≤ I := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro z hz
      simpa [Algebra.smul_def] using hr z hz
    have hle : Ideal.span {r} * m ^ (n + T) ≤ m ^ T * I := by
      rw [pow_add, ← Ideal.mul_assoc]
      calc
        Ideal.span {r} * m ^ n * m ^ T ≤ I * m ^ T :=
          Ideal.mul_mono hrmul le_rfl
        _ = m ^ T * I := Ideal.mul_comm _ _
    exact hle (Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton r)) hs)

end

end GaloisForLFunctions.HTGeometry
