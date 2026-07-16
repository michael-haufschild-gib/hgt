import Mathlib.LinearAlgebra.Matrix.PosDef
import GaloisForLFunctions.HTGeometry.LeeYangForcingThreshold

/-!
# The positivity pencil `t • A − P`: its localization locus is a closed forcing ray

For real square matrices with `A` positive semidefinite, the set of weights `t` at
which the pencil `t • A − P` is positive semidefinite is a forcing family (an up-set:
added weight on the positive block preserves positivity,
`isForcingFamily_pencilPositivityLocus`) and is closed
(`isClosed_pencilPositivityLocus`): positivity is an intersection of closed
half-lines in `t`, one for each test vector.

By the threshold theory of `LeeYangForcingThreshold` the locus is therefore decided
by the margin sign away from its threshold, attains its threshold, and — under the
free half `1 ≤ sInf` — positivity of `A − P` at the physical weight `t = 1` is
*exactly* the pinning of the pencil threshold at `1`
(`pencil_posSemidef_iff_csInf_eq_one`): a no-margin equality, not an inequality.
-/

open Matrix Set

namespace GaloisForLFunctions

variable {n : Type*} [Fintype n]

/-- The localization locus of the pencil `t • A − P`: the set of weights at which the
pencil is positive semidefinite. -/
def pencilPositivityLocus (A P : Matrix n n ℝ) : Set ℝ :=
  {t : ℝ | (t • A - P).PosSemidef}

/-- **Monotone forcing for the pencil.** If `A` is positive semidefinite, added weight
preserves pencil positivity: the locus is a forcing family. -/
theorem isForcingFamily_pencilPositivityLocus {A P : Matrix n n ℝ}
    (hA : A.PosSemidef) : IsForcingFamily (pencilPositivityLocus A P) := by
  intro s t hs hst
  have hdecomp : t • A - P = (s • A - P) + (t - s) • A := by
    rw [sub_smul]
    abel
  show (t • A - P).PosSemidef
  rw [hdecomp]
  exact Matrix.PosSemidef.add hs (hA.smul (sub_nonneg.mpr hst))

/-- **Positivity is a closed condition on the weight.** The pencil locus is the
intersection over test vectors of closed half-lines in `t`, hence closed. -/
theorem isClosed_pencilPositivityLocus {A P : Matrix n n ℝ}
    (hA : A.IsHermitian) (hP : P.IsHermitian) :
    IsClosed (pencilPositivityLocus A P) := by
  have hrepr : pencilPositivityLocus A P
      = ⋂ x : n → ℝ, {t : ℝ | x ⬝ᵥ (P *ᵥ x) ≤ t * (x ⬝ᵥ (A *ᵥ x))} := by
    ext t
    simp only [pencilPositivityLocus, mem_setOf_eq, mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · intro h x
      have hx := h.2 x
      rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul] at hx
      linarith
    · intro h
      refine ⟨(hA.smul (IsSelfAdjoint.all t)).sub hP, fun x => ?_⟩
      have hx := h x
      rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      linarith
  rw [hrepr]
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.mul continuous_const)

/-- **The no-margin equality for the pencil.** Under the free half `1 ≤ sInf`,
positivity of `A − P` at the physical weight is exactly the pinning of the pencil
threshold at `1`. -/
theorem pencil_posSemidef_iff_csInf_eq_one {A P : Matrix n n ℝ}
    (hA : A.PosSemidef) (hP : P.IsHermitian)
    (hne : (pencilPositivityLocus A P).Nonempty)
    (hbd : BddBelow (pencilPositivityLocus A P))
    (hfree : 1 ≤ sInf (pencilPositivityLocus A P)) :
    (A - P).PosSemidef ↔ sInf (pencilPositivityLocus A P) = 1 := by
  have h1 : (A - P).PosSemidef ↔ (1 : ℝ) ∈ pencilPositivityLocus A P := by
    simp [pencilPositivityLocus]
  rw [h1, mem_iff_eq_csInf_of_le
    (isClosed_pencilPositivityLocus hA.isHermitian hP) hne hbd hfree]
  exact eq_comm

end GaloisForLFunctions
