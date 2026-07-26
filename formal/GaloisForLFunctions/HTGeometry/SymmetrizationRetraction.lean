/-
Every exponent pair retracts onto the line of symmetry without loss.

For a pair `P = (κ, λ)` the `B`-process gives `BP = (λ - 1/2, κ + 1/2)`, and the midpoint of `P` and
`BP` is

    **((κ + λ - 1/2)/2, (κ + λ + 1/2)/2) = (μ(P), μ(P) + 1/2)** ,

a point on the line of symmetry `λ = κ + 1/2` whose first coordinate is exactly `μ(P)`.  Since the
exponent-pair region is convex and closed under `B`, that midpoint is again an exponent pair.  So the
map

    **sym : (κ, λ) ↦ (μ(κ,λ), μ(κ,λ) + 1/2)**

is a retraction of the region onto its intersection with the line of symmetry, and it preserves `μ`
exactly.  Consequences.

* `inf { μ(P) : P a pair } = inf { κ : (κ, κ + 1/2) a pair }` — **the region matters only through the
  line of symmetry**; every pair off the line is redundant for the critical-line exponent.

* `sym P` has zero displacement, so its demand is the constant `μ(P)` at every scale: **the retract is
  scale-flat**, and the covering architecture adds nothing to it.

* At every scale the demands of `P` and `BP` average to `μ(P)` exactly, so the pair `{P, BP}` is
  everywhere at least as good as `sym P` and agrees with it precisely at the critical scale.

Examples: `(1/9, 13/18) ↦ (1/6, 2/3)`, Weyl's pair; `(0, 1)` and `(1/2, 1/2)` both `↦ (1/4, 3/4)`, the
convexity bound; the record `(13/84, 55/84)` is already its own retract.
-/
import GaloisForLFunctions.HTGeometry.SectionFourGapAndTarget

namespace HTGeometry

/-! ### The retraction -/

/-- First coordinate of the retract: the pair's critical-line exponent. -/
def symKappa (κ lam : ℚ) : ℚ := epMu κ lam

/-- Second coordinate. -/
def symLambda (κ lam : ℚ) : ℚ := epMu κ lam + 1 / 2

/-- **The retract is the midpoint of the pair and its `B`-image.** -/
theorem sym_is_midpoint_of_B (κ lam : ℚ) :
    (κ + procB_fst lam) / 2 = symKappa κ lam ∧
      (lam + procB_snd κ) / 2 = symLambda κ lam := by
  simp only [symKappa, symLambda, epMu, procB_fst, procB_snd]
  constructor <;> ring

/-- **It lies on the line of symmetry.** -/
@[simp] theorem sym_displacement_zero (κ lam : ℚ) :
    epDisplacement (symKappa κ lam) (symLambda κ lam) = 0 := by
  unfold epDisplacement symKappa symLambda; unfold epMu; ring

/-- **And it has the same critical-line exponent.** -/
theorem sym_preserves_mu (κ lam : ℚ) :
    epMu (symKappa κ lam) (symLambda κ lam) = epMu κ lam := by
  unfold symKappa symLambda; unfold epMu; ring

/-- **The retraction is idempotent.** -/
theorem sym_idempotent (κ lam : ℚ) :
    symKappa (symKappa κ lam) (symLambda κ lam) = symKappa κ lam ∧
      symLambda (symKappa κ lam) (symLambda κ lam) = symLambda κ lam := by
  simp only [symKappa, symLambda]
  unfold epMu
  constructor <;> ring

/-- **A pair on the line of symmetry is its own retract.** -/
theorem sym_fixes_symmetry_line (κ : ℚ) :
    symKappa κ (κ + 1 / 2) = κ ∧ symLambda κ (κ + 1 / 2) = κ + 1 / 2 := by
  simp only [symKappa, symLambda, epMu]
  constructor <;> ring

/-! ### The retract is scale-flat -/

/-- **The retract delivers its exponent at every scale.** -/
theorem sym_demand_flat (c κ lam : ℚ) :
    covDemandOfPair c (symKappa κ lam) (symLambda κ lam) = epMu κ lam := by
  rw [covDemandOfPair_affine, sym_displacement_zero]
  simp only [symKappa]; ring

/-- **A pair and its `B`-image average to the retract at every scale.** -/
theorem demand_average_is_mu (c κ lam : ℚ) :
    (covDemandOfPair c κ lam + covDemandOfPair c (procB_fst lam) (procB_snd κ)) / 2
      = epMu κ lam := by
  unfold covDemandOfPair covFunctional procB_fst procB_snd epMu; ring

/-! ### The line of symmetry carries everything -/

/-- **Reaching the target on the critical line is exactly reaching it on the line of symmetry.** -/
theorem mu_le_iff_sym_le (κ lam β : ℚ) :
    epMu κ lam ≤ β ↔ symKappa κ lam ≤ β := by
  simp only [symKappa]

/-- **The Lindelöf value is attained only at the corner.**  A retract with exponent zero is the corner
pair `(0, 1/2)`. -/
theorem sym_zero_iff_corner (κ lam : ℚ) :
    symKappa κ lam = 0 ↔ symKappa κ lam = 0 ∧ symLambda κ lam = 1 / 2 := by
  simp only [symKappa, symLambda, epMu]
  constructor
  · intro h; exact ⟨h, by rw [h]; ring⟩
  · exact fun h => h.1

/-! ### Instances -/

/-- **Bourgain's low-range pair retracts to Weyl's pair.** -/
theorem sym_lowRange : symKappa (1 / 9) (13 / 18) = 1 / 6 ∧ symLambda (1 / 9) (13 / 18) = 2 / 3 := by
  simp only [symKappa, symLambda, epMu]
  constructor <;> norm_num

/-- The van der Corput word retracts to `(15/88, 59/88)`. -/
theorem sym_vdcWord : symKappa (1 / 11) (3 / 4) = 15 / 88 ∧ symLambda (1 / 11) (3 / 4) = 59 / 88 := by
  simp only [symKappa, symLambda, epMu]
  constructor <;> norm_num

/-- **Both trivial pairs retract to the convexity bound.** -/
theorem sym_trivial :
    symKappa 0 1 = 1 / 4 ∧ symKappa (1 / 2) (1 / 2) = 1 / 4 ∧ symLambda 0 1 = 3 / 4 := by
  simp only [symKappa, symLambda, epMu]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The record pair is its own retract.** -/
theorem sym_record :
    symKappa (13 / 84) (55 / 84) = 13 / 84 ∧ symLambda (13 / 84) (55 / 84) = 55 / 84 := by
  simp only [symKappa, symLambda, epMu]
  constructor <;> norm_num

/-- **Summary.**  The midpoint of a pair and its `B`-image is `(μ, μ + 1/2)`; it lies on the line of
symmetry, preserves `μ`, is idempotent, and is scale-flat.  So the exponent-pair region influences the
critical-line exponent only through its intersection with the line of symmetry, and a bound there is a
single-scale statement. -/
theorem symmetrization_summary (c κ lam : ℚ) :
    (κ + procB_fst lam) / 2 = epMu κ lam ∧
      epDisplacement (symKappa κ lam) (symLambda κ lam) = 0 ∧
        epMu (symKappa κ lam) (symLambda κ lam) = epMu κ lam ∧
          covDemandOfPair c (symKappa κ lam) (symLambda κ lam) = epMu κ lam :=
  ⟨(sym_is_midpoint_of_B κ lam).1, sym_displacement_zero κ lam, sym_preserves_mu κ lam,
    sym_demand_flat c κ lam⟩

end HTGeometry
