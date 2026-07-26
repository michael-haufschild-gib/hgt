/-
A `t`-free bound at any admissible length requires the corner exactly.

An exponent pair gives `|Σ_(n ∼ M) n^(-it)| ≪ t^κ M^(λ-κ)`.  A **`t`-free** bound at length `M = t^c`
means `t^κ M^(λ-κ) ≤ M^(1/2) t^ε`, i.e.

    κ ≤ c · (1/2 - (λ - κ)) = c · (-d) ,   `d := (λ - κ) - 1/2` ,

so it needs a pair below the line of symmetry (`d < 0`) with `κ / (-d) ≤ c`.  The approximate
functional equation supplies only `c ≤ 1/2`, so the requirement is `κ ≤ -d/2`, i.e.

    2κ ≤ 1/2 - λ + κ   ⟺   **κ + λ ≤ 1/2** .

Since the exponent-pair region satisfies `κ ≥ 0` and `λ ≥ 1/2`, hence `κ + λ ≥ 1/2`, the condition
holds **exactly at `(κ, λ) = (0, 1/2)`**.

This sharpens the earlier statement — which concluded `a = 0` only in the limit — to an exact
equivalence at every admissible length.  It also identifies the vanishing-abscissa coordinate with the
exponent-pair sum: `σ*(P) = 1/2 + 2μ(P) = **κ + λ**`, so the distance `13/42` from `17/21` to `1/2`
recorded earlier is the distance from Bourgain's `κ+λ` to the corner's.
-/
import GaloisForLFunctions.HTGeometry.DerivativeTestOptimality

namespace HTGeometry

/-! ### The vanishing abscissa is the exponent-pair sum -/

/-- **`σ*(P) = 1/2 + 2μ(P) = κ + λ`.** -/
theorem vanishingAbscissa_eq_sum (κ lam : ℚ) :
    1 / 2 + 2 * epMu κ lam = κ + lam := by
  unfold epMu; ring

/-- For the record pair it is `17/21`. -/
theorem vanishingAbscissa_bourgain :
    1 / 2 + 2 * epMu bourgainKappa bourgainLambda = 17 / 21 := by
  rw [vanishingAbscissa_eq_sum]
  unfold bourgainKappa bourgainLambda; norm_num

/-- For Weyl's it is `5/6`. -/
theorem vanishingAbscissa_weyl :
    1 / 2 + 2 * epMu weylKappa weylLambda = 5 / 6 := by
  rw [vanishingAbscissa_eq_sum]
  unfold weylKappa weylLambda; norm_num

/-- **And the Lindelöf value is the corner's sum.** -/
theorem vanishingAbscissa_corner :
    1 / 2 + 2 * epMu cornerKappa cornerLambda = 1 / 2 := by
  rw [vanishingAbscissa_eq_sum]
  unfold cornerKappa cornerLambda; norm_num

/-- The recorded distance is the distance in `κ + λ`. -/
theorem abscissa_distance :
    (17 : ℚ) / 21 - 1 / 2 = 13 / 42 := by norm_num

/-! ### The `t`-free criterion -/

/-- The length exponent above which a pair gives a `t`-free bound: `κ / (−d)`. -/
def tFreeThreshold (κ lam : ℚ) : ℚ := κ / (1 / 2 - (lam - κ))

/-- **A pair gives a `t`-free bound at length `t^c` exactly when `κ ≤ c(−d)`.** -/
theorem tFree_iff {κ lam c : ℚ} (hd : 0 < 1 / 2 - (lam - κ)) :
    tFreeThreshold κ lam ≤ c ↔ κ ≤ c * (1 / 2 - (lam - κ)) := by
  unfold tFreeThreshold
  rw [div_le_iff₀ hd]

/-- **At the critical length the criterion is `κ + λ ≤ 1/2`.** -/
theorem tFree_at_critical_iff {κ lam : ℚ} :
    κ ≤ (1 / 2) * (1 / 2 - (lam - κ)) ↔ κ + lam ≤ 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **On the exponent-pair region that forces the corner.** -/
theorem tFree_forces_corner {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h : κ + lam ≤ 1 / 2) : κ = 0 ∧ lam = 1 / 2 := by
  constructor <;> linarith

/-- **The sharp statement.**  A `t`-free bound at any length `t^c` with `c ≤ 1/2` requires
`(κ, λ) = (0, 1/2)`. -/
theorem tFree_requires_corner {κ lam c : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (hc : 0 < c) (hc' : c ≤ 1 / 2) (h : κ ≤ c * (1 / 2 - (lam - κ))) :
    κ = 0 ∧ lam = 1 / 2 := by
  have hstep : κ ≤ (1 / 2) * (1 / 2 - (lam - κ)) := by
    rcases le_or_gt (1 / 2 - (lam - κ)) 0 with hneg | hpos
    · nlinarith
    · nlinarith
  exact tFree_forces_corner hκ hlam (tFree_at_critical_iff.mp hstep)

/-- **And the corner does give it**, at every length. -/
theorem corner_is_tFree (c : ℚ) :
    (0 : ℚ) ≤ c * (1 / 2 - (1 / 2 - 0)) := by
  norm_num

/-! ### The published pairs are far from it -/

/-- The `t`-free threshold of the trivial pair `(1/2, 1/2)`. -/
theorem tFreeThreshold_trivial : tFreeThreshold (1 / 2) (1 / 2) = 1 := by
  unfold tFreeThreshold; norm_num

/-- **It exceeds the admissible range `c ≤ 1/2` by a factor two.** -/
theorem trivial_threshold_too_large : (1 : ℚ) / 2 < tFreeThreshold (1 / 2) (1 / 2) := by
  rw [tFreeThreshold_trivial]; norm_num

/-- The `t`-free threshold of the `B`-image of the record pair's `A`-image, `(55/194, 55/97)`. -/
theorem tFreeThreshold_procB_image : tFreeThreshold (55 / 194) (55 / 97) = 55 / 42 := by
  unfold tFreeThreshold; norm_num

/-- **Also far outside the range.** -/
theorem procB_image_threshold_too_large :
    (1 : ℚ) / 2 < tFreeThreshold (55 / 194) (55 / 97) := by
  rw [tFreeThreshold_procB_image]; norm_num

/-- **Summary.**  The `t`-free requirement is exactly `κ + λ ≤ 1/2`, i.e. the corner; the best
below-line pairs have thresholds `1` and `55/42`, both beyond the admissible `1/2`; and the
vanishing-abscissa coordinate is `κ + λ` itself. -/
theorem tFree_summary :
    tFreeThreshold (1 / 2) (1 / 2) = 1 ∧
      tFreeThreshold (55 / 194) (55 / 97) = 55 / 42 ∧
      (1 / 2 + 2 * epMu bourgainKappa bourgainLambda = 17 / 21) :=
  ⟨tFreeThreshold_trivial, tFreeThreshold_procB_image, vanishingAbscissa_bourgain⟩

end HTGeometry
