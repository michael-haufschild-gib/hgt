import GaloisForLFunctions.RHTower.SecondMomentTailBound
import GaloisForLFunctions.RHTower.ProlateGroundTotalMass

/-!
# The tail of the normalized prolate integral is uniformly small

The corpus bounds the second moment of the normalized rescaled profile on the window,
`normalizedProlate_secondMoment_le`.  Feeding that into the second-moment tail bound gives, for
every cut `K` inside the window,

```text
| ∫_K^{sqrt c} Psi_c |  ≤  sqrt(N / K) ,
```

uniformly in the bandwidth, where `N` is any bound for the window second moment.  Together with the
evenness of the profile this makes the whole tail of `∫ Psi_c` as small as one likes, which is the
hypothesis the three-epsilon transfer needs to turn locally uniform convergence on compacts into
convergence of the integrals.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The window second moment dominates any sub-interval second moment. -/
theorem intervalIntegral_secondMoment_mono {c K N : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hKc : K ≤ Real.sqrt c) (hcpos : 0 < c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hmom : (∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
      ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2) ≤ N) :
    (∫ ξ in K..(Real.sqrt c), ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2) ≤ N := by
  have hcont : Continuous fun ξ : ℝ => ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2 :=
    (continuous_pow 2).mul ((continuous_normalizedProlateProfile hsm).pow 2)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hleft : (-Real.sqrt c : ℝ) ≤ K := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := fun ξ : ℝ => ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2)
    (μ := MeasureTheory.volume) (a := -Real.sqrt c) (b := K) (c := Real.sqrt c)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hnn : (0 : ℝ) ≤ ∫ ξ in (-Real.sqrt c)..K,
      ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2 :=
    intervalIntegral.integral_nonneg hleft fun ξ _ => by positivity
  linarith [hadd, hnn, hmom]

/-- **The tail of the normalized prolate integral, uniformly.** -/
theorem normalizedProlate_tail_le {c K N : ℝ} {Phi : ℝ → ℝ}
    (hcpos : 0 < c) (hK : 0 < K) (hKc : K ≤ Real.sqrt c) (hN : 0 < N)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hmom : (∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
      ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2) ≤ N) :
    |∫ ξ in K..(Real.sqrt c), normalizedProlateProfile c Phi ξ| ≤ Real.sqrt (N / K) :=
  intervalIntegral_abs_le_sqrt hK hKc hN (continuous_normalizedProlateProfile hsm)
    (intervalIntegral_secondMoment_mono hK hKc hcpos hsm hmom)

/-- **The tail is small when the cut is far out.**  For any target `δ` a cut past `N/δ²` works. -/
theorem normalizedProlate_tail_lt {c K N δ : ℝ} {Phi : ℝ → ℝ}
    (hcpos : 0 < c) (hK : 0 < K) (hKc : K ≤ Real.sqrt c) (hN : 0 < N) (hδ : 0 < δ)
    (hcut : N / δ ^ 2 < K)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hmom : (∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
      ξ ^ 2 * (normalizedProlateProfile c Phi ξ) ^ 2) ≤ N) :
    |∫ ξ in K..(Real.sqrt c), normalizedProlateProfile c Phi ξ| < δ := by
  refine lt_of_le_of_lt (normalizedProlate_tail_le hcpos hK hKc hN hsm hmom) ?_
  have hlt : N / K < δ ^ 2 := by
    rw [div_lt_iff₀ hK]
    rw [div_lt_iff₀ (by positivity)] at hcut
    nlinarith [hcut]
  calc Real.sqrt (N / K) < Real.sqrt (δ ^ 2) := by
        refine Real.sqrt_lt_sqrt (by positivity) hlt
    _ = δ := Real.sqrt_sq hδ.le

end GaloisForLFunctions.RHTower

end
