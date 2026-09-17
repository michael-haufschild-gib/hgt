import GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimePrimitiveRecovery

/-!
# Label-preserving Gamma-valuation primitive profile

The cumulative adjacent-prime primitive is the source-native inverse of
adjacent incidence, but its final scalar sum at each valuation depth erases
prime labels.  This module retains the primitive before that aggregation.

The resulting infinite profile is globally `ℓ¹` on the height-Köthe source,
with the first height seminorm paying both endpoints of every adjacent
prime-index difference.  It separates every literal prime-power coordinate:
the only zero profile has zero value on every such coordinate.  The old weak
Schur kernel factors through this profile only after the per-depth scalar
aggregation.  Hence it cannot serve as a label-preserving boundary object.

No Xi divisor, zero-location statement, Riemann-hypothesis premise, numerical
computation, or added axiom occurs.
-/

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-- The unaggregated cumulative adjacent-prime primitive, retaining depth and
prime-index labels. -/
def gammaValuationAdjacentPrimitiveProfile
    (a : DeningerHeightKothe) (en : ℕ × ℕ) : ℂ :=
  gammaValuationAdjacentPrimitiveTerm en.1 a en.2

theorem gammaValuationNthPrimeAxis_pair_injective :
    Function.Injective (fun en : ℕ × ℕ =>
      gammaValuationNthPrimeAxis en.1 en.2) := by
  rintro ⟨e, n⟩ ⟨f, m⟩ h
  have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact Prod.ext (congrArg Prod.snd hpair)
    (nthPrimeSubtype_injective (congrArg Prod.fst hpair))

theorem gammaValuationNthPrimeIndexWeight_le_height (e n : ℕ) :
    (n + 1 : ℝ) ≤ deningerHeight (gammaValuationNthPrimeAxis e n) := by
  rw [gammaValuationNthPrimeAxis, deningerHeight_gammaValuationAxis]
  have hindex : (n + 1 : ℝ) ≤ (nthPrimeSubtype n : ℝ) := by
    exact_mod_cast (le_trans (by omega : n + 1 ≤ n + 2)
      (nthPrimeSubtype_index_add_two_le n))
  have hp1 : (1 : ℝ) ≤ (nthPrimeSubtype n : ℝ) := by
    exact_mod_cast (nthPrimeSubtype n).2.one_le
  have hpow : (nthPrimeSubtype n : ℝ) ^ 1 ≤
      (nthPrimeSubtype n : ℝ) ^ (e + 1) :=
    pow_le_pow_right₀ hp1 (by omega)
  exact hindex.trans (by simpa using hpow)

/-- First height controls the complete ordered depth/prime-index primitive
profile, including both endpoints of each adjacent difference. -/
theorem summable_gammaValuationAdjacentPrimitiveProfile
    (a : DeningerHeightKothe) :
    Summable (gammaValuationAdjacentPrimitiveProfile a) := by
  let w : ℕ × ℕ → ℝ := fun en =>
    (en.2 + 1 : ℝ) * ‖gammaValuationNthPrimeCoord en.1 a en.2‖
  have hbase : Summable (fun en : ℕ × ℕ =>
      deningerHeight (gammaValuationNthPrimeAxis en.1 en.2) ^ 1 *
        ‖gammaValuationNthPrimeCoord en.1 a en.2‖) :=
    (deningerHeightSeminorm_summable a 1).comp_injective
      gammaValuationNthPrimeAxis_pair_injective
  have hw : Summable w := Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
      (fun en => by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa using gammaValuationNthPrimeIndexWeight_le_height en.1 en.2)
      hbase
  have hshift : Summable (fun en : ℕ × ℕ => w (en.1, en.2 + 1)) :=
    hw.comp_injective (by
      rintro ⟨e, n⟩ ⟨f, m⟩ h
      change (e, n + 1) = (f, m + 1) at h
      have hfst : e = f := congrArg (fun z : ℕ × ℕ => z.1) h
      have hsnd : n + 1 = m + 1 := congrArg (fun z : ℕ × ℕ => z.2) h
      subst f
      have hnm : n = m := Nat.succ_injective hsnd
      subst m
      rfl)
  have hmajor : Summable (fun en : ℕ × ℕ =>
      w en + w (en.1, en.2 + 1)) := hw.add hshift
  refine Summable.of_norm_bounded hmajor (fun en => ?_)
  rcases en with ⟨e, n⟩
  change ‖gammaValuationAdjacentPrimitiveTerm e a n‖ ≤
    w (e, n) + w (e, n + 1)
  rw [gammaValuationAdjacentPrimitiveTerm, norm_mul]
  have hcast : ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) := by
    rw [show (((n + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    norm_num
  rw [hcast]
  calc
    (n + 1 : ℝ) *
        ‖gammaValuationNthPrimeCoord e a n -
          gammaValuationNthPrimeCoord e a (n + 1)‖ ≤
      (n + 1 : ℝ) *
        (‖gammaValuationNthPrimeCoord e a n‖ +
          ‖gammaValuationNthPrimeCoord e a (n + 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ w (e, n) + w (e, n + 1) := by
      dsimp [w]
      rw [mul_add]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

/-- The unaggregated profile is faithful on the literal prime-power source
axes.  Summability excludes the otherwise possible constant tail. -/
theorem gammaValuationAdjacentPrimitiveProfile_eq_zero_iff_axis_zero
    (a : DeningerHeightKothe) :
    (∀ en : ℕ × ℕ, gammaValuationAdjacentPrimitiveProfile a en = 0) ↔
      ∀ e n : ℕ, gammaValuationNthPrimeCoord e a n = 0 := by
  constructor
  · intro hprofile e
    let c : ℕ → ℂ := fun n => gammaValuationNthPrimeCoord e a n
    have hstep : ∀ n : ℕ, c n = c (n + 1) := by
      intro n
      have h := hprofile (e, n)
      change ((n + 1 : ℕ) : ℂ) * (c n - c (n + 1)) = 0 at h
      have hcoeff : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hcoeff)
    have hconst : ∀ n : ℕ, c n = c 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => exact (hstep n).symm.trans ih
    have hsum : Summable c := Summable.of_norm
        ((deningerHeightKothe_summable_norm a).comp_injective
          (gammaValuationNthPrimeAxis_injective e))
    have hzero : Tendsto c atTop (𝓝 0) := hsum.tendsto_atTop_zero
    have hconstTendsto : Tendsto (fun _ : ℕ => c 0) atTop (𝓝 (c 0)) :=
      tendsto_const_nhds
    have hconstZero : Tendsto (fun _ : ℕ => c 0) atTop (𝓝 0) :=
      hzero.congr' (Eventually.of_forall hconst)
    have hc0 : c 0 = 0 := by
      exact tendsto_nhds_unique hconstTendsto hconstZero
    intro n
    change c n = 0
    rw [hconst n, hc0]
  · intro h en
    rcases en with ⟨e, n⟩
    simp only [gammaValuationAdjacentPrimitiveProfile,
      gammaValuationAdjacentPrimitiveTerm, h e n, h e (n + 1), sub_self,
      mul_zero]

/-- Aggregating the labelled profile over prime index is exactly the old
depth layer sum. -/
theorem tsum_gammaValuationAdjacentPrimitiveProfile_eq_layerSum
    (a : DeningerHeightKothe) (e : ℕ) :
    ∑' n : ℕ, gammaValuationAdjacentPrimitiveProfile a (e, n) =
      gammaValuationLayerSum e a := by
  change gammaValuationAdjacentPrimitive e a = gammaValuationLayerSum e a
  exact gammaValuationAdjacentPrimitive_eq_layerSum e a

/-- The weak Schur kernel performs its loss of prime labels precisely by the
two per-depth scalar aggregations displayed here. -/
theorem gammaValuationWeakKernel_eq_labelledProfile_aggregate
    (a b : DeningerHeightKothe) :
    gammaValuationWeakKernel a b =
      ∑' e : ℕ,
        conj (∑' n : ℕ, gammaValuationAdjacentPrimitiveProfile a (e, n)) *
          ∑' n : ℕ, gammaValuationAdjacentPrimitiveProfile b (e, n) := by
  unfold gammaValuationWeakKernel
  apply tsum_congr
  intro e
  rw [← tsum_gammaValuationAdjacentPrimitiveProfile_eq_layerSum a e,
    ← tsum_gammaValuationAdjacentPrimitiveProfile_eq_layerSum b e]

end

end RHTower
