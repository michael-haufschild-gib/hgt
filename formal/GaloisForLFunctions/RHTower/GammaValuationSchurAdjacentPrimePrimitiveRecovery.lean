import GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimeIncidenceNoGo

/-!
# Cumulative adjacent-prime primitive recovers the weak Gamma-valuation kernel

P-G85 proves that a local edge Gram cannot equal P-G78's complete prime covariance.  P-G86
constructs the exact positive survivor.  At each valuation depth, the all-prime layer sum is the
absolutely convergent cumulative path primitive

`sum_n (n+1) (a_n-a_(n+1))`.

The terminal flux `N a_N` vanishes because the first Deninger height seminorm controls
`(n+1)|a_n|`.  Replacing each layer sum by this primitive therefore recovers the entire weak Köthe
kernel exactly, including nonadjacent prime covariance.  Adjacent incidence is sufficient only
after applying its nonlocal inverse; an edge-by-edge scalar Feshbach average is not that inverse.
-/

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

def gammaValuationNthPrimeAxis (e n : ℕ) : DeningerPrimeLattice :=
  gammaSewnMobiusApertureStokesPrimePowerAxis (nthPrimeSubtype n, e)

theorem gammaValuationNthPrimeAxis_injective (e : ℕ) :
    Function.Injective (gammaValuationNthPrimeAxis e) := by
  intro n m h
  have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact nthPrimeSubtype_injective (congrArg Prod.fst hpair)

def gammaValuationNthPrimeCoord
    (e : ℕ) (a : DeningerHeightKothe) (n : ℕ) : ℂ :=
  (a : DeningerPrimeLattice → ℂ) (gammaValuationNthPrimeAxis e n)

theorem nthPrimeSubtype_index_add_two_le (n : ℕ) :
    n + 2 ≤ (nthPrimeSubtype n : ℕ) := by
  induction n with
  | zero => exact (nthPrimeSubtype 0).2.two_le
  | succ n ih =>
      have hmono := nthPrimeSubtype_strictMono (Nat.lt_succ_self n)
      omega

private theorem nthPrimeIndexWeight_le_height (e n : ℕ) :
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

/-- First Köthe height controls the index-weighted ordered-prime coordinates. -/
theorem summable_gammaValuationNthPrimeCoord_indexWeight
    (e : ℕ) (a : DeningerHeightKothe) :
    Summable (fun n : ℕ =>
      (n + 1 : ℝ) * ‖gammaValuationNthPrimeCoord e a n‖) := by
  have hbase : Summable (fun n : ℕ =>
      deningerHeight (gammaValuationNthPrimeAxis e n) ^ 1 *
        ‖gammaValuationNthPrimeCoord e a n‖) :=
    (deningerHeightSeminorm_summable a 1).comp_injective
      (gammaValuationNthPrimeAxis_injective e)
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun n => by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa using nthPrimeIndexWeight_le_height e n)
    hbase

def gammaValuationAdjacentPrimitiveTerm
    (e : ℕ) (a : DeningerHeightKothe) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (gammaValuationNthPrimeCoord e a n -
      gammaValuationNthPrimeCoord e a (n + 1))

theorem summable_gammaValuationAdjacentPrimitiveTerm
    (e : ℕ) (a : DeningerHeightKothe) :
    Summable (gammaValuationAdjacentPrimitiveTerm e a) := by
  let w : ℕ → ℝ := fun n =>
    (n + 1 : ℝ) * ‖gammaValuationNthPrimeCoord e a n‖
  have hw : Summable w := summable_gammaValuationNthPrimeCoord_indexWeight e a
  have hshift : Summable (fun n : ℕ => w (n + 1)) :=
    hw.comp_injective Nat.succ_injective
  have hmajor : Summable (fun n : ℕ => w n + w (n + 1)) := hw.add hshift
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rw [gammaValuationAdjacentPrimitiveTerm, norm_mul]
  have hcast : ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) := by simp
  rw [hcast]
  calc
    (n + 1 : ℝ) *
        ‖gammaValuationNthPrimeCoord e a n -
          gammaValuationNthPrimeCoord e a (n + 1)‖ ≤
      (n + 1 : ℝ) *
        (‖gammaValuationNthPrimeCoord e a n‖ +
          ‖gammaValuationNthPrimeCoord e a (n + 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ w n + w (n + 1) := by
      dsimp [w]
      nlinarith [norm_nonneg (gammaValuationNthPrimeCoord e a (n + 1))]

def gammaValuationAdjacentPrimitive
    (e : ℕ) (a : DeningerHeightKothe) : ℂ :=
  ∑' n : ℕ, gammaValuationAdjacentPrimitiveTerm e a n

private theorem sum_range_gammaValuationAdjacentPrimitiveTerm
    (e : ℕ) (a : DeningerHeightKothe) (N : ℕ) :
    (∑ n ∈ Finset.range N, gammaValuationAdjacentPrimitiveTerm e a n) =
      (∑ n ∈ Finset.range N, gammaValuationNthPrimeCoord e a n) -
        (N : ℂ) * gammaValuationNthPrimeCoord e a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [gammaValuationAdjacentPrimitiveTerm]
      push_cast
      ring

private theorem tendsto_gammaValuationNthPrimeCoord_boundary_zero
    (e : ℕ) (a : DeningerHeightKothe) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) * gammaValuationNthPrimeCoord e a N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hweight := summable_gammaValuationNthPrimeCoord_indexWeight e a
  have hzero := hweight.tendsto_atTop_zero
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _)
    (Eventually.of_forall fun N => ?_) hzero
  rw [norm_mul]
  have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hcast]
  exact mul_le_mul_of_nonneg_right (by positivity) (norm_nonneg _)

private theorem summable_gammaValuationNthPrimeCoord
    (e : ℕ) (a : DeningerHeightKothe) :
    Summable (gammaValuationNthPrimeCoord e a) := by
  exact Summable.of_norm
    ((deningerHeightKothe_summable_norm a).comp_injective
      (gammaValuationNthPrimeAxis_injective e))

theorem gammaValuationAdjacentPrimitive_eq_layerSum
    (e : ℕ) (a : DeningerHeightKothe) :
    gammaValuationAdjacentPrimitive e a = gammaValuationLayerSum e a := by
  have hprim := summable_gammaValuationAdjacentPrimitiveTerm e a
  have hcoord := summable_gammaValuationNthPrimeCoord e a
  have hprimLimit := (hprim.hasSum_iff_tendsto_nat).mp hprim.hasSum
  have hcoordLimit := (hcoord.hasSum_iff_tendsto_nat).mp hcoord.hasSum
  have hboundary := tendsto_gammaValuationNthPrimeCoord_boundary_zero e a
  have hrhs : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gammaValuationNthPrimeCoord e a n) -
        (N : ℂ) * gammaValuationNthPrimeCoord e a N) atTop
      (𝓝 (∑' n : ℕ, gammaValuationNthPrimeCoord e a n)) := by
    simpa using hcoordLimit.sub hboundary
  have hrewrite : (fun N : ℕ =>
      ∑ n ∈ Finset.range N, gammaValuationAdjacentPrimitiveTerm e a n) =
      fun N : ℕ =>
        (∑ n ∈ Finset.range N, gammaValuationNthPrimeCoord e a n) -
          (N : ℂ) * gammaValuationNthPrimeCoord e a N := by
    funext N
    exact sum_range_gammaValuationAdjacentPrimitiveTerm e a N
  rw [hrewrite] at hprimLimit
  have htsum : gammaValuationAdjacentPrimitive e a =
      ∑' n : ℕ, gammaValuationNthPrimeCoord e a n := by
    exact tendsto_nhds_unique hprimLimit hrhs
  rw [htsum, gammaValuationLayerSum]
  let f : Nat.Primes → ℂ := fun p =>
    (a : DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
  rw [← nthPrimeEquiv.tsum_eq f]
  rfl

def gammaValuationAdjacentPrimitiveKernel
    (a b : DeningerHeightKothe) : ℂ :=
  ∑' e : ℕ,
    conj (gammaValuationAdjacentPrimitive e a) *
      gammaValuationAdjacentPrimitive e b

/-- **P-G86 exact recovery.**  Inverse adjacent incidence equals complete weak covariance. -/
theorem gammaValuationAdjacentPrimitiveKernel_eq_weakKernel
    (a b : DeningerHeightKothe) :
    gammaValuationAdjacentPrimitiveKernel a b = gammaValuationWeakKernel a b := by
  unfold gammaValuationAdjacentPrimitiveKernel gammaValuationWeakKernel
  apply tsum_congr
  intro e
  rw [gammaValuationAdjacentPrimitive_eq_layerSum,
    gammaValuationAdjacentPrimitive_eq_layerSum]

/-- Cumulative primitive restores covariance missed by the local edge Gram in P-G85. -/
theorem gammaValuationAdjacentPrimitiveKernel_indexZero_indexTwo_eq_one :
    gammaValuationAdjacentPrimitiveKernel
        (gammaValuationAxisDelta (nthPrimeSubtype 0) 0)
        (gammaValuationAxisDelta (nthPrimeSubtype 2) 0) = 1 := by
  rw [gammaValuationAdjacentPrimitiveKernel_eq_weakKernel,
    gammaValuationWeakKernel_axisDelta_sameDepth]

end

end RHTower
