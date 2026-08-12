import GaloisForLFunctions.RHTower.GammaValuationSchurWeakKotheKernel
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalAdjacentPrimeCofinalFeshbach

/-!
# Adjacent-prime incidence cannot equal the weak Gamma-valuation kernel

P-G84 constructs a summable physical Feshbach fraction on the ordered adjacent-prime path.  This
module tests whether path locality can identify that scalar assembly with P-G78's all-prime weak
Köthe kernel.

The adjacent edge-block Gram is absolutely summable on the Köthe source.  Nevertheless it vanishes
between prime-axis deltas at prime indices `0` and `2`, whereas the weak Gamma-valuation kernel is
exactly one on the same two deltas at a common depth.  Hence adjacent local incidence cannot be the
global weak Schur kernel.  Any path realization of the latter must contain a nonlocal cumulative
inverse-incidence or boundary-flux term; local packet positivity and summability are insufficient.
-/

open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

def gammaValuationAdjacentLowerAxis (z : ℕ × ℕ) : DeningerPrimeLattice :=
  gammaSewnMobiusApertureStokesPrimePowerAxis (nthPrimeSubtype z.2, z.1)

def gammaValuationAdjacentUpperAxis (z : ℕ × ℕ) : DeningerPrimeLattice :=
  gammaSewnMobiusApertureStokesPrimePowerAxis (nthPrimeSubtype (z.2 + 1), z.1)

theorem gammaValuationAdjacentLowerAxis_injective :
    Function.Injective gammaValuationAdjacentLowerAxis := by
  rintro ⟨e, n⟩ ⟨f, m⟩ h
  have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  have hef : e = f := congrArg Prod.snd hpair
  have hnm : n = m := nthPrimeSubtype_injective (congrArg Prod.fst hpair)
  exact Prod.ext hef hnm

theorem gammaValuationAdjacentUpperAxis_injective :
    Function.Injective gammaValuationAdjacentUpperAxis := by
  rintro ⟨e, n⟩ ⟨f, m⟩ h
  have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  have hef : e = f := congrArg Prod.snd hpair
  have hsucc : n + 1 = m + 1 :=
    nthPrimeSubtype_injective (congrArg Prod.fst hpair)
  exact Prod.ext hef (by omega)

def gammaValuationAdjacentEdgeVector
    (a : DeningerHeightKothe) (z : ℕ × ℕ) : ℂ :=
  (a : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentLowerAxis z) +
    (a : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentUpperAxis z)

theorem summable_norm_gammaValuationAdjacentEdgeVector
    (a : DeningerHeightKothe) :
    Summable (fun z : ℕ × ℕ => ‖gammaValuationAdjacentEdgeVector a z‖) := by
  have hl : Summable (fun z : ℕ × ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentLowerAxis z)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      gammaValuationAdjacentLowerAxis_injective
  have hu : Summable (fun z : ℕ × ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentUpperAxis z)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      gammaValuationAdjacentUpperAxis_injective
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun z => norm_add_le _ _) (hl.add hu)

def gammaValuationAdjacentEdgeTerm
    (a b : DeningerHeightKothe) (z : ℕ × ℕ) : ℂ :=
  conj (gammaValuationAdjacentEdgeVector a z) *
    gammaValuationAdjacentEdgeVector b z

theorem summable_gammaValuationAdjacentEdgeTerm
    (a b : DeningerHeightKothe) :
    Summable (gammaValuationAdjacentEdgeTerm a b) := by
  let C := 2 * deningerHeightSeminorm 0 b
  have hbase : Summable (fun z : ℕ × ℕ =>
      ‖gammaValuationAdjacentEdgeVector a z‖ * C) :=
    (summable_norm_gammaValuationAdjacentEdgeVector a).mul_right C
  refine Summable.of_norm_bounded hbase fun z => ?_
  rw [gammaValuationAdjacentEdgeTerm, norm_mul, Complex.norm_conj]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖gammaValuationAdjacentEdgeVector b z‖ ≤
        ‖(b : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentLowerAxis z)‖ +
          ‖(b : DeningerPrimeLattice → ℂ) (gammaValuationAdjacentUpperAxis z)‖ :=
      norm_add_le _ _
    _ ≤ deningerHeightSeminorm 0 b + deningerHeightSeminorm 0 b :=
      add_le_add (deningerHeightKothe_norm_le b _) (deningerHeightKothe_norm_le b _)
    _ = C := by simp [C, two_mul]

/-- Absolutely convergent adjacent edge-block Gram on the Köthe source. -/
def gammaValuationAdjacentEdgeKernel
    (a b : DeningerHeightKothe) : ℂ :=
  ∑' z : ℕ × ℕ, gammaValuationAdjacentEdgeTerm a b z

def gammaValuationAxisDelta (p : Nat.Primes) (e : ℕ) : DeningerHeightKothe :=
  deningerKotheDelta deningerHeightKotheData
    (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))

theorem gammaValuationAxisDelta_coord
    (p q : Nat.Primes) (e f : ℕ) :
    ((gammaValuationAxisDelta p e : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (q, f)) =
      if p = q ∧ e = f then 1 else 0 := by
  rw [gammaValuationAxisDelta, deningerKotheDelta_coe]
  by_cases h : p = q ∧ e = f
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    simp only [Pi.single_apply, ite_eq_right_iff]
    intro haxis
    have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective haxis
    exact (h ⟨(congrArg Prod.fst hpair).symm,
      (congrArg Prod.snd hpair).symm⟩).elim

theorem gammaValuationLayerSum_axisDelta
    (p : Nat.Primes) (e f : ℕ) :
    gammaValuationLayerSum f (gammaValuationAxisDelta p e) =
      if e = f then 1 else 0 := by
  rw [gammaValuationLayerSum]
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl, tsum_eq_single p]
    · simp [gammaValuationAxisDelta_coord]
    · intro q hqp
      simp [gammaValuationAxisDelta_coord, hqp.symm]
  · rw [if_neg hef]
    have hzero : (fun q : Nat.Primes =>
        ((gammaValuationAxisDelta p e : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (q, f))) =
        fun _ => 0 := by
      funext q
      simp [gammaValuationAxisDelta_coord, hef]
    rw [hzero, tsum_zero]

/-- Complete prime covariance couples every two prime deltas at the same depth. -/
theorem gammaValuationWeakKernel_axisDelta_sameDepth
    (p q : Nat.Primes) (e : ℕ) :
    gammaValuationWeakKernel (gammaValuationAxisDelta p e)
        (gammaValuationAxisDelta q e) = 1 := by
  rw [gammaValuationWeakKernel, tsum_eq_single e]
  · simp [gammaValuationLayerSum_axisDelta]
  · intro f hfe
    simp [gammaValuationLayerSum_axisDelta, hfe.symm]

private theorem gammaValuationAdjacentEdgeTerm_indexZero_indexTwo_zero
    (z : ℕ × ℕ) :
    gammaValuationAdjacentEdgeTerm
        (gammaValuationAxisDelta (nthPrimeSubtype 0) 0)
        (gammaValuationAxisDelta (nthPrimeSubtype 2) 0) z = 0 := by
  rcases z with ⟨e, n⟩
  by_cases hn : n = 0
  · subst n
    have h20 : nthPrimeSubtype 2 ≠ nthPrimeSubtype 0 :=
      nthPrimeSubtype_injective.ne (by omega)
    have h21 : nthPrimeSubtype 2 ≠ nthPrimeSubtype (0 + 1) :=
      nthPrimeSubtype_injective.ne (by omega)
    simp [gammaValuationAdjacentEdgeTerm, gammaValuationAdjacentEdgeVector,
      gammaValuationAdjacentLowerAxis, gammaValuationAdjacentUpperAxis,
      gammaValuationAxisDelta_coord, h20, h21]
  · have h0n : nthPrimeSubtype 0 ≠ nthPrimeSubtype n :=
      nthPrimeSubtype_injective.ne (Ne.symm hn)
    have h0s : nthPrimeSubtype 0 ≠ nthPrimeSubtype (n + 1) :=
      nthPrimeSubtype_injective.ne (by omega)
    simp [gammaValuationAdjacentEdgeTerm, gammaValuationAdjacentEdgeVector,
      gammaValuationAdjacentLowerAxis, gammaValuationAdjacentUpperAxis,
      gammaValuationAxisDelta_coord, h0n, h0s]

/-- Adjacent edge locality misses the first nonadjacent prime pair. -/
theorem gammaValuationAdjacentEdgeKernel_indexZero_indexTwo_eq_zero :
    gammaValuationAdjacentEdgeKernel
        (gammaValuationAxisDelta (nthPrimeSubtype 0) 0)
        (gammaValuationAxisDelta (nthPrimeSubtype 2) 0) = 0 := by
  unfold gammaValuationAdjacentEdgeKernel
  have hzero : (fun z : ℕ × ℕ =>
      gammaValuationAdjacentEdgeTerm
        (gammaValuationAxisDelta (nthPrimeSubtype 0) 0)
        (gammaValuationAxisDelta (nthPrimeSubtype 2) 0) z) =
      fun _ => 0 := by
    funext z
    exact gammaValuationAdjacentEdgeTerm_indexZero_indexTwo_zero z
  rw [hzero, tsum_zero]

/-- **P-G85 incidence no-go.**  Summable adjacent path Gram is not P-G78's weak kernel. -/
theorem gammaValuationAdjacentEdgeKernel_ne_gammaValuationWeakKernel :
    gammaValuationAdjacentEdgeKernel ≠ gammaValuationWeakKernel := by
  intro h
  have hpair := congrFun (congrFun h
    (gammaValuationAxisDelta (nthPrimeSubtype 0) 0))
    (gammaValuationAxisDelta (nthPrimeSubtype 2) 0)
  rw [gammaValuationAdjacentEdgeKernel_indexZero_indexTwo_eq_zero,
    gammaValuationWeakKernel_axisDelta_sameDepth] at hpair
  norm_num at hpair

end

end RHTower
