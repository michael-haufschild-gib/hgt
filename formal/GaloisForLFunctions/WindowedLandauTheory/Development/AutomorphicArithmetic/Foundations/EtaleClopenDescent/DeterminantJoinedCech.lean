import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartMinors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap

/-! A right Čech cocycle joins the determinant cocycle on the left.
Moving the right chart indices past the homogeneous equations gives
the sign determined by the two cardinalities. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] {d : ℕ} (T : WeightedChartSystem k d S E)

section Join

variable {κ : Type} [LinearOrder κ] (ρ : Fin (d + 1) ⊕ₗ κ → Fin (d + 1) → S)

/-- Join the ordered minor on the left charts and equations with a
cochain of fixed cardinal degree on the right charts. -/
def joinOrderedMinors (r : ℕ) (b : Finset (Fin (d + 1)) → E)
    (s : Finset (ChartPair d ⊕ₗ κ)) : E :=
  (-1 : ℤ) ^ (r * (rgt s).card) •
    T.act (orderedMinor ρ (uni (lft (lft s)) (rgt s))) (b (rgt (lft s)))

theorem joinOrderedMinors_apply (r : ℕ) (b : Finset (Fin (d + 1)) → E)
    (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    T.joinOrderedMinors ρ r b (uni (uni I J) L) =
      (-1 : ℤ) ^ (r * L.card) • T.act (orderedMinor ρ (uni I L)) (b J) := by
  simp only [joinOrderedMinors, lft_uni, rgt_uni]

/-- The determinant join is closed when the right cochain is closed. -/
theorem wd_joinOrderedMinors_eq_zero (z : κ → S)
    (hρ : ∀ v : E, wd (fun l => T.act (Sum.elim (fun _ => 1) z (ofLex l)))
      (fun L => T.act (orderedMinor ρ L) v) = 0)
    (r : ℕ) (b : Finset (Fin (d + 1)) → E)
    (hb : deltaL k (Fin (d + 1)) E b = 0) (hs : ∀ J, J.card ≠ r → b J = 0) :
    wd (T.weights z) (T.joinOrderedMinors ρ r b) = 0 := by
  funext s
  obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  have hW : (fun t : ChartPair d => T.weights z (toLex (Sum.inl t))) = 1 := by
    funext t
    simp [weights]
  rw [wd_uni, hW, wd_one, deltaL_uni, card_uni, Pi.zero_apply]
  let M := orderedMinor ρ
  let α := (-1 : ℤ) ^ (r * L.card)
  have hJ : deltaL k (Fin (d + 1)) E (fun K => T.joinOrderedMinors ρ r b (uni (uni I K) L)) J = 0 := by
    let f : E →ₗ[k] E := α • T.act (M (uni I L))
    have hm : (fun K => T.joinOrderedMinors ρ r b (uni (uni I K) L)) = mapCochain f b := by
      funext K
      rw [T.joinOrderedMinors_apply]
      rfl
    rw [hm, ← mapCochain_delta, hb]
    exact map_zero f
  rw [hJ, smul_zero, add_zero]
  let c (C : Finset (Fin (d + 1) ⊕ₗ κ)) : E := T.act (M C) (b J)
  have hi : (fun K => T.joinOrderedMinors ρ r b (uni (uni K J) L)) = α • (fun K => c (uni K L)) := by
    funext K
    rw [T.joinOrderedMinors_apply, Pi.smul_apply]
  rw [hi, map_zsmul, Pi.smul_apply]
  have hvert : (-1 : ℤ) ^ (I.card + J.card) •
      wd (fun l => T.weights z (toLex (Sum.inr l)))
        (fun U => T.joinOrderedMinors ρ r b (uni (uni I J) U)) L =
      α • ((-1 : ℤ) ^ I.card • wd (fun l => T.act (z l)) (fun U => c (uni I U)) L) := by
    rw [wd_apply, wd_apply, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [T.joinOrderedMinors_apply]
    change _ • (cubeSign L l • T.act (z l)
        (((-1 : ℤ) ^ (r * (L.erase l).card)) • c (uni I (L.erase l)))) =
      α • ((-1 : ℤ) ^ I.card • (cubeSign L l • T.act (z l) (c (uni I (L.erase l)))))
    by_cases hJr : J.card = r
    · rw [map_zsmul, smul_comm (cubeSign L l), smul_smul, smul_smul α]
      congr 1
      change (-1 : ℤ) ^ (I.card + J.card) * (-1 : ℤ) ^ (r * (L.erase l).card) =
        (-1 : ℤ) ^ (r * L.card) * (-1 : ℤ) ^ I.card
      rw [← pow_add, ← pow_add, hJr, ← Finset.card_erase_add_one hl, Nat.mul_add, Nat.mul_one]
      congr 1
      omega
    · simp only [c, hs J hJr, map_zero, smul_zero]
  rw [hvert, ← smul_add]
  have hc := congrFun (hρ (b J)) (uni I L)
  rw [wd_uni] at hc
  simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr, map_one, Pi.zero_apply] at hc
  change wd (1 : Fin (d + 1) → Module.End k E) (fun K => c (uni K L)) I +
    (-1 : ℤ) ^ I.card • wd (fun l => T.act (z l)) (fun U => c (uni I U)) L = 0 at hc
  rw [wd_one] at hc
  rw [hc, smul_zero]

end Join

abbrev minorJoin (r : ℕ) (b : Finset (Fin (d + 1)) → E) :=
  T.joinOrderedMinors T.minorRows r b

theorem minorJoin_apply (r : ℕ) (b : Finset (Fin (d + 1)) → E)
    (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d)) :
    T.minorJoin r b (uni (uni I J) L) =
      (-1 : ℤ) ^ (r * L.card) • T.act (orderedMinor T.minorRows (uni I L)) (b J) :=
  T.joinOrderedMinors_apply T.minorRows r b I J L

theorem wd_minorJoin_eq_zero (r : ℕ) (b : Finset (Fin (d + 1)) → E)
    (hb : deltaL k (Fin (d + 1)) E b = 0) (hs : ∀ J, J.card ≠ r → b J = 0) :
    wd (T.weights T.homogeneousMinor) (T.minorJoin r b) = 0 :=
  T.wd_joinOrderedMinors_eq_zero T.minorRows T.homogeneousMinor
    T.wd_orderedChartMinor_eq_zero r b hb hs

end GlobalTheory.WH.WeightedChartSystem
