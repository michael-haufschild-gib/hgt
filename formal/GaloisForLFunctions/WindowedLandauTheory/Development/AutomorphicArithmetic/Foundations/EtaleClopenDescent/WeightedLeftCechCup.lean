import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupLeibniz

/-! Cup product in the first chart direction commutes with the joined
weighted differential on a closed right factor. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k E M N ι κ : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

private theorem wd_cup_right
    (μ : E →ₗ[k] M →ₗ[k] N) (m s t : ℕ) (I : Finset ι) (J : Finset κ)
    (c : Finset ι → Finset κ → E) (a : Finset ι → M)
    (ha : ∀ L, L.card ≠ m + 1 → a L = 0)
    (w : κ → Module.End k E) (w' : κ → Module.End k N)
    (hw : ∀ l x y, w' l (μ x y) = μ (w l x) y) :
    (-1 : ℤ) ^ (I.card + s) • wd w' (fun L =>
      (-1 : ℤ) ^ (m * (L.card + t)) • cechCup μ (fun P => c P L) a I) J =
    (-1 : ℤ) ^ (m * (J.card + t)) •
      ∑ i ∈ I, μ ((-1 : ℤ) ^ ((I.filter (· ≤ i)).card + s) •
        wd w (c (I.filter (· ≤ i))) J) (a (I.filter (i ≤ ·))) := by
  simp only [wd_apply, cechCup_apply, map_smul, map_zsmul, map_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, hw]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  by_cases hcard : (I.filter (i ≤ ·)).card = m + 1
  · have hI := card_filter_le_add_card_filter_ge I i hi
    have hcardI : I.card = (I.filter (· ≤ i)).card + m := by omega
    have hsign : (-1 : ℤ) ^ (I.card + s) * (-1 : ℤ) ^ (m * ((J.erase j).card + t)) =
        (-1 : ℤ) ^ (m * (J.card + t)) * (-1 : ℤ) ^ ((I.filter (· ≤ i)).card + s) := by
      rw [← pow_add, ← pow_add, hcardI, ← Finset.card_erase_add_one hj]
      simp only [Nat.mul_add, Nat.mul_one]
      congr 1
      omega
    rw [smul_comm (GlobalTheory.cubeSign J j) ((-1 : ℤ) ^ (m * ((J.erase j).card + t))),
      smul_smul, smul_smul ((-1 : ℤ) ^ (m * (J.card + t))), hsign]
  · rw [ha _ hcard]
    simp only [map_zero, smul_zero]

open WeightedChartSystem

variable {S : Type} [CommRing S] [Algebra k S] {d : ℕ}

/-- Cup in the first chart direction, with the sign for moving the
right cocycle past the second chart and homogeneous index sets. -/
def weightedLeftCup (μ : E →ₗ[k] M →ₗ[k] N) (m : ℕ)
    (c : Finset (ChartPair d ⊕ₗ κ) → E)
    (a : Finset (Fin (d + 1)) → M) (B : Finset (ChartPair d ⊕ₗ κ)) : N :=
  (-1 : ℤ) ^ (m * ((rgt (lft B)).card + (rgt B).card)) •
    cechCup μ (fun I => c (uni (uni I (rgt (lft B))) (rgt B))) a (lft (lft B))

theorem weightedLeftCup_apply (μ : E →ₗ[k] M →ₗ[k] N) (m : ℕ)
    (c : Finset (ChartPair d ⊕ₗ κ) → E) (a : Finset (Fin (d + 1)) → M)
    (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    weightedLeftCup μ m c a (uni (uni I J) L) =
      (-1 : ℤ) ^ (m * (J.card + L.card)) • cechCup μ (fun P => c (uni (uni P J) L)) a I := by
  simp only [weightedLeftCup, lft_uni, rgt_uni]

/-- The weighted left cup of two cocycles is closed when the
coefficient pairing commutes with the homogeneous weights. -/
theorem wd_weightedLeftCup_eq_zero (T : WeightedChartSystem k d S E)
    (U : WeightedChartSystem k d S N) (z : κ → S)
    (μ : E →ₗ[k] M →ₗ[k] N) (m : ℕ)
    (c : Finset (ChartPair d ⊕ₗ κ) → E) (a : Finset (Fin (d + 1)) → M)
    (hc : wd (T.weights z) c = 0) (hc₀ : ∀ J L, c (uni (uni ∅ J) L) = 0)
    (ha : deltaL k (Fin (d + 1)) M a = 0)
    (ha₀ : ∀ I, I.card ≠ m + 1 → a I = 0)
    (hact : ∀ l x y, U.act (z l) (μ x y) = μ (T.act (z l) x) y) :
    wd (U.weights z) (weightedLeftCup μ m c a) = 0 := by
  funext B
  obtain ⟨A, L, rfl⟩ : ∃ A L, B = uni A L := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  obtain ⟨I, J, rfl⟩ : ∃ I J, A = uni I J := ⟨lft A, rgt A, (uni_lft_rgt A).symm⟩
  let v := weightedLeftCup μ m c a
  let C (P Q : Finset (Fin (d + 1))) (K : Finset κ) := c (uni (uni P Q) K)
  let α := (-1 : ℤ) ^ (m * (J.card + L.card))
  have hU : (fun a' : ChartPair d => U.weights z (toLex (Sum.inl a'))) = 1 := by
    funext a'
    simp [weights]
  have hT : (fun a' : ChartPair d => T.weights z (toLex (Sum.inl a'))) = 1 := by
    funext a'
    simp [weights]
  change wd (U.weights z) v (uni (uni I J) L) = 0
  rw [wd_uni, hU, wd_one, deltaL_uni, card_uni]
  have h₁ : deltaL k (Fin (d + 1)) N (fun P => v (uni (uni P J) L)) I =
      α • cechCup μ (deltaL k (Fin (d + 1)) E (fun P => C P J L)) a I := by
    have he : (fun P => v (uni (uni P J) L)) = α • cechCup μ (fun P => C P J L) a := by
      funext P
      exact weightedLeftCup_apply μ m c a P J L
    rw [he, map_zsmul, Pi.smul_apply, deltaL_cechCup_of_rightCycle μ _ a
      (hc₀ J L) (ha₀ ∅ (by simp)) ha]
  have h₂ : (-1 : ℤ) ^ I.card • deltaL k (Fin (d + 1)) N (fun Q => v (uni (uni I Q) L)) J =
      α • ∑ i ∈ I, μ ((-1 : ℤ) ^ (I.filter (· ≤ i)).card •
        deltaL k (Fin (d + 1)) E (fun Q => C (I.filter (· ≤ i)) Q L) J)
          (a (I.filter (i ≤ ·))) := by
    have he := wd_cup_right μ m 0 L.card I J (fun P Q => C P Q L) a ha₀ 1 1
      (fun _ x y => by simp)
    simpa only [wd_one, Nat.add_zero, C, v, weightedLeftCup_apply, α] using he
  have h₃ : (-1 : ℤ) ^ (I.card + J.card) •
      wd (fun l => U.weights z (toLex (Sum.inr l))) (fun K => v (uni (uni I J) K)) L =
      α • ∑ i ∈ I, μ ((-1 : ℤ) ^ ((I.filter (· ≤ i)).card + J.card) •
        wd (fun l => T.act (z l)) (C (I.filter (· ≤ i)) J) L)
          (a (I.filter (i ≤ ·))) := by
    have he := wd_cup_right μ m J.card J.card I L (fun P K => C P J K) a ha₀
      (fun l => T.act (z l)) (fun l => U.act (z l)) hact
    simpa only [weights, ofLex_toLex, Sum.elim_inr, C, v, weightedLeftCup_apply, α,
      Nat.add_comm _ J.card] using he
  rw [h₁, h₂, h₃, ← smul_add, ← smul_add, cechCup_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
  have he := congrFun hc (uni (uni (I.filter (· ≤ i)) J) L)
  rw [wd_uni, hT, wd_one, deltaL_uni, card_uni, Pi.zero_apply] at he
  simp only [weights, ofLex_toLex, Sum.elim_inr] at he
  rw [← LinearMap.add_apply, ← map_add, ← LinearMap.add_apply, ← map_add]
  rw [he, map_zero, LinearMap.zero_apply]

end GlobalTheory.WH
