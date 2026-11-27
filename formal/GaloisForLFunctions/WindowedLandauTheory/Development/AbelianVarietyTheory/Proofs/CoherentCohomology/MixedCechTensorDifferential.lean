import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MixedCechTensorCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTensorProduct

/-! The tensor cochain equivalence respects the Čech differential and the
grading by the cardinality of an intersection. -/

noncomputable section

open TensorProduct GlobalTheory.WH GlobalTheory.CechDR
open Finset.HasAntidiagonal
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace HTGeometry.FinsetCechDatum

variable {K ι κ : Type} [Field K] [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  (A : FinsetCechDatum.{0} ι) (B : FinsetCechDatum.{0} κ)
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ))
  [∀ s, Module K (A.obj s)] [∀ t, Module K (B.obj t)] [∀ u, Module K (D.obj u)]
  (hA : ∀ {s t} (h : s ⊆ t) (r : K) (x : A.obj s), A.res h (r • x) = r • A.res h x)
  (hB : ∀ {s t} (h : s ⊆ t) (r : K) (x : B.obj s), B.res h (r • x) = r • B.res h x)
  (hD : ∀ {s t} (h : s ⊆ t) (r : K) (x : D.obj s), D.res h (r • x) = r • D.res h x)
  (hzero : ∀ s t, ¬ (s.Nonempty ∧ t.Nonempty) → Subsingleton (D.obj (uni s t)))
  (e : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
    (A.obj s ⊗[K] B.obj t ≃ₗ[K] D.obj (uni s t)))

private theorem regular_eq_zero_of_not_nonempty {T : Type} [LinearOrder T]
    (C : FinsetCechDatum.{0} T) [∀ s, Module K (C.obj s)]
    (x : C.regular (K := K)) {s : Finset T} (hs : ¬ s.Nonempty) : x.1 s = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · exact x.2
  · exact (hs h).elim

private theorem map_d_apply {T M : Type} [LinearOrder T] [AddCommGroup M] [Module K M]
    (C : FinsetCechDatum.{0} T) [∀ s, Module K (C.obj s)]
    (x : C.Cochain) (s : Finset T) (φ : C.obj s →ₗ[K] M) :
    φ (C.d x s) = ∑ i ∈ s, (cechSign s i : ℤ) • φ (C.res (Finset.erase_subset i s) (x (s.erase i))) := by
  rw [FinsetCechDatum.d, map_sum]
  exact Finset.sum_congr rfl fun _ _ => map_zsmul _ _ _

local notation "G" => A.graded hA
local notation "H" => B.graded hB
local notation "T" => D.graded hD
local notation "E" => mixedTensorEquiv A B D hzero e

theorem mixedTensorEquiv_d
    (hnat : ∀ {s s' t t'} (hs : s ⊆ s') (ht : t ⊆ t')
      (hs₀ : s.Nonempty) (ht₀ : t.Nonempty) (a : A.obj s) (b : B.obj t),
      D.res (uni_mono hs ht) (e s t hs₀ ht₀ (a ⊗ₜ b)) =
        e s' t' (hs₀.mono hs) (ht₀.mono ht) (A.res hs a ⊗ₜ B.res ht b))
    (z : A.regular (K := K) ⊗[K] B.regular (K := K)) :
    E (((G).tensorComplex H).d z) = (T).d (E z) := by
  have Hmap : (E).toLinearMap ∘ₗ tensorDifferential G H = (T).d ∘ₗ (E).toLinearMap := by
    refine TensorProduct.ext' fun a b => ?_
    let y := E (a ⊗ₜ[K] b)
    have hdiff : tensorDifferential G H (a ⊗ₜ[K] b) = (G).d a ⊗ₜ b + (G).σ a ⊗ₜ (H).d b := by
      simp only [tensorDifferential, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    simp only [LinearMap.comp_apply, hdiff, map_add]
    refine Subtype.ext (funext fun u => ?_)
    obtain ⟨s, t, rfl⟩ : ∃ s t, u = uni s t := ⟨lft u, rgt u, (uni_lft_rgt u).symm⟩
    by_cases hs : s.Nonempty ∧ t.Nonempty
    · let L : A.obj s →ₗ[K] D.obj (uni s t) :=
        (e s t hs.1 hs.2).toLinearMap ∘ₗ (TensorProduct.mk K (A.obj s) (B.obj t)).flip (b.1 t)
      let R : B.obj t →ₗ[K] D.obj (uni s t) :=
        (e s t hs.1 hs.2).toLinearMap ∘ₗ TensorProduct.mk K (A.obj s) (B.obj t) (a.1 s)
      have hL (i : ι) :
          D.res (uni_mono (Finset.erase_subset i s) (Finset.Subset.refl t)) (y.1 (uni (s.erase i) t)) =
            L (A.res (Finset.erase_subset i s) (a.1 (s.erase i))) := by
        by_cases hi : (s.erase i).Nonempty
        · rw [show y.1 (uni (s.erase i) t) = _ from
            mixedTensorEquiv_tmul A B D hzero e a b _ _ hi hs.2]
          change _ = e s t hs.1 hs.2 (A.res _ (a.1 (s.erase i)) ⊗ₜ b.1 t)
          rw [hnat (Finset.erase_subset i s) (Finset.Subset.refl t) hi hs.2, B.res_refl]
        · have hz : y.1 (uni (s.erase i) t) = 0 := (hzero _ _ fun h => hi h.1).elim _ _
          rw [hz, regular_eq_zero_of_not_nonempty A a hi, map_zero, map_zero, map_zero]
      have hR (j : κ) :
          D.res (uni_mono (Finset.Subset.refl s) (Finset.erase_subset j t)) (y.1 (uni s (t.erase j))) =
            R (B.res (Finset.erase_subset j t) (b.1 (t.erase j))) := by
        by_cases hj : (t.erase j).Nonempty
        · rw [show y.1 (uni s (t.erase j)) = _ from
            mixedTensorEquiv_tmul A B D hzero e a b _ _ hs.1 hj]
          change _ = e s t hs.1 hs.2 (a.1 s ⊗ₜ B.res _ (b.1 (t.erase j)))
          rw [hnat (Finset.Subset.refl s) (Finset.erase_subset j t) hs.1 hj, A.res_refl]
        · have hz : y.1 (uni s (t.erase j)) = 0 := (hzero _ _ fun h => hj h.2).elim _ _
          rw [hz, regular_eq_zero_of_not_nonempty B b hj, map_zero, map_zero, map_zero]
      have hDL : (D.leftSlice t).d (fun I => y.1 (uni I t)) s = L (A.d a.1 s) := by
        rw [map_d_apply]
        exact Finset.sum_congr rfl fun i _ => congrArg ((cechSign s i : ℤ) • ·) (hL i)
      have hDR : (D.rightSlice s).d (fun J => y.1 (uni s J)) t = R (B.d b.1 t) := by
        rw [map_d_apply]
        exact Finset.sum_congr rfl fun j _ => congrArg ((cechSign t j : ℤ) • ·) (hR j)
      have hsigma : ((G).σ a).1 s = (-1 : ℤ) ^ s.card • a.1 s := rfl
      have hσtmul : (((-1 : ℤ) ^ s.card) • a.1 s) ⊗ₜ[K] B.d b.1 t =
          ((-1 : ℤ) ^ s.card) • (a.1 s ⊗ₜ[K] B.d b.1 t) :=
        map_zsmul ((TensorProduct.mk K (A.obj s) (B.obj t)).flip _) _ _
      change (E ((G).d a ⊗ₜ b)).1 (uni s t) + (E ((G).σ a ⊗ₜ (H).d b)).1 (uni s t) =
        D.d y.1 (uni s t)
      rw [D.d_uni, hDL, hDR,
        mixedTensorEquiv_tmul A B D hzero e ((G).d a) b s t hs.1 hs.2,
        mixedTensorEquiv_tmul A B D hzero e ((G).σ a) ((H).d b) s t hs.1 hs.2,
        A.graded_d_apply hA, B.graded_d_apply hB, hsigma, hσtmul, map_zsmul]
      rfl
    · exact (hzero s t hs).elim _ _
  exact LinearMap.congr_fun Hmap z

theorem mixedTensorEquiv_π (n : ℕ) (z : A.regular (K := K) ⊗[K] B.regular (K := K)) :
    E (((G).tensorComplex H).π n z) = (T).π n (E z) := by
  have hmap : (E).toLinearMap ∘ₗ (G).tensorProjection H n = (T).π n ∘ₗ (E).toLinearMap := by
    refine TensorProduct.ext' fun a b => Subtype.ext (funext fun u => ?_)
    obtain ⟨s, t, rfl⟩ : ∃ s t, u = uni s t := ⟨lft u, rgt u, (uni_lft_rgt u).symm⟩
    by_cases hs : s.Nonempty ∧ t.Nonempty
    · let ev : D.regular (K := K) →ₗ[K] D.obj (uni s t) :=
        LinearMap.proj (uni s t) ∘ₗ (D.regular (K := K)).subtype
      let w := ev (E (a ⊗ₜ[K] b))
      have hcoeff (x : ℕ × ℕ) :
          ev (E (TensorProduct.map ((G).π x.1) ((H).π x.2) (a ⊗ₜ[K] b))) =
            if x = (s.card, t.card) then w else 0 := by
        rw [TensorProduct.map_tmul]
        change (E ((G).π x.1 a ⊗ₜ (H).π x.2 b)).1 (uni s t) = _
        rw [mixedTensorEquiv_tmul A B D hzero e _ _ s t hs.1 hs.2,
          A.graded_π_apply hA, B.graded_π_apply hB]
        by_cases h₁ : x.1 = s.card
        · by_cases h₂ : x.2 = t.card
          · rw [if_pos (Prod.ext h₁ h₂), if_pos h₁.symm, if_pos h₂.symm]
            exact (mixedTensorEquiv_tmul A B D hzero e a b s t hs.1 hs.2).symm
          · rw [if_neg (fun h => h₂ (congrArg Prod.snd h)), if_neg (Ne.symm h₂), tmul_zero, map_zero]
        · rw [if_neg (fun h => h₁ (congrArg Prod.fst h)), if_neg (Ne.symm h₁), zero_tmul, map_zero]
      change ev (E ((G).tensorProjection H n (a ⊗ₜ b))) = ((T).π n (E (a ⊗ₜ b))).1 (uni s t)
      rw [FiniteGradedComplex.tensorProjection, LinearMap.sum_apply, map_sum, map_sum,
        D.graded_π_apply hD, card_uni]
      simp only [hcoeff]
      by_cases hn : s.card + t.card = n
      · have hmem : (s.card, t.card) ∈ antidiagonal n := by simpa using hn
        rw [Finset.sum_eq_single_of_mem (s.card, t.card) hmem (fun _ _ hx => if_neg hx),
          if_pos rfl, if_pos hn]
        rfl
      · rw [if_neg hn]
        refine Finset.sum_eq_zero fun x hx => if_neg fun he => hn ?_
        have hh : x.1 + x.2 = n := by simpa using hx
        simpa only [he] using hh
    · exact (hzero s t hs).elim _ _
  exact LinearMap.congr_fun hmap z

end HTGeometry.FinsetCechDatum
