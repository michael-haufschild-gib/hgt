import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.AutomorphicRowTie
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CompareProductWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleRowsFromCounts
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRowWeightBounds
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RowProjectorWeights

/-! The joined Jacquet weights are compared with normalized
unipotent weights on polynomial labels. Both the character and
its inverse enter the local exceptional event. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

local instance factGForJoin {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem weight_of_join {D : D7} (A : AllRows D) (hL : admLq D) (hJoin : AllJoinA A)
    (bounds : ∀ k : Fin 2, LocalRowWeightBounds (D.host.g k) D.R.r D.host.q D.host.d) :
    WeightAllRows A := by
  classical
  obtain ⟨ψ, hψ, hlevel⟩ := hJoin.level
  refine ⟨?_, ?_⟩
  · intro k v f
    rw [hlevel]
    exact ((hL k (ψ k) (hψ k)).1 f).2
  intro k S hS
  obtain ⟨hnn, hsq, hcmp, -⟩ := hL k (ψ k) (hψ k)
  let Ω := Fin D.R.r → ZMod (D.host.g k)
  let P : Ω → ℝ := fun c => wtOf D k (eUk D k (ψ k)) (monicOf c)
  let J : Ω → ℝ := fun c => wtOf D k (eJk D k (ψ k)) (monicOf c)
  let B : Finset (D.nd.PlG k → Ω) := univ.filter (fun x => ¬ goodAt D k (fun v => monicOf (x v)))
  have hP0 (c : Ω) : 0 ≤ P c := (hnn _).1
  have hP1 : ∑ c, P c = 1 := sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
  have hJ1 : ∑ c, J c = 1 := sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'
  have hPJ (c : Ω) : (1 - 1 / (D.host.g k : ℝ)) * P c ≤ J c := by
    by_cases hc : IsLabel D k (monicOf c)
    · exact hcmp _ hc
    · change (1 - 1 / (D.host.g k : ℝ)) * wtOf D k (eUk D k (ψ k)) (monicOf c) ≤
        wtOf D k (eJk D k (ψ k)) (monicOf c)
      rw [wtOf_eq_zero_of_not_label _ hc, wtOf_eq_zero_of_not_label _ hc, mul_zero]

  let S' := S.filter (fun t => ∀ v, IsLabel D k (t v))
  let cv (t : Tup D k) : D.nd.PlG k → Ω := fun v i => (t v).coeff i
  have hcv {t : Tup D k} (ht : t ∈ S') : (fun v => monicOf (cv t v)) = t := by
    funext v
    obtain ⟨hm, hdeg, -⟩ := (Finset.mem_filter.mp ht).2 v
    exact monicOf_coeffs _ hm hdeg
  have hred : locShare D A.eVec k S ≤ ∑ x ∈ B, ∏ v, J (x v) := by
    unfold locShare
    have hremove : ∑ t ∈ S, ∏ v, wtOf D k (A.eVec k v) (t v) =
        ∑ t ∈ S', ∏ v, wtOf D k (A.eVec k v) (t v) := by
      symm
      apply Finset.sum_filter_of_ne
      intro t _ hne v
      by_contra hv
      exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv))
    rw [hremove]
    calc
      ∑ t ∈ S', ∏ v, wtOf D k (A.eVec k v) (t v) = ∑ t ∈ S', ∏ v, J (cv t v) := by
        refine Finset.sum_congr rfl fun t ht => Finset.prod_congr rfl fun v _ => ?_
        change _ = wtOf D k (eJk D k (ψ k)) (monicOf (cv t v))
        rw [hlevel, congrFun (hcv ht) v]
      _ = ∑ x ∈ S'.image cv, ∏ v, J (x v) := by
        symm
        refine Finset.sum_image ?_
        intro t ht t' ht' hh
        rw [← hcv ht, ← hcv ht', hh]
      _ ≤ ∑ x ∈ B, ∏ v, J (x v) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcv ht).symm ▸ hS t (Finset.mem_filter.mp ht).1⟩
        · intro x _ _
          exact Finset.prod_nonneg fun v _ => (hnn _).2

  have hg : (1 : ℝ) ≤ D.host.g k := by exact_mod_cast (D.host.g_prime k).one_lt.le
  have htransfer := comparison_transfer (fun _ : D.nd.PlG k => Ω) (fun _ => P) (fun _ => J)
    (D.host.g k : ℝ) B hg (fun _ => hP0) (fun _ => hP1) (fun _ => hJ1) (fun _ => hPJ)
  have hPsq : ∀ c ∈ squarefreeCoefficients (D.host.g k) D.R.r,
      P c = squarefreeWeight (D.host.g k) (monicOf c) := by
    intro c hc
    obtain ⟨hs, h0⟩ : Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := (Finset.mem_filter.mp hc).2
    have hl : IsLabel D k (monicOf c) := ⟨monic_monicOf c, natDegree_monicOf c, h0⟩
    change wtOf D k (eUk D k (ψ k)) (monicOf c) = _
    rw [hsq _ hl hs]
    simp only [squarefreeWeight, degreeType, Multiset.map_map, Function.comp_def, one_div, Multiset.prod_map_inv]
    first | rfl | (convert rfl; all_goals rfl)
  have hW := local_bad_weight_le (D.host.g k) D.R.r D.host.q D.host.d (bounds k)
    (D.nd.chiT k) P hP0 hP1 hPsq
  have hB : B = univ.filter (fun x : D.nd.PlG k → Ω =>
      ¬ (IsGood D.R.r (D.host.g k) (fun v => monicOf (x v)) (D.nd.chiT k) ∧
        IsGood D.R.r (D.host.g k) (fun v => monicOf (x v)) (fun v j => (D.nd.chiT k v j)⁻¹))) := by
    ext x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [← hB] at hW
  refine hred.trans (htransfer.trans ((add_le_add hW le_rfl).trans_eq ?_))
  rw [D.nd.card_PlG k, Fintype.card_fin, Wg]
  ring

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.weight_of_join
