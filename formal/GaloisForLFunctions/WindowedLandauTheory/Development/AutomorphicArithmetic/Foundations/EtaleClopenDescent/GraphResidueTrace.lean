import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalResolution
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginVolumeCochain
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicOriginTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCocycleTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleJoinedCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechSubcoverLift

/-! The diagonal resolution computes the alternating trace. Its
graph class can be evaluated by its residue on the left cover. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.WH

private theorem mapCochain_mixed_boundary {k M N ι κ : Type}
    [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [LinearOrder ι] [LinearOrder κ]
    {A : Finset ι → Finset κ → Submodule k M} {B : Finset ι → Finset κ → Submodule k N}
    (g : M →ₗ[k] N) (hg : ∀ I J, A I J ≤ (B I J).comap g) {m : ℤ}
    {c : Finset (ι ⊕ₗ κ) → M} (hc : c ∈ (mixedCech A).B m) :
    mapCochain g c ∈ (mixedCech B).B m := by
  obtain ⟨a, ha, he⟩ := hc
  refine ⟨mapCochain g a, acx_mem_terms_iff.mpr fun I => ?_, ?_⟩
  · have h := acx_mem_terms_iff.mp ha I
    change g (a I) ∈ if (I.card : ℤ) = m - 1 then
      (if (lft I).Nonempty ∧ (rgt I).Nonempty then B (lft I) (rgt I) else ⊥) else ⊥
    change a I ∈ _ at h
    split_ifs at h ⊢ with hI hJ
    · exact hg _ _ h
    · rw [(Submodule.mem_bot k).mp h, map_zero]
      exact zero_mem _
    · rw [(Submodule.mem_bot k).mp h, map_zero]
      exact zero_mem _
  · change wd 1 a = c at he
    change wd 1 (mapCochain g a) = mapCochain g c
    rw [wd_one, ← mapCochain_delta, ← he, wd_one]

end GlobalTheory.WH

namespace GlobalTheory.PD

variable {k F E L : Type} [Field k] [CharZero k] [IsAlgClosed k]
  [Field F] [Field E] [Field L] [Algebra k F] [Algebra k E] [Algebra k L]
  [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower k F E] [IsScalarTower k F L]
  [IsScalarTower k E L] [IsScalarTower F E L] [Module.Finite E L] [Algebra.Etale E L]
  {d p q : ℕ} {x : Fin (d + 1) → F} (j₂ : E →ₐ[k] L)

local notation "ι" => Fin (d + 1)
local notation "A" => fun a (I : Finset ι) => omB k E (rB k E x I) a
local notation "Bform" => fun a (I : Finset ι) => omB k L (rB k L x I) a
local notation "G" => fun a (I : Finset (ι ⊕ₗ ι)) => omB k L (RY x j₂ (lft I) (rgt I)) a
local notation "C" => cech ((A) p)
local notation "H" => fun (I J : Finset ι) => omB k L (RY x j₂ I J) d
local notation "j₁" => IsScalarTower.toAlgHom k E L
local notation "g" => graphDRPullback (j₁) j₂
local notation "S" => fun (I J : Finset ι) => Submodule.map₂
  (TensorProduct.mk k (DR k E) (DR k E)) ((A) q I) ((A) p J)

omit [CharZero k] [IsAlgClosed k] in
/-- Dropping the extra diagonal equations leaves the de Rham Čech
representative unchanged. -/
theorem diagonalCechPart_restrictAppendedDiagonal {κ : Type} [LinearOrder κ]
    (c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ DiagonalIndex d)) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) :
    diagonalCechPart (restrictAppendedDiagonal q p c) = diagonalCechPart c := by
  have h₀ : uni (∅ : Finset κ) (∅ : Finset (DiagonalIndex d)) = ∅ :=
    Finset.card_eq_zero.mp (by simp only [card_uni, Finset.card_empty, zero_add])
  funext I
  simp only [diagonalCechPart, mapCochain_apply, chartPart, restrictAppendedDiagonal,
    lft_uni, rgt_uni, h₀]

omit [CharZero k] [IsAlgClosed k] [Module.Finite E L] [Algebra.Etale E L] in
/-- Graph pullback of the Čech representative is the Koszul-empty
component of graph pullback on the original weighted cochain. -/
theorem graphDRPullback_diagonalCechPart {κ : Type} [LinearOrder κ]
    (c : Finset (ChartPair d ⊕ₗ κ) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) (I : Finset (ChartPair d)) :
    (g) (diagonalCechPart c I) = chartPart (fun J => graphFormPullback (j₁) j₂ (c J)) I := rfl

omit [CharZero k] [IsAlgClosed k] [Algebra F L] [IsScalarTower k F L] [IsScalarTower F E L] in
private theorem trace_graph_residue_projection
    (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (a : Finset ι → DR k E) (b : Finset ι → DR k L) :
    topResidue τ ρ (traceDR k E L
      (cechCup (LinearMap.mul k (DR k L)) (fun I => pullbackDR (j₁) (a I)) b Finset.univ)) =
      cupResidueFunctional τ ρ a (fun J => traceDR k E L (b J)) := by
  rw [cupResidueFunctional_apply, cechCup_apply, cechCup_apply, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (topResidue τ ρ) (traceDR_pullback_mul _ _)

/-- If the graph of a diagonal representative is the left edge of
an origin volume cochain in mixed cohomology, its alternating trace
is the residue of that volume coefficient. -/
theorem IsFinCover.alternatingTrace_eq_residue_of_graph
    (hE : IsFinCover k E x) (hL : IsFinCover k L x) (hqp : q + p = d)
    (hchart : ∀ A₁ A₂ : Finset (ι ⊕ₗ ι), A₁.Nonempty → A₁ ⊆ A₂ →
      RY x j₂ (lft A₁) (rgt A₁) ≤ RY x j₂ (lft A₂) (rgt A₂))
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    [∀ m : ℕ, Module.Finite k ((C).H (m : ℤ))]
    (u : ∀ m : ℕ, (C).H (m : ℤ) →ₗ[k] (C).H (m : ℤ))
    (hlift : ∀ m : ℕ, ∀ a : (C).Z (m : ℤ),
      ∃ b ∈ (cech ((G) p)).Z (m : ℤ),
        (∀ J, b (uni ∅ J) = pullbackDR j₂ (a.val J)) ∧
        ∃ a' : (C).Z (m : ℤ),
          (∀ I, a'.val I = traceDR k E L (b (uni I ∅))) ∧
          u m (Submodule.Quotient.mk a) = Submodule.Quotient.mk a')
    (hedge : ∀ a' ∈ (cech ((Bform) d)).Z (d : ℤ),
      edge1 a' ∈ (mixedCech (H)).B ((d : ℤ) + 2) → a' ∈ (cech ((Bform) d)).B (d : ℤ))
    {c : Finset (ι ⊕ₗ ι) → DR k E ⊗[k] DR k E}
    (hc : c ∈ (mixedCech (S)).Z ((d : ℤ) + 2))
    (hid : ∀ m ≤ d, ∀ a ∈ (C).Z (m : ℤ),
      a - cupAlongLeft (traceWedgeTensorAction τ ρ) a c ∈ (C).B (m : ℤ))
    (b : rB k L x {0})
    (hgraph : (fun I => (g) (c I)) - edge1 (originVolumeCochain b) ∈
      (mixedCech (H)).B ((d : ℤ) + 2)) :
    ∑ m ∈ Finset.range (d + 1), (-1 : k) ^ m * LinearMap.trace k _ (u m) =
      ρ (Algebra.trace F L (b : L)) := by
  letI : Module.Finite F E := hE.fin
  let μ := LinearMap.mul k (DR k L)
  let Mx := mixedCech (H)
  let Ctop := cech ((Bform) d)
  obtain ⟨m, r, e, f, hparts, hcz, hres⟩ := hE.cocycle_resolution_of_diagonal_action
    τ hτ ρ hρ hqp hc hid
  let f₀ (j : Fin m) : (C).Z (r j : ℤ) := ⟨f j, (hparts j).2.2⟩
  choose t ht hright f₁ htrace hu using fun j => hlift (r j) (f₀ j)
  let a (j : Fin m) (I : Finset ι) := pullbackDR (j₁) (e j I)
  let v (j : Fin m) (I : Finset ι) := t j (uni I ∅)
  let W (j : Fin m) := cechCup μ (a j) (v j)
  let Lj (j : Fin m) := cechJoin μ (a j) (fun I => t j (uni ∅ I))
  have hleft (I : Finset ι) :
      RY x j₂ I ∅ = rB k L x I := by
    change rB k L x I ⊔ pullbackChartAlgebra j₂ (rB k E x ∅) = _
    rw [pullbackChartAlgebra_rB_empty, sup_bot_eq]
  have hmap₁ (I : Finset ι) : (rB k E x I).map (j₁) ≤ rB k L x I := by
    rintro _ ⟨x', hx', rfl⟩
    exact (show IsIntegral (rA k x I) x' from hx').algebraMap
  have hamap (j : Fin m) : a j ∈ (cech ((Bform) q)).Z ((d - r j : ℕ) : ℤ) := by
    let P : (Finset ι → DR k E) →ₗ[k] (Finset ι → DR k L) :=
      mapCochain (pullbackDR (j₁)).toLinearMap
    have he := (hparts j).2.1
    obtain ⟨ha, hD⟩ := isMap_mapCochain ((A) q) ((Bform) q)
      (pullbackDR (j₁)).toLinearMap
      (fun I _ => IsDRMap.regularForms k (isDRMap_pullbackDR k (j₁)) (hmap₁ I) q)
      ((d - r j : ℕ) : ℤ) (e j) he.1
    exact ⟨ha, LinearMap.mem_ker.mpr (hD.symm.trans
      ((congrArg P (LinearMap.mem_ker.mp he.2)).trans (map_zero P)))⟩
  have hv (j : Fin m) : v j ∈ (cech ((Bform) p)).C (r j : ℤ) := by
    have h := isMap_restrictIndex ((G) p) ((Bform) p) (joinedLeft (κ := ι))
      (fun I _ => (congrArg (fun R : Subalgebra k L => omB k L R p)
        (by rw [map_joinedLeft, lft_uni, rgt_uni, hleft])).le)
      (r j : ℤ) (t j) (ht j).1
    have he : restrictIndex (k := k) (joinedLeft (κ := ι)) (t j) = v j := by
      funext I
      rw [restrictIndex_apply, map_joinedLeft]
    exact he ▸ h.1
  have hmul (I J : Finset ι) (R : Subalgebra k L)
      (hI : rB k L x I ≤ R) (hJ : rB k L x J ≤ R)
      {y₁ y₂ : DR k L} (hy₁ : y₁ ∈ (Bform) q I) (hy₂ : y₂ ∈ (Bform) p J) :
      μ y₁ y₂ ∈ omB k L R d :=
    Eq.mp (congrArg (fun t => y₁ * y₂ ∈ omB k L R t) hqp)
      (mul_mem_omB (omB_mono hI q hy₁) (omB_mono hJ p hy₂))
  have hJ (j : Fin m) : Lj j - (-1 : ℤ) ^ (r j) • edge1 (W j) ∈ Mx.B ((d : ℤ) + 2) ∧
      deltaL k ι (DR k L) (W j) = 0 := by
    have hreg {I J I' : Finset ι} {T : Finset (ι ⊕ₗ ι)}
        (_ : J.Nonempty) (_ : I'.Nonempty) (hT : T.Nonempty)
        (hi : I' ⊆ I) (ht : T ⊆ uni I J)
        {x' y' : DR k L} (hx' : x' ∈ (Bform) q I') (hy' : y' ∈ (G) p T) :
        μ x' y' ∈ (H) I J := by
      have hr : RY x j₂ (lft T) (rgt T) ≤ RY x j₂ I J :=
        by simpa only [lft_uni, rgt_uni] using hchart T (uni I J) hT ht
      exact Eq.mp (congrArg (fun t => x' * y' ∈ omB k L (RY x j₂ I J) t) hqp)
        (mul_mem_omB (omB_mono ((rB_mono hi).trans le_sup_left) q hx') (omB_mono hr p hy'))
    have he := joinedCup_sub_edge1_mem_mixed_boundary μ ((Bform) q) ((G) p) (H) hreg
      (hamap j) (ht j)
    have hdeg : ((d - r j : ℕ) : ℤ) + r j + 2 = (d : ℤ) + 2 := by
      rw [Nat.cast_sub (hparts j).1]
      omega
    simpa only [hdeg, Lj, W, v] using he
  have hW (j : Fin m) : W j ∈ Ctop.Z (d : ℤ) := by
    refine ⟨?_, (hJ j).2⟩
    have he := cechCup_mem μ ((Bform) q) ((Bform) p) ((Bform) d)
      (fun {I J K} _ _ hI hJ => hmul I J _ (rB_mono hI) (rB_mono hJ))
      (hamap j).1 (hv j)
    have hh : ((d - r j : ℕ) : ℤ) + r j = (d : ℤ) := by
      rw [Nat.cast_sub (hparts j).1]
      omega
    rwa [hh] at he
  let Λ : Finset ι → DR k L := ∑ j, (-1 : ℤ) ^ (r j) • W j
  have hΛ : Λ ∈ Ctop.Z (d : ℤ) := Submodule.sum_mem _ fun j _ => zsmul_mem (hW j) _
  have hgraphReg (I J : Finset ι) : (S) I J ≤ ((H) I J).comap (g) := by
    refine Submodule.map₂_le.mpr fun x' hx' y' hy' => ?_
    change (g) (x' ⊗ₜ[k] y') ∈ (H) I J
    rw [graphDRPullback_tmul]
    have h₁ : (rB k E x I).map (j₁) ≤ RY x j₂ I J := (hmap₁ I).trans le_sup_left
    have h₂ : (rB k E x J).map j₂ ≤ RY x j₂ I J := (rB_map_le_R2 j₂ (x := x) J).trans le_sup_right
    have hx : pullbackDR (j₁) x' ∈ omB k L (RY x j₂ I J) q :=
      IsDRMap.regularForms k (isDRMap_pullbackDR k (j₁)) h₁ q hx'
    have hy : pullbackDR j₂ y' ∈ omB k L (RY x j₂ I J) p :=
      IsDRMap.regularForms k (isDRMap_pullbackDR k j₂) h₂ p hy'
    exact Eq.mp (congrArg (fun t => _ ∈ omB k L (RY x j₂ I J) t) hqp) (mul_mem_omB hx hy)
  have hjoin : (fun I => (g) (c I)) - ∑ j, Lj j ∈ Mx.B ((d : ℤ) + 2) := by
    have hm := mapCochain_mixed_boundary (g) hgraphReg hcz
    convert hm using 1
    funext I
    simp only [mapCochain_apply, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Lj, cechJoin, hright, a]
      exact (graphDRPullback_tmul (j₁) j₂ (e j (lft I)) (f j (rgt I))).symm
  have hcup : (∑ j, (Lj j - (-1 : ℤ) ^ (r j) • edge1 (W j))) ∈ Mx.B ((d : ℤ) + 2) :=
    Submodule.sum_mem _ fun j _ => (hJ j).1
  have hl : Λ - originVolumeCochain b ∈ Ctop.B (d : ℤ) := by
    apply hedge _ (sub_mem hΛ (originVolumeCochain_mem_cycles hL.pd b))
    have he := sub_mem (sub_mem hgraph hjoin) hcup
    convert he using 1
    funext I
    by_cases hk : (rgt I).card = 1 <;>
      simp only [edge1, hk, if_true, if_false, Pi.sub_apply, Λ, Finset.sum_apply,
        Pi.smul_apply, Finset.sum_sub_distrib, smul_zero, sub_zero, Finset.sum_const_zero] <;> abel
  obtain ⟨τL, hτL⟩ := hL.topDegreeForms.1
  have hresL := hL.topResidue_cech_boundary τL hτL ρ hρ hl
  have hform : Λ Finset.univ ∈ omB k L (rB k L x Finset.univ) d := by
    have hm := Submodule.mem_pi.mp hΛ.1 Finset.univ (Set.mem_univ _)
    simpa [Ctop, cech, cechC] using hm
  have hformdeg : Λ Finset.univ ∈ ExteriorDifferentials k L d :=
    omB_le_degree (B := rB k L x Finset.univ) (p := d) hform
  have hvol := hL.topDegreeForms.2.1 τL hτL _ hformdeg
  have hLres : topResidue τ ρ (traceDR k E L (Λ Finset.univ)) = ρ (Algebra.trace F L (b : L)) := by
    calc
      _ = topResidue τL ρ (Λ Finset.univ) := by
        nth_rw 1 [hvol]
        rw [topResidue_apply, traceDR_vol0_coefficient τ hτ, topResidue_apply]
      _ = _ := by
        rw [Pi.sub_apply, map_sub, sub_eq_zero, originVolumeCochain, if_pos rfl] at hresL
        exact hresL.trans (by rw [topResidue_apply, map_smul, hτL.1, smul_eq_mul, mul_one])
  rw [alternating_trace_of_cocycle_resolution (C) u d r f₀ f₁
    (fun j => cupResidueFunctional τ ρ (e j)) (fun j => (hparts j).1)
    (fun j _ hy => hE.cupResidueFunctional_eq_zero_of_boundary τ hτ ρ hρ hqp
      (Nat.sub_add_cancel (hparts j).1) (hparts j).2.1 hy)
    (fun r z => hres r z.val z.property) hu, ← hLres]
  simp only [Λ, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he := trace_graph_residue_projection τ ρ (e j) (v j)
  simp only [v, ← htrace j] at he
  rw [he, ← Int.cast_smul_eq_zsmul k]
  simp

end GlobalTheory.PD
