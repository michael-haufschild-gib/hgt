import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.FrobeniusInvariantSubspace
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.RestrictionOfSeparatedInertia
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.PrimeToInertiaRoots

/-! Good polynomial tuples rule out proper common invariant subspaces.
The long prime cycle also rules out new subspaces upon restriction to a
normal subgroup with finite solvable quotient containing the inertia elements. -/

noncomputable section

open Polynomial Matrix Module
open WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

namespace WindowedLandauTheory.CyclotomicNorms

/-- A good tuple gives an irreducible representation even on normal subgroups with solvable quotient. -/
theorem irreducibility_of_good_tuple : IrreducibilityCriterion := by
  intro N g hgf PP J f χ _hBB hgood ℓ hℓf i hℓ G hGg ρ τ φ ι hconj hinj hchar
  classical
  have hℓp : ℓ.Prime := hℓf.out
  have hℓg : ℓ ≠ g i := fun h => hℓ (by rw [h]; exact Set.mem_union_left _ (Set.mem_singleton _))
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := hgood i
  have hpoly : ∀ v, GoodPoly N (f i v) := fun v => ⟨(hG1 v).1, (hG1 v).2.1, (hG1 v).2.2, hG2 v⟩
  choose r σ hr hrf hσ using fun v => exists_index (hpoly v)
  have hmemr : ∀ v j, r v j ∈ rootsBar (f i v) := by
    intro v j; rw [← hrf v]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  have hr0 : ∀ v j, r v j ≠ 0 := fun v j => ne_zero_of_mem (hpoly v) (hmemr v j)
  have hrfin : ∀ v j, IsOfFinOrder (r v j) := fun v j => fbar_isOfFinOrder (hr0 v j)
  let L : PP i → Fin N → Fbar ℓ := fun v j => ι v (primeToPart ℓ (r v j))
  have hLinj : ∀ v, Function.Injective (L v) := by
    intro v j k h
    have h1 := primeToPart_eq_of_map_eq (ι v) (hinj v) (hr0 v j) (hr0 v k) h
    exact hr v (hG3 ℓ hℓp hℓ v _ (hmemr v j) _ (hmemr v k) h1)
  have hLσ : ∀ v j, L v (σ v j) = L v j ^ (g i) := by
    intro v j
    show ι v (primeToPart ℓ (r v (σ v j))) = ι v (primeToPart ℓ (r v j)) ^ (g i)
    rw [hσ v j, primeToPart_pow, map_pow]
    exact orderOf_injective (frobenius (Fbar (g i)) (g i)).toMonoidHom (frobenius_inj _ _) (r v j)
  have hroots : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots =
      Finset.univ.val.map (L v) := by
    intro v
    have hcp : (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly =
        ((Finset.univ.val.map (L v)).map fun a => X - C a).prod := by
      rw [hchar v, ← hrf v, Multiset.map_map, Multiset.map_map]; rfl
    rw [hcp, roots_multiset_prod_X_sub_C]

  have hirr : IrredOn ρ ⊤ :=
    irredOn_of_indexed_labels hpoly hG5 r σ hrf hσ L hLinj hLσ ρ τ φ hconj hroots

  have hpart3 : ∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot
      (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))))) := by
    intro v j hroot
    have hmem := (mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hroot
    rw [hroots v] at hmem
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem
    have hc0 : algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (χ i v j).ne_zero
    have h1 := primeToPart_eq_of_map_eq (ι v) (hinj v) (hr0 v k) hc0 hk
    exact hG4 ℓ hℓp hℓg v j _ (hmemr v k) h1

  have hpart2 : ∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → IsSolvable (G ⧸ H) →
      (∀ v, τ v ∈ H) → IrredOn ρ H := by
    intro H hHn hfin hsolv hτH W hW
    obtain ⟨v₀, q₀, hq₀i, hq₀f, hq₀p, hN2, hN3⟩ := hG6
    have hpc : q₀.natDegree ∈ (σ v₀).cycleType :=
      mem_cycleType_of_factor (hpoly v₀) (hr v₀) (hrf v₀) (hσ v₀) q₀ hq₀i hq₀f hq₀p
    have hN8 : 8 ≤ N := by
      have h2 := hq₀p.two_le
      have h5 : 5 ≤ q₀.natDegree := by
        rcases (show q₀.natDegree = 2 ∨ q₀.natDegree = 3 ∨ q₀.natDegree = 4 ∨
          5 ≤ q₀.natDegree by omega) with h | h | h | h
        · omega
        · omega
        · exact absurd (h ▸ hq₀p) (by norm_num)
        · exact h
      omega
    let ρΓ : Representation (Fbar ℓ) ρ.range (Fin N → Fbar ℓ) := repGL.comp ρ.range.subtype
    have hρΓ : ∀ (y : ρ.range) x, ρΓ y x = repGL (y : GL (Fin N) (Fbar ℓ)) x := fun _ _ => rfl
    have hinjΓ : Function.Injective ρΓ := fun a b h => Subtype.ext (repGL_injective h)
    let H' : Subgroup ρ.range := H.map ρ.rangeRestrict
    have hH' : H'.Normal := hHn.map _ ρ.rangeRestrict_surjective
    have hle : H ≤ H'.comap ρ.rangeRestrict := fun h hh => Subgroup.mem_map_of_mem _ hh
    let ψ := QuotientGroup.map H H' ρ.rangeRestrict hle
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective z
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hfin' : Finite (ρ.range ⧸ H') := Finite.of_surjective ψ hψ
    letI : IsSolvable (G ⧸ H) := hsolv
    have hsolv' : IsSolvable (ρ.range ⧸ H') := solvable_of_surjective hψ
    let T : ρ.range := ρ.rangeRestrict (τ v₀)
    let Φ : ρ.range := ρ.rangeRestrict (φ v₀)
    have hTΦ : Φ * T * Φ⁻¹ = T ^ (g i) := by
      show ρ.rangeRestrict (φ v₀) * ρ.rangeRestrict (τ v₀) * (ρ.rangeRestrict (φ v₀))⁻¹ =
        ρ.rangeRestrict (τ v₀) ^ (g i)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
      apply Subtype.ext
      rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj v₀, map_pow]

    obtain ⟨e, he⟩ := exists_eigenbasis_of_roots (ρ (τ v₀)) (L v₀) (hLinj v₀) (hroots v₀)
    have hTpow : ∀ (n : ℕ) j, ρΓ (T ^ n) (e j) = L v₀ j ^ n • e j := by
      intro n j
      rw [map_pow]
      exact (he j).pow_apply n
    have hlfin : ∀ j, IsOfFinOrder (L v₀ j) :=
      fun j => (ι v₀).isOfFinOrder (primeToPart_isOfFinOrder ℓ _ (hrfin v₀ j))
    have hMo : 0 < ∏ j, orderOf (L v₀ j) := Finset.prod_pos (fun j _ => (hlfin j).orderOf_pos)
    have hlM : ∀ j, L v₀ j ^ (∏ j, orderOf (L v₀ j)) = 1 := fun j =>
      orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    have hTfin : IsOfFinOrder T := by
      rw [isOfFinOrder_iff_pow_eq_one]
      refine ⟨_, hMo, hinjΓ ?_⟩
      rw [map_one]
      exact e.ext (fun j => by rw [hTpow, hlM, one_smul]; rfl)
    let I : Subgroup ρ.range := Subgroup.zpowers T
    have hInat : ∀ y ∈ I, ∃ n : ℕ, T ^ n = y := fun y hy =>
      (Submonoid.mem_powers_iff _ _).mp (hTfin.mem_powers_iff_mem_zpowers.mpr hy)
    have hconjI : ∀ y ∈ I, Φ * y * Φ⁻¹ ∈ I := by
      intro y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [← conj_pow, hTΦ, ← pow_mul]
      exact Subgroup.npow_mem_zpowers _ _
    have hIfin : Finite I := by
      have hsub : (I : Set ρ.range) ⊆ Set.range (fun n : Fin (orderOf T) => T ^ (n : ℕ)) := by
        intro y hy
        obtain ⟨n, rfl⟩ := hInat y hy
        exact ⟨⟨n % orderOf T, Nat.mod_lt _ hTfin.orderOf_pos⟩, pow_mod_orderOf T n⟩
      exact ((Set.finite_range _).subset hsub).to_subtype
    have hIiff : ∀ y, y ∈ I ↔ Φ * y * Φ⁻¹ ∈ I := by
      intro y
      refine ⟨hconjI y, fun hy => ?_⟩
      let c : I → I := fun z => ⟨Φ * z * Φ⁻¹, hconjI z z.2⟩
      have hc : Function.Injective c := by
        intro a b hab
        apply Subtype.ext
        have := congrArg Subtype.val hab
        simpa [c] using this
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hc) ⟨_, hy⟩
      have hzy : (z : ρ.range) = y := by
        have := congrArg Subtype.val hz
        simpa [c] using this
      exact hzy ▸ z.2
    let χ' : Fin N → ρ.range → Fbar ℓ := fun j y => e.repr (ρΓ y (e j)) j
    have hχpow : ∀ j (n : ℕ), χ' j (T ^ n) = L v₀ j ^ n := by
      intro j n
      show e.repr (ρΓ (T ^ n) (e j)) j = _
      rw [hTpow]
      simp
    refine restriction_of_prime_cycle ρ.range (Fbar ℓ) (Fin N → Fbar ℓ) ρΓ N H' I e χ' Φ (σ v₀)⁻¹ q₀.natDegree hN8
      hfin' hsolv' ?_ ?_ ?_ ?_ hIiff ?_ hq₀p (by rw [Fintype.card_fin]; exact hN2) hN3
      (by rw [Equiv.Perm.cycleType_inv]; exact hpc) W ?_
    · exact (Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem _ (hτH v₀))
    · intro W' hW'
      apply hirr W'
      intro h _ x hx
      have := hW' (ρ.rangeRestrict h) x hx
      rwa [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply] at this
    · intro j y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [hTpow, hχpow]
    · intro j k hjk
      refine ⟨T, Subgroup.mem_zpowers T, ?_⟩
      have h1 := hχpow j 1
      have h2 := hχpow k 1
      rw [pow_one, pow_one] at h1 h2
      rw [h1, h2]
      exact fun h => hjk (hLinj v₀ h)
    · intro j y hy
      have hz : Φ⁻¹ * y * Φ ∈ I := by
        rw [hIiff]; simpa [mul_assoc] using hy
      obtain ⟨n, hn⟩ := hInat _ hz
      have hy' : y = T ^ (g i * n) := by
        rw [pow_mul, ← hTΦ, conj_pow, hn]; group
      rw [← hn, hy', hχpow, hχpow, pow_mul, ← hLσ]
      simp
    · intro h hh x hx
      obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.mp hh
      rw [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply]
      exact hW h0 hh0 x hx
  exact ⟨hirr, hpart2, hpart3⟩

end WindowedLandauTheory.CyclotomicNorms
