import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidualInertiaOfLocalComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TheoremThreePrimeOfInertia

/-! The lattice reduction at a designated type place uses the same root map
for the rank-one character and the full tame parameter. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.CyclotomicNorms
open ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.nd.l i

/-- Reduce the rank-one character into the same residue field as the representation. -/
abbrev chiBar : Γ →* (Fbar ℓ)ˣ :=
  (Units.map ((D.naut.kFbar i).comp (residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i 1)

theorem isOpen_ker_chiBar : IsOpen ((chiBar D i).ker : Set Γ) := by
  have hm := (isAdic_iff.mp (D.nd.O_adic i)).1 1
  rw [pow_one] at hm
  have hc : Continuous fun s : Γ => chi1 D.nd i s - 1 := (D.nd.chi_cont i 1).sub continuous_const
  have he : ((chiBar D i).ker : Set Γ) =
      (fun s => chi1 D.nd i s - 1) ⁻¹' (maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, Units.val_one, Set.mem_preimage]
    change D.naut.kFbar i (residue (D.nd.O i) (chi1 D.nd i s)) = 1 ↔
      chi1 D.nd i s - 1 ∈ maximalIdeal (D.nd.O i)
    rw [map_eq_one_iff _ (D.naut.kFbar i).injective, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  rw [he]
  exact hm.preimage hc

/-- The two type-character orientations yield the same exclusion at the
designated tame element after reduction. -/
theorem not_isRoot_at_designated_place {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE) (P : List (Part D.naut.CG)) (hg : goodSig D.nd D.naut P)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) (hk : ℓ ≠ D.host.g k) (v : D.nd.PlG k)
    (hfull : (D.naut.items₂ k _ (isoLoc D.nd D.naut P (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (isoLoc D.nd D.naut P (D.naut.plGw k v)))
    (hI : (r (D.ntypes.tg k v)).val.charpoly.map (iotaO D.nd D.naut i) =
      D.naut.inePol (isoLoc D.nd D.naut P (D.naut.plGw k v)) (D.ntypes.tg k v)) :
    ¬ ((mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) (D.ntypes.tg k v)).val.charpoly.IsRoot
      (chiBar D i (D.ntypes.tg k v) : Fbar ℓ) := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let w := D.naut.plGw k v
  let f := D.naut.items₂ k w (isoLoc D.nd D.naut P w)
  let τ := D.ntypes.tg k v
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩
  let c := algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k))
  obtain ⟨hm, hs, -⟩ := (hg k).1
  have hgood : CycleTypeFiniteOrder.GoodPoly D.R.r f :=
    ⟨(hm v).1, (hm v).2.1, (hm v).2.2, hs v⟩
  have hp := map_residue_eq_prod_localTameMap D i T k v (r τ).val.charpoly (rootsBar f)
    (fun _ hx => CycleTypeFiniteOrder.ne_zero_of_mem hgood hx) (hI.trans (D.ntypes.inertiaCharpoly_type k v _ hfull))
  have ht := D.ntypes.chiT_tg i k v hk
  obtain ⟨u, hu, hc⟩ : ∃ u : (ZMod (D.host.g k))ˣ,
      (u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹) ∧
      iotaO D.nd D.naut i (chi1 D.nd i τ) = D.ntypes.teichC k (c u) :=
    ht.elim (fun h => ⟨_, Or.inl rfl, h⟩) (fun h => ⟨_, Or.inr rfl, h⟩)
  have hu₀ : c u ≠ 0 := (_root_.map_ne_zero c).mpr u.ne_zero
  have hχ := map_residue_eq_prod_localTameMap D i T k v (X - C (chi1 D.nd i τ)) {c u}
    (by simp [hu₀]) (by simp [hc])
  have hv : (chiBar D i τ : Fbar ℓ) = localTameMap D i k v (primeToPart ℓ (c u)) := by
    change ((D.naut.kFbar i).comp (residue (D.nd.O i))) (chi1 D.nd i τ) = _
    simpa using hχ
  change ¬ ((mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) τ).val.charpoly.IsRoot _
  rw [charpoly_mapRep, hp, hv]
  exact goodSig_not_isRoot_of_labels D i P hg k hk v j (localTameMap D i k v)
    (fun _ _ => localTameMap_injective_primeTo D i k v) u hu

end WindowedLandauTheory.NormalizedTypes
