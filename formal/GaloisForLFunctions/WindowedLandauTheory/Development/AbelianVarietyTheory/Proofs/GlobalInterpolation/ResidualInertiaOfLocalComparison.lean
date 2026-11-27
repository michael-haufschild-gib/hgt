import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidualInertiaPolynomial
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildResidualUnipotence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusOnTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IrreducibilityOfTheoremThree

/-! Local–global matching on inertia gives the residual eigenvalue and
Frobenius relations at the designated places. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Matrix Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.CyclotomicNorms
open ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

/-- Reduction of a continuous integral representation has open kernel in
the adic topology, even after embedding the residue field into a larger field. -/
theorem isOpen_ker_of_ideal_adic {Γ R K : Type} [Group Γ] [TopologicalSpace Γ]
    [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R] [Field K]
    {n : ℕ} (r : Γ →* GL (Fin n) R) (hr : Continuous fun s => (r s).val)
    (hR : IsAdic (maximalIdeal R)) (k : ResidueField R →+* K) :
    IsOpen ((mapRep (k.comp (residue R)) r).ker : Set Γ) := by
  have hm : IsOpen (maximalIdeal R : Set R) := by simpa using (isAdic_iff.mp hR).1 1
  have he : ((mapRep (k.comp (residue R)) r).ker : Set Γ) =
      ⋂ u : Fin n, ⋂ v : Fin n, {s | (r s).val u v - (1 : Matrix (Fin n) (Fin n) R) u v ∈ maximalIdeal R} := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    rw [Units.ext_iff]
    change ((r s).val.map (k.comp (residue R))) = 1 ↔ _
    rw [← Matrix.map_one (k.comp (residue R)) (map_zero _) (map_one _), ← Matrix.ext_iff]
    refine forall_congr' fun u => forall_congr' fun v => ?_
    rw [Matrix.map_apply, Matrix.map_apply, RingHom.comp_apply, RingHom.comp_apply, k.injective.eq_iff,
      ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rw [he]
  exact isOpen_iInter_of_finite fun u => isOpen_iInter_of_finite fun v =>
    hm.preimage (((continuous_apply v).comp ((continuous_apply u).comp hr)).sub continuous_const)

variable (D : D7) (i : D.nd.Loc) (P : List (Part D.naut.CG))

local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.nd.l i

/-- The residue map on tame labels at the coefficient place of a localization. -/
abbrev localTameMap (k : Fin 2) (v : D.nd.PlG k) :
    Fb (D.host.g k) (D.host.g_prime k) →* Fbar ℓ :=
  (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom.toMonoidHom.comp
    (D.ntypes.iota k v (D.nd.w i))

theorem localTameMap_injective_primeTo (k : Fin 2) (v : D.nd.PlG k)
    {x y : Fb (D.host.g k) (D.host.g_prime k)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hpx : (orderOf x).Coprime ℓ) (hpy : (orderOf y).Coprime ℓ)
    (he : localTameMap D i k v x = localTameMap D i k v y) : x = y := by
  have hc (n : ℕ) : n.Coprime ℓ → n.Coprime (D.what₂.places.resChar (D.nd.w i)) := by
    rw [D.nd.w_l i]
    exact id
  exact D.ntypes.iota_inj k v (D.nd.w i) x y hx hy (hc _ hpx) (hc _ hpy)
    ((fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).injective he)

/-- Reduction reads all nonzero Teichmüller factors through the same local
map, including those of the character's linear polynomial. -/
theorem map_residue_eq_prod_localTameMap {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (v : D.nd.PlG k)
    (f : (D.nd.O i)[X]) (S : Multiset (Fb (D.host.g k) (D.host.g_prime k)))
    (hS : ∀ x ∈ S, x ≠ 0)
    (he : f.map (iotaO D.nd D.naut i) = (S.map fun x => X - C (D.ntypes.teichC k x)).prod) :
    f.map ((D.naut.kFbar i).comp (residue (D.nd.O i))) =
      (S.map fun x => X - C (localTameMap D i k v (primeToPart ℓ x))).prod := by
  refine (map_residue_eq_prod_primeToPart T i k v f S hS he).trans ?_
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  change X - C (localTameMap D i k v (primeToPart (D.what₂.places.resChar (D.nd.w i)) x)) = _
  rw [congrArg (fun n => primeToPart n x) (D.nd.w_l i)]

/-- An inertia element with unipotent integral polynomial acts trivially
after reduction if it lies in wild inertia of distinct characteristic. -/
theorem residual_eq_one_of_wild_charpoly
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : Continuous fun s => (r s).val)
    (k : Fin 2) (hk : ℓ ≠ D.host.g k) (v : D.nd.PlG k)
    {s : Γ} (hW : ∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1)
    (hu : (r s).val.charpoly.map (iotaO D.nd D.naut i) = (X - 1) ^ D.R.r) :
    (mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) s = 1 := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let w := D.naut.plGw k v
  have hp : (D.nd.plOm.1 w).valuation (D.host.g k : D.nd.Om) < 1 := by
    simpa using (D.nd.plOm.2 w (D.host.g k : 𝓞 D.host.E)).mpr (D.naut.plGw_over k v)
  have hj : Function.Injective (iotaO D.nd D.naut i) :=
    (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hu' : (r s).val.charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective _ hj
    rw [hu, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  refine eq_one_of_wild_of_unipotent _ hk hp _ (isOpen_ker_of_ideal_adic r hr (D.nd.O_adic i) (D.naut.kFbar i))
    hW ?_
  rw [charpoly_mapRep, hu', Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]

/-- At the designated type places, local–global characteristic-polynomial
matching supplies Frobenius conjugation and the multiset of tame roots
after reduction. -/
theorem tame_fixed_of_local_charpoly {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i P r)
    (hg : goodSig D.nd D.naut P) (k : Fin 2) (hk : ℓ ≠ D.host.g k) (v : D.nd.PlG k)
    (hfull : (D.naut.items₂ k _ (isoLoc D.nd D.naut P (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (isoLoc D.nd D.naut P (D.naut.plGw k v)))
    (hI : ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      (r s).val.charpoly.map (iotaO D.nd D.naut i) =
        D.naut.inePol (isoLoc D.nd D.naut P (D.naut.plGw k v)) s)
    (hW : ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      D.naut.inePol (isoLoc D.nd D.naut P (D.naut.plGw k v)) s = (X - 1) ^ D.R.r) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI : Fact (ℓ).Prime := D.nd.lPrime i
    let ρ := mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r
    ∃ a : Fbar (D.host.g k) →* Fbar ℓ,
      (∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ → a x = a y → x = y) ∧
      (ρ (D.ntypes.tg k v)).val.charpoly =
        ((rootsBar (D.naut.items₂ k _ (isoLoc D.nd D.naut P (D.naut.plGw k v)))).map
          fun x => X - C (a (primeToPart ℓ x))).prod ∧
      ∃ φ : Γ, ρ (φ * D.ntypes.tg k v * φ⁻¹) = ρ (D.ntypes.tg k v) ^ D.host.g k := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  letI : Fact (ℓ).Prime := D.nd.lPrime i
  letI := D.nd.acOm
  let w := D.naut.plGw k v
  let L := isoLoc D.nd D.naut P w
  let f := D.naut.items₂ k w L
  let ρ := mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r
  refine ⟨localTameMap D i k v, fun _ _ => localTameMap_injective_primeTo D i k v, ?_, ?_⟩
  · obtain ⟨hm, hs, -⟩ := (hg k).1
    have hgood : CycleTypeFiniteOrder.GoodPoly D.R.r f :=
      ⟨(hm v).1, (hm v).2.1, (hm v).2.2, hs v⟩
    have hpol := (hI (D.ntypes.tg k v) (D.ntypes.tg_mem k v)).trans
      (D.ntypes.inertiaCharpoly_type k v L hfull)
    change (ρ (D.ntypes.tg k v)).val.charpoly = _
    rw [charpoly_mapRep]
    exact map_residue_eq_prod_localTameMap D i T k v _ (rootsBar f)
      (fun _ hx => CycleTypeFiniteOrder.ne_zero_of_mem hgood hx) hpol
  · apply exists_frobenius_conj_of_wild_trivial D k v ρ
    intro s hs hratio
    exact residual_eq_one_of_wild_charpoly D i r hr.1 k hk v hratio ((hI s hs).trans (hW s hs hratio))

end WindowedLandauTheory.NormalizedTypes
