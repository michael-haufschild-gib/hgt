import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors

/-!
# Every ray class character is induced from a primitive character of its conductor

Let `𝔪 = 𝔪₀ 𝔪∞` be a modulus of a number field `K`, `J ⊇ 𝔪₀` an ideal and `𝔫 = J 𝔪∞`
(`divisorModulus`).

* **The map of ray class groups** (`rayClassReduction`, `rayClassReduction_surjective`). The
  ideals prime to `𝔪₀` are prime to `J`, and `K^{𝔪,1}_+ ≤ K^{𝔫,1}_+`; so `[I] ↦ [I]` is a
  homomorphism `r : Cl_𝔪 → Cl_𝔫`. It is onto: a class of `Cl_𝔫` differs from the image of a class
  with the same ideal class by a principal class `[(γ)]`, and the residue and the signs of `γ`
  are those of an element prime to `𝔪₀`, since units lift along `𝓞_K/𝔪₀ → 𝓞_K/J`.
* **Descent** (`ker_rayClassReduction_le`, `descendHecke`). A character `ψ` of `Cl_𝔪` whose finite
  part is trivial on the residues `≡ 1 mod J` is trivial on `ker r`: it is `ψ' ∘ r` for one
  character `ψ'` of `Cl_𝔫`, with `ψ'(𝔞) = ψ(𝔞)` on the integral ideals prime to `𝔪₀`
  (`heckeValue_descendHecke`) and finite part `χ'_f ∘ π = χ_f` (`finiteResidueCharacter_descendHecke`).
* **The primitive character** (`primitiveHecke`, `heckeFiniteConductor_primitiveHecke`). For
  `J` the finite conductor of `ψ` the character `ψ'` is primitive.
* **Euler products** (`heckeL_eq_heckeL_descendHecke_mul`). For `Re s > 1`,
  `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The divisor modulus and the map of ray class groups -/

/-- The modulus `J 𝔪∞` for an ideal `J ⊇ 𝔪₀`. -/
@[reducible] def divisorModulus (J : Ideal (𝓞 K)) (hJ : 𝔪.fin ≤ J) : Modulus K :=
  ⟨J, fun h => 𝔪.fin_ne_bot (le_bot_iff.mp (h ▸ hJ)), 𝔪.inf⟩

variable {J : Ideal (𝓞 K)} (hJ : 𝔪.fin ≤ J)

/-- The primes of `J` are primes of `𝔪₀`. -/
theorem dvd_fin_of_dvd_divisorModulus {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ (divisorModulus 𝔪 J hJ).fin) : v.asIdeal ∣ 𝔪.fin :=
  Ideal.dvd_iff_le.mpr (hJ.trans (Ideal.dvd_iff_le.mp hv))

theorem primeToUnits_le_divisorModulus :
    primeToUnits 𝔪 ≤ primeToUnits (divisorModulus 𝔪 J hJ) :=
  fun _ hα v hv => hα v (dvd_fin_of_dvd_divisorModulus 𝔪 hJ hv)

theorem idealGroup_le_divisorModulus :
    idealGroup 𝔪 ≤ idealGroup (divisorModulus 𝔪 J hJ) :=
  fun _ hI v hv => hI v (dvd_fin_of_dvd_divisorModulus 𝔪 hJ hv)

/-- Reduction of residues `π : (𝓞_K/𝔪₀)ˣ → (𝓞_K/J)ˣ`. -/
def residueReduction : (𝓞 K ⧸ 𝔪.fin)ˣ →* (𝓞 K ⧸ (divisorModulus 𝔪 J hJ).fin)ˣ :=
  Units.map (Ideal.Quotient.factor hJ).toMonoidHom

omit [NumberField K] in
theorem coe_residueReduction (u : (𝓞 K ⧸ 𝔪.fin)ˣ) :
    (residueReduction 𝔪 hJ u : 𝓞 K ⧸ (divisorModulus 𝔪 J hJ).fin) =
      Ideal.Quotient.factor hJ (u : 𝓞 K ⧸ 𝔪.fin) := rfl

/-- Units lift along `𝓞_K/𝔪₀ → 𝓞_K/J`. -/
theorem residueReduction_surjective : Function.Surjective (residueReduction 𝔪 hJ) := by
  haveI : Finite (𝓞 K ⧸ 𝔪.fin) := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  exact FiniteRing.units_map_surjective (Ideal.Quotient.factor hJ)
    (Ideal.Quotient.factor_surjective hJ)

theorem unitMod_divisorModulus {r : 𝓞 K}
    (hr : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → r ∉ v.asIdeal) :
    unitMod (divisorModulus 𝔪 J hJ)
        (fun v hv => hr v (dvd_fin_of_dvd_divisorModulus 𝔪 hJ hv)) =
      residueReduction 𝔪 hJ (unitMod 𝔪 hr) :=
  Units.ext (Ideal.Quotient.factor_mk hJ r).symm

/-- The residue modulo `J` of an element prime to `𝔪₀` is the image of its residue modulo
`𝔪₀`. -/
theorem reduce_divisorModulus (α : primeToUnits 𝔪) :
    reduce (divisorModulus 𝔪 J hJ) ⟨α, primeToUnits_le_divisorModulus 𝔪 hJ α.2⟩ =
      residueReduction 𝔪 hJ (reduce 𝔪 α) := by
  obtain ⟨-, hab, h⟩ := unitFraction_spec 𝔪 α
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
      (unitFraction 𝔪 α).1 ∉ v.asIdeal := fun v hv => (hab v hv).1
  have hb : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
      (unitFraction 𝔪 α).2 ∉ v.asIdeal := fun v hv => (hab v hv).2
  rw [reduce_eq (divisorModulus 𝔪 J hJ) _
      (fun v hv => ha v (dvd_fin_of_dvd_divisorModulus 𝔪 hJ hv))
      (fun v hv => hb v (dvd_fin_of_dvd_divisorModulus 𝔪 hJ hv)) h,
    reduce_eq 𝔪 α ha hb h, map_mul, map_inv, unitMod_divisorModulus 𝔪 hJ ha,
    unitMod_divisorModulus 𝔪 hJ hb]

/-- Residue and signs modulo `𝔫` of an element prime to `𝔪₀`. -/
theorem rayHom_divisorModulus (α : primeToUnits 𝔪) :
    rayHom (divisorModulus 𝔪 J hJ) ⟨α, primeToUnits_le_divisorModulus 𝔪 hJ α.2⟩ =
      (residueReduction 𝔪 hJ (rayHom 𝔪 α).1, (rayHom 𝔪 α).2) :=
  Prod.ext (reduce_divisorModulus 𝔪 hJ α) rfl

theorem rayGroup_le_divisorModulus : rayGroup 𝔪 ≤ rayGroup (divisorModulus 𝔪 J hJ) := by
  rintro _ ⟨α, hα, rfl⟩
  have h1 : rayHom 𝔪 α = 1 := hα
  refine ⟨⟨α, primeToUnits_le_divisorModulus 𝔪 hJ α.2⟩, ?_, rfl⟩
  show rayHom (divisorModulus 𝔪 J hJ) _ = 1
  rw [rayHom_divisorModulus, h1]
  exact Prod.ext (map_one _) rfl

theorem rayPrincipal_le_divisorModulus :
    rayPrincipal 𝔪 ≤ rayPrincipal (divisorModulus 𝔪 J hJ) :=
  Subgroup.map_mono (rayGroup_le_divisorModulus 𝔪 hJ)

/-- **The map of ray class groups** `r : Cl_𝔪 → Cl_𝔫`, `[I] ↦ [I]`. -/
def rayClassReduction : RayClassGroup 𝔪 →* RayClassGroup (divisorModulus 𝔪 J hJ) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (idealGroup_le_divisorModulus 𝔪 hJ))
    fun _ hI => Subgroup.mem_subgroupOf.mpr
      (rayPrincipal_le_divisorModulus 𝔪 hJ (Subgroup.mem_subgroupOf.mp hI))

theorem rayClassReduction_rayClass (I : idealGroup 𝔪) :
    rayClassReduction 𝔪 hJ (rayClass 𝔪 I) =
      rayClass (divisorModulus 𝔪 J hJ) ⟨I, idealGroup_le_divisorModulus 𝔪 hJ I.2⟩ := rfl

theorem rayClassReduction_rayClassOfElt (α : primeToUnits 𝔪) :
    rayClassReduction 𝔪 hJ (rayClassOfElt 𝔪 α) =
      rayClassOfElt (divisorModulus 𝔪 J hJ)
        ⟨α, primeToUnits_le_divisorModulus 𝔪 hJ α.2⟩ := rfl

/-- `r` commutes with the maps to the ideal class group. -/
theorem toClassGroup_rayClassReduction (c : RayClassGroup 𝔪) :
    toClassGroup (divisorModulus 𝔪 J hJ) (rayClassReduction 𝔪 hJ c) = toClassGroup 𝔪 c := by
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective c
  exact (toClassGroup_rayClass (divisorModulus 𝔪 J hJ)
    ⟨I, idealGroup_le_divisorModulus 𝔪 hJ I.2⟩).trans (toClassGroup_rayClass 𝔪 I).symm

/-- **`Cl_𝔪 → Cl_𝔫` is onto.** -/
theorem rayClassReduction_surjective : Function.Surjective (rayClassReduction 𝔪 hJ) := by
  intro c
  -- a class `d` of `Cl_𝔪` with the ideal class of `c`
  obtain ⟨d, hd⟩ := toClassGroup_surjective 𝔪 (toClassGroup (divisorModulus 𝔪 J hJ) c)
  have hker : toClassGroup (divisorModulus 𝔪 J hJ) (c * (rayClassReduction 𝔪 hJ d)⁻¹) = 1 := by
    rw [map_mul, map_inv, toClassGroup_rayClassReduction, hd, mul_inv_cancel]
  -- `c r(d)⁻¹ = [(γ)]` with `γ` prime to `J`
  obtain ⟨γ, hγ⟩ := ker_toClassGroup_le (divisorModulus 𝔪 J hJ) _ hker
  -- `δ` prime to `𝔪₀` with the residue modulo `J` and the signs of `γ`
  obtain ⟨u, hu⟩ := residueReduction_surjective 𝔪 hJ (rayHom (divisorModulus 𝔪 J hJ) γ).1
  obtain ⟨δ, hδ⟩ := rayHom_surjective 𝔪 (u, (rayHom (divisorModulus 𝔪 J hJ) γ).2)
  have hδγ : rayHom (divisorModulus 𝔪 J hJ) ⟨δ, primeToUnits_le_divisorModulus 𝔪 hJ δ.2⟩ =
      rayHom (divisorModulus 𝔪 J hJ) γ := by
    rw [rayHom_divisorModulus, hδ]
    exact Prod.ext hu rfl
  have hmem : (⟨δ, primeToUnits_le_divisorModulus 𝔪 hJ δ.2⟩ :
      primeToUnits (divisorModulus 𝔪 J hJ)) * γ⁻¹ ∈ (rayHom (divisorModulus 𝔪 J hJ)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hδγ, mul_inv_cancel]
  have hcls := ker_rayHom_le (divisorModulus 𝔪 J hJ) hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hcls
  refine ⟨rayClassOfElt 𝔪 δ * d, ?_⟩
  rw [map_mul, rayClassReduction_rayClassOfElt, hcls, hγ, inv_mul_cancel_right]

/-! ### Descent of characters -/

/-- **The kernel of `r` is killed by the characters whose finite part descends.** If the finite
part of `ψ` is trivial on the residues `≡ 1 mod J`, then `ψ` is trivial on `ker r`: a class of
the kernel is `[(α)]` with `α ≡ 1 mod^× J` positive at `𝔪∞`. -/
theorem ker_rayClassReduction_le (ψ : HeckeCharacter 𝔪)
    (hψ : (residueReduction 𝔪 hJ).ker ≤ (finiteResidueCharacter 𝔪 ψ).ker) :
    (rayClassReduction 𝔪 hJ).ker ≤ ψ.ker := by
  intro c hc
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective c
  have h1 : ((Subgroup.inclusion (idealGroup_le_divisorModulus 𝔪 hJ) I :
      idealGroup (divisorModulus 𝔪 J hJ)) : RayClassGroup (divisorModulus 𝔪 J hJ)) = 1 :=
    MonoidHom.mem_ker.mp hc
  have hI : (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal (divisorModulus 𝔪 J hJ) :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
      (Subgroup.inclusion (idealGroup_le_divisorModulus 𝔪 hJ) I)).mp h1)
  obtain ⟨_, ⟨β, hβ, rfl⟩, hβI⟩ := hI
  have hβI' : toPrincipalIdeal (𝓞 K) K (β : Kˣ) = I := hβI
  have hβm : (β : Kˣ) ∈ primeToUnits 𝔪 :=
    (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mp (by rw [hβI']; exact I.2)
  have hcls : rayClass 𝔪 I = rayClassOfElt 𝔪 ⟨β, hβm⟩ :=
    congrArg (rayClass 𝔪) (Subtype.ext hβI'.symm)
  -- residue modulo `J` and signs of `β` are trivial
  have h2 : (residueReduction 𝔪 hJ (rayHom 𝔪 ⟨β, hβm⟩).1, (rayHom 𝔪 ⟨β, hβm⟩).2) = 1 :=
    (rayHom_divisorModulus 𝔪 hJ ⟨β, hβm⟩).symm.trans hβ
  have hred : residueReduction 𝔪 hJ (reduce 𝔪 ⟨β, hβm⟩) = 1 := congrArg Prod.fst h2
  have hsign : signAtInf 𝔪 (β : Kˣ) = 1 := congrArg Prod.snd h2
  show ψ (rayClass 𝔪 I) = 1
  rw [hcls, character_rayClassOfElt_eq, MonoidHom.mem_ker.mp (hψ (MonoidHom.mem_ker.mpr hred)),
    one_mul]
  exact (congrArg (infiniteSignCharacter 𝔪 ψ) hsign).trans (map_one _)

variable (ψ : HeckeCharacter 𝔪) (hψ : (rayClassReduction 𝔪 hJ).ker ≤ ψ.ker)

/-- **The character of `Cl_𝔫` induced by a character of `Cl_𝔪` trivial on `ker r`.** -/
def descendHecke : HeckeCharacter (divisorModulus 𝔪 J hJ) :=
  MonoidHom.liftOfSurjective (rayClassReduction 𝔪 hJ) (rayClassReduction_surjective 𝔪 hJ)
    ⟨ψ, hψ⟩

theorem descendHecke_apply (c : RayClassGroup 𝔪) :
    descendHecke 𝔪 hJ ψ hψ (rayClassReduction 𝔪 hJ c) = ψ c :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ψ, hψ⟩ c

/-- `ψ'` is trivial iff `ψ` is. -/
theorem descendHecke_eq_one_iff : descendHecke 𝔪 hJ ψ hψ = 1 ↔ ψ = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun c => ?_
    rw [← descendHecke_apply 𝔪 hJ ψ hψ c, h]
    rfl
  · intro h
    refine MonoidHom.ext fun c => ?_
    obtain ⟨d, rfl⟩ := rayClassReduction_surjective 𝔪 hJ c
    rw [descendHecke_apply, h]
    rfl

/-- **`ψ'(𝔞) = ψ(𝔞)`** on the integral ideals prime to `𝔪₀`. -/
theorem heckeValue_descendHecke {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hm : idealUnit hI ∈ idealGroup 𝔪) :
    heckeValue (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) I = heckeValue 𝔪 ψ I := by
  rw [heckeValue_of_mem (divisorModulus 𝔪 J hJ) _ hI (idealGroup_le_divisorModulus 𝔪 hJ hm),
    heckeValue_of_mem 𝔪 ψ hI hm]
  exact congrArg Units.val (descendHecke_apply 𝔪 hJ ψ hψ (rayClass 𝔪 ⟨_, hm⟩))

/-- At a prime: `ψ(v) = 0` if `v | 𝔪₀`, and `ψ(v) = ψ'(v)` otherwise. -/
theorem heckeValue_prime_eq_descendHecke (v : HeightOneSpectrum (𝓞 K)) :
    heckeValue 𝔪 ψ v.asIdeal = if v.asIdeal ∣ 𝔪.fin then 0
      else heckeValue (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) v.asIdeal := by
  by_cases hv : v.asIdeal ∣ 𝔪.fin
  · rw [if_pos hv]
    apply heckeValue_of_not_mem
    rintro ⟨hI, hm⟩
    have h := hm v hv
    rw [coe_idealUnit, count_self] at h
    exact one_ne_zero h
  · rw [if_neg hv]
    have hm : idealUnit v.ne_bot ∈ idealGroup 𝔪 := by
      intro w hw
      rw [coe_idealUnit]
      exact count_maximal_coprime K w (fun h => hv (h.symm ▸ hw))
    exact (heckeValue_descendHecke 𝔪 hJ ψ hψ v.ne_bot hm).symm

/-- `r` on the classes of principal ideals, read by residues and signs. -/
theorem rayClassReduction_fullRayResidueClass (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) :
    rayClassReduction 𝔪 hJ (fullRayResidueClass 𝔪 g) =
      fullRayResidueClass (divisorModulus 𝔪 J hJ) (residueReduction 𝔪 hJ g.1, g.2) := by
  obtain ⟨α, rfl⟩ := rayHom_surjective 𝔪 g
  rw [fullRayResidueClass_rayHom, rayClassReduction_rayClassOfElt]
  exact (fullRayResidueClass_rayHom (divisorModulus 𝔪 J hJ) _).symm.trans
    (congrArg (fullRayResidueClass (divisorModulus 𝔪 J hJ)) (rayHom_divisorModulus 𝔪 hJ α))

/-- **The finite part of `ψ'`**: `χ'_f ∘ π = χ_f`. -/
theorem finiteResidueCharacter_descendHecke (u : (𝓞 K ⧸ 𝔪.fin)ˣ) :
    finiteResidueCharacter (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ)
        (residueReduction 𝔪 hJ u) = finiteResidueCharacter 𝔪 ψ u := by
  have h := descendHecke_apply 𝔪 hJ ψ hψ (fullRayResidueClass 𝔪 (u, 1))
  rw [rayClassReduction_fullRayResidueClass] at h
  exact h

/-- **Euler products.** `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})` for `Re s > 1`:
the Euler factors agree at `v ∤ 𝔪₀`, and the factor of `ψ` at `v | 𝔪₀` is `1`. -/
theorem heckeL_eq_heckeL_descendHecke_mul {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = heckeL (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) s *
      ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
        (1 - heckeValue (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) v.asIdeal *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  let F (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
    if v.asIdeal ∣ 𝔪.fin then
      1 - heckePrimeTerm (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) s v else 1
  have hF : HasProd F (∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
      (1 - heckeValue (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) v.asIdeal *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
    have h : HasProd F (∏ v ∈ (finite_primes_dvd 𝔪).toFinset, F v) :=
      hasProd_prod_of_ne_finset_one (by
        intro v hv
        simp only [Set.Finite.mem_toFinset] at hv
        exact if_neg hv)
    convert h using 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact (if_pos hv).symm
  have h := (heckeL_eulerProduct_hasProd (divisorModulus 𝔪 J hJ)
    (descendHecke 𝔪 hJ ψ hψ) hs).mul hF
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      (1 - heckePrimeTerm (divisorModulus 𝔪 J hJ) (descendHecke 𝔪 hJ ψ hψ) s v)⁻¹ * F v =
        (1 - heckePrimeTerm 𝔪 ψ s v)⁻¹ := by
    have hne := heckeEulerDenominator_ne_zero (divisorModulus 𝔪 J hJ)
      (descendHecke 𝔪 hJ ψ hψ) hs v
    have hval := heckeValue_prime_eq_descendHecke 𝔪 hJ ψ hψ v
    by_cases hm : v.asIdeal ∣ 𝔪.fin
    · rw [if_pos hm] at hval
      simp only [F, if_pos hm]
      rw [inv_mul_cancel₀ hne, heckePrimeTerm, hval, zero_mul, sub_zero, inv_one]
    · rw [if_neg hm] at hval
      simp only [F, if_neg hm, mul_one]
      rw [heckePrimeTerm, heckePrimeTerm, hval]
  simp only [hlocal] at h
  exact (heckeL_eulerProduct_hasProd 𝔪 ψ hs).unique h

/-! ### The primitive character -/

/-- The finite part of `ψ` is trivial on the residues `≡ 1` modulo its conductor. -/
theorem ker_residueReduction_conductor_le (ψ : HeckeCharacter 𝔪) :
    (residueReduction 𝔪 (modulus_le_heckeFiniteConductor 𝔪 ψ)).ker ≤
      (finiteResidueCharacter 𝔪 ψ).ker := by
  intro u hu
  have h := heckePrimitiveFiniteCharacter_unit 𝔪 ψ u
  have h1 : heckeConductorReduction 𝔪 ψ (u : 𝓞 K ⧸ 𝔪.fin) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp hu)
  rw [h1, map_one, finiteHeckeWeight_unit] at h
  exact MonoidHom.mem_ker.mpr (Units.ext (h.symm.trans Units.val_one.symm))

/-- **The modulus of the conductor** of `ψ`: its finite conductor and the real places of `𝔪`. -/
def conductorModulus (ψ : HeckeCharacter 𝔪) : Modulus K :=
  divisorModulus 𝔪 (heckeFiniteConductor 𝔪 ψ) (modulus_le_heckeFiniteConductor 𝔪 ψ)

/-- **The primitive character** of a ray class character `ψ`: the character modulo the
conductor that induces `ψ`. -/
def primitiveHecke (ψ : HeckeCharacter 𝔪) : HeckeCharacter (conductorModulus 𝔪 ψ) :=
  descendHecke 𝔪 (modulus_le_heckeFiniteConductor 𝔪 ψ) ψ
    (ker_rayClassReduction_le 𝔪 _ ψ (ker_residueReduction_conductor_le 𝔪 ψ))

/-- **The primitive character is primitive**: its finite part is the primitive character of
the finite part of `ψ`. -/
theorem heckeFiniteConductor_primitiveHecke (ψ : HeckeCharacter 𝔪) :
    heckeFiniteConductor (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) =
      (conductorModulus 𝔪 ψ).fin := by
  have h : finiteHeckeWeight (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) =
      heckePrimitiveFiniteCharacter 𝔪 ψ := by
    apply heckePrimitiveFiniteCharacter_unique
    ext u
    rw [FiniteRing.inflateChar_unit, finiteHeckeWeight_unit]
    exact (finiteHeckeWeight_unit (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
      (residueReduction 𝔪 (modulus_le_heckeFiniteConductor 𝔪 ψ) u)).trans
      (congrArg Units.val (finiteResidueCharacter_descendHecke 𝔪 _ ψ _ u))
  have hp : FiniteRing.IsPrimitive
      (finiteHeckeWeight (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)) := by
    rw [h]
    exact heckePrimitiveFiniteCharacter_isPrimitive 𝔪 ψ
  exact (finiteHeckeWeight_isPrimitive_iff (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)).mp hp

theorem primitiveHecke_eq_one_iff (ψ : HeckeCharacter 𝔪) : primitiveHecke 𝔪 ψ = 1 ↔ ψ = 1 :=
  descendHecke_eq_one_iff 𝔪 _ ψ _

/-- `ψ'(𝔞) = ψ(𝔞)` on the integral ideals prime to `𝔪₀`. -/
theorem heckeValue_primitiveHecke (ψ : HeckeCharacter 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hm : idealUnit hI ∈ idealGroup 𝔪) :
    heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) I = heckeValue 𝔪 ψ I :=
  heckeValue_descendHecke 𝔪 _ ψ _ hI hm

/-- `ψ(v) = ψ'(v)` at the primes `v ∤ 𝔪₀`. -/
theorem heckeValue_primitiveHecke_prime (ψ : HeckeCharacter 𝔪) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ 𝔪.fin) :
    heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal =
      heckeValue 𝔪 ψ v.asIdeal := by
  have h := heckeValue_prime_eq_descendHecke 𝔪 (modulus_le_heckeFiniteConductor 𝔪 ψ) ψ
    (ker_rayClassReduction_le 𝔪 _ ψ (ker_residueReduction_conductor_le 𝔪 ψ)) v
  rw [if_neg hv] at h
  exact h.symm

/-- **Every Hecke `L`-series is the `L`-series of its primitive character** up to the Euler
factors at the modulus: `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})` for `Re s > 1`. -/
theorem heckeL_eq_heckeL_primitiveHecke_mul (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = heckeL (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s *
      ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
        (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) :=
  heckeL_eq_heckeL_descendHecke_mul 𝔪 _ ψ _ hs

end GaloisForLFunctions.HeckeLFunctions
