import GaloisForLFunctions.RHTower.Artin.IdealsArePrincipalUpToADescentSetOfPrimes
import GaloisForLFunctions.RHTower.Artin.TheDegreeDividesTheNormIndexOfACyclicExtension
import GaloisForLFunctions.RHTower.Artin.IdealsWithTrivialArtinSymbolInACyclicExtensionAreNormsModuloARay

/-!
# The Artin map of a cyclic extension is trivial on a ray

**The reciprocity law for cyclic extensions**
(`exists_rayPrincipal_le_ker_artinMap_of_forall_mem_zpowers`). Let `L/K` be a cyclic extension
of number fields with group `G` of order `n`. There is `c ≥ 1`, divisible by the ramified
primes, such that the Artin symbol `((α), L/K)` is trivial for every `α ≡ 1 mod^× c` positive at
the real places.

Proof. Take `q ≥ 1` with `S`, the set of primes of `K` dividing `q`, such that `L/K` is
unramified outside `S` and the primes of `K` and of `L` are principal up to `S`, and
`c = q^{J+1}` with `J` so large that the ray modulo `(c) ∞` lies in the congruence subgroup `W`
at `S` and in the group `P` of elements positive at the ramified places. Put

  `Θ(α) = Π_{v ∉ S} Frob_v^{v(α)}`  (`artinMapOutside`),  `U = N L^× · (K^× ∩ W ∩ P) · K_S`.

* `ker Θ ⊂ U` (`ofMul_mem_of_artinMapOutside_eq_one`): the part `𝔞` of `(α)` outside `S` has
  trivial Artin symbol, so `𝔞 = (γ) N(𝔄)` with `γ` in the ray modulo `(c) ∞`; and `𝔄 = (y) 𝔄₂`
  with `𝔄₂` supported above `S`. Then `α / (γ N(y))` is a unit outside `S`.
* `n` divides `[K^× : U]` (the second inequality), and `[K^× : ker Θ]` divides `n`.

Hence `U = ker Θ`, and the ray modulo `(c) ∞` lies in `U`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-- If the kernel of a homomorphism to a finite group `F` lies in a subgroup `U` whose index is
divisible by `|F|`, then `U` is the kernel. -/
theorem le_ker_of_ker_le_of_card_dvd_index {A F : Type*} [AddGroup A] [AddGroup F] [Finite F]
    (f : A →+ F) {U : AddSubgroup A} (hker : f.ker ≤ U) (hdvd : Nat.card F ∣ U.index) :
    U ≤ f.ker := by
  have h1 : f.ker.index ∣ Nat.card F := by
    rw [AddSubgroup.index_ker]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  have h0 : f.ker.index ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at h1
    exact Nat.card_pos.ne' h1
  have hU : U.index = f.ker.index :=
    Nat.dvd_antisymm (AddSubgroup.index_dvd_of_le hker) (h1.trans hdvd)
  have h3 := AddSubgroup.relIndex_mul_index hker
  rw [hU] at h3
  exact AddSubgroup.relIndex_eq_one.mp
    (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (h3.trans (one_mul _).symm))

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction infinitePlaceMulAction

/-- The Artin symbol outside a finite set `S` of primes: `I ↦ Π_{v ∉ S} Frob_v^{v(I)}`. -/
def artinMapOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* G :=
  primeValuesHom fun v => if v ∈ S then 1 else frobeniusOrOne K L G v

variable {K L G}

/-- The Artin symbol outside `S` is trivial on the ideals supported on `S`. -/
theorem artinMapOutside_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))}
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : I ∈ idealsSupportedOn (S : Set (HeightOneSpectrum (𝓞 K)))) :
    artinMapOutside K L G S I = 1 := by
  refine Subgroup.mem_bot.mp (primeValuesHom_mem ⊥ I fun v hv => ?_)
  rw [if_pos (not_not.mp fun hS => hv (h v hS))]
  exact Subgroup.one_mem _

/-- The Artin symbol outside `S` is the Artin symbol on the ideals prime to `S`. -/
theorem artinMapOutside_eq_artinMap {S : Finset (HeightOneSpectrum (𝓞 K))}
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ∀ v ∈ S, count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0) :
    artinMapOutside K L G S I = artinMap K L G I := by
  show primeValuesHom _ I = primeValuesHom (frobeniusOrOne K L G) I
  exact primeValuesHom_congr I fun v hv => if_neg fun hS => hv (h v hS)

variable (K L G)

/-- **The kernel of the Artin symbol outside `S` lies in `N L^× · W · K_S`**, for a cyclic
extension unramified outside the set `S` of primes dividing `c`, with the primes of `L`
principal up to `S`, and `W` a group containing the ray modulo `(c) ∞`. -/
theorem ofMul_mem_of_artinMapOutside_eq_one {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (c : ℕ) [NeZero c]
    (hSc : ∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∈ v.asIdeal ↔ v ∈ S)
    (hram : ∀ v, v ∉ S → IsUnramifiedPrime K L G v)
    (hL : PrincipalOutside L (primesAbove K L G S : Set (HeightOneSpectrum (𝓞 L))))
    {W : AddSubgroup (Additive Kˣ)}
    (hW : ∀ γ ∈ rayGroup (normModulus K c), Additive.ofMul γ ∈ W) {α : Kˣ}
    (hα : artinMapOutside K L G S (toPrincipalIdeal (𝓞 K) K α) = 1) :
    Additive.ofMul α ∈ (actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔ W ⊔
      (sUnits L G (primesAbove K L G S)).comap (baseIncl K L) := by
  -- `(α) = 𝔞 𝔰` with `𝔞` prime to `S` and `𝔰` supported on `S`
  obtain ⟨𝔞, h𝔞, 𝔰, h𝔰, hα𝔞⟩ := Subgroup.mem_sup.mp
    (mem_idealGroup_sup_idealsSupportedOn K c (toPrincipalIdeal (𝓞 K) K α))
  have h𝔰S : 𝔰 ∈ idealsSupportedOn (S : Set (HeightOneSpectrum (𝓞 K))) := fun v hv =>
    h𝔰 v fun h => hv ((hSc v).mp h)
  have h𝔞S : ∀ v ∈ S, count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 := fun v hv =>
    h𝔞 v ((dvd_normModulus_fin_iff K c v).mpr ((hSc v).mpr hv))
  have hart : artinMap K L G 𝔞 = 1 := by
    have h1 := congrArg (artinMapOutside K L G S) hα𝔞
    rw [map_mul, artinMapOutside_eq_one h𝔰S, mul_one, artinMapOutside_eq_artinMap h𝔞S, hα] at h1
    exact h1
  -- `𝔞 = (γ) N(𝔄)` with `γ` in the ray, and `𝔄 = (y) 𝔄₂` with `𝔄₂` supported above `S`
  obtain ⟨_, ⟨γ, hγ, rfl⟩, _, ⟨𝔄, rfl⟩, h𝔞eq⟩ := Subgroup.mem_sup.mp
    (mem_rayPrincipal_sup_range_idealNormHom_of_artinMap_eq_one K L hσ c
      (fun v hv => hram v fun h => hv ((hSc v).mpr h)) h𝔞 hart)
  obtain ⟨_, ⟨y, rfl⟩, 𝔄₂, h𝔄₂, rfl⟩ := Subgroup.mem_sup.mp
    (mem_range_toPrincipalIdeal_sup_idealsSupportedOn hL 𝔄)
  have h𝔄₂' : 𝔄₂ ∈ idealsSupportedOn {w : HeightOneSpectrum (𝓞 L) |
      w.under (𝓞 K) ∈ (S : Set (HeightOneSpectrum (𝓞 K)))} := fun w hw => h𝔄₂ w hw
  -- the ideal of `α / (γ N(y))` is supported on `S`
  have e : toPrincipalIdeal (𝓞 K) K (α / (γ * Units.map (Algebra.norm K : L →* K) y)) =
      idealNormHom K L 𝔄₂ * 𝔰 := by
    rw [map_div, div_eq_iff_eq_mul', ← hα𝔞, ← h𝔞eq, map_mul, map_mul,
      idealNormHom_toPrincipalIdeal]
    simp only [mul_assoc]
  have hβ : toPrincipalIdeal (𝓞 K) K (α / (γ * Units.map (Algebra.norm K : L →* K) y)) ∈
      idealsSupportedOn (S : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [e]
    exact Subgroup.mul_mem _ (idealNormHom_mem_idealsSupportedOn K L h𝔄₂') h𝔰S
  rw [← div_mul_cancel α (γ * Units.map (Algebra.norm K : L →* K) y), ofMul_mul, ofMul_mul]
  exact AddSubgroup.add_mem _
    (AddSubgroup.mem_sup_right (ofMul_mem_comap_sUnits_of_toPrincipalIdeal_mem K L G S hβ))
    (AddSubgroup.mem_sup_left (AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (hW γ hγ))
      (AddSubgroup.mem_sup_left (ofMul_norm_mem_comap_range_actionNorm K L G y))))

/-- **The reciprocity law for cyclic extensions.** For a cyclic extension `L/K` of number
fields there is `c ≥ 1`, divisible by the ramified primes, such that the Artin map is trivial
on the principal ideals of the ray modulo `(c) ∞`. -/
theorem exists_rayPrincipal_le_ker_artinMap_of_forall_mem_zpowers {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    ∃ (c : ℕ) (_ : NeZero c),
      (∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v) ∧
      rayPrincipal (normModulus K c) ≤ (artinMap K L G).ker := by
  obtain ⟨q, S, hq, hSq, hram, hK, hL⟩ := exists_nat_unramified_principalOutside K L G
  letI : Fintype (primesAbove K L G S) := Fintype.ofFinite _
  obtain ⟨J, hJ⟩ := exists_level_le_congruenceSubgroup (K := K) (S := primesAbove K L G S) 0
  haveI : NeZero (q ^ (J + 1)) := ⟨pow_ne_zero _ hq⟩
  -- the primes dividing `c = q^{J+1}` are the primes of `S`
  have hSc : ∀ v : HeightOneSpectrum (𝓞 K),
      ((q ^ (J + 1) : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ v ∈ S := fun v => by
    rw [hSq, Nat.cast_pow]
    exact ⟨fun h => v.isPrime.mem_of_pow_mem _ h,
      fun h => Ideal.pow_mem_of_mem _ h _ (Nat.succ_pos J)⟩
  refine ⟨q ^ (J + 1), inferInstance, fun v hv => hram v fun h => hv ((hSc v).mpr h), ?_⟩
  -- the ray lies in the congruence subgroup and in the positive elements
  have hW : ∀ γ ∈ rayGroup (normModulus K (q ^ (J + 1))), Additive.ofMul γ ∈
      (congruenceSubgroup K (primesAbove K L G S) 0).comap (baseIncl K L) ⊓
        positiveAtRamified K L := fun γ hγ =>
    ⟨AddSubgroup.mem_comap.mpr (hJ γ (level_anti (Int.ofNat_le.mpr (Nat.le_succ J))
      (algebraMap_sub_one_mem_level_of_mem_rayGroup K L G S (Nat.succ_ne_zero J)
        (fun v hv => (hSq v).mp hv) hγ))),
      ofMul_mem_positiveAtRamified_of_mem_rayGroup K L hγ⟩
  -- the kernel of the Artin symbol outside `S` lies in `U`, and `n` divides the index of `U`
  have hker : (MonoidHom.toAdditive
      ((artinMapOutside K L G S).comp (toPrincipalIdeal (𝓞 K) K))).ker ≤
      (actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔
        (congruenceSubgroup K (primesAbove K L G S) 0).comap (baseIncl K L) ⊓
          positiveAtRamified K L ⊔
        (sUnits L G (primesAbove K L G S)).comap (baseIncl K L) := fun x hx =>
    ofMul_mem_of_artinMapOutside_eq_one K L G hσ S (q ^ (J + 1)) hSc hram hL hW
      (α := Additive.toMul x) (congrArg Additive.toMul (AddMonoidHom.mem_ker.mp hx))
  have hdvd := card_dvd_index_norm_sup_congruence_sup_sUnits
    (invariantDivisorsDescend_primesAbove S hram hK) hσ 0
  have hU := le_ker_of_ker_le_of_card_dvd_index _ hker (by
    rw [show Nat.card (Additive G) = Fintype.card G from Nat.card_eq_fintype_card (α := G)]
    exact hdvd)
  -- the ray lies in `U`
  rintro _ ⟨γ, hγ, rfl⟩
  have h := hU (AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right (hW γ hγ)))
  have hcount : ∀ v ∈ S, count K v ((toPrincipalIdeal (𝓞 K) K γ :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0 := fun v hv =>
    rayPrincipal_le (normModulus K (q ^ (J + 1))) (Subgroup.mem_map_of_mem _ hγ) v
      ((dvd_normModulus_fin_iff K _ v).mpr ((hSc v).mpr hv))
  rw [MonoidHom.mem_ker, ← artinMapOutside_eq_artinMap hcount]
  exact congrArg Additive.toMul (AddMonoidHom.mem_ker.mp h)

end GaloisForLFunctions
