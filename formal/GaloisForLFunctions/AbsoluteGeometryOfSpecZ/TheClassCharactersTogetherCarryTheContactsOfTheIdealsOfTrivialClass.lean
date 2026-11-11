import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction

/-!
# The class characters together carry the contacts of the ideals of trivial class

Let `K` be a number field and `h` the number of characters of its class group (the ray class
characters of the unit modulus). Summed over these characters the contacts
`Λ_ψ(n) = Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭` keep the powers `𝔭^k` on which every class character is
`1`, each `h` times (`sum_heckeValue_trivialModulus`, `sum_heckeMangoldt_trivialModulus`); these
are the principal ones (`forall_heckeValue_eq_one_iff_isPrincipal`, `classTrivialContact_eq`).

* **The pairing** (`tendsto_ringForm_add_classTrivialContact`). `h` times the jets and the
  counterterm of the ring, with twice the contacts of the ideals of trivial class, tends to
  `2 d₁ d₂ − Σ_ψ Z_ψ(f)`: one pole plane, the zeros of all `L(s, ψ)`.
* **The index** (`exists_le_negIndex_classGram_iff`). The sum of Weil's forms of the class
  characters has `n` negative squares on some family of `n` tests iff the completions of the
  `L(s, ψ)` have together at least `n` distinct zeros to the right of the critical line.

Per unit of the pairing of the ring the pole plane has the weight `1/h`: the square of `K` with
its contacts restricted to the trivial class is the square of an unramified cover of degree `h`
seen on the comb of `K`, and the base enters it with weight one over the degree.
-/

noncomputable section

open Finset Filter Topology MeasureTheory NumberField
open Zeta23
open scoped Classical Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens HTGeometry

/-! ### Orthogonality -/

/-- The characters of a finite abelian group are finitely many. -/
theorem finite_character (G : Type*) [CommGroup G] [Finite G] : Finite (G →* ℂˣ) :=
  inferInstance

/-- **Orthogonality.** The characters of a finite abelian group sum to zero at a nontrivial
element. -/
theorem sum_monoidHom_apply_eq_zero {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) : ∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ) = 0 := by
  obtain ⟨φ₀, hφ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  have hmul : ((φ₀ g : ℂˣ) : ℂ) * ∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ) =
      ∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft φ₀) _ _ fun φ => by
      show ((φ₀ g : ℂˣ) : ℂ) * ((φ g : ℂˣ) : ℂ) = (((φ₀ * φ) g : ℂˣ) : ℂ)
      rw [MonoidHom.mul_apply, Units.val_mul]
  have hne : ((φ₀ g : ℂˣ) : ℂ) ≠ 1 := fun h => hφ₀ (Units.val_eq_one.mp h)
  have h0 : (((φ₀ g : ℂˣ) : ℂ) - 1) * ∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, hmul, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

variable (K : Type*) [Field K] [NumberField K]

/-- The class characters of a number field are finitely many. -/
local instance instFintypeClassCharacter : Fintype (HeckeCharacter (trivialModulus K)) :=
  @Fintype.ofFinite _ (finite_character (RayClassGroup (trivialModulus K)))

theorem mem_idealGroup_trivialModulus {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    idealUnit hI ∈ idealGroup (trivialModulus K) := by
  intro v hv
  exact (v.prime.not_unit (isUnit_of_dvd_one hv)).elim

/-- **Orthogonality of the class characters on an ideal.** -/
theorem sum_heckeValue_trivialModulus {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∑ ψ : HeckeCharacter (trivialModulus K), heckeValue (trivialModulus K) ψ I =
      if ∀ ψ : HeckeCharacter (trivialModulus K), heckeValue (trivialModulus K) ψ I = 1 then
        (Fintype.card (HeckeCharacter (trivialModulus K)) : ℂ) else 0 := by
  have hm := mem_idealGroup_trivialModulus K hI
  have hval : ∀ ψ : HeckeCharacter (trivialModulus K), heckeValue (trivialModulus K) ψ I =
      ((ψ (rayClass (trivialModulus K) ⟨idealUnit hI, hm⟩) : ℂˣ) : ℂ) := fun ψ =>
    heckeValue_of_mem (trivialModulus K) ψ hI hm
  simp only [hval]
  by_cases h1 : rayClass (trivialModulus K) ⟨idealUnit hI, hm⟩ = 1
  · have hone : ∀ ψ : HeckeCharacter (trivialModulus K),
        ((ψ (rayClass (trivialModulus K) ⟨idealUnit hI, hm⟩) : ℂˣ) : ℂ) = 1 := fun ψ => by
      rw [h1, map_one, Units.val_one]
    rw [if_pos hone, Finset.sum_congr rfl fun ψ _ => hone ψ, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  · haveI : NeZero (Monoid.exponent (RayClassGroup (trivialModulus K))) :=
      ⟨@Monoid.exponent_ne_zero_of_finite (RayClassGroup (trivialModulus K)) _ _⟩
    obtain ⟨φ₀, hφ₀⟩ := @CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (RayClassGroup (trivialModulus K)) ℂ _ _ _ _ _ h1
    rw [if_neg fun hall => hφ₀ (Units.val_eq_one.mp (hall φ₀)),
      @sum_monoidHom_apply_eq_zero (RayClassGroup (trivialModulus K)) _ _ _ _ h1]

/-- The contact order of the norm `n` carried by the powers of prime ideals on which every
class character is `1`. -/
def classTrivialContact (n : ℕ) : ℝ :=
  ∑ pk ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n),
    if ∀ ψ : HeckeCharacter (trivialModulus K),
        heckeValue (trivialModulus K) ψ (pk.1 ^ pk.2) = 1 then
      Real.log (Ideal.absNorm pk.1) else 0

/-- **The contacts of the class characters add up to the ideals of trivial class.** -/
theorem sum_heckeMangoldt_trivialModulus (n : ℕ) :
    ∑ ψ : HeckeCharacter (trivialModulus K), heckeMangoldt (trivialModulus K) ψ n =
      ((Fintype.card (HeckeCharacter (trivialModulus K)) * classTrivialContact K n : ℝ) : ℂ) := by
  simp only [heckeMangoldt]
  rw [Finset.sum_comm, classTrivialContact, Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  obtain ⟨h1, -⟩ := Finset.mem_filter.mp hpk
  obtain ⟨-, hP0, -, -⟩ := mem_primePowersLe.mp h1
  have hPk : P ^ k ≠ ⊥ := pow_ne_zero k hP0
  dsimp only
  rw [← Finset.sum_mul]
  simp only [← heckeValue_pow]
  rw [sum_heckeValue_trivialModulus K hPk]
  split_ifs with h
  · rw [Complex.ofReal_mul, Complex.ofReal_natCast]
  · rw [zero_mul, mul_zero, Complex.ofReal_zero]

/-! ### Trivial class is principal -/

/-- For the unit modulus the ray class group injects into the class group: an element of `K`
satisfies no congruence and no sign condition. -/
theorem toClassGroup_trivialModulus_injective :
    Function.Injective (toClassGroup (trivialModulus K)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨γ, rfl⟩ := ker_toClassGroup_le (trivialModulus K) c hc
  haveI h1 : Subsingleton (𝓞 K ⧸ (trivialModulus K).fin) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  haveI h2 : IsEmpty (trivialModulus K).inf := Set.isEmpty_coe_sort.mpr rfl
  exact MonoidHom.mem_ker.mp
    (ker_rayHom_le (trivialModulus K) (MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)))

/-- **An ideal on which every class character is `1` is principal, and conversely.** -/
theorem forall_heckeValue_eq_one_iff_isPrincipal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (∀ ψ : HeckeCharacter (trivialModulus K), heckeValue (trivialModulus K) ψ I = 1) ↔
      I.IsPrincipal := by
  have hm := mem_idealGroup_trivialModulus K hI
  have hval : ∀ ψ : HeckeCharacter (trivialModulus K), heckeValue (trivialModulus K) ψ I =
      ((ψ (rayClass (trivialModulus K) ⟨idealUnit hI, hm⟩) : ℂˣ) : ℂ) := fun ψ =>
    heckeValue_of_mem (trivialModulus K) ψ hI hm
  have hclass : rayClass (trivialModulus K) ⟨idealUnit hI, hm⟩ = 1 ↔ I.IsPrincipal := by
    rw [← (toClassGroup_trivialModulus_injective K).eq_iff, map_one, toClassGroup_rayClass]
    show ClassGroup.mk K (FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩) = 1 ↔ _
    rw [ClassGroup.mk_mk0, ClassGroup.mk0_eq_one_iff]
  rw [← hclass]
  constructor
  · intro hall
    by_contra h1
    haveI : NeZero (Monoid.exponent (RayClassGroup (trivialModulus K))) :=
      ⟨@Monoid.exponent_ne_zero_of_finite (RayClassGroup (trivialModulus K)) _ _⟩
    obtain ⟨φ₀, hφ₀⟩ := @CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (RayClassGroup (trivialModulus K)) ℂ _ _ _ _ _ h1
    exact hφ₀ (Units.val_eq_one.mp ((hval φ₀).symm.trans (hall φ₀)))
  · intro h1 ψ
    rw [hval ψ, h1, map_one, Units.val_one]

/-- **The contacts of the class characters together are those of the principal ideals.** -/
theorem classTrivialContact_eq (n : ℕ) :
    classTrivialContact K n =
      ∑ pk ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n),
        if (pk.1 ^ pk.2).IsPrincipal then Real.log (Ideal.absNorm pk.1) else 0 := by
  rw [classTrivialContact]
  refine Finset.sum_congr rfl fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  obtain ⟨h1, -⟩ := Finset.mem_filter.mp hpk
  obtain ⟨-, hP0, -, -⟩ := mem_primePowersLe.mp h1
  have hPk : P ^ k ≠ ⊥ := pow_ne_zero k hP0
  dsimp only
  rw [if_congr (forall_heckeValue_eq_one_iff_isPrincipal K hPk) rfl rfl]

/-! ### Linearity of the contacts in the weight -/

theorem weightedContact_sum {ι : Type*} (s : Finset ι) (w : ι → ℕ → ℝ) (f : ℝ → ℝ) (L N : ℕ) :
    weightedContact (fun n => ∑ i ∈ s, w i n) f L N = ∑ i ∈ s, weightedContact (w i) f L N := by
  simp only [weightedContact, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem weightedContact_const_mul (c : ℝ) (w : ℕ → ℝ) (f : ℝ → ℝ) (L N : ℕ) :
    weightedContact (fun n => c * w n) f L N = c * weightedContact w f L N := by
  simp only [weightedContact, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring

/-! ### The pairing and the index -/

/-- Only the trivial character has a pole plane. -/
theorem sum_heckePole_re :
    ∑ ψ : HeckeCharacter (trivialModulus K), (heckePole (trivialModulus K) ψ).re = 1 := by
  have h : ∀ ψ : HeckeCharacter (trivialModulus K),
      (heckePole (trivialModulus K) ψ).re = if ψ = 1 then 1 else 0 := fun ψ => by
    rw [heckePole]
    split_ifs
    · exact Complex.one_re
    · exact Complex.zero_re
  simp only [h]
  rw [Finset.sum_ite_eq' Finset.univ (1 : HeckeCharacter (trivialModulus K)) fun _ => (1 : ℝ),
    if_pos (Finset.mem_univ _)]

variable {f : ℝ → ℝ}

/-- **The pairing with the contacts of the ideals of trivial class.** `h` times the jets and the
counterterm of the ring, with twice the contacts of the ideals of trivial class, tends to one
pole plane minus the sums over the zeros of all the `L(s, ψ)`. -/
theorem tendsto_ringForm_add_classTrivialContact (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K₀ : ℕ} (hK : 1 ≤ K₀)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => (Fintype.card (HeckeCharacter (trivialModulus K)) : ℝ) *
        (ringForm K f (3 * K₀) N +
          2 * weightedContact (classTrivialContact K) f (3 * K₀) N)) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        ∑ ψ : HeckeCharacter (trivialModulus K),
          heckeZeroSum (trivialModulus K) ψ (heckeFiniteConductor_trivialModulus K ψ) f)) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset (HeckeCharacter (trivialModulus K)))
    fun ψ _ => tendsto_ringForm_add_classContact K ψ hf hfc hK hsupp
  have hlim : ∑ ψ : HeckeCharacter (trivialModulus K),
        ((heckePole (trivialModulus K) ψ).re *
            (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) -
          heckeZeroSum (trivialModulus K) ψ (heckeFiniteConductor_trivialModulus K ψ) f) =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        ∑ ψ : HeckeCharacter (trivialModulus K),
          heckeZeroSum (trivialModulus K) ψ (heckeFiniteConductor_trivialModulus K ψ) f := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_heckePole_re, one_mul]
  rw [hlim] at hsum
  refine hsum.congr fun N => ?_
  -- the contacts of the characters add up
  have hw : (fun n => ∑ ψ : HeckeCharacter (trivialModulus K),
        (heckeMangoldt (trivialModulus K) ψ n).re) =
      fun n => (Fintype.card (HeckeCharacter (trivialModulus K)) : ℝ) *
        classTrivialContact K n := funext fun n => by
    rw [← Complex.re_sum, sum_heckeMangoldt_trivialModulus, Complex.ofReal_re]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, ← weightedContact_sum, hw, weightedContact_const_mul]
  ring

/-- **The Hodge index of the class characters together.** The sum of Weil's forms of the class
characters has `n` negative squares on some family of `n` tests iff the completions of the
`L(s, ψ)` have together at least `n` distinct zeros to the right of the critical line. -/
theorem exists_le_negIndex_classGram_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (∑ ψ : HeckeCharacter (trivialModulus K),
          ArithmeticCastelnuovoSeveri.zeroGram (classZeros K ψ) f)) ↔
      (n : ℕ∞) ≤ (⋃ ψ : HeckeCharacter (trivialModulus K),
        ArithmeticCastelnuovoSeveri.rightZeros (classZeros K ψ)).encard :=
  exists_le_negIndex_sum_zeroGram_iff (fun ψ => classZeros K ψ) (temperedConfig_classZeros K) n

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
