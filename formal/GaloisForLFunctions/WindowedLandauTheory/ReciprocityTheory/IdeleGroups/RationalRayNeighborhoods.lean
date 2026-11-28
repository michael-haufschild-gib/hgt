import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.OpenIdelicCongruences
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayContinuity
import GaloisForLFunctions.RHTower.Artin.RelativeNormsOfRayElementsAreRayElements

/-! Kernels of rational ray class maps are cofinal among the open
subgroups pulled back from the compact idelic class quotient. -/

noncomputable section

open Topology NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions WithZero
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K : Type*} [Field K] [NumberField K]

/-- A rational modulus can realize any prescribed finite list of local congruence depths. -/
theorem exists_rational_ray_levels
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : S → ℕ) :
    ∃ (c : ℕ) (hc : NeZero c),
      letI := hc
      ∀ v : S, n v + 1 ≤ exponent (normModulus K c) v.val := by
  classical
  let I : Ideal (𝓞 K) := ∏ v : S, v.val.asIdeal ^ (n v + 1)
  have hI : I ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.val.ne_bot
  let c := I.absNorm
  letI : NeZero c := ⟨fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)⟩
  refine ⟨c, inferInstance, fun v => ?_⟩
  have hD : I ∣ (normModulus K c).fin :=
    Ideal.dvd_span_singleton.mpr (Ideal.absNorm_mem I)
  have hd : v.val.asIdeal ^ (n v + 1) ∣ I := Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
  have hf : FiniteMultiplicity v.val.asIdeal (normModulus K c).fin :=
    finiteMultiplicity_of_emultiplicity_eq_natCast
      (UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.val.prime.irreducible (normModulus K c).fin_ne_bot)
  exact hf.le_multiplicity_of_pow_dvd (hd.trans hD)

theorem exists_rationalRay_ker_mem_nhds
    (U : Set (CompactIdeleClassQuotient K)) (hU : U ∈ 𝓝 1) :
    ∃ (c : ℕ) (hc : NeZero c),
      letI := hc
      ∀ x ∈ (toRayClass (normModulus K c)).ker, toCompactIdeleClassQuotient K x ∈ U := by
  obtain ⟨S, n, hlevel⟩ := exists_finite_congruences_mem_nhds U hU
  obtain ⟨c, hc, hm⟩ := exists_rational_ray_levels S n
  letI := hc
  let m := normModulus K c
  refine ⟨c, hc, fun x hx => ?_⟩
  let q := toCompactIdeleClassQuotient K
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod m x
  let y : idelesOneMod m := ⟨diagonal K a * x, ha⟩
  have hY : rayClass m (toCoprimeIdeals m y) = 1 := by
    have e := toRayClass_normalized m a⁻¹ y
    change toRayClass m (diagonal K a⁻¹ * (diagonal K a * x)) = _ at e
    rw [map_inv, inv_mul_cancel_left] at e
    exact e.symm.trans (MonoidHom.mem_ker.mp hx)
  obtain ⟨u, hu, he⟩ : toFractionalIdeal y.val ∈ rayPrincipal m :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hY)
  have hu' : diagonal K u ∈ idelesOneMod m := by
    have h := hu
    rw [← rayUnits_eq] at h
    exact h
  let z := y.val * (diagonal K u)⁻¹
  have hz : z ∈ idelesOneMod m := mul_mem y.2 (inv_mem hu')
  have hez : toFractionalIdeal z = 1 := by
    change toFractionalIdeal (y.val * (diagonal K u)⁻¹) = 1
    rw [map_mul, map_inv, toFractionalIdeal_diagonal, he, mul_inv_cancel]
  have hqz : q z = q x := by
    change q ((diagonal K a * x) * (diagonal K u)⁻¹) = q x
    have ha' : q (diagonal K a) = 1 := toCompactIdeleClassQuotient_diagonal K a
    have hu' : q (diagonal K u) = 1 := toCompactIdeleClassQuotient_diagonal K u
    rw [map_mul, map_mul, map_inv, ha', hu', inv_one]
    exact (congrArg (· * (1 : CompactIdeleClassQuotient K)) (one_mul (q x))).trans (mul_one (q x))
  change q x ∈ U
  rw [← hqz]
  refine hlevel z (fun v => by simpa only [Units.val_one, count_one]
    using (toFractionalIdeal_eq_iff.mp hez v)) (mem_positiveAt.mpr ((mem_idelesOneMod m).mp hz).2)
    fun v => ?_
  have hm' : n v + 1 ≤ exponent m v.val := hm v
  have hd := (one_le_exponent_iff m v.val).mp ((Nat.succ_le_succ (Nat.zero_le (n v))).trans hm')
  have h := mem_unitsLevel.mp (((mem_idelesOneMod m).mp hz).1 v.val hd)
  refine mem_unitsLevel.mpr ⟨h.1, h.2.trans ?_⟩
  rw [exp_le_exp]
  have hle : (n v : ℤ) ≤ (exponent m v.val : ℤ) := by exact_mod_cast (Nat.le_succ _).trans (hm v)
  exact neg_le_neg hle

theorem exists_rationalRay_ker_le_open
    (H : Subgroup (CompactIdeleClassQuotient K)) (hH : IsOpen (H : Set (CompactIdeleClassQuotient K))) :
    ∃ (c : ℕ) (hc : NeZero c),
      letI := hc
      (toRayClass (normModulus K c)).ker ≤ H.comap (toCompactIdeleClassQuotient K) := by
  obtain ⟨c, hc, h⟩ := exists_rationalRay_ker_mem_nhds (K := K)
    (H : Set (CompactIdeleClassQuotient K)) (hH.mem_nhds H.one_mem)
  exact ⟨c, hc, h⟩

private theorem toRayClass_archPositive (m : Modulus K) {x : IdeleGroup K}
    (hx : x ∈ archPositive K) : toRayClass m x = 1 := by
  have hf : toFinite K x = 1 := MonoidHom.mem_ker.mp hx.1
  have hp (v : HeightOneSpectrum (𝓞 K)) : finiteProj v x = 1 := by
    apply Units.ext
    exact congrArg (fun z : (FiniteAdeleRing (𝓞 K) K)ˣ =>
      (z : FiniteAdeleRing (𝓞 K) K) v) hf
  have hm : x ∈ idelesOneMod m :=
    (mem_idelesOneMod m).mpr ⟨fun v _ => by rw [hp]; exact one_mem _,
      fun w _ => (mem_positiveAt.mp hx.2) w (Set.mem_univ _)⟩
  have hi : toFractionalIdeal x = 1 := toFractionalIdeal_eq_iff.mpr fun w => by
    rw [ord, ← coe_finiteProj, hp, Units.val_one, map_one, log_one, neg_zero,
      Units.val_one, count_one]
  have h := toRayClass_normalized m 1 ⟨x, hm⟩
  simp only [map_one, one_mul] at h
  rw [h]
  exact (congrArg (rayClass m) (show toCoprimeIdeals m ⟨x, hm⟩ = 1 from Subtype.ext hi)).trans
    (map_one _)

/-- The ray class map on the quotient by principal and positive archimedean ideles. -/
def compactToRayClass (m : Modulus K) : CompactIdeleClassQuotient K →* RayClassGroup m :=
  QuotientGroup.lift _ (toRayClass m) (sup_le
    (fun _ ⟨a, ha⟩ => MonoidHom.mem_ker.mpr (ha ▸ toRayClass_diagonal m a))
    (fun _ hx => MonoidHom.mem_ker.mpr (toRayClass_archPositive m hx)))

theorem continuous_compactToRayClass (m : Modulus K)
    [TopologicalSpace (RayClassGroup m)] [DiscreteTopology (RayClassGroup m)] :
    Continuous (compactToRayClass m) :=
  Continuous.quotient_lift (continuous_toRayClass m) _

theorem compactToRayClass_surjective (m : Modulus K) :
    Function.Surjective (compactToRayClass m) := by
  intro x
  obtain ⟨y, hy⟩ := toRayClass_surjective m x
  exact ⟨toCompactIdeleClassQuotient K y, hy⟩

theorem exists_rational_ray_factor {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (χ : CompactIdeleClassQuotient K →* A) (hc : Continuous χ) :
    ∃ (c : ℕ) (hn : NeZero c),
      letI := hn
      ∃ f : RayClassGroup (normModulus K c) →* A,
        f.comp (compactToRayClass (normModulus K c)) = χ := by
  have hker : IsOpen (χ.ker : Set (CompactIdeleClassQuotient K)) :=
    (isOpen_discrete ({1} : Set A)).preimage hc
  obtain ⟨c, hn, hp⟩ := exists_rationalRay_ker_le_open χ.ker hker
  letI := hn
  let m := normModulus K c
  have hle : (compactToRayClass m).ker ≤ χ.ker := by
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
    exact hp ha
  let hsurj := compactToRayClass_surjective m
  refine ⟨c, hn, (compactToRayClass m).liftOfSurjective hsurj ⟨χ, hle⟩, ?_⟩
  exact (compactToRayClass m).liftOfRightInverse_comp _ (Function.rightInverse_surjInv hsurj) ⟨χ, hle⟩

end GlobalTheory.Reciprocity
