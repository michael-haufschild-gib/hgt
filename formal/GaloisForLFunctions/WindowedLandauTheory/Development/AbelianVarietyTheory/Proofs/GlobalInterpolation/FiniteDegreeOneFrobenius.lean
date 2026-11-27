import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DegreeOnePrimeInRayClass
import GaloisForLFunctions.RHTower.Artin.TheArtinMapOfACyclicExtensionIsTrivialOnARay

/-! Prescribed finite arithmetic Frobenius at primes of rational-prime norm. -/

noncomputable section

open scoped Classical NumberField nonZeroDivisors Pointwise
open NumberField IsDedekindDomain FractionalIdeal
open GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.DegreeOneFrobenius

/-- A prescribed generator occurs as Frobenius at a degree-one prime outside a finite set. -/
theorem exists_cyclic_prime (Z L C : Type) [Field Z] [NumberField Z]
    [Field L] [NumberField L] [Algebra Z L] [CommGroup C] [Fintype C]
    [MulSemiringAction C L] [IsGaloisGroup C Z L]
    (g : C) (hgen : ∀ u : C, u ∈ Subgroup.zpowers g)
    (T : Set (HeightOneSpectrum (𝓞 Z))) (hT : T.Finite) :
    ∃ w : HeightOneSpectrum (𝓞 Z), w ∉ T ∧ (Ideal.absNorm w.asIdeal).Prime ∧
      IsUnramifiedPrime Z L C w ∧ frobeniusElement Z L C w = g := by
  obtain ⟨c, hc, hram, hrec⟩ := exists_rayPrincipal_le_ker_artinMap_of_forall_mem_zpowers Z L C hgen
  letI : NeZero c := hc
  let m := normModulus Z c
  have hur (w : HeightOneSpectrum (𝓞 Z)) (hw : ¬ w.asIdeal ∣ m.fin) := hram w
    (fun h => hw ((dvd_normModulus_fin_iff Z c w).mpr h))
  let e : RayClassGroup m →* C := QuotientGroup.lift _
    ((artinMap Z L C).comp (idealGroup m).subtype)
    (fun I hI => MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hrec (Subgroup.mem_subgroupOf.mp hI))))
  obtain ⟨I, hI, hg⟩ := exists_mem_idealGroup_artinMap_eq Z L C m hur g
  obtain ⟨w, hw, hnorm, hwc, he⟩ := exists_degree_one_prime_in_ray_class m (rayClass m ⟨I, hI⟩) T hT
  have hd : ¬ w.asIdeal ∣ m.fin := by
    intro h
    have hcount := hwc w h
    rw [coe_idealUnit, count_self] at hcount
    exact one_ne_zero hcount
  have hfrob := congrArg e he
  change artinMap Z L C (idealUnit w.ne_bot) = artinMap Z L C I at hfrob
  rw [artinMap_idealUnit_prime, frobeniusOrOne, if_pos (hur w hd), hg] at hfrob
  exact ⟨w, hw, hnorm, hur w hd, hfrob⟩

/-- The distinguished Artin automorphism is arithmetic Frobenius at the chosen prime. -/
theorem isArithFrobAt_frobeniusElement (Z L C : Type)
    [Field Z] [NumberField Z] [Field L] [NumberField L] [Algebra Z L]
    [CommGroup C] [Fintype C] [MulSemiringAction C L] [IsGaloisGroup C Z L]
    (w : HeightOneSpectrum (𝓞 Z)) :
    IsArithFrobAt (𝓞 Z) (frobeniusElement Z L C w) (primeAbove Z L w) :=
  IsArithFrobAt.arithFrobAt (𝓞 Z) C (primeAbove Z L w)

/-- A finite set of primes has finitely many primes above it in a number-field extension. -/
theorem finite_under_preimage {F Z : Type} [Field F] [Field Z]
    [NumberField F] [NumberField Z] [Algebra F Z]
    {T : Set (HeightOneSpectrum (𝓞 F))} (hT : T.Finite) :
    ((fun w : HeightOneSpectrum (𝓞 Z) => w.under (𝓞 F)) ⁻¹' T).Finite := by
  refine hT.preimage' fun v _ => ?_
  letI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 Z)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 Z) => w.asIdeal)
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w hw
  have he : w.under (𝓞 F) = v := hw
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal he).symm⟩⟩

/-- Each automorphism of a finite Galois extension is arithmetic Frobenius
at a prime of rational-prime norm outside any prescribed finite set. -/
theorem exists_arithmeticFrobenius_away (F L : Type) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (σ : (L ≃ₐ[F] L)) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ T ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ P.LiesOver v.asIdeal ∧ IsArithFrobAt (𝓞 F) σ P := by
  let C := Subgroup.zpowers σ
  let E := IntermediateField.fixedField C
  let g : C := ⟨σ, Subgroup.mem_zpowers _⟩
  letI : NumberField E := NumberField.of_module_finite F E
  letI : Fintype C := Fintype.ofFinite C
  letI : CommGroup C := IsCyclic.commGroup
  letI : IsGaloisGroup C E L := IsGaloisGroup.subgroup (L ≃ₐ[F] L) F L C
  have hg (u : C) : u ∈ Subgroup.zpowers g := by
    obtain ⟨n, hn⟩ := u.2
    exact ⟨n, Subtype.ext hn⟩
  obtain ⟨w, hw, hp, -, hf⟩ := exists_cyclic_prime E L C g hg _ (finite_under_preimage hT)
  let v := w.under (𝓞 F)
  let P := primeAbove E L w
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hP : P.under (𝓞 E) = w.asIdeal := (Ideal.over_def P w.asIdeal).symm
  have hPv : P.under (𝓞 F) = v.asIdeal := by
    rw [← Ideal.under_under (A := 𝓞 F) (B := 𝓞 E) P, hP]
    rfl
  have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  have hdeg : w.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.Prime.eq_one_of_pow (hn ▸ hp)
  rw [hdeg, pow_one] at hn
  have hcard : Nat.card (𝓞 F ⧸ P.under (𝓞 F)) = Nat.card (𝓞 E ⧸ P.under (𝓞 E)) := by
    rw [hPv, hP, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, ← Ideal.absNorm_apply]
    exact hn
  refine ⟨v, hw, hn ▸ hp, P, inferInstance, ⟨hPv.symm⟩, ?_⟩
  have h := isArithFrobAt_frobeniusElement E L C w
  rw [hf] at h
  intro x
  change σ • x - x ^ Nat.card (𝓞 F ⧸ P.under (𝓞 F)) ∈ P
  rw [hcard]
  exact h x

end GlobalTheory.DegreeOneFrobenius
