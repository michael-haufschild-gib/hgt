import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsoluteInertiaRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedRootOrder
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! The tame Kummer character of a uniformizer is surjective. A proper
image would give a nontrivial radical fixed by absolute inertia and hence
lying in an unramified extension. -/

noncomputable section

open NumberField IsDedekindDomain WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

private theorem card_ideal_inertia {E L : Type} [Field E] [Field L] [NumberField E] [NumberField L]
    [Algebra E L] [IsGalois E L] (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Nat.card (Q.inertia (L ≃ₐ[E] L)) = Q.ramificationIdx (𝓞 E) := by
  letI : IsGaloisGroup (L ≃ₐ[E] L) (𝓞 E) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ E L
  letI : (Q.under (𝓞 E)).IsPrime := Ideal.IsPrime.under _ Q
  have h := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[E] L) (Q.under (𝓞 E)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (L ≃ₐ[E] L)] at h

private theorem unramified_of_absolute_inertia_fixes {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (L : IntermediateField E Ω) [FiniteDimensional E L] [IsGalois E L] [NumberField L]
    (M : IntermediateField E L) [NumberField M] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation ((x : L) : Ω) < 1)
    (hfix : ∀ σ ∈ Ine (F := E) A, ∀ y : M, σ ((y : L) : Ω) = ((y : L) : Ω)) :
    (Q.under (𝓞 M)).ramificationIdx (𝓞 E) = 1 := by
  letI : IsGalois M L := IsGalois.tower_top_of_isGalois E M L
  let f : Q.inertia (L ≃ₐ[M] L) → Q.inertia (L ≃ₐ[E] L) := fun τ =>
    ⟨τ.val.restrictScalars E, AddSubgroup.mem_inertia.mpr
      (fun x => AddSubgroup.mem_inertia.mp τ.property x)⟩
  have hinj : Function.Injective f := fun τ υ h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    intro τ
    have hτ (x : 𝓞 L) : A.valuation ((τ.val (x : L) : Ω) - (x : L)) < 1 := by
      have hsm : algebraMap (𝓞 L) L (τ.val • x) = τ.val (x : L) := rfl
      have h := (hQ _).mp (AddSubgroup.mem_inertia.mp τ.2 x)
      change A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (τ.val • x - x))) < 1 at h
      rw [map_sub, map_sub, hsm] at h
      exact h
    obtain ⟨σ, hσ, hs⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ.val hτ
    have hτM (y : M) : τ.val (algebraMap M L y) = algebraMap M L y :=
      Subtype.ext ((hs (y : L)).symm.trans (hfix σ hσ y))
    refine ⟨⟨{ τ.val.toRingEquiv with commutes' := hτM }, ?_⟩, rfl⟩
    exact AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x
  have hc := Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩
  have htower : Q.ramificationIdx (𝓞 E) =
      (Q.under (𝓞 M)).ramificationIdx (𝓞 E) * Q.ramificationIdx (𝓞 M) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 M)) Q
  rw [card_ideal_inertia, card_ideal_inertia, htower] at hc
  exact Nat.eq_of_mul_eq_mul_right (Ideal.ramificationIdx_pos Q (𝓞 M))
    (by rw [one_mul]; exact hc.symm)

private theorem root_order_le_one_of_inertia_fixed {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 E) ∈ v.asIdeal) (hsq : (p : 𝓞 E) ∉ v.asIdeal ^ 2)
    {n : ℕ} {z : Ω} (hzn : z ^ n = (p : Ω))
    (hfix : ∀ σ ∈ Ine (F := E) A, σ z = z) : n ≤ 1 := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : IsGalois E Ω := {}
  letI : FiniteDimensional E (IntermediateField.adjoin E {z}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  let L := IntermediateField.normalClosure E (IntermediateField.adjoin E {z}) Ω
  letI : NumberField L := NumberField.of_module_finite E L
  have hzL : z ∈ L := IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E z)
  let zL : L := ⟨z, hzL⟩
  let M := IntermediateField.adjoin E {zL}
  letI : NumberField M := NumberField.of_module_finite E M
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
    (fun x => mem_of_isIntegral_int A (x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ L Ω)))
  let Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  letI : Q.IsPrime := Ideal.comap_isPrime f _
  have hQ (x : 𝓞 L) : x ∈ Q ↔ A.valuation ((x : L) : Ω) < 1 :=
    Ideal.mem_comap.trans (A.valuation_lt_one_iff (f x))
  have hfixM (σ : G E Ω) (hI : σ ∈ Ine (F := E) A) (x : M) : σ ((x : L) : Ω) = ((x : L) : Ω) := by
    have hle : M.toSubalgebra ≤ AlgHom.equalizer ((σ : Ω →ₐ[E] Ω).comp L.val) L.val := by
      change (IntermediateField.adjoin E {zL}).toSubalgebra ≤ _
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic zL)]
      refine Algebra.adjoin_le ?_
      rintro _ rfl
      exact hfix σ hI
    exact hle x.2
  have he := unramified_of_absolute_inertia_fixes A L M Q hQ hfixM
  have hunder : (Q.under (𝓞 M)).under (𝓞 E) = v.asIdeal := by
    ext x
    rw [Ideal.under_under, Ideal.mem_comap, hQ, ← hA x]
    rfl
  let zM : M := ⟨zL, IntermediateField.mem_adjoin_simple_self E zL⟩
  have hzMn : zM ^ n = (p : M) := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hzn
  exact root_order_le_one_of_unramified v (Q.under (𝓞 M)) hunder he p Fact.out hp hsq hzMn

/-- Absolute inertia realizes every multiplier of a prime-to-characteristic
radical of a uniformizer. -/
theorem exists_inertia_mul_of_radical {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 E) ∈ v.asIdeal) (hsq : (p : 𝓞 E) ∉ v.asIdeal ^ 2)
    {m : ℕ} (hm : 0 < m) (hpm : p.Coprime m) {y μ : Ω}
    (hy : y ^ m = (p : Ω)) (hμ : μ ^ m = 1) :
    ∃ σ ∈ Ine (F := E) A, σ y = μ * y := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  letI : NeZero m := ⟨hm.ne'⟩
  have hp₀ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpv : A.valuation (p : Ω) < 1 := by simpa using (hA (p : 𝓞 E)).mpr hp
  have hy₀ : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact hp₀ hy.symm
  have hpow (σ : G E Ω) : (σ y / y) ^ m = 1 := ratio_pow_eq_one σ hp₀ hy
  let χ : Ine (F := E) A →* rootsOfUnity m Ω :=
    { toFun := fun σ => ⟨Units.mk0 (σ.val y / y) (div_ne_zero (by simpa using hy₀) hy₀), by
        rw [mem_rootsOfUnity]
        ext
        simp [hpow]⟩
      map_one' := by ext; simp [hy₀]
      map_mul' := fun σ τ => by
        ext
        exact ratio_mul A hpv σ.2 hm hpm τ.val hy }
  have hχ (σ : Ine (F := E) A) : (((χ σ : rootsOfUnity m Ω) : Ωˣ) : Ω) = σ.val y / y := rfl
  obtain ⟨⟨a, σ₀, hσ₀⟩, ha⟩ := IsCyclic.exists_generator (α := χ.range)
  let d := orderOf a
  have ham : a ^ m = 1 := by ext; simpa [← hσ₀, hχ] using hpow σ₀.val
  have hdm : d ∣ m := orderOf_dvd_of_pow_eq_one ham
  have hσ (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : (σ y / y) ^ d = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ha ⟨χ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩)
    have h : χ ⟨σ, hσ⟩ ^ d = 1 := by
      have he := congrArg Subtype.val hi
      simp only [Subgroup.coe_zpow] at he
      rw [← he, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show d = orderOf a from rfl, pow_orderOf_eq_one, one_zpow]
    simpa [hχ] using congrArg (fun z : rootsOfUnity m Ω => ((z : Ωˣ) : Ω)) h
  let z := y ^ d
  have hfix (σ : G E Ω) (hI : σ ∈ Ine (F := E) A) : σ z = z := by
    have he : σ y = (σ y / y) * y := (div_mul_cancel₀ _ hy₀).symm
    change σ (y ^ d) = y ^ d
    rw [map_pow, he, mul_pow, hσ σ hI, one_mul]
  let n := m / d
  have hnd : d * n = m := Nat.mul_div_cancel' hdm
  have hzn : z ^ n = (p : Ω) := by rw [show z = y ^ d from rfl, ← pow_mul, hnd, hy]
  have hn := root_order_le_one_of_inertia_fixed A v hA p hp hsq hzn hfix
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (fun he => hm.ne' (by simpa [he] using hnd.symm))
  have hdm' : d = m := by rwa [le_antisymm hn hn₀, mul_one] at hnd
  have hgen : IsPrimitiveRoot (σ₀.val y / y) m := by
    have horder : orderOf (σ₀.val y / y) = m := by
      rw [← hχ, orderOf_units, Subgroup.orderOf_coe, hσ₀, ← show d = orderOf a from rfl, hdm']
    rw [← horder]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨i, -, hi⟩ := hgen.eq_pow_of_pow_eq_one hμ
  refine ⟨σ₀.val ^ i, pow_mem σ₀.2 i, ?_⟩
  exact (div_eq_iff hy₀).mp ((ratio_npow A hpv σ₀.2 hm hpm hy i).trans hi)

end GlobalTheory.TameKummer
