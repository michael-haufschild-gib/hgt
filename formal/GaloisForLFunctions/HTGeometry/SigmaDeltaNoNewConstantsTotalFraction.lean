import GaloisForLFunctions.HTGeometry.FractionRingDifference
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraTower
import GaloisForLFunctions.HTGeometry.KolchinNullstellensatzDiffFG
import GaloisForLFunctions.HTGeometry.SigmaDeltaNoNewConstantsFieldExtension

/-!
# No new constants in the total fraction field

This is Hardouin--Singer Corollary 6.15 for a domain.  Given a fixed fraction `c`, adjoin its full
differential jet tower to the original finitely generated ring.  Any nonzero stable ideal in that
ring meets the original domain after clearing one denominator, so simplicity contracts from the
original ring.  Proposition 6.14 then applies to the enlarged finitely generated domain.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

universe u

variable {C K R : Type u}
  [Field C] [Algebra ℚ C] [Differential C] [IsDifferentiallyClosed C]
  [Field K] [CharZero K] [Algebra C K] [Differential K] [DifferentialAlgebra C K]
  [CommRing R] [IsDomain R] [Algebra K R] [Differential R] [DifferentialAlgebra K R]
  [Algebra C R] [IsScalarTower C K R]

/-- **Hardouin--Singer Corollary 6.15, domain form.**  The fraction field of a differentially
finitely generated `σ`-`δ`-simple domain has no new difference constants. -/
theorem exists_eq_algebraMap_fractionRing_of_isSigmaDeltaSimple_of_diffFG
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hσδ : CommutesDeriv σR)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσC : ∀ c : C, σK (algebraMap C K c) = algebraMap C K c)
    (hfix : ∀ a : K, σK a = a → ∃ c : C, algebraMap C K c = a)
    (hsimple : IsSigmaDeltaSimple σR)
    {k : ℕ} (y : Fin k → R)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := K) (L := R) y))
    {c : FractionRing R}
    (hc : fractionRingEquiv σR c = c) :
    ∃ d : C, c = algebraMap C (FractionRing R) d := by
  classical
  letI : Algebra ℚ R := ((algebraMap K R).comp (algebraMap ℚ K)).toAlgebra
  letI : Differential (FractionRing R) := fractionRingDifferential R
  letI : DifferentialAlgebra R (FractionRing R) :=
    ⟨fractionRingDifferential_algebraMap R⟩
  letI : DifferentialAlgebra K (FractionRing R) :=
    differentialAlgebra_trans (C := K) (K := R) (E := FractionRing R)
  letI : DifferentialAlgebra C (FractionRing R) :=
    differentialAlgebra_trans (C := C) (K := K) (E := FractionRing R)
  let z : Fin (k + 1) → FractionRing R :=
    Fin.lastCases c (fun i => algebraMap R (FractionRing R) (y i))
  let A := differentialGeneratorSubalgebra (A := K) z
  have hzmem (i : Fin (k + 1)) : z i ∈ A := by
    rw [← differentialJet_zero (z i)]
    exact Algebra.subset_adjoin ⟨(i, 0), rfl⟩
  have hRmem (r : R) : algebraMap R (FractionRing R) r ∈ A := by
    obtain ⟨Q, rfl⟩ := hy r
    change algebraMap R (FractionRing R)
      (differentialPolynomialEvalOver (K := K) y Q) ∈
        differentialGeneratorSubalgebra (A := K) z
    rw [differentialGeneratorSubalgebra_eq_range]
    let Q' : DifferentialPolynomial (Fin (k + 1)) K :=
      differentialRename Fin.castSucc Q
    refine ⟨Q', ?_⟩
    have hrename : differentialPolynomialEvalOver (K := K) z Q' =
        differentialPolynomialEvalOver (K := K)
          (fun i => algebraMap R (FractionRing R) (y i)) Q := by
      rw [show Q' = differentialRename Fin.castSucc Q from rfl,
        differentialPolynomialEvalOver_differentialRename]
      have hz : (fun i : Fin k => z i.castSucc) =
          (fun i => algebraMap R (FractionRing R) (y i)) := by
        funext i
        simp [z]
      rw [hz]
    have hmap := map_differentialPolynomialEvalOver
      (F := K) (L := R) (M := FractionRing R)
      (algebraMap R (FractionRing R))
      (fun r => (fractionRingDifferential_algebraMap R r).symm)
      (fun a => by
        exact IsScalarTower.algebraMap_apply K R (FractionRing R) a)
      y Q
    exact hrename.trans hmap.symm
  let σF : FractionRing R ≃+* FractionRing R := fractionRingEquiv σR
  have hσFδ : CommutesDeriv σF := fractionRingEquiv_commutesDeriv σR hσδ
  have hσFbase (a : K) : σF (algebraMap K (FractionRing R) a) =
      algebraMap K (FractionRing R) (σK a) := by
    rw [IsScalarTower.algebraMap_apply K R (FractionRing R),
      fractionRingEquiv_algebraMap, hcompat,
      IsScalarTower.algebraMap_apply K R (FractionRing R)]
  have hσFsymmδ : CommutesDeriv σF.symm := by
    intro w
    apply σF.injective
    rw [σF.apply_symm_apply, hσFδ, σF.apply_symm_apply]
  have hσFsymmR (r : R) :
      σF.symm (algebraMap R (FractionRing R) r) =
        algebraMap R (FractionRing R) (σR.symm r) := by
    apply σF.injective
    rw [σF.apply_symm_apply, fractionRingEquiv_algebraMap, σR.apply_symm_apply]
  have hσFsymmbase (a : K) : σF.symm (algebraMap K (FractionRing R) a) =
      algebraMap K (FractionRing R) (σK.symm a) := by
    apply σF.injective
    rw [σF.apply_symm_apply, hσFbase, σK.apply_symm_apply]
  have hσgen (i : Fin (k + 1)) : σF (z i) ∈ A := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [z, σF, hc] using hzmem (Fin.last k)
    · rw [show z j.castSucc = algebraMap R (FractionRing R) (y j) by simp [z],
        fractionRingEquiv_algebraMap]
      exact hRmem (σR (y j))
  have hσsymmgen (i : Fin (k + 1)) : σF.symm (z i) ∈ A := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hcsymm : σF.symm c = c := by
        apply σF.injective
        rw [σF.apply_symm_apply, hc]
      simpa [z, hcsymm] using hzmem (Fin.last k)
    · rw [show z j.castSucc = algebraMap R (FractionRing R) (y j) by simp [z],
        hσFsymmR]
      exact hRmem (σR.symm (y j))
  have mapsA (ρ : FractionRing R ≃+* FractionRing R)
      (hρδ : CommutesDeriv ρ)
      (hρbase : ∀ a : K, ρ (algebraMap K (FractionRing R) a) ∈ A)
      (hρgen : ∀ i, ρ (z i) ∈ A) :
      ∀ w ∈ A, ρ w ∈ A := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem w hw =>
        obtain ⟨⟨i, n⟩, rfl⟩ := hw
        change ρ (differentialJet n (z i)) ∈ A
        induction n with
        | zero => simpa using hρgen i
        | succ n ih =>
            rw [differentialJet_succ, hρδ]
            exact differentialGeneratorSubalgebra_deriv_stable z _ ih
    | algebraMap a => exact hρbase a
    | add a b _ _ ha hb => rw [map_add]; exact A.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact A.mul_mem ha hb
  have hσAmap : ∀ w ∈ A, σF w ∈ A :=
    mapsA σF hσFδ (fun a => by
      rw [hσFbase]
      exact A.algebraMap_mem (σK a)) hσgen
  have hσAsymmMap : ∀ w ∈ A, σF.symm w ∈ A :=
    mapsA σF.symm hσFsymmδ
      (fun a => hσFsymmbase a ▸ A.algebraMap_mem (σK.symm a)) hσsymmgen
  let σA : A ≃+* A :=
    { toFun := fun w : A =>
        ⟨σF (w : FractionRing R), hσAmap (w : FractionRing R) w.2⟩
      invFun := fun w : A =>
        ⟨σF.symm (w : FractionRing R), hσAsymmMap (w : FractionRing R) w.2⟩
      left_inv := fun w =>
        Subtype.ext (σF.symm_apply_apply (w : FractionRing R))
      right_inv := fun w =>
        Subtype.ext (σF.apply_symm_apply (w : FractionRing R))
      map_mul' := fun a b =>
        Subtype.ext (map_mul σF (a : FractionRing R) (b : FractionRing R))
      map_add' := fun a b =>
        Subtype.ext (map_add σF (a : FractionRing R) (b : FractionRing R)) }
  have hσAδ : CommutesDeriv σA := by
    intro w
    apply Subtype.ext
    exact hσFδ w
  have hσAbase (a : K) : σA (algebraMap K A a) = algebraMap K A (σK a) := by
    apply Subtype.ext
    exact hσFbase a
  let f : R →+* A :=
    { (algebraMap R (FractionRing R)).codRestrict A hRmem with }
  have hfσ (r : R) : σA (f r) = f (σR r) := by
    apply Subtype.ext
    exact fractionRingEquiv_algebraMap σR r
  have hfδ (r : R) : f (Differential.deriv r) = Differential.deriv (f r) := by
    apply Subtype.ext
    exact (fractionRingDifferential_algebraMap R r).symm
  have hAsimple : IsSigmaDeltaSimple σA := by
    intro J hJ
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    have hJnonzero : ∃ u ∈ J, u ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hJbot
      apply le_antisymm
      · intro u hu
        exact Ideal.mem_bot.mpr (hnone u hu)
      · exact bot_le
    obtain ⟨u, huJ, hu0⟩ := hJnonzero
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R (u : FractionRing R)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap R (FractionRing R) b ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)).not.mpr hb0
    have ha0 : a ≠ 0 := by
      intro ha
      apply hu0
      apply Subtype.ext
      rw [ha, map_zero, zero_div] at hab
      exact hab.symm
    have hfaJ : f a ∈ J := by
      have hmul : f b * u ∈ J := J.mul_mem_left (f b) huJ
      have heq : f b * u = f a := by
        apply Subtype.ext
        change algebraMap R (FractionRing R) b * (u : FractionRing R) =
          algebraMap R (FractionRing R) a
        rw [← hab]
        field_simp
      rwa [heq] at hmul
    let I : Ideal R := Ideal.comap f J
    have hIstable : IsSigmaDeltaIdeal σR I := by
      refine ⟨?_, ?_⟩
      · intro r hr
        change f (σR r) ∈ J
        rw [← hfσ]
        exact hJ.1 (f r) hr
      · intro r hr
        change f (Differential.deriv r) ∈ J
        rw [hfδ]
        exact hJ.2 (f r) hr
    have hIneBot : I ≠ ⊥ := by
      intro hIbot
      have haI : a ∈ I := hfaJ
      rw [hIbot] at haI
      exact ha0 (Ideal.mem_bot.mp haI)
    have hItop : I = ⊤ := (hsimple I hIstable).resolve_left hIneBot
    have honeJ : f 1 ∈ J := by
      change (1 : R) ∈ I
      rw [hItop]
      trivial
    exact Or.inr (Ideal.eq_top_of_isUnit_mem J honeJ (by simp))
  have hyA : Function.Surjective
      (differentialPolynomialEvalOver (K := K)
        (fun i => differentialGeneratorIn (A := K) z i)) :=
    differentialPolynomialEvalOver_generatorIn_surjective z
  have hσAc (w : C) : σK (algebraMap C K w) = algebraMap C K w := hσC w
  let cA : A := differentialGeneratorIn (A := K) z (Fin.last k)
  have hcA : σA cA = cA := by
    apply Subtype.ext
    simpa [cA, z, σA, σF] using hc
  obtain ⟨d, hd⟩ :=
    exists_eq_algebraMap_of_isSigmaDeltaSimple_of_diffFG_fieldExtension
      σK σA hσAδ hσAbase hσAc hfix hAsimple
      (fun i => differentialGeneratorIn (A := K) z i) hyA hcA
  refine ⟨d, ?_⟩
  have hdval := congrArg Subtype.val hd
  simpa [cA, z, IsScalarTower.algebraMap_apply C K (FractionRing R)] using hdval

end

end GaloisForLFunctions.HTGeometry
