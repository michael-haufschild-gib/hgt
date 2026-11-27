import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexTeichmullerPlace
import Mathlib.RingTheory.KrullDimension.PID

/-! An integral p-adic coefficient ring reduces at the ambient valuation.
An isomorphism of algebraic closures can make this reduction agree with any
prescribed embedding of the coefficient residue field. -/

noncomputable section

open Polynomial IsLocalRing
open WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.MainNotions.N

namespace GlobalTheory.TeichPlace

private theorem isAlgClosure_of_ringHom {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (f : K →+* Fbar p) : letI := f.toAlgebra; IsAlgClosure K (Fbar p) := by
  letI : Algebra K (Fbar p) := f.toAlgebra
  have hp : (p : K) = 0 := f.injective (by rw [map_natCast, map_zero, CharP.cast_eq_zero (Fbar p) p])
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : IsScalarTower (ZMod p) K (Fbar p) := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (fun g : ZMod p →+* Fbar p => g x)
      (RingHom.ext_zmod (algebraMap (ZMod p) (Fbar p))
        ((algebraMap K (Fbar p)).comp (algebraMap (ZMod p) K)))
  exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ZMod p) K⟩

private theorem exists_ringEquiv_of_isAlgClosure {K L M : Type*}
    [Field K] [Field L] [Field M] (f : K →+* L) (g : K →+* M)
    (hf : letI := f.toAlgebra; IsAlgClosure K L)
    (hg : letI := g.toAlgebra; IsAlgClosure K M) :
    ∃ e : L ≃+* M, ∀ x, e (f x) = g x := by
  letI : Algebra K L := f.toAlgebra
  letI : Algebra K M := g.toAlgebra
  letI : IsAlgClosure K L := hf
  letI : IsAlgClosure K M := hg
  let e := IsAlgClosure.equiv K L M
  exact ⟨e.toRingEquiv, e.commutes⟩

/-- Two embeddings into the algebraic closure of a prime field differ by an automorphism. -/
theorem exists_residue_aut_of_embeddings {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (f g : K →+* Fbar p) : ∃ e : Fbar p ≃+* Fbar p, ∀ x, e (f x) = g x :=
  exists_ringEquiv_of_isAlgClosure f g (isAlgClosure_of_ringHom f) (isAlgClosure_of_ringHom g)

private def padicIntToIntegralClosure (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →+* padicAlgClIntegers p :=
  ((algebraMap ℚ_[p] (PadicAlgCl p)).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict _ fun x => by
    change ((x : ℚ_[p]) : PadicAlgCl p) ∈ padicAlgClIntegers p
    rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe,
      PadicAlgCl.valuation_coe, NNReal.coe_one, PadicAlgCl.norm_extends]
    exact x.2

/-- Choose the ambient residue identification so that reduction agrees with
a prescribed residue embedding of an integral p-adic discrete valuation ring. -/
theorem exists_eq_residue_of_integral_order (p : ℕ) [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Algebra.IsIntegral ℤ_[p] O]
    (j : O →+* PadicAlgCl p)
    (hj : ∀ x : ℤ_[p], j (algebraMap ℤ_[p] O x) =
      algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p]))
    (t : ResidueField O →+* Fbar p) :
    ∃ κ : ResidueField (padicAlgClIntegers p) ≃+* Fbar p,
      ∀ y : O, ∃ h : j y ∈ padicAlgClIntegers p,
        κ (residue (padicAlgClIntegers p) ⟨j y, h⟩) = t (residue O y) := by
  let B := padicAlgClIntegers p
  let b := padicIntToIntegralClosure p
  have hmem (y : O) : j y ∈ B := by
    obtain ⟨f, hf, hy⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[p]) y
    have he : (algebraMap B (PadicAlgCl p)).comp b = j.comp (algebraMap ℤ_[p] O) :=
      RingHom.ext fun x => (hj x).symm
    have hroot : aeval (j y) (f.map b) = 0 := by
      rw [aeval_def, eval₂_map, he, ← hom_eval₂]
      exact (congrArg j hy).trans (map_zero j)
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := PadicAlgCl p)).mp
      (show IsIntegral B (j y) from ⟨f.map b, hf.map _, hroot⟩)
    rw [← hz]
    exact z.2
  let j₀ : O →+* B := j.codRestrict _ hmem
  obtain ⟨κ₀⟩ := nonempty_padicAlgCl_residueField_equiv p
  let s : O →+* Fbar p := κ₀.toRingHom.comp ((residue B).comp j₀)
  have hp : (p : O) ≠ 0 := by
    intro h
    have he := congrArg j h
    rw [map_natCast, map_zero] at he
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he
  have hker : RingHom.ker s = maximalIdeal O := by
    apply IsLocalRing.eq_maximalIdeal
    apply (RingHom.ker_isPrime s).isMaximal_of_ne_bot
    intro he
    have h : (p : O) ∈ RingHom.ker s :=
      RingHom.mem_ker.mpr (by rw [map_natCast, CharP.cast_eq_zero (Fbar p) p])
    rw [he, Ideal.mem_bot] at h
    exact hp h
  let v : ResidueField O →+* Fbar p := Ideal.Quotient.lift _ s
    (fun x hx => RingHom.mem_ker.mp (by rw [hker]; exact hx))
  obtain ⟨e, he⟩ := exists_residue_aut_of_embeddings v t
  refine ⟨κ₀.trans e, fun y => ⟨hmem y, ?_⟩⟩
  exact he (residue O y)

end GlobalTheory.TeichPlace

namespace WindowedLandauTheory.NormalizedTypes

open WindowedLandauTheory.BasicNotions GlobalTheory.TeichPlace

/-- The complex place pulled back through the row's p-adic embedding realizes
its prescribed coefficient residue embedding. -/
theorem exists_redCompat (D : D7) (i : D.nd.Loc) :
    ∃ (B : ValuationSubring ℂ)
      (κ : ResidueField B ≃+* Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i))),
      RedCompat D i B (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.w_l i) κ := by
  let p := D.nd.l i
  letI : Fact p.Prime := D.nd.lPrime i
  let j := (D.naut.iotaQ i).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
  obtain ⟨κ, hκ⟩ := exists_eq_residue_of_integral_order p j (D.naut.iotaQ_alg i) (D.naut.kFbar i)
  let V := padicAlgClIntegers p
  let e := D.naut.iotaQC i
  let B := V.comap e.symm.toRingHom
  let θ := valuationComapEquiv V e.symm
  let τ := fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
  let κ' := (ResidueField.mapEquiv θ).trans (κ.trans τ.symm)
  refine ⟨B, κ', ?_⟩
  intro y
  obtain ⟨hy, hred⟩ := hκ y
  have hyB : e (j y) ∈ B := ValuationSubring.mem_comap.mpr (by
    change e.symm (e (j y)) ∈ V
    rwa [e.symm_apply_apply])
  refine ⟨hyB, ?_⟩
  change τ (τ.symm (κ (ResidueField.mapEquiv θ (residue B ⟨e (j y), hyB⟩)))) = _
  rw [RingEquiv.apply_symm_apply, ResidueField.mapEquiv_apply, ResidueField.map_residue]
  have he : (θ : B →+* V) ⟨e (j y), hyB⟩ = ⟨j y, hy⟩ :=
    Subtype.ext (e.symm_apply_apply _)
  rw [he]
  exact hred

end WindowedLandauTheory.NormalizedTypes
