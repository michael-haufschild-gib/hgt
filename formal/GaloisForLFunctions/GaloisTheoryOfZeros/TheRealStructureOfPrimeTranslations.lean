import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentralizerOfPrimeTranslations
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import Mathlib.LinearAlgebra.Complex.Module

/-!
# The real structure of prime translations

The full real-algebra centralizer of the translations at two and three consists
uniquely of translations and translations composed with ordinary conjugation.
Every commuting endomorphism is invertible. Preserving the augmentation ideal
reduces this centralizer to identity and conjugation, so its unique nonidentity
map recovers ordinary conjugation on every actual zero coordinate.

The scalar action is forced by the common invariant character line. Its two
possibilities reduce the classification to the complex-linear centralizer.
Conjugation acts on translating points by conjugating values at conjugate
exponents; the interchange law determines composition in the real centralizer.
The base is the full real field; no arithmetic descent or purity is asserted.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem rawZero_conj_mem (z : ℂ) (hz : z ∈ rawZeroRelationGroup) :
    (starRingEnd ℂ) z ∈ rawZeroRelationGroup := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨q,rfl⟩ := hz
    exact (rawZeroRelationRoot (xiZeroCopyConjEquiv q)).property
  | zero =>
    rw [map_zero]
    exact rawZeroRelationGroup.zero_mem
  | add z w _ _ hz hw =>
    rw [map_add]
    exact rawZeroRelationGroup.add_mem hz hw
  | neg z _ hz =>
    rw [map_neg]
    exact rawZeroRelationGroup.neg_mem hz

/-- Ordinary conjugation preserves the entire original integer zero group. -/
def rawZeroConjugation : rawZeroRelationGroup ≃+ rawZeroRelationGroup where
  toFun z := ⟨(starRingEnd ℂ) (z : ℂ),rawZero_conj_mem z z.property⟩
  invFun z := ⟨(starRingEnd ℂ) (z : ℂ),rawZero_conj_mem z z.property⟩
  left_inv z := Subtype.ext (star_star (z : ℂ))
  right_inv z := Subtype.ext (star_star (z : ℂ))
  map_add' z w := Subtype.ext (map_add (starRingEnd ℂ) (z : ℂ) (w : ℂ))

theorem rawZeroConjugation_coe (z : rawZeroRelationGroup) :
    (rawZeroConjugation z : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

theorem rawZeroConjugation_square (z : rawZeroRelationGroup) :
    rawZeroConjugation (rawZeroConjugation z) = z := rawZeroConjugation.left_inv z

theorem rawZeroConjugation_root (q : XiZeroCopy) :
    rawZeroConjugation (rawZeroRelationRoot q) = rawZeroRelationRoot (xiZeroCopyConjEquiv q) := rfl

/-- Conjugating coefficients and actual exponents defines a real structure on the full zero algebra. -/
def zeroMotiveRealConjugation : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra :=
  (AddMonoidAlgebra.mapAlgHom rawZeroRelationGroup Complex.conjAe.toAlgHom).comp
    (AddMonoidAlgebra.domCongr ℝ ℂ rawZeroConjugation).toAlgHom

/-- The real structure conjugates the coefficient at the conjugate exponent. -/
theorem zeroMotiveRealConjugation_coeff (f : ZeroMotiveAlgebra) (z : rawZeroRelationGroup) :
    (zeroMotiveRealConjugation f).coeff z = (starRingEnd ℂ) (f.coeff (rawZeroConjugation z)) := by
  simp only [zeroMotiveRealConjugation,AlgHom.comp_apply,AddMonoidAlgebra.coeff_mapAlgHom]
  change Complex.conjAe ((AddMonoidAlgebra.domCongr ℝ ℂ rawZeroConjugation f).coeff z) = _
  rw [AddMonoidAlgebra.coeff_domCongr]
  rfl

theorem zeroMotiveRealConjugation_single (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotiveRealConjugation (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (rawZeroConjugation z) ((starRingEnd ℂ) a) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  rw [zeroMotiveRealConjugation_coeff,AddMonoidAlgebra.coeff_single,AddMonoidAlgebra.coeff_single]
  by_cases h : rawZeroConjugation w = z
  · have he : w = rawZeroConjugation z := by
      apply rawZeroConjugation.injective
      rw [rawZeroConjugation_square]
      exact h
    subst w
    rw [rawZeroConjugation_square,Finsupp.single_eq_same,Finsupp.single_eq_same]
  · have he : w ≠ rawZeroConjugation z := by
      intro hw
      exact h (by rw [hw,rawZeroConjugation_square])
    rw [Finsupp.single_eq_of_ne h,Finsupp.single_eq_of_ne he,map_zero]

/-- The real structure is an involution on every regular function. -/
theorem zeroMotiveRealConjugation_square (f : ZeroMotiveAlgebra) :
    zeroMotiveRealConjugation (zeroMotiveRealConjugation f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro z
  rw [zeroMotiveRealConjugation_coeff,zeroMotiveRealConjugation_coeff,rawZeroConjugation_square]
  exact star_star _

private theorem realZeroAlgHom_ext {B : Type*} [Semiring B] [Algebra ℝ B]
    {F G : ZeroMotiveAlgebra →ₐ[ℝ] B}
    (h : ∀ z : rawZeroRelationGroup, ∀ a : ℂ,
      F (AddMonoidAlgebra.single z a) = G (AddMonoidAlgebra.single z a)) : F = G := by
  apply AddMonoidAlgebra.algHom_ext
  · intro z
    exact h z 1
  · apply AlgHom.ext
    intro a
    exact h 0 a

/-- Real-algebra commutation with both prime translations. -/
def RealCommutesWithPrimeTranslations (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) : Prop :=
  (∀ f, F (zeroMotivePrimeTranslation 2 f) = zeroMotivePrimeTranslation 2 (F f)) ∧
  (∀ f, F (zeroMotivePrimeTranslation 3 f) = zeroMotivePrimeTranslation 3 (F f))

private theorem realPrimeCommutant_comp
    (F G : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra)
    (hF : RealCommutesWithPrimeTranslations F) (hG : RealCommutesWithPrimeTranslations G) :
    RealCommutesWithPrimeTranslations (F.comp G) := by
  constructor
  · intro f
    change F (G (zeroMotivePrimeTranslation 2 f)) = _
    rw [hG.1,hF.1]
    rfl
  · intro f
    change F (G (zeroMotivePrimeTranslation 3 f)) = _
    rw [hG.2,hF.2]
    rfl

theorem zeroMotiveTranslation_real_commutes (χ : RawZeroMotivePoint) :
    RealCommutesWithPrimeTranslations ((zeroMotiveTranslation χ).restrictScalars ℝ) := by
  have h : CommutesWithPrimeTranslations (zeroMotiveTranslation χ).toLinearMap := by
    rw [zeroMotiveTranslation_diagonal]
    exact zeroMotiveDiagonal_commutes _
  exact h

private theorem zeroPrimeEigenvalue_zero (p : ℕ) : zeroPrimeEigenvalue p 0 = 1 := by
  change Complex.exp ((Real.log p : ℂ)*0) = 1
  rw [mul_zero,Complex.exp_zero]

private theorem zeroMotivePrimeTranslation_constant (p : ℕ) (a : ℂ) :
    zeroMotivePrimeTranslation p (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a := by
  rw [zeroMotivePrimeTranslation,zeroMotiveTranslation_single,map_zero (rawZeroMotiveFlow (Real.log p))]
  change AddMonoidAlgebra.single (0 : rawZeroRelationGroup) (a*1) = AddMonoidAlgebra.single 0 a
  rw [mul_one]

/-- The action of a real-algebra endomorphism on constants, read at the identity point. -/
def zeroMotiveConstantAction (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) : ℂ →ₐ[ℝ] ℂ :=
  ((zeroMotiveEvaluation 0).restrictScalars ℝ).comp (F.comp AddMonoidAlgebra.singleZeroAlgHom)

/-- Prime commutation forces every scalar to remain a scalar. -/
theorem realPrimeCommutant_constant (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra)
    (hF : RealCommutesWithPrimeTranslations F) (a : ℂ) :
    F (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (zeroMotiveConstantAction F a) := by
  have h₂ : zeroMotivePrimeTranslation 2 (F (AddMonoidAlgebra.single 0 a)) =
      zeroPrimeEigenvalue 2 0 • F (AddMonoidAlgebra.single 0 a) := by
    rw [zeroPrimeEigenvalue_zero,one_smul]
    exact (hF.1 _).symm.trans (congrArg F (zeroMotivePrimeTranslation_constant 2 a))
  have h₃ : zeroMotivePrimeTranslation 3 (F (AddMonoidAlgebra.single 0 a)) =
      zeroPrimeEigenvalue 3 0 • F (AddMonoidAlgebra.single 0 a) := by
    rw [zeroPrimeEigenvalue_zero,one_smul]
    exact (hF.2 _).symm.trans (congrArg F (zeroMotivePrimeTranslation_constant 3 a))
  have he := zeroMotive_joint_eigenvector 0 (F (AddMonoidAlgebra.single 0 a)) h₂ h₃
  have ha : zeroMotiveConstantAction F a = (F (AddMonoidAlgebra.single 0 a)).coeff 0 := by
    change zeroMotiveEvaluation 0 (F (AddMonoidAlgebra.single 0 a)) = _
    conv_lhs => rw [he]
    rw [zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one]
  rw [ha]
  exact he

/-- Only the ordinary and conjugate scalar actions can occur in the real centralizer. -/
theorem realPrimeCommutant_scalar_dichotomy
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) :
    zeroMotiveConstantAction F = AlgHom.id ℝ ℂ ∨
      zeroMotiveConstantAction F = Complex.conjAe.toAlgHom :=
  Complex.real_algHom_eq_id_or_conj (zeroMotiveConstantAction F)

private theorem zeroPrimeEigenvalue_conjugate (p : ℕ) (z : rawZeroRelationGroup) :
    (starRingEnd ℂ) (zeroPrimeEigenvalue p (rawZeroConjugation z)) = zeroPrimeEigenvalue p z := by
  change (starRingEnd ℂ) (Complex.exp ((Real.log p : ℂ)*(starRingEnd ℂ) (z : ℂ))) =
    Complex.exp ((Real.log p : ℂ)*(z : ℂ))
  rw [← Complex.exp_conj,map_mul,Complex.conj_ofReal]
  exact congrArg (fun w : ℂ => Complex.exp ((Real.log p : ℂ)*w)) (star_star (z : ℂ))

/-- Ordinary conjugation commutes with every prime translation. -/
theorem zeroMotiveRealConjugation_prime (p : ℕ) (f : ZeroMotiveAlgebra) :
    zeroMotiveRealConjugation (zeroMotivePrimeTranslation p f) =
      zeroMotivePrimeTranslation p (zeroMotiveRealConjugation f) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro z
  rw [zeroMotiveRealConjugation_coeff,zeroMotivePrimeTranslation_coeff,
    zeroMotivePrimeTranslation_coeff,zeroMotiveRealConjugation_coeff,map_mul,
    zeroPrimeEigenvalue_conjugate]

/-- The ordinary real structure belongs to the two-prime centralizer. -/
theorem zeroMotiveRealConjugation_commutes :
    RealCommutesWithPrimeTranslations zeroMotiveRealConjugation :=
  ⟨zeroMotiveRealConjugation_prime 2,zeroMotiveRealConjugation_prime 3⟩

/-- Every translation fixes the coefficient field pointwise. -/
theorem zeroMotiveTranslation_constant (χ : RawZeroMotivePoint) (a : ℂ) :
    zeroMotiveTranslation χ (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a := by
  rw [zeroMotiveTranslation_single,map_zero χ]
  change AddMonoidAlgebra.single (0 : rawZeroRelationGroup) (a*1) =
    AddMonoidAlgebra.single (0 : rawZeroRelationGroup) a
  rw [mul_one]

/-- The real structure has the ordinary conjugate action on constants. -/
theorem zeroMotiveRealConjugation_constant (a : ℂ) :
    zeroMotiveRealConjugation (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 ((starRingEnd ℂ) a) := by
  rw [zeroMotiveRealConjugation_single,map_zero rawZeroConjugation]

/-- Augmentation is conjugated, rather than fixed as a complex-valued map. -/
theorem zeroMotiveRealConjugation_augmentation (f : ZeroMotiveAlgebra) :
    zeroMotiveEvaluation 0 (zeroMotiveRealConjugation f) =
      (starRingEnd ℂ) (zeroMotiveEvaluation 0 f) := by
  have he : ((zeroMotiveEvaluation 0).restrictScalars ℝ).comp zeroMotiveRealConjugation =
      Complex.conjAe.toAlgHom.comp ((zeroMotiveEvaluation 0).restrictScalars ℝ) := by
    apply realZeroAlgHom_ext
    intro z a
    change zeroMotiveEvaluation 0 (zeroMotiveRealConjugation (AddMonoidAlgebra.single z a)) =
      (starRingEnd ℂ) (zeroMotiveEvaluation 0 (AddMonoidAlgebra.single z a))
    rw [zeroMotiveRealConjugation_single,zeroMotiveEvaluation_single,
      zeroMotiveEvaluation_single,zero_mul,zero_mul,Complex.exp_zero,mul_one,mul_one]
  exact DFunLike.congr_fun he f

private theorem realPrimeCommutant_complex (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra)
    (hF : RealCommutesWithPrimeTranslations F)
    (hc : ∀ a : ℂ, F (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a) :
    ∃ χ : RawZeroMotivePoint, F = (zeroMotiveTranslation χ).restrictScalars ℝ := by
  let G : ZeroMotiveAlgebra →ₐ[ℂ] ZeroMotiveAlgebra := {
    F.toRingHom with
    commutes' := fun a => hc a }
  have hG : CommutesWithPrimeTranslations G.toLinearMap := hF
  obtain ⟨χ,he,_⟩ := (primeTranslation_algebra_centralizer G).mp hG
  refine ⟨χ,?_⟩
  apply AlgHom.ext
  intro f
  exact DFunLike.congr_fun he f

/-- The full real-algebra centralizer consists of translations and translated conjugation. -/
theorem primeTranslation_real_algebra_centralizer
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) :
    RealCommutesWithPrimeTranslations F ↔
      ∃ χ : RawZeroMotivePoint,
        F = (zeroMotiveTranslation χ).restrictScalars ℝ ∨
        F = ((zeroMotiveTranslation χ).restrictScalars ℝ).comp zeroMotiveRealConjugation := by
  constructor
  · intro hF
    rcases realPrimeCommutant_scalar_dichotomy F with hs | hs
    · have hc (a : ℂ) : F (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a := by
        have he := realPrimeCommutant_constant F hF a
        rw [hs] at he
        exact he
      obtain ⟨χ,hχ⟩ := realPrimeCommutant_complex F hF hc
      exact ⟨χ,Or.inl hχ⟩
    · let H := F.comp zeroMotiveRealConjugation
      have hH : RealCommutesWithPrimeTranslations H :=
        realPrimeCommutant_comp F zeroMotiveRealConjugation hF zeroMotiveRealConjugation_commutes
      have hc (a : ℂ) : H (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a := by
        change F (zeroMotiveRealConjugation (AddMonoidAlgebra.single 0 a)) = _
        rw [zeroMotiveRealConjugation_constant,realPrimeCommutant_constant F hF,hs]
        change AddMonoidAlgebra.single (0 : rawZeroRelationGroup)
          ((starRingEnd ℂ) ((starRingEnd ℂ) a)) = AddMonoidAlgebra.single 0 a
        exact congrArg (AddMonoidAlgebra.single (0 : rawZeroRelationGroup)) (star_star a)
      obtain ⟨χ,hχ⟩ := realPrimeCommutant_complex H hH hc
      refine ⟨χ,Or.inr ?_⟩
      calc
        F = H.comp zeroMotiveRealConjugation := by
          apply AlgHom.ext
          intro f
          change F f = F (zeroMotiveRealConjugation (zeroMotiveRealConjugation f))
          rw [zeroMotiveRealConjugation_square]
        _ = ((zeroMotiveTranslation χ).restrictScalars ℝ).comp zeroMotiveRealConjugation := by
          rw [hχ]
  · rintro ⟨χ,h | h⟩
    · rw [h]
      exact zeroMotiveTranslation_real_commutes χ
    · rw [h]
      exact realPrimeCommutant_comp _ _ (zeroMotiveTranslation_real_commutes χ)
        zeroMotiveRealConjugation_commutes

private theorem realTranslation_injective : Function.Injective
    (fun χ : RawZeroMotivePoint => (zeroMotiveTranslation χ).restrictScalars ℝ) := by
  intro χ ψ h
  apply zeroMotiveTranslation_injective
  apply AlgHom.ext
  intro f
  exact DFunLike.congr_fun h f

/-- Ordinary and conjugate translations are distinguished by their action on the constant `i`. -/
theorem zeroMotiveRealTranslation_disjoint (χ ψ : RawZeroMotivePoint) :
    (zeroMotiveTranslation χ).restrictScalars ℝ ≠
      ((zeroMotiveTranslation ψ).restrictScalars ℝ).comp zeroMotiveRealConjugation := by
  intro h
  have he := congrArg (fun F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra =>
    (F (AddMonoidAlgebra.single (0 : rawZeroRelationGroup) I)).coeff 0) h
  change (zeroMotiveTranslation χ (AddMonoidAlgebra.single 0 I)).coeff 0 =
    (zeroMotiveTranslation ψ (zeroMotiveRealConjugation (AddMonoidAlgebra.single 0 I))).coeff 0 at he
  rw [zeroMotiveTranslation_constant,zeroMotiveRealConjugation_constant,
    zeroMotiveTranslation_constant,AddMonoidAlgebra.coeff_single,AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same,Finsupp.single_eq_same] at he
  have him := congrArg Complex.im he
  norm_num [Complex.conj_I] at him

/-- A translation with an optional ordinary real conjugation. -/
def zeroMotiveRealAffine (χ : RawZeroMotivePoint) (b : Bool) :
    ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra :=
  if b then ((zeroMotiveTranslation χ).restrictScalars ℝ).comp zeroMotiveRealConjugation
  else (zeroMotiveTranslation χ).restrictScalars ℝ

/-- Both the translating point and the conjugation choice are uniquely determined. -/
theorem zeroMotiveRealAffine_injective : Function.Injective
    (fun d : RawZeroMotivePoint × Bool => zeroMotiveRealAffine d.1 d.2) := by
  rintro ⟨χ,b⟩ ⟨ψ,c⟩ h
  cases b <;> cases c
  · change (zeroMotiveTranslation χ).restrictScalars ℝ =
      (zeroMotiveTranslation ψ).restrictScalars ℝ at h
    exact Prod.ext (realTranslation_injective h) rfl
  · exact False.elim (zeroMotiveRealTranslation_disjoint χ ψ h)
  · exact False.elim (zeroMotiveRealTranslation_disjoint ψ χ h.symm)
  · have hc : χ = ψ := by
      apply realTranslation_injective
      apply AlgHom.ext
      intro f
      have he := DFunLike.congr_fun h (zeroMotiveRealConjugation f)
      change zeroMotiveTranslation χ (zeroMotiveRealConjugation (zeroMotiveRealConjugation f)) =
        zeroMotiveTranslation ψ (zeroMotiveRealConjugation (zeroMotiveRealConjugation f)) at he
      change zeroMotiveTranslation χ f = zeroMotiveTranslation ψ f
      rw [zeroMotiveRealConjugation_square] at he
      exact he
    exact Prod.ext hc rfl

/-- The real centralizer has unique translation and conjugation coordinates. -/
theorem primeTranslation_real_centralizer_unique
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) :
    RealCommutesWithPrimeTranslations F ↔
      ∃! d : RawZeroMotivePoint × Bool, F = zeroMotiveRealAffine d.1 d.2 := by
  constructor
  · intro hF
    obtain ⟨χ,hχ⟩ := (primeTranslation_real_algebra_centralizer F).mp hF
    obtain ⟨d,hd⟩ : ∃ d : RawZeroMotivePoint × Bool, F = zeroMotiveRealAffine d.1 d.2 := by
      rcases hχ with h | h
      · exact ⟨(χ,false),h⟩
      · exact ⟨(χ,true),h⟩
    refine ⟨d,hd,?_⟩
    intro e he
    exact zeroMotiveRealAffine_injective (he.symm.trans hd)
  · rintro ⟨⟨χ,b⟩,rfl,_⟩
    cases b
    · exact zeroMotiveTranslation_real_commutes χ
    · exact realPrimeCommutant_comp _ _ (zeroMotiveTranslation_real_commutes χ)
        zeroMotiveRealConjugation_commutes

/-- The real structure is invertible on the full coordinate algebra. -/
theorem zeroMotiveRealConjugation_bijective : Function.Bijective zeroMotiveRealConjugation := by
  constructor
  · intro f g h
    exact (zeroMotiveRealConjugation_square f).symm.trans
      ((congrArg zeroMotiveRealConjugation h).trans (zeroMotiveRealConjugation_square g))
  · intro f
    exact ⟨zeroMotiveRealConjugation f,zeroMotiveRealConjugation_square f⟩

/-- Real-algebra endomorphisms commuting with both prime translations are automatically automorphisms. -/
theorem primeTranslation_real_endomorphism_bijective
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra)
    (hF : RealCommutesWithPrimeTranslations F) : Function.Bijective F := by
  obtain ⟨χ,h | h⟩ := (primeTranslation_real_algebra_centralizer F).mp hF
  · rw [h]
    exact zeroMotiveTranslation_bijective χ
  · rw [h]
    exact (zeroMotiveTranslation_bijective χ).comp zeroMotiveRealConjugation_bijective

/-- Preserving the identity point means preserving the augmentation ideal over the real base. -/
def PreservesZeroMotiveIdentity (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) : Prop :=
  ∀ f, zeroMotiveEvaluation 0 f = 0 → zeroMotiveEvaluation 0 (F f) = 0

/-- Conjugation preserves the augmentation ideal even though it conjugates scalar values. -/
theorem zeroMotiveRealConjugation_preserves_identity :
    PreservesZeroMotiveIdentity zeroMotiveRealConjugation := by
  intro f hf
  rw [zeroMotiveRealConjugation_augmentation,hf,map_zero]

/-- A translation preserves the identity point exactly when its translating point is trivial. -/
theorem zeroMotiveTranslation_preserves_identity_iff (χ : RawZeroMotivePoint) :
    PreservesZeroMotiveIdentity ((zeroMotiveTranslation χ).restrictScalars ℝ) ↔ χ = 0 := by
  constructor
  · intro h
    apply AddMonoidHom.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    change ((χ z).toMul : ℂ) = 1
    have hzero : zeroMotiveEvaluation 0 (AddMonoidAlgebra.single z 1-1) = 0 := by
      rw [map_sub,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,one_mul,map_one,sub_self]
    have he := h (AddMonoidAlgebra.single z 1-1) hzero
    change zeroMotiveEvaluation 0 (zeroMotiveTranslation χ (AddMonoidAlgebra.single z 1-1)) = 0 at he
    rw [map_sub,zeroMotiveTranslation_single,map_one,map_sub,zeroMotiveEvaluation_single,
      map_one,zero_mul,Complex.exp_zero,mul_one,one_mul] at he
    exact sub_eq_zero.mp he
  · rintro rfl
    rw [zeroMotiveTranslation_zero]
    intro f hf
    exact hf

/-- The pointed real-algebra centralizer consists exactly of identity and ordinary conjugation. -/
theorem primeTranslation_real_pointed_centralizer
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) :
    (RealCommutesWithPrimeTranslations F ∧ PreservesZeroMotiveIdentity F) ↔
      F = AlgHom.id ℝ ZeroMotiveAlgebra ∨ F = zeroMotiveRealConjugation := by
  constructor
  · rintro ⟨hF,hpoint⟩
    obtain ⟨χ,h | h⟩ := (primeTranslation_real_algebra_centralizer F).mp hF
    · rw [h] at hpoint ⊢
      have hχ := (zeroMotiveTranslation_preserves_identity_iff χ).mp hpoint
      rw [hχ,zeroMotiveTranslation_zero]
      left
      rfl
    · rw [h] at hpoint ⊢
      have htrans : PreservesZeroMotiveIdentity ((zeroMotiveTranslation χ).restrictScalars ℝ) := by
        intro f hf
        have hconj := zeroMotiveRealConjugation_preserves_identity f hf
        have he := hpoint (zeroMotiveRealConjugation f) hconj
        change zeroMotiveEvaluation 0
          (zeroMotiveTranslation χ (zeroMotiveRealConjugation (zeroMotiveRealConjugation f))) = 0 at he
        rw [zeroMotiveRealConjugation_square] at he
        exact he
      have hχ := (zeroMotiveTranslation_preserves_identity_iff χ).mp htrans
      rw [hχ,zeroMotiveTranslation_zero]
      right
      apply AlgHom.ext
      intro f
      rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨fun _ => rfl,fun _ => rfl⟩,fun _ h => h⟩
    · exact ⟨zeroMotiveRealConjugation_commutes,zeroMotiveRealConjugation_preserves_identity⟩

/-- Ordinary conjugation remains nontrivial because it reverses the constant `i`. -/
theorem zeroMotiveRealConjugation_ne_id :
    zeroMotiveRealConjugation ≠ AlgHom.id ℝ ZeroMotiveAlgebra := by
  intro h
  apply zeroMotiveRealTranslation_disjoint 0 0
  rw [zeroMotiveTranslation_zero,h]
  apply AlgHom.ext
  intro f
  rfl

/-- Prime commutation and the identity ideal characterize conjugation as the unique nonidentity real symmetry. -/
theorem zeroMotiveRealConjugation_unique
    (F : ZeroMotiveAlgebra →ₐ[ℝ] ZeroMotiveAlgebra) :
    (RealCommutesWithPrimeTranslations F ∧ PreservesZeroMotiveIdentity F ∧
      F ≠ AlgHom.id ℝ ZeroMotiveAlgebra) ↔ F = zeroMotiveRealConjugation := by
  constructor
  · rintro ⟨hF,hpoint,hne⟩
    exact ((primeTranslation_real_pointed_centralizer F).mp ⟨hF,hpoint⟩).resolve_left hne
  · rintro rfl
    exact ⟨zeroMotiveRealConjugation_commutes,zeroMotiveRealConjugation_preserves_identity,
      zeroMotiveRealConjugation_ne_id⟩

private def conjugateUnitAddHom : Additive ℂˣ →+ Additive ℂˣ where
  toFun a := Additive.ofMul (Units.map (starRingEnd ℂ).toMonoidHom a.toMul)
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_one (starRingEnd ℂ)
  map_add' a b := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_mul (starRingEnd ℂ) (a.toMul : ℂ) (b.toMul : ℂ)

/-- Conjugation acts on motive points by conjugating values at conjugate exponents. -/
def zeroMotivePointRealConjugation : RawZeroMotivePoint →+ RawZeroMotivePoint where
  toFun χ := conjugateUnitAddHom.comp (χ.comp rawZeroConjugation.toAddMonoidHom)
  map_zero' := by
    apply AddMonoidHom.ext
    intro z
    exact map_zero conjugateUnitAddHom
  map_add' χ ψ := by
    apply AddMonoidHom.ext
    intro z
    exact map_add conjugateUnitAddHom (χ (rawZeroConjugation z)) (ψ (rawZeroConjugation z))

theorem zeroMotivePointRealConjugation_value (χ : RawZeroMotivePoint) (z : rawZeroRelationGroup) :
    (((zeroMotivePointRealConjugation χ) z).toMul : ℂ) =
      (starRingEnd ℂ) ((χ (rawZeroConjugation z)).toMul : ℂ) := rfl

/-- The induced conjugation on the full complex point group is involutive. -/
theorem zeroMotivePointRealConjugation_square (χ : RawZeroMotivePoint) :
    zeroMotivePointRealConjugation (zeroMotivePointRealConjugation χ) = χ := by
  apply AddMonoidHom.ext
  intro z
  apply Additive.toMul.injective
  apply Units.ext
  rw [zeroMotivePointRealConjugation_value,zeroMotivePointRealConjugation_value,
    rawZeroConjugation_square]
  exact star_star _

/-- This interchange law determines composition in the real prime-translation centralizer. -/
theorem zeroMotiveRealConjugation_translation (χ : RawZeroMotivePoint) :
    zeroMotiveRealConjugation.comp ((zeroMotiveTranslation χ).restrictScalars ℝ) =
      ((zeroMotiveTranslation (zeroMotivePointRealConjugation χ)).restrictScalars ℝ).comp
        zeroMotiveRealConjugation := by
  apply AlgHom.ext
  intro f
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro z
  change (zeroMotiveRealConjugation (zeroMotiveTranslation χ f)).coeff z =
    (zeroMotiveTranslation (zeroMotivePointRealConjugation χ) (zeroMotiveRealConjugation f)).coeff z
  rw [zeroMotiveRealConjugation_coeff,zeroMotiveTranslation_coeff,zeroMotiveTranslation_coeff,
    zeroMotiveRealConjugation_coeff,zeroMotivePointRealConjugation_value,map_mul]

/-- The distinguished real structure acts by ordinary conjugation on every actual zero coordinate. -/
theorem zeroMotiveRealConjugation_zeroCoordinate (q : XiZeroCopy) :
    zeroMotiveRealConjugation (AddMonoidAlgebra.single (rawZeroRelationRoot q) 1) =
      AddMonoidAlgebra.single (rawZeroRelationRoot (xiZeroCopyConjEquiv q)) 1 := by
  rw [zeroMotiveRealConjugation_single,rawZeroConjugation_root,map_one (starRingEnd ℂ)]

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawZeroConjugation_root
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_square

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realPrimeCommutant_constant
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realPrimeCommutant_scalar_dichotomy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_prime
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_augmentation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_real_algebra_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealAffine_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_real_centralizer_unique
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_real_endomorphism_bijective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveTranslation_preserves_identity_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_real_pointed_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_ne_id
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_unique
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotivePointRealConjugation_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_translation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRealConjugation_zeroCoordinate
