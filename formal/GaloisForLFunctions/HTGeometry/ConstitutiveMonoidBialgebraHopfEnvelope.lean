import Mathlib
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex

/-!
# Monoid bialgebra, Hopf envelope, antipode defect, one-sided representation

The polynomial monoid bialgebra `k[t]` with `Δ(t) = t ⊗ t`, `ε(t) = 1` has no antipode, because an
antipode would make its group-like generator a unit.  Laurent localization repairs this, and the
inclusion is the Hopf envelope.  On the operator side the unilateral shift realizes `t` one-sidedly:
the representation does not extend to the Laurent algebra, and it does exactly after any quotient
that kills the rank-one Toeplitz defect.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped LaurentPolynomial TensorProduct

/-! ## The monoid bialgebra -/

section MonoidBialgebra

variable (k : Type*) [CommRing k]

/-- The monoid bialgebra `B = k[t]`, with `Δ(t) = t ⊗ t` and `ε(t) = 1`. -/
abbrev MonoidBialg : Type _ := AddMonoidAlgebra k ℕ

/-- The group-like generator `t` of the monoid bialgebra. -/
noncomputable def tGen : MonoidBialg k := AddMonoidAlgebra.single (1 : ℕ) (1 : k)

/-- The identification of the monoid bialgebra with the polynomial ring `k[t]`. -/
noncomputable def polyEquivMonoidBialg : Polynomial k ≃ₐ[k] MonoidBialg k :=
  Polynomial.toFinsuppIsoAlg k

@[simp] theorem polyEquivMonoidBialg_X : polyEquivMonoidBialg k Polynomial.X = tGen k := by
  simp [polyEquivMonoidBialg, tGen, Polynomial.toFinsuppIsoAlg]

variable {k}

/-- **Clause 1, equation (1).**  The generator is group-like. -/
theorem isGroupLikeElem_tGen : IsGroupLikeElem k (tGen k) where
  counit_eq_one := by
    rw [tGen, AddMonoidAlgebra.counit_single]
    simp
  comul_eq_tmul_self := by
    rw [tGen, AddMonoidAlgebra.comul_single]
    simp

theorem counit_tGen : Coalgebra.counit (R := k) (tGen k) = 1 :=
  isGroupLikeElem_tGen.counit_eq_one

theorem comul_tGen : Coalgebra.comul (R := k) (tGen k) = tGen k ⊗ₜ[k] tGen k :=
  isGroupLikeElem_tGen.comul_eq_tmul_self

/-- **Clause 2, first step.**  The generator is not invertible. -/
theorem not_isUnit_tGen [Nontrivial k] : ¬ IsUnit (tGen k) := by
  intro h
  have hX : IsUnit (Polynomial.X : Polynomial k) := by
    have h2 := h.map (polyEquivMonoidBialg k).symm.toAlgHom.toRingHom
    have h3 : (polyEquivMonoidBialg k).symm (tGen k) = (Polynomial.X : Polynomial k) := by
      rw [← polyEquivMonoidBialg_X k, AlgEquiv.symm_apply_apply]
    rwa [show ((polyEquivMonoidBialg k).symm.toAlgHom.toRingHom) (tGen k)
      = (polyEquivMonoidBialg k).symm (tGen k) from rfl, h3] at h2
  exact Polynomial.not_isUnit_X hX

/-- **Clause 2.**  The monoid bialgebra has no antipode.  The antipode identity at the group-like
generator reads `S(t)·t = ε(t)·1 = 1`, which would make `t` invertible. -/
theorem no_antipode [Nontrivial k] (S : MonoidBialg k →ₗ[k] MonoidBialg k)
    (hS : S (tGen k) * tGen k = 1) : False := by
  refine not_isUnit_tGen (IsUnit.of_mul_eq_one (S (tGen k)) ?_)
  rw [mul_comm]
  exact hS

/-- In any Hopf algebra a group-like element is invertible; this is the abstract reason the monoid
bialgebra cannot carry one. -/
theorem isUnit_of_isGroupLikeElem {A : Type*} [CommRing A] [HopfAlgebra k A] {a : A}
    (ha : IsGroupLikeElem k a) : IsUnit a := ha.isUnit

end MonoidBialgebra

/-! ## The Hopf envelope -/

section HopfEnvelope

variable (k : Type*) [CommRing k]

/-- The Hopf envelope `H = k[t, t⁻¹]`, equation (2). -/
abbrev HopfEnv : Type _ := LaurentPolynomial k

/-- **Clause 3.**  The Laurent algebra is a Hopf algebra with `S(t) = t⁻¹`. -/
theorem antipode_T_one :
    HopfAlgebra.antipode k (LaurentPolynomial.T 1 : HopfEnv k) = LaurentPolynomial.T (-1) :=
  LaurentPolynomial.antipode_T 1

theorem isUnit_T_one : IsUnit (LaurentPolynomial.T 1 : HopfEnv k) := by
  refine IsUnit.of_mul_eq_one (LaurentPolynomial.T (-1)) ?_
  rw [← LaurentPolynomial.T_add]
  norm_num

/-- The canonical bialgebra map `B → H` of the Hopf envelope. -/
noncomputable def hopfEnvInclusion : MonoidBialg k →ₐc[k] AddMonoidAlgebra k ℤ :=
  AddMonoidAlgebra.mapDomainBialgHom k (Nat.castAddMonoidHom ℤ)

theorem hopfEnvInclusion_tGen :
    hopfEnvInclusion k (tGen k) = AddMonoidAlgebra.single (1 : ℤ) (1 : k) := by
  show AddMonoidAlgebra.mapDomainAlgHom k k (Nat.castAddMonoidHom ℤ)
      (AddMonoidAlgebra.single (1 : ℕ) (1 : k)) = AddMonoidAlgebra.single (1 : ℤ) (1 : k)
  simp

/-- **Clause 5.**  The passage `B ↪ H` is the group completion `ℕ → ℤ`: every additive monoid map
from `ℕ` into a group extends uniquely to `ℤ`. -/
theorem nat_int_group_completion {G : Type*} [AddCommGroup G] (φ : ℕ →+ G) :
    ∃! ψ : ℤ →+ G, ψ.comp (Nat.castAddMonoidHom ℤ) = φ := by
  refine ⟨zmultiplesHom G (φ 1), ?_, ?_⟩
  · refine AddMonoidHom.ext_nat ?_
    show ((1 : ℕ) : ℤ) • φ 1 = φ 1
    simp
  · intro ψ hψ
    refine AddMonoidHom.ext_int ?_
    have h1 := congrArg (fun f : ℕ →+ G => f 1) hψ
    show ψ 1 = ((1 : ℤ)) • φ 1
    simp only [one_smul]
    show ψ (((1 : ℕ) : ℤ)) = φ 1
    exact h1

end HopfEnvelope

/-! ## The one-sided shift representation -/

section ShiftRepresentation

theorem shiftOp_zero : shiftOp 0 = 1 := by
  ext f k
  show shiftFun 0 (f : ℕ → ℂ) k = (f : ℕ → ℂ) k
  rw [shiftFun_of_le (Nat.zero_le k), Nat.sub_zero]

theorem shiftOp_comp (m n : ℕ) : shiftOp m ∘L shiftOp n = shiftOp (m + n) := by
  ext f k
  show shiftFun m (fun j => shiftFun n (f : ℕ → ℂ) j) k = shiftFun (m + n) (f : ℕ → ℂ) k
  rw [shiftFun_shiftFun]

/-- The shift as a monoid homomorphism from the multiplicative copy of `ℕ`. -/
noncomputable def hopfEnvelopeShiftMonoidHom :
    Multiplicative ℕ →* (ToeplitzSpace →L[ℂ] ToeplitzSpace) where
  toFun n := shiftOp (Multiplicative.toAdd n)
  map_one' := shiftOp_zero
  map_mul' m n := by
    show shiftOp (Multiplicative.toAdd m + Multiplicative.toAdd n)
      = shiftOp (Multiplicative.toAdd m) * shiftOp (Multiplicative.toAdd n)
    rw [← shiftOp_comp]
    rfl

/-- **Clause 6, equation (3).**  The one-sided representation `ρ(t) = V` of the monoid
bialgebra. -/
noncomputable def shiftRep : MonoidBialg ℂ →ₐ[ℂ] (ToeplitzSpace →L[ℂ] ToeplitzSpace) :=
  AddMonoidAlgebra.lift ℂ (ToeplitzSpace →L[ℂ] ToeplitzSpace) ℕ hopfEnvelopeShiftMonoidHom

@[simp] theorem shiftRep_tGen : shiftRep (tGen ℂ) = shiftOp 1 := by
  simp [shiftRep, tGen, hopfEnvelopeShiftMonoidHom]

/-- **Clause 6.**  The one-sided representation does not extend to the Hopf envelope: an algebra
map from the Laurent algebra would make the shift invertible, but it is not surjective. -/
theorem shiftRep_not_extends
    (σ : HopfEnv ℂ →ₐ[ℂ] (ToeplitzSpace →L[ℂ] ToeplitzSpace))
    (h : σ (LaurentPolynomial.T 1) = shiftOp 1) : False := by
  have hu : IsUnit (shiftOp 1) := by
    rw [← h]
    exact (isUnit_T_one ℂ).map σ
  exact shiftOp_not_surjective Nat.one_pos
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2

/-- **Clause 8, equation (4).**  The erased operator defect is the rank-one projection onto the
first basis vector. -/
theorem defect_eq_rankOne :
    1 - shiftOp 1 ∘L backOp 1 = defectOp 1 ∧
      (∀ (f : ToeplitzSpace) (j : ℕ), (defectOp 1 f : ℕ → ℂ) j = if j = 0 then (f : ℕ → ℂ) 0
        else 0) ∧
      Module.finrank ℂ (LinearMap.range (defectOp 1).toLinearMap) = 1 := by
  refine ⟨?_, fun f j => ?_, ?_⟩
  · rw [defectOp, ContinuousLinearMap.one_def]
  · rw [defectOp_apply]
    by_cases hj : j = 0
    · rw [if_pos (by omega), if_pos hj, hj]
    · rw [if_neg (by omega), if_neg hj]
  · rw [range_defectOp, finrank_defectSubmodule]

/-- **Clause 7.**  After any unital quotient that kills the Toeplitz defect — in particular the
Calkin quotient, whose kernel contains every finite-rank operator — the image of the shift is a
unit, and the representation extends uniquely to the Hopf envelope. -/
theorem boundary_representation_extends {Q : Type*} [Ring Q] [Algebra ℂ Q]
    (φ : (ToeplitzSpace →L[ℂ] ToeplitzSpace) →ₐ[ℂ] Q) (hφ : φ (defectOp 1) = 0) :
    (φ (backOp 1) * φ (shiftOp 1) = 1 ∧ φ (shiftOp 1) * φ (backOp 1) = 1) ∧
      ∃! σ : HopfEnv ℂ →ₐ[ℂ] Q, σ (LaurentPolynomial.T 1) = φ (shiftOp 1) := by
  have h1 : φ (backOp 1) * φ (shiftOp 1) = 1 := by
    rw [← map_mul]
    show φ (backOp 1 ∘L shiftOp 1) = 1
    rw [backOp_comp_shiftOp, ← ContinuousLinearMap.one_def, map_one]
  have h2 : φ (shiftOp 1) * φ (backOp 1) = 1 := by
    rw [← map_mul]
    show φ (shiftOp 1 ∘L backOp 1) = 1
    have hsplit : shiftOp 1 ∘L backOp 1 = 1 - defectOp 1 := by
      rw [defectOp, ContinuousLinearMap.one_def]
      abel
    rw [hsplit, map_sub, hφ, map_one, sub_zero]
  set u : Qˣ := ⟨φ (shiftOp 1), φ (backOp 1), h2, h1⟩ with hu
  refine ⟨⟨h1, h2⟩, ?_⟩
  refine ⟨AddMonoidAlgebra.lift ℂ Q ℤ ((Units.coeHom Q).comp (zpowersHom Qˣ u)), ?_, ?_⟩
  · show AddMonoidAlgebra.lift ℂ Q ℤ ((Units.coeHom Q).comp (zpowersHom Qˣ u))
      (LaurentPolynomial.T 1) = φ (shiftOp 1)
    rw [LaurentPolynomial.T, AddMonoidAlgebra.lift_single]
    simp [hu]
  · intro σ hσ
    have hone : σ (LaurentPolynomial.T 1) = ((u : Qˣ) : Q) := hσ
    have hmul : ∀ a b : ℤ, σ (LaurentPolynomial.T (a + b))
        = σ (LaurentPolynomial.T a) * σ (LaurentPolynomial.T b) := by
      intro a b
      rw [LaurentPolynomial.T_add, map_mul]
    have hzero : σ (LaurentPolynomial.T 0) = 1 := by
      rw [LaurentPolynomial.T_zero, map_one]
    have hneg : σ (LaurentPolynomial.T (-1)) = ((u⁻¹ : Qˣ) : Q) := by
      have h0 : σ (LaurentPolynomial.T (-1)) * ((u : Qˣ) : Q) = 1 := by
        rw [← hone, ← map_mul, ← LaurentPolynomial.T_add]
        norm_num
      calc σ (LaurentPolynomial.T (-1))
          = σ (LaurentPolynomial.T (-1)) * (((u : Qˣ) : Q) * ((u⁻¹ : Qˣ) : Q)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        _ = σ (LaurentPolynomial.T (-1)) * ((u : Qˣ) : Q) * ((u⁻¹ : Qˣ) : Q) := by
            rw [mul_assoc]
        _ = ((u⁻¹ : Qˣ) : Q) := by rw [h0, one_mul]
    have hT : ∀ m : ℤ, σ (LaurentPolynomial.T m) = ((u ^ m : Qˣ) : Q) := by
      intro m
      refine Int.induction_on m ?_ ?_ ?_
      · simp
      · intro i ih
        rw [hmul, ih, hone, ← Units.val_mul]
        congr 1
        group
      · intro i ih
        rw [show (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) by ring, hmul, ih, hneg, ← Units.val_mul]
        congr 1
        group
    refine (AddMonoidAlgebra.lift ℂ Q ℤ).symm.injective ?_
    rw [Equiv.symm_apply_apply]
    refine MonoidHom.ext fun n => ?_
    show σ (AddMonoidAlgebra.single (Multiplicative.toAdd n) (1 : ℂ))
      = ((u ^ (Multiplicative.toAdd n) : Qˣ) : Q)
    exact hT (Multiplicative.toAdd n)

end ShiftRepresentation

/-! ## Clause 4 — the universal property of the Hopf envelope -/

section Universal

variable {k : Type*} [CommRing k]

/-- An algebra map out of the monoid bialgebra is determined by the image of the generator. -/
theorem algHom_ext_tGen {K : Type*} [Semiring K] [Algebra k K]
    {F G : MonoidBialg k →ₐ[k] K} (h : F (tGen k) = G (tGen k)) : F = G := by
  refine (AddMonoidAlgebra.lift k K ℕ).symm.injective (MonoidHom.ext_mnat ?_)
  show F (AddMonoidAlgebra.single (1 : ℕ) (1 : k)) = G (AddMonoidAlgebra.single (1 : ℕ) (1 : k))
  exact h

/-- An algebra map out of the Laurent algebra is determined by the image of `T 1`. -/
theorem algHom_ext_T {K : Type*} [Semiring K] [Algebra k K]
    {F G : AddMonoidAlgebra k ℤ →ₐ[k] K}
    (h : F (AddMonoidAlgebra.single (1 : ℤ) (1 : k))
      = G (AddMonoidAlgebra.single (1 : ℤ) (1 : k))) : F = G := by
  refine (AddMonoidAlgebra.lift k K ℤ).symm.injective (MonoidHom.ext_mint ?_)
  show F (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = G (AddMonoidAlgebra.single (1 : ℤ) (1 : k))
  exact h

/-- **Clause 4.**  Every algebra map from the monoid bialgebra to a Hopf algebra that sends the
generator to a group-like element factors uniquely through the Hopf envelope; and every basis image
of the extension is again group-like, so the extension is comultiplicative on the basis.  This is
the universal property of `B ↪ H` among maps to Hopf algebras: in a Hopf algebra the image of the
group-like generator is automatically invertible. -/
theorem hopfEnvelope_universal {K : Type*} [CommRing K] [HopfAlgebra k K]
    (f : MonoidBialg k →ₐ[k] K) (hf : IsGroupLikeElem k (f (tGen k))) :
    ∃! g : AddMonoidAlgebra k ℤ →ₐ[k] K,
      g (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = f (tGen k) := by
  classical
  set a : GroupLike k K := ⟨f (tGen k), hf⟩ with ha
  set u : Kˣ := GroupLike.toUnits k a with hu
  have huval : ((u : Kˣ) : K) = f (tGen k) := rfl
  refine ⟨AddMonoidAlgebra.lift k K ℤ ((Units.coeHom K).comp (zpowersHom Kˣ u)), ?_, ?_⟩
  · show (AddMonoidAlgebra.lift k K ℤ ((Units.coeHom K).comp (zpowersHom Kˣ u)))
        (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = f (tGen k)
    rw [AddMonoidAlgebra.lift_single]
    simp [huval]
  · intro g hg
    refine algHom_ext_T ?_
    rw [hg, AddMonoidAlgebra.lift_single]
    simp [huval]

/-- The extension of a group-like generator stays group-like on every basis element, which is what
makes the factorization a map of bialgebras. -/
theorem hopfEnvelope_extension_isGroupLike {K : Type*} [CommRing K] [HopfAlgebra k K]
    (f : MonoidBialg k →ₐ[k] K) (hf : IsGroupLikeElem k (f (tGen k))) (n : ℤ) :
    IsGroupLikeElem k
      (((AddMonoidAlgebra.lift k K ℤ
        ((Units.coeHom K).comp (zpowersHom Kˣ (GroupLike.toUnits k ⟨f (tGen k), hf⟩))))
          (AddMonoidAlgebra.single n (1 : k)))) := by
  set a : GroupLike k K := ⟨f (tGen k), hf⟩ with ha
  have hval : ((AddMonoidAlgebra.lift k K ℤ
      ((Units.coeHom K).comp (zpowersHom Kˣ (GroupLike.toUnits k a))))
        (AddMonoidAlgebra.single n (1 : k)))
      = ((a ^ n : GroupLike k K) : K) := by
    rw [AddMonoidAlgebra.lift_single]
    simp only [one_smul, MonoidHom.coe_comp, Function.comp_apply, zpowersHom_apply,
      Units.coeHom_apply]
    rw [← map_zpow]
    rfl
  rw [hval]
  exact (a ^ n).2

/-- The composite of the extension with the Hopf-envelope inclusion recovers the original map. -/
theorem hopfEnvelope_universal_comp {K : Type*} [CommRing K] [HopfAlgebra k K]
    (f : MonoidBialg k →ₐ[k] K)
    (g : AddMonoidAlgebra k ℤ →ₐ[k] K)
    (hg : g (AddMonoidAlgebra.single (1 : ℤ) (1 : k)) = f (tGen k)) :
    g.comp (AddMonoidAlgebra.mapDomainAlgHom k k (Nat.castAddMonoidHom ℤ)) = f := by
  refine algHom_ext_tGen ?_
  show g (AddMonoidAlgebra.mapDomainAlgHom k k (Nat.castAddMonoidHom ℤ) (tGen k)) = f (tGen k)
  rw [tGen]
  simp only [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rw [show ((Nat.castAddMonoidHom ℤ) 1) = (1 : ℤ) from rfl]
  exact hg

end Universal

end GaloisForLFunctions.HTGeometry
