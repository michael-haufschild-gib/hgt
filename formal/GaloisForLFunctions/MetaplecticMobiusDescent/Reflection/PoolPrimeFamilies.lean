/-
Pool prime families adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.ThreeBlockPhases
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.HybridRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Fourier.PositiveLogProfiles

/-!
# Pool prime families

Prime families from prime pools, reflected exponents and slot indices; residual parts are
admissible; source frozen phases and the original reflected source identity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
theorem admissible_primeIndex_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P : PrimeIndex K, P.val) = K := by
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hK.1).mp hK.2.1
  have hv : (primeSupport K).val = UniqueFactorizationMonoid.normalizedFactors K := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = ∏ P ∈ primeSupport K, P := Finset.prod_coe_sort _ _
    _ = (primeSupport K).val.prod := (Finset.prod_val _).symm
    _ = K := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hK.1

theorem idealRowHom_cube_eq_quadratic (K : Ideal Eis) (hK : Admissible K) (z : Eis) :
    idealRowHom z K ^ 3 = canonicalQuadraticRowOfIdeal K z := by
  conv_lhs => rw [←admissible_primeIndex_product K hK,map_prod,←Finset.prod_pow]
  rw [canonicalQuadraticRowOfIdeal_eq_prime_product K ((admissible_iff_native K).mp hK)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime z P.val (admissiblePrimeGood K hK P),
    ←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),
    (complexSexticChar_powers P.val (admissiblePrimeGood K hK P)).2.1]


end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss
open NormalizedReflection CanonicalRowCompletion
noncomputable section
noncomputable local instance bracketField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance bracketFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem marked_bracket_cube (P : Ideal Eis) [P.IsMaximal]
    (hg : lambda ∉ P) (n b : Eis) :
    bracket (complexSexticChar P hg) 0 (Ideal.Quotient.mk P (n*b^3)) =
      (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ *
      (idealRowHom n P)⁻¹^2 * (if IsCoprime P (Ideal.span {b}) then 1 else 0) := by
  have h6 : (complexSexticChar P hg (Ideal.Quotient.mk P b))^6 =
      if b∈P then 0 else 1 := by
    have h := idealRowHom_prime_sixth_mask b P hg
    rw [idealRowHom_prime _ P hg,map_pow,map_pow] at h
    simpa only [prime_coprime_span_iff,ite_not] using h
  have h6' : (complexSexticChar P hg (Ideal.Quotient.mk P b))^6 = 0 ∨
      (complexSexticChar P hg (Ideal.Quotient.mk P b))^6 = 1 := by
    rw [h6]; split_ifs <;> simp
  let ψ : Eis →* ℂ := (complexSexticChar P hg).toMonoidHom.comp (Ideal.Quotient.mk P).toMonoidHom
  have he := InverseMoment.inverse_square_cube_mask ψ n b h6'
  change ((complexSexticChar P hg) (Ideal.Quotient.mk P (n*b^3)))⁻¹^2 =
    ((complexSexticChar P hg) (Ideal.Quotient.mk P n))⁻¹^2 *
      ((complexSexticChar P hg) (Ideal.Quotient.mk P b))^6 at he
  simp only [bracket,show (0:ℕ) ≠ 4 by decide,↓reduceIte,
    MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),inv_pow]
  simp only [inv_pow] at he
  rw [he,rootCard_eq_sqrt_absNorm,idealRowHom_prime n P hg,h6,
    prime_coprime_span_iff]
  by_cases hb : b ∈ P <;> simp [hb]

theorem marked_bracket_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (n b : Eis) :
    (∏ i, bracket (complexSexticChar (P i) (hg i)) 0 (Ideal.Quotient.mk (P i) (n*b^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (idealRowHom n (∏ i, P i))⁻¹^2 *
      (if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0) := by
  simp_rw [marked_bracket_cube]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  have hn : (∏ i, (Real.sqrt (Ideal.absNorm (P i) : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ := by
    rw [map_prod,Nat.cast_prod,Real.sqrt_prod,Complex.ofReal_prod,Finset.prod_inv_distrib]
    intro i hi
    positivity
  have hc : (∏ i, (idealRowHom n (P i))⁻¹^2) = (idealRowHom n (∏ i, P i))⁻¹^2 := by
    rw [map_prod,Finset.prod_pow,Finset.prod_inv_distrib]
  have hm : (∏ i, if IsCoprime (P i) (Ideal.span {b}) then (1:ℂ) else 0) =
      if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0 := by
    classical
    by_cases h : ∀ i, IsCoprime (P i) (Ideal.span {b})
    · simp [h,IsCoprime.prod_left (fun i _ => h i)]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hp : ¬ IsCoprime (∏ i, P i) (Ideal.span {b}) := by
        intro hp
        exact hi (hp.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem P (Finset.mem_univ i)))
      rw [if_neg hp]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [hn,hc,hm]

theorem marked_bracket_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (n b : Ideal Eis) (hb : primaryIdealGenerator b ≠ 0) :
    (∏ i, bracket (complexSexticChar (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  rw [marked_bracket_product,InverseMoment.inverseCubicKernel_eq_inverse_square,
    (primaryIdealGenerator_spec b hb).1]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
theorem residual_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (R : Finset ι) (hR : Admissible (∏ i ∈ R, P i))
    (n b : Ideal Eis) :
    (∏ i ∈ R, bracket (complexSexticChar (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))) =
      canonicalQuadraticRowOfIdeal (∏ i ∈ R, P i) (primaryIdealGenerator (n*b)) := by
  have hl (i : ι) : bracket (complexSexticChar (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3)) =
      idealRowHom (primaryIdealGenerator (n*b)) (P i)^3 := by
    rw [bracket_one_eq_quadratic,primaryIdealGenerator_mul,idealRowHom_prime _ (P i) (hg i)]
    rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),
      (complexSexticChar_powers (P i) (hg i)).2.1]
    simp only [map_mul,map_pow,complexQuadraticChar_cube]

  simp_rw [hl]
  rw [Finset.prod_pow,← map_prod,idealRowHom_cube_eq_quadratic _ hR]

theorem marked_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (n b : Ideal Eis) (hb : primaryIdealGenerator b ≠ 0) :
    (∏ i ∈ S, bracket (complexSexticChar (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  have he := marked_bracket_hybrid (fun i : S => P i.val) (fun i => hg i.val) n b hb
  have hl : (∏ i : S, bracket (complexSexticChar (P i.val) (hg i.val)) 0
      (Ideal.Quotient.mk (P i.val) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))) =
      ∏ i ∈ S, bracket (complexSexticChar (P i) (hg i)) 0
        (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3)) := by
    exact Finset.prod_coe_sort S (fun i => bracket (complexSexticChar (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3)))
  rw [hl] at he
  simpa only [Finset.prod_coe_sort] using he

theorem full_branch_sum_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hSj : ∀ i ∈ S, j i = 0)
    (hR : Admissible (∏ i ∈ R, P i)) (n b : Ideal Eis) (hb : primaryIdealGenerator b ≠ 0) :
    (∑ e : ι → Fin 3, reflectedBranch P hg j e (primaryIdealGenerator n) (primaryIdealGenerator b)) =
      (∏ i ∈ F, bracket (complexSexticChar (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))) *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      canonicalQuadraticRowOfIdeal (∏ i ∈ R, P i) (primaryIdealGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  trans ∏ i, bracket (complexSexticChar (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))
  · exact (prod_bracket_eq_full_branches P hg j (primaryIdealGenerator n) (primaryIdealGenerator b)).symm
  let v := fun i => bracket (complexSexticChar (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryIdealGenerator n*(primaryIdealGenerator b)^3))
  have hr : (∏ i ∈ R, v i) = canonicalQuadraticRowOfIdeal (∏ i ∈ R, P i) (primaryIdealGenerator (n*b)) := by
    rw [← residual_bracket_finset P hg R hR n b]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hRj i hi]
  have hs : (∏ i ∈ S, v i) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
    rw [← marked_bracket_finset P hg S n b hb]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hSj i hi]
  have hv : (∏ i, v i) = (∏ i ∈ R, v i)*(∏ i ∈ S, v i)*(∏ i ∈ F, v i) := by
    rw [← Finset.prod_union hRS,← Finset.prod_union hF,hu]
  change (∏ i, v i) = _
  rw [hv,hr,hs]
  ring

end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss NormalizedReflection
open InverseMoment
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance coefficientFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def sourceRowPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (R F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ R, p i)

def sourceSlotPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  markedWithFrozen hp hg c S F * ramifiedBlock hg (fun _ => 0) S
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ S, p i)

def sourceFrozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  star D.fixedFactor * frozenCore hp hg c j F * ramifiedBlock hg j F
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

def sourceColumn [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b *
  ∏ i ∈ F, bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryIdealGenerator n*(primaryIdealGenerator b)^3))

theorem mixed_coefficient_hybrid [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryIdealGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * cuspBadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg (markedActiveExponent S j) R F u m * sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m *
      sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m) *
      sourceColumn D s hc hg (markedActiveExponent S j) F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      canonicalQuadraticRowOfIdeal (∏ i ∈ R, Ideal.span {p i}) (primaryIdealGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hrj : ∀ i ∈ R, markedActiveExponent S j i = 1 := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hRS hi hs
    simp only [markedActiveExponent,hn,ite_false,hRj i hi]
  have hsj : ∀ i ∈ S, markedActiveExponent S j i = 0 := by
    intro i hi
    simp only [markedActiveExponent,hi,ite_true]
  have hmask : IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro k hk
    exact hcop (fun h => Finset.disjoint_left.mp hRS hi (h ▸ hk))
  rw [mixed_model_coefficient,modelRowPhase_three_blocks D s hp hg hcop hprimary R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj,
    frozenPhase_split D hp hg (markedActiveExponent S j) R S F hRS hF hu,← Finset.mul_sum,
    full_branch_sum_hybrid (fun i => Ideal.span {p i}) hg R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj hR n b hb,if_pos hmask,mul_one]
  unfold sourceRowPhase sourceSlotPhase sourceFrozenPhase sourceColumn
  ring

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss NormalizedReflection
open InverseMoment
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance independentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem ramifiedBlock_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖ramifiedBlock hg j S u m‖ = 1 := by
  unfold ramifiedBlock
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact unitArgumentFactor_norm _ _ _ (unit_ramified_quotient_ne_zero _ (hg i) u m)

theorem sourceRowPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (R F : Finset ι) (hd : Disjoint R F) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s hp hg j R F u m‖ ≤ 1 := by
  rw [sourceRowPhase,norm_mul,norm_mul,residualWithFrozen_norm D hp hg hchar hcop R F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

theorem sourceSlotPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    ‖sourceSlotPhase s hp hg j S F u m‖ ≤ 1 := by
  rw [sourceSlotPhase,norm_mul,norm_mul,markedWithFrozen_norm D hp hg hchar hcop S F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

omit [Fintype ι] in
theorem frozenArgument_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) : frozenArgument hg j F = frozenArgument hg j' F := by
  unfold frozenArgument
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem frozenCore_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis)
    (j j' : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i = j' i) :
    frozenCore hp hg c j F = frozenCore hp hg c j' F := by
  unfold frozenCore
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem ramifiedBlock_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock hg j F u m = ramifiedBlock hg j' F u m := by
  unfold ramifiedBlock
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

theorem marked_phases_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (R S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg (markedActiveExponent S j) R F u m = sourceRowPhase s hp hg j R F u m ∧
    sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m = sourceSlotPhase s hp hg j S F u m ∧
    sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m = sourceFrozenPhase D s hp hg j F u m := by
  have hj : ∀ i ∈ F, markedActiveExponent S j i = j i := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
    simp only [markedActiveExponent,hn,ite_false]
  simp only [sourceRowPhase,sourceSlotPhase,sourceFrozenPhase,
    frozenArgument_congr hg _ _ F hj,frozenCore_congr hp hg c _ _ F hj,
    ramifiedBlock_congr hg _ _ F hj]
  simp

theorem marked_sourceColumn_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg (markedActiveExponent S j) F u m n b =
      sourceColumn D s hc hg j F u m n b := by
  unfold sourceColumn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
  simp only [markedActiveExponent,hn,ite_false]

theorem mixed_coefficient_hybrid_original_exponents [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryIdealGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * cuspBadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      sourceColumn D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      canonicalQuadraticRowOfIdeal (∏ i ∈ R, Ideal.span {p i}) (primaryIdealGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hd : Disjoint S F := hF.mono_left Finset.subset_union_right
  have he := mixed_coefficient_hybrid D s hp hc hg hcop hprimary R S F hRS hF hu j hRj hR u m n b hb
  obtain ⟨hr,hs,hf⟩ := marked_phases_eq D s hp hg j R S F hd u m
  rw [hr,hs,hf,marked_sourceColumn_eq D s hc hg j S F hd u m n b] at he
  exact he

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Eis}
noncomputable local instance transportFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] [Fintype κ] in
theorem residualWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) :
    residualWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c R F =
      residualWithFrozen hp hg c (R.image f) (F.image f) := by
  unfold residualWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf R i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem markedWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) :
    markedWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c S F =
      markedWithFrozen hp hg c (S.image f) (F.image f) := by
  unfold markedWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf S i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem ramifiedBlock_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S : Finset κ) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock (fun i => hg (f i)) (fun i => j (f i)) S u m =
      ramifiedBlock hg j (S.image f) u m := by
  unfold ramifiedBlock
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem frozenArgument_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenArgument (fun i => hg (f i)) (fun i => j (f i)) F =
      frozenArgument hg j (F.image f) := by
  unfold frozenArgument
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceRowPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) R F u m =
      sourceRowPhase s hp hg j (R.image f) (F.image f) u m := by
  unfold sourceRowPhase
  rw [residualWithFrozen_transport hp hg c f hf R F,
    ramifiedBlock_transport hg (fun _ => 1) f hf R,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceSlotPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) S F u m =
      sourceSlotPhase s hp hg j (S.image f) (F.image f) u m := by
  unfold sourceSlotPhase
  rw [markedWithFrozen_transport hp hg c f hf S F,
    ramifiedBlock_transport hg (fun _ => 0) f hf S,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein
noncomputable section

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

theorem sourceRowPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg j (R.image f) (F.image f) u m =
      sourceRowPhase s hq hqg j' (R.image g) (F.image g) u m := by
  rw [← sourceRowPhase_transport s hp hg j f hf R F u m,
    ← sourceRowPhase_transport s hq hqg j' g hg' R F u m]
  exact sourceRowPhase_congr_functions s _ _ _ _ _ _ R F u m (funext he) (funext hj)

theorem sourceSlotPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s hp hg j (S.image f) (F.image f) u m =
      sourceSlotPhase s hq hqg j' (S.image g) (F.image g) u m := by
  rw [← sourceSlotPhase_transport s hp hg j f hf S F u m,
    ← sourceSlotPhase_transport s hq hqg j' g hg' S F u m]
  exact sourceSlotPhase_congr_functions s _ _ _ _ _ _ S F u m (funext he) (funext hj)

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss NormalizedReflection
noncomputable section
noncomputable local instance sectorIndependentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

lemma frozenCore_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (c : Eis) (j j' : κ → ℕ) (F : Finset κ) (he : p=q) (hj : j=j') :
    frozenCore hp hg c j F = frozenCore hq hqg c j' F := by
  subst q; subst j'; rfl

lemma ramifiedBlock_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    ramifiedBlock hg j F u m = ramifiedBlock hqg j' F u m := by
  subst q; subst j'; rfl

def frozenColumnProduct {κ : Type*} [Fintype κ]
    {p : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) : ℂ :=
  ∏ i ∈ F, bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryIdealGenerator n*(primaryIdealGenerator b)^3))

theorem frozenColumnProduct_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) (n b : Ideal Eis) :
    frozenColumnProduct (fun i => hg (f i)) (fun i => j (f i)) F n b =
      frozenColumnProduct hg j (F.image f) n b := by
  unfold frozenColumnProduct
  rw [Finset.prod_image hf.injOn]

lemma frozenColumnProduct_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) (he : p=q) (hj : j=j') :
    frozenColumnProduct hg j F n b = frozenColumnProduct hqg j' F n b := by
  subst q; subst j'; rfl

theorem sourceFrozenPhase_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (hN : (9:Eis)*c ∣ N) (hr : lambda^2 ∣ (∏ i, p i)-1) (hr₀ : lambda^2 ∣ (∏ i, q i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (hmatrix : ∀ i j, N ∣ D.matrix (fun _ => 1) i j-D₀.matrix (fun _ => 1) i j)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s hp hg j (F.image f) u m =
      sourceFrozenPhase D₀ s hq hqg j' (F.image g) u m := by
  unfold sourceFrozenPhase
  rw [controlled_fixedFactor_eq D D₀ hN hr hr₀ hbase (hmatrix 0 0) (hmatrix 0 1),
    ← frozenCore_transport hp hg c j f hf F,← frozenCore_transport hq hqg c j' g hg' F,
    ← ramifiedBlock_transport hg j f hf F,← ramifiedBlock_transport hqg j' g hg' F,
    frozenCore_congr_functions _ _ _ _ c _ _ F (funext he) (funext hj),
    ramifiedBlock_congr_functions _ _ _ _ F _ _ (funext he) (funext hj)]

theorem sourceColumn_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hqg : ∀ i, lambda ∉ Ideal.span {q i})
    (hbad : traceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, q i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1-D₀.matrix (fun _ => 1) 1 1)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg j (F.image f) u m n b =
      sourceColumn D₀ s hc hqg j' (F.image g) u m n b := by
  unfold sourceColumn
  rw [controlled_static_array_eq D D₀ hc s hbad hr hd u m n b]
  congr 1
  change frozenColumnProduct hg j (F.image f) n b = frozenColumnProduct hqg j' (F.image g) n b
  rw [← frozenColumnProduct_transport hg j f hf F,← frozenColumnProduct_transport hqg j' g hg' F]
  exact frozenColumnProduct_congr_functions _ _ _ _ F n b (funext he) (funext hj)

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss
noncomputable section

theorem exists_common_reflected_coefficients {α Q κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, lambda ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (γ : Q → Eisˣ → ℕ → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x u m, sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
        γ (sector x) u m) ∧
      ∀ x u m n b, sourceColumn (D x) s hc (hg x) (j x) (F.image (f x)) u m n b =
        β (sector x) u m n b := by
  have hbad : traceLambda^3*c ∣ N := by
    apply (show traceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨traceLambda,?_⟩
    rw [← traceLambda_pow_four]
    ring
  let G := fun x => sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x))
  let B := fun x => sourceColumn (D x) s hc (hg x) (j x) (F.image (f x))
  have hG : G.FactorsThrough sector := by
    intro x y hxy
    funext u m
    exact sourceFrozenPhase_sector_independent (D x) (D y) s (hp x) (hg x) (hp y) (hg y)
      hN (hprimary x) (hprimary y) hbase (hmatrix x y hxy) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m
  have hB : B.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact sourceColumn_sector_independent (D x) (D y) s hc (hg x) (hg y) hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m n b
  obtain ⟨γ,hγ⟩ := (Function.factorsThrough_iff G).mp hG
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff B).mp hB
  refine ⟨γ,β,?_,?_⟩
  · intro x u m
    exact congrFun (congrFun (congrFun hγ x) u) m
  · intro x u m n b
    exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, lambda ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, lambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedProduct : Eis) (r P : α → Eis)
    (hprod : ∀ x, (∏ i, p x i) = fixedProduct*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧ (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧ (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
          γ (separateSector N (r x) (P x)) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (hg x) (j x) (F.image (f x)) u m n b =
          β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N fixedProduct (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_common_reflected_coefficients p N a c mode E s hp hc hg hN hprimary hbase
    j f hf hfixed hjfixed F sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
theorem canonical_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then lambda^2 ∣ a-1 else lambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, (G x).ideal (f x i)=(G y).ideal (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (G x).generator_ne_zero (G x).generator_good
          (j x) (F.image (f x)) u m =
          γ (separateSector N (primaryIdealGenerator (row x)) (primaryIdealGenerator (slot x))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (G x).generator_good (j x) (F.image (f x)) u m n b =
          β (separateSector N (primaryIdealGenerator (row x)) (primaryIdealGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryIdealGenerator fixedIdeal*primaryIdealGenerator (row x)*primaryIdealGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryIdealGenerator_mul,primaryIdealGenerator_mul]
  obtain ⟨E,_,_,_,_,γ,β,hγ,hβ⟩ := exists_separate_common_reflected_coefficients
    (fun x => (G x).generator) N a c mode D s (fun x => (G x).generator_ne_zero) hc
    (fun x => (G x).generator_good) hN (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    j f hf (fun x y i => congrArg primaryIdealPrime (hfixed x y i)) hjfixed F
    (primaryIdealGenerator fixedIdeal) (fun x => primaryIdealGenerator (row x)) (fun x => primaryIdealGenerator (slot x)) hproduct
  exact ⟨E,γ,β,hγ,hβ⟩

end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section

namespace PrimeFamily
variable {ι κ : Type*}

def sum (G : PrimeFamily ι) (H : PrimeFamily κ) : PrimeFamily (ι ⊕ κ) where
  ideal := Sum.elim G.ideal H.ideal
  maximal i := by cases i with | inl i => exact G.maximal i | inr i => exact H.maximal i
  good i := by cases i with | inl i => exact G.good i | inr i => exact H.good i

lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))

def residual (K : Ideal Eis) (hK : Admissible K) : PrimeFamily (PrimeIndex K) where
  ideal := fun P => P.val
  maximal _P := inferInstance
  good := admissiblePrimeGood K hK

lemma residual_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P, (residual K hK).ideal P) = K := admissible_primeIndex_product K hK

lemma residual_dvd (K : Ideal Eis) (hK : Admissible K) (P : PrimeIndex K) : P.val ∣ K :=
  Ideal.dvd_iff_le.mpr (primeIndex_le K hK.1 P)

lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)

def reflected {φ σ : Type*} (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) : PrimeFamily (φ ⊕ (PrimeIndex K ⊕ σ)) := F.sum ((residual K hK).sum S)

lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring

lemma reflected_pairwise {φ σ : Type*} [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hKS : IsCoprime K (∏ i, S.ideal i))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hFS : ∀ f i, IsCoprime (F.ideal f) (S.ideal i)) :
    Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal) := by
  apply sum_pairwise F _ hF
  · apply sum_pairwise _ S (residual_pairwise K hK) hS
    intro P i
    exact (hKS.of_isCoprime_of_dvd_left (residual_dvd K hK P)).of_isCoprime_of_dvd_right
      (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ i))
  · intro f i
    cases i with
    | inl P => exact (hFK f).of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hFS f i

lemma reflected_period {φ σ : Type*}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (N : Eis)
    (hF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hK' : IsCoprime (Ideal.span {N}) K)
    (hS : ∀ i, IsCoprime (Ideal.span {N}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {N}) ((F.reflected K hK S).ideal i) := by
  intro i
  cases i with
  | inl f => exact hF f
  | inr i => cases i with
    | inl P => exact hK'.of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hS i

end PrimeFamily
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section

def reflectedExponent {φ ρ σ : Type*} (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ : Type*) [Fintype φ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ : Type*) [Fintype ρ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ : Type*) [Fintype σ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

lemma reflected_indices_partition (φ ρ σ : Type*) [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  constructor
  · rintro i ⟨r, rfl⟩ ⟨s, h⟩
    cases h
  constructor
  · rintro i (⟨r, rfl⟩ | ⟨s, rfl⟩) ⟨f, h⟩ <;> cases h
  · ext i
    cases i with
    | inl f => simp
    | inr i => cases i with
      | inl r => simp
      | inr s => simp

lemma reflected_residual_exponent {φ ρ σ : Type*} [Fintype ρ] (jF : φ → ℕ) :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
lemma reflected_residual_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl
end PrimeFamily

theorem moving_common_reflected_coefficients {α φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : α → Ideal Eis) (hK : ∀ x, Admissible (K x))
    (S : α → PrimeFamily σ) (jF : φ → ℕ)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then lambda^2 ∣ a-1
      else lambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : ∀ x, Pairwise (Function.onFun IsCoprime (S x).ideal))
    (hKS : ∀ x, IsCoprime (K x) (∏ i, (S x).ideal i))
    (hFK : ∀ x f, IsCoprime (F.ideal f) (K x))
    (hFS : ∀ x f i, IsCoprime (F.ideal f) ((S x).ideal i))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : ∀ x, IsCoprime (Ideal.span {N}) (K x))
    (hNS : ∀ x i, IsCoprime (Ideal.span {N}) ((S x).ideal i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (F.reflected (K x) (hK x) (S x)).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s
          (F.reflected (K x) (hK x) (S x)).generator_ne_zero
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m =
          γ (separateSector N (primaryIdealGenerator (K x))
            (primaryIdealGenerator (∏ i, (S x).ideal i))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m n b =
          β (separateSector N (primaryIdealGenerator (K x))
            (primaryIdealGenerator (∏ i, (S x).ideal i))) u m n b := by
  classical
  simpa only [frozenIndices] using canonical_common_reflected_coefficients
    (fun x => F.reflected (K x) (hK x) (S x)) N a c mode s hc hN hbase hac
    (fun x => F.reflected_pairwise (K x) (hK x) (S x) hF (hS x) (hKS x) (hFK x) (hFS x))
    (fun x => F.reflected_period (K x) (hK x) (S x) N hNF (hNK x) (hNS x))
    (fun _ => reflectedExponent jF) (fun _ => Sum.inl) (fun _ => Sum.inl_injective)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) Finset.univ (∏ i, F.ideal i) K
    (fun x => ∏ i, (S x).ideal i) (fun x => F.reflected_product (K x) (hK x) (S x))

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

theorem markedCompletedT_twist_congr_primary (Ψ Φ : Eis→*ℂ)
    (h : ∀ n : Eis, lambda^2∣n-1 → Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT Ψ W X d=markedCompletedT Φ W X d := by
  unfold markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hi:primaryIdealGenerator I=0
  · simp only [CompletedGauss.summand,columnWeight,
      squarefreeGaussCoefficient_of_primary_zero I hi,zero_mul,zero_div]
  by_cases hj:primaryIdealGenerator J=0
  · simp only [CompletedGauss.summand,cubeWeight,MonoidHom.coe_mk,OneHom.coe_mk,
      hj,angularFactor,map_zero,norm_zero,Complex.ofReal_zero,div_zero,star_zero,
      zero_pow (by decide:(3:ℕ)≠0),zero_mul,mul_zero,zero_div]
  simp only [CompletedGauss.summand,columnWeight,cubeWeight,MonoidHom.coe_mk,OneHom.coe_mk,
    h _ (primaryIdealGenerator_spec I hi).2,h _ (primaryIdealGenerator_spec J hj).2]

theorem actual_marked_row_fixed_factor {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ m f z) W X d=
      markedCompletedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X d :=
by
  apply markedCompletedT_twist_congr_primary
  intro n hn
  exact D.row_primary Ψ Q hmLam hm2 n hn

def freePrimeFamily (I Q : Ideal Eis) (hI : quadraticSupported I) : PrimeFamily (FreePrimeIndex I Q) where
  ideal P := P.val.val
  maximal _P := inferInstance
  good P := (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

def markedSumSlots {ι σ : Type*} [Fintype ι] [Fintype σ] : Finset (ι⊕σ) :=
  Finset.univ.filter (fun x => x.isRight)

lemma actual_sextic_power_congr (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda∉P) (hQ : lambda∉Q) (hPQ : P=Q) (j : ℕ) (n : Eis) :
    (complexSexticChar P hP^j) (Ideal.Quotient.mk P n)=
      (complexSexticChar Q hQ^j) (Ideal.Quotient.mk Q n) := by
  subst Q
  rfl

lemma unmarked_sum_twist {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) (n : Eis) :
    unmarkedSexticTwist (G.sum S).generator (G.sum S).generator_good
      (Sum.elim j (fun _ => 0)) markedSumSlots n =
    ∏ i, (complexSexticChar (G.ideal i) (G.good i)^j i) (Ideal.Quotient.mk _ n) := by
  let : DecidableEq (ι⊕σ) := Classical.decEq _
  have hset : (Finset.univ : Finset (ι⊕σ))\markedSumSlots = Finset.univ.filter (fun x => x.isLeft) := by
    ext x
    cases x <;> simp [markedSumSlots]
  unfold unmarkedSexticTwist
  change (∏ i∈Finset.univ\markedSumSlots, _) = _
  rw [hset,Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isLeft_inl,Sum.isLeft_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,mul_one,Sum.elim_inl]
  apply Finset.prod_congr rfl
  intro i hi
  exact actual_sextic_power_congr _ _ ((G.sum S).generator_good (Sum.inl i)) (G.good i)
    ((G.sum S).generator_span (Sum.inl i)) (j i) n

theorem free_row_eq_joined_unmarked {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : quadraticSupported I) (S : PrimeFamily σ) :
    freePrimeRow I hI Q =
      unmarkedSexticTwist ((freePrimeFamily I Q hI).sum S).generator
        ((freePrimeFamily I Q hI).sum S).generator_good
        (Sum.elim (fun P : FreePrimeIndex I Q => (UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
          (fun _ => 0)) markedSumSlots := by
  ext n
  rw [unmarked_sum_twist]
  rfl

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

lemma joined_whole_prime_mark {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (A : Ideal Eis) :
    (∏ i∈(markedSumSlots : Finset (ι⊕σ)),
      if Ideal.span {(G.sum S).generator i}∣A then (1:ℂ) else 0)=
      ∏ i, if S.ideal i∣A then (1:ℂ) else 0 := by
  unfold markedSumSlots
  rw [Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(G.sum S).generator_span]
  rfl

theorem actual_marked_row_eq_joined {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) :
    let Q₀ := Q*Ideal.span {(72:Eis)}
    let G := (freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S
    let j := Sum.elim
      (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ => 0)
    markedCompletedT (rowTwist Ψ m f z) W X (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
      markedCompletedT (D.fixedFactor Ψ Q*unmarkedSexticTwist G.generator G.generator_good j markedSumSlots)
        W X (fun A => ∏ i∈markedSumSlots, if Ideal.span {G.generator i}∣A then (1:ℂ) else 0) := by
  dsimp only
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2,
    free_row_eq_joined_unmarked D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S]
  congr 1
  funext A
  exact (joined_whole_prime_mark (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S A).symm

lemma joined_free_pairwise {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : quadraticSupported I) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hdis : ∀ P : FreePrimeIndex I Q, ∀ i, S.ideal i≠P.val.val) :
    Pairwise (Function.onFun IsCoprime ((freePrimeFamily I Q hI).sum S).ideal) := by
  apply PrimeFamily.sum_pairwise (freePrimeFamily I Q hI) S
  · exact freePrimeIndex_pairwise_coprime I Q
  · exact hS
  · intro P i
    exact Ideal.isCoprime_of_isMaximal (hdis P i).symm

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

abbrev markedRowFamily {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported).sum S

def markedRowExponent {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}) ⊕ σ → ℕ :=
  Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => 0)

theorem actual_marked_row_overlap_zero {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})) (i : σ)
    (hPi : S.ideal i=P.val.val) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=0 := by
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2]
  exact markedCompletedT_free_overlap_zero D.movingIdeal (Q*Ideal.span {(72:Eis)})
    D.movingSupported S P i hPi (D.fixedFactor Ψ Q) W X

def markedCuspSource {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
    fixedActiveFunctionWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
    (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
      (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X

theorem actual_marked_row_source {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠0)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm : ∀ n, ‖Ψ n‖≤1)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((markedRowFamily D S Q).ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    markedCuspSource (markedRowFamily D S Q)
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) c hc G N hN hNp W X := by
  have hQ0 : Q*Ideal.span {(72:Eis)}≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    ((markedRowFamily D S Q).marked_source
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm)
      (Q*Ideal.span {(72:Eis)}) hQ0 (D.fixedFactor_periodic Ψ Q hΨ) c hc hcQ G N hN hNp
      W hWcompact lo hi hlo hsupp hW X hX)
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal Eis) (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i)) (i : ι) :
    IsCoprime (Ideal.span {(9:Eis)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:Eis)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    have h3:IsCoprime (3:Eis) (P.generator i):=by
      simpa only [Units.val_one,pow_zero,mul_one] using
        ramified_primary_coprime (1:Eisˣ) 0 (P.generator i) (P.generator_primary i)
    simpa only [show (3:Eis)^2=9 by norm_num] using (h3.pow_left : IsCoprime ((3:Eis)^2) (P.generator i))
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))

lemma markedRowFamily_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i))
    (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)})) :
    ∀ i, IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D S Q).ideal i) := by
  apply PrimeFamily.level_coprime _ _ _ hcQ
  intro i
  cases i with
  | inl P => exact freePrimeIndex_coprime _ _ P
  | inr i => exact hS i

lemma markedRowFamily_odd {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2) :
    ∀ i, ringChar (Eis⧸(markedRowFamily D S Q).ideal i)≠2 := by
  intro i
  cases i with
  | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  | inr i => exact hS i

lemma markedRowExponent_lt {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    ∀ i : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})⊕σ, markedRowExponent D Q i<6 := by
  intro i
  cases i with
  | inl P => exact Nat.mod_lt _ (by norm_num)
  | inr i => norm_num [markedRowExponent]
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def joinedInactiveCoefficient (P : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) : ι⊕σ→ℂ :=
  Sum.elim (fun i => if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0)
    (fun i => (Ideal.absNorm (S.ideal i):ℂ)⁻¹)

lemma joined_inactive_weight (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (A : Finset (ι⊕σ)) :
    localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
      (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
        (Sum.elim j (fun _ => 0)) markedSumSlots) A =
    ∏ i∈(Finset.univ:Finset (ι⊕σ))\A, joinedInactiveCoefficient P S j i := by
  have ho : ∀ i, ringChar (Eis⧸(P.sum S).ideal i)≠2 := by
    intro i
    cases i with
    | inl i => exact hP i
    | inr i => exact hS i
  have hj' : ∀ i : ι⊕σ, Sum.elim j (fun _ => 0) i<6 := by
    intro i
    cases i with
    | inl i => exact hj i
    | inr i => norm_num
  rw [mixed_inactive_weight (P.sum S) ho _ hj']
  apply Finset.prod_congr (by ext i; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro i hi
  cases i <;> simp [markedSumSlots,joinedInactiveCoefficient,PrimeFamily.sum]

theorem joined_inactive_three_blocks {α β : Type*} [Fintype α] [Fintype β]
    (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (e : α⊕β≃ι) (he : ∀ a, j (e (Sum.inl a))=1)
    (F : Finset (ι⊕σ)→ℂ) :
    (∑ A : Finset (ι⊕σ),
      localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
        (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
          (Sum.elim j (fun _ => 0)) markedSumSlots) A * F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,
        if j (e (Sum.inr b))=0 then 1-(Ideal.absNorm (P.ideal (e (Sum.inr b))):ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*F (markedActiveSet e B T) := by
  have hz : ∀ a, joinedInactiveCoefficient P S j (Sum.inl (e (Sum.inl a)))=0 := by
    intro a
    simp [joinedInactiveCoefficient,he a]
  have h := inactive_weight_three_blocks e (joinedInactiveCoefficient P S j) hz F
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
  intro A hA
  congr 1
  exact joined_inactive_weight P S hP hS j hj A
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
lemma residualPart_admissible (I R:Ideal Eis) (hbad:∀P∈fixedBadPrimes,P∣R) :
    CanonicalQuadraticSieve.Admissible (rowResidualPart I R) :=
  (CanonicalQuadraticSieve.admissible_iff_native _).mpr
    (CompletedGauss.rowResidualPart_admissible I R hbad)
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.freePrimeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_fiber_inactive_sum (S : PrimeFamily σ)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (H : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ)→ℂ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
        ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_ne_zero
        (mixedPrimeFunction ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
          ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_good
          (Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
            (fun _ => 0)) markedSumSlots) A * H A)=
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*H (markedActiveSet E B T) := by
  have hodd : ∀ P : FreePrimeIndex D.movingIdeal Q₀,
      ringChar (Eis⧸(freePrimeFamily D.movingIdeal Q₀ D.movingSupported).ideal P)≠2 := by
    intro P
    exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  have hres : ∀ a, (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count
      (E (Sum.inl a)).val.val%6=1 := by
    intro a
    exact D.freePrimeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
  have he := joined_inactive_three_blocks (freePrimeFamily D.movingIdeal Q₀ D.movingSupported)
    S hodd hS (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => Nat.mod_lt _ (by norm_num)) E hres H
  refine he.trans ?_
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  apply Finset.sum_congr (by ext T; simp only [Finset.mem_univ])
  intro T hT
  congr 2
  apply Finset.prod_congr (by ext b; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro b hb
  rw [D.freePrimeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  change (if completedLocalExponent R F b.val=0 then
    1-(Ideal.absNorm (E (Sum.inr b)).val.val:ℂ)⁻¹ else 0)=_
  rw [D.freePrimeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  rfl
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

lemma markedActiveEquiv_frozen (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (b : B) :
    (markedActiveEquiv e B T (Sum.inl b)).val=Sum.inl (e (Sum.inr b.val)) := rfl
lemma markedActiveEquiv_residual (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (a : α) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inl a))).val=Sum.inl (e (Sum.inl a)) := rfl
lemma markedActiveEquiv_slot (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (t : T) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inr t))).val=Sum.inr t.val := rfl
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open Eisenstein CompletedGauss CubicJacobi  
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma cuspPrimeCofactor_reindex (p : ι→Eis) (e : κ≃ι) (k : κ) :
    cuspPrimeCofactor (fun k => p (e k)) k=cuspPrimeCofactor p (e k) := by
  unfold cuspPrimeCofactor
  apply Finset.prod_equiv e
  · intro i
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,ne_eq,EmbeddingLike.apply_eq_iff_eq]
  · intro i hi
    rfl

lemma cuspCrossNumerator_reindex (a c l : Eis) (p : ι→Eis) (e : κ≃ι) (h : ι→Eis) :
    cuspCrossNumerator a c l (fun k => p (e k)) (fun k => h (e k))=
      cuspCrossNumerator a c l p h := by
  unfold cuspCrossNumerator
  simp_rw [cuspPrimeCofactor_reindex]
  rw [e.prod_comp,e.sum_comp (fun i => h i*cuspPrimeCofactor p i)]

def unitFrequencyEquiv (p : ι→Eis) (e : κ≃ι) :
    (∀ k, (Eis⧸Ideal.span {p (e k)})ˣ)≃(∀ i, (Eis⧸Ideal.span {p i})ˣ) :=
  Equiv.piCongrLeft (fun i => (Eis⧸Ideal.span {p i})ˣ) e

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_apply (p : ι→Eis) (e : κ≃ι)
    (v : ∀ k, (Eis⧸Ideal.span {p (e k)})ˣ) (k : κ) :
    unitFrequencyEquiv p e v (e k)=v k := Equiv.piCongrLeft_apply_apply _ _ _ _

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_one (p : ι→Eis) (e : κ≃ι) :
    unitFrequencyEquiv p e (fun _ => 1)=(fun _ => 1) := by
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  exact unitFrequencyEquiv_apply p e _ k

def reindexControlled {p : ι→Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    ControlledStratumArithmetic (fun k => p (e k)) N a c mode where
  lift v k := D.lift (unitFrequencyEquiv p e v) (e k)
  lift_period v k := D.lift_period _ _
  lift_residue v k := (D.lift_residue _ _).trans (congrArg Units.val (unitFrequencyEquiv_apply p e v k))
  U := D.U
  w := D.w
  bezout := by simpa only [e.prod_comp] using D.bezout
  sigma k := D.sigma (e k)
  epsilon k := D.epsilon (e k)
  sigma_value k := by simpa only [cuspPrimeCofactor_reindex] using D.sigma_value (e k)
  epsilon_value k := by simpa only [cuspPrimeCofactor_reindex] using D.epsilon_value (e k)
  matrix v := D.matrix (unitFrequencyEquiv p e v)
  numerator v := by
    rw [D.numerator,cuspCrossNumerator_reindex]
  denominator v := by simpa only [e.prod_comp] using D.denominator (unitFrequencyEquiv p e v)
  matrix_fixed v i j := by
    simpa only [unitFrequencyEquiv_one] using D.matrix_fixed (unitFrequencyEquiv p e v) i j
  conditions v := D.conditions (unitFrequencyEquiv p e v)
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss InverseMoment
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

lemma reindexControlled_matrix_one (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]

lemma reindexControlled_fixedFactor (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]

lemma reindexControlled_U (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).U=D.U := rfl

def reindexMarks (e : κ≃ι) (S : Finset ι) : Finset κ := Finset.univ.filter (fun k => e k∈S)

omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι) (S : Finset ι) (k : κ) : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]

lemma mixedActiveBracket_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (hp : ∀ i, p i≠0) (hg : ∀ i, lambda∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (k : κ) (x : Eis) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl

theorem mixedReflectedValue_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, lambda∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.freePrimeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => residualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.freePrimeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.freePrimeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryIdealPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)

lemma original_active_exponent
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
      (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ : σ => 0)
      (markedActiveEquiv E B T x).val =
    Sum.elim (fun b : B => completedLocalExponent R F b.val.val)
      (Sum.elim (fun _ : PrimeIndex K => 1) (fun _ : T => 0)) x := by
  cases x with
  | inl b => exact D.freePrimeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a => exact D.freePrimeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_marks
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ) :
    reindexMarks (markedActiveEquiv E B T) (activeMarks (markedActiveSet E B T) markedSumSlots)=
    Finset.univ.filter (fun x : B⊕(PrimeIndex K⊕T) => match x with
      | Sum.inr (Sum.inr _) => True | _ => False) := by
  ext x
  simp only [mem_reindexMarks,mem_activeMarks,Finset.mem_filter,Finset.mem_univ,true_and]
  cases x with
  | inl b => simp [markedActiveEquiv_frozen,markedSumSlots]
  | inr x => cases x with
    | inl a => simp [markedActiveEquiv_residual,markedSumSlots]
    | inr t => simp [markedActiveEquiv_slot,markedSumSlots]
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
lemma maximal_coprime_of_not_dvd (P J : Ideal Eis) [P.IsMaximal] (h : ¬P∣J) : IsCoprime P J := by
  rw [Ideal.isCoprime_iff_codisjoint]
  apply ((Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint).mp
  exact fun hle => h (Ideal.dvd_iff_le.mpr hle)


end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

lemma poolPrimeFamily_pairwise (R Q Q₀ : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

lemma poolPrimeFamily_period (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    IsCoprime Q₀ ((poolPrimeFamily R Q Q₀).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  exact FreeReflection.pool_free R Q Q₀ P (Ideal.dvd_iff_le.mp h)

lemma poolPrimeFamily_odd (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    ringChar (Eis⧸(poolPrimeFamily R Q Q₀).ideal P)≠2 := FreeReflection.pool_odd R Q Q₀ P

lemma poolPrimeFamily_fiber_row_coprime (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    IsCoprime ((poolPrimeFamily R Q Q₀).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_divides (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    (poolPrimeFamily R Q Q₀).ideal P∣I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_exponent (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    completedLocalExponent I F ((poolPrimeFamily R Q Q₀).ideal P)=completedLocalExponent R F P.val :=
  nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask P

lemma pool_restrict_completion_coprime (R Q Q₀ : Ideal Eis)
    (B : Finset (FreeReflection.pool R Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ b : B, IsCoprime (Ideal.span {(9:Eis)*c}) (((poolPrimeFamily R Q Q₀).restrict B).ideal b) := by
  exact ((poolPrimeFamily R Q Q₀).restrict B).level_coprime Q₀ c hc
    (fun b => poolPrimeFamily_period R Q Q₀ b.val)
end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

def castControlled {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode) :
    ControlledStratumArithmetic q N a c mode := h ▸ D

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : ∀ i, lambda∉Ideal.span {p i}) (hgq : ∀ i, lambda∉Ideal.span {q i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.freePrimeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => residualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

lemma original_active_marks_eq_slots :
    reindexMarks EA (activeMarks (markedActiveSet E B T) markedSumSlots)=slotIndices B (PrimeIndex K) T := by
  rw [original_active_marks D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  ext x
  cases x with
  | inl b => simp [slotIndices]
  | inr x => cases x with
    | inl a => simp [slotIndices]
    | inr t => simp [slotIndices]

def originalCanonicalControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode) :
    ControlledStratumArithmetic (PF).generator N a c mode :=
  castControlled (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T))
    (reindexControlled C EA)

theorem original_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue C s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue (originalCanonicalControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  rw [← mixedReflectedValue_reindex C EA]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  exact (mixedReflectedValue_cast _ (reindexControlled C EA) s _ (PF).generator_ne_zero hc _ (PF).generator_good _ _ W X).symm
end
end InverseReflectedPhase

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
