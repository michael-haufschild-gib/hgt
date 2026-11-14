/-
Three-block phases adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.PrimeFamiliesAndIdealCounts
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.MixedReflectedValues

/-!
# Three-block phases

Restriction of prime families, marked active sets and ramified blocks; residual and marked
phases with frozen cores; the inactive weight splits over three blocks. Prime indices of the
canonical quadratic sieve (`CanonicalQuadraticSieve.PrimeIndex`) are maximal ideals.
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
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss NormalizedReflection
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance threeBlockFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def residualWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis) (R F : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, FirstPassCubeLabels.crossSymbol p hg i k^4)*
    (residualPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, FirstPassCubeLabels.crossSymbol p hg i k^4)

def markedWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis) (P F : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, FirstPassCubeLabels.crossSymbol p hg i k^2)*
    (markedPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, FirstPassCubeLabels.crossSymbol p hg i k^2)

def frozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i)

theorem activePhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0) :
    D.activePhase hp hg j = residualWithFrozen hp hg c R F *
      markedWithFrozen hp hg c P F * frozenPhase D hp hg j F := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c (hp i) (hg i)
    else markedPrimeScalar (p i) c (hp i) (hg i)
  let v : ι → ℂ := fun i => (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i)
  have hm : (∏ i ∈ R ∪ P, v i) = ∏ i ∈ R ∪ P,
      (∏ k ∈ Finset.univ.erase i, FirstPassCubeLabels.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [v,hRj i hr,l,hr,ite_true]
      rw [controlled_residual_phase]
      ring
    · have hp' : i ∈ P := (Finset.mem_union.mp hi).resolve_left hr
      simp only [v,hPj i hp',l,hr,ite_false]
      rw [controlled_marked_phase]
      ring
  have hfull : D.activePhase hp hg j = (∏ i ∈ R ∪ P, v i)*frozenPhase D hp hg j F := by
    change (∏ i, v i) = (∏ i ∈ R ∪ P, v i)*(∏ i ∈ F, v i)
    rw [← Finset.prod_union hF,hu]
  rw [hfull,hm,ordered_cross_frozen_partition _ l 4 2 R P F hRP hF hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hRP,mul_one]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [l,hn]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss NormalizedReflection
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance ramifiedFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def ramifiedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∏ i ∈ S, unitArgumentFactor (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (u.val*lambda^m))

theorem ramifiedPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss 
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance frozenSplitFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenArgument [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ F, frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i)

def frozenCore [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : Eis)
    (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, frozenPrimeScalar (p i) c (hp i) (hg i) (j i) *
    frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k)

theorem frozen_cuspPrimeCofactor_split (hp : ∀ i, p i ≠ 0) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (i : ι) (hi : i ∈ F) :
    cuspPrimeCofactor p i = (∏ k ∈ F.erase i, p k)*(∏ k ∈ R, p k)*(∏ k ∈ S, p k) := by
  apply mul_left_cancel₀ (hp i)
  rw [cuspPrime_mul_cofactor,← hu,Finset.prod_union hF,Finset.prod_union hRS,
    ← Finset.mul_prod_erase F p hi]
  ring

theorem frozenPhase_split [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (R S F : Finset ι) (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F)
    (hu : (R ∪ S) ∪ F = Finset.univ) :
    frozenPhase D hp hg j F = frozenCore hp hg c j F *
      frozenArgument hg j F (∏ i ∈ R, p i) * frozenArgument hg j F (∏ i ∈ S, p i) := by
  unfold frozenPhase
  simp_rw [controlled_frozen_phase]
  have he (i : ι) (hi : i ∈ F) :
      frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (cuspPrimeCofactor p i) =
      (frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k))*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ R, p k)*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ S, p k) := by
    rw [frozen_cuspPrimeCofactor_split hp R S F hRS hF hu i hi,map_mul,map_mul]
    ring
  rw [Finset.prod_congr rfl he]
  simp only [Finset.prod_mul_distrib,frozenCore,frozenArgument,MonoidHom.finsetProd_apply]

omit [Fintype ι] in
theorem frozenArgument_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) (z : Eis) :
    ‖frozenArgument hg j F z‖ ≤ 1 := by
  simp only [frozenArgument,MonoidHom.finsetProd_apply,norm_prod]
  apply Finset.prod_le_one
  · intro i hi; exact norm_nonneg _
  · intro i hi
    unfold frozenCofactorCharacter
    split_ifs
    · exact FiniteRayExpansion.norm_char_le_one (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)
    · exact FiniteRayExpansion.norm_char_le_one ((complexSexticChar (Ideal.span {p i}) (hg i))^(2*j i+2))
        (Ideal.Quotient.mk (Ideal.span {p i}) z)

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein  CompletedGauss NormalizedReflection
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance phaseNormField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseNormFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem crossSymbol_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖FirstPassCubeLabels.crossSymbol p hg i k‖ = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have hn : Ideal.Quotient.mk (Ideal.span {p i}) (p k)≠0 :=
    fun hz=>hnot (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  exact finiteMulChar_unit_norm (complexSexticChar (Ideal.span {p i}) (hg i))
    (Units.mk0 _ hn)


theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,finiteMulChar_unit_norm,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (residueTraceQuotientChar 1 (p i) (hp i))
    (residueTraceQuotientChar_primitive (p i) (hp i)) j hj (D.epsilon i)

theorem markedPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 0 (by decide)
  rw [controlled_marked_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖FirstPassCubeLabels.crossSymbol p hg i k^2‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 1 (by decide)
  rw [controlled_residual_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖FirstPassCubeLabels.crossSymbol p hg i k^4‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,residualPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hR : (∏ k ∈ R.erase i, ‖FirstPassCubeLabels.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖FirstPassCubeLabels.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hR,hF,one_mul]

theorem markedWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,markedPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hP : (∏ k ∈ P.erase i, ‖FirstPassCubeLabels.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖FirstPassCubeLabels.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hP,hF,one_mul]

end
end InverseReflectedPhase

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace CanonicalQuadraticSieve
abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primeIndex_good (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (P : PrimeIndex I) :
    lambda ∉ P.val :=
  (primaryIdealPrime_spec P.val (primaryIdealPrime_factor_ne_zero I P.val hI
    (Multiset.mem_toFinset.mp P.property))).2.1

theorem primeIndex_le (I : Ideal O) (hI : I ≠ 0) (P : PrimeIndex I) : I ≤ P.val :=
  ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp P.property)).2

def admissiblePrimeGood (K:Ideal Eis) (hK:Admissible K) (P:PrimeIndex K) : lambda∉P.val :=
  (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).1

end CanonicalQuadraticSieve

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

lemma freePrimeRow_zero_at_prime (I Q : Ideal Eis) (hI : quadraticSupported I)
    (P : FreePrimeIndex I Q) (n : Eis) (hn : n∈P.val.val) : freePrimeRow I hI Q n=0 := by
  unfold freePrimeRow
  change (∏ p : FreePrimeIndex I Q, _)=0
  apply Finset.prod_eq_zero (Finset.mem_univ P)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma primaryIdealGenerator_mem_of_ideal_dvd (P A : Ideal Eis) (hPA : P∣A) : primaryIdealGenerator A∈P := by
  by_cases hz : primaryIdealGenerator A=0
  · rw [hz]
    exact Ideal.zero_mem _
  have ha0 : primaryIdealGenerator A∈Ideal.span {primaryIdealGenerator A} := Ideal.subset_span (by simp)
  have ha : primaryIdealGenerator A∈A := ((primaryIdealGenerator_spec A hz).1.le) ha0
  exact (Ideal.dvd_iff_le.mp hPA) ha

lemma free_row_whole_mark_overlap {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : quadraticSupported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val) (A : Ideal Eis) :
    freePrimeRow I hI Q (primaryIdealGenerator A)*
      (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  by_cases hd : S.ideal i∣A
  · have hn := primaryIdealGenerator_mem_of_ideal_dvd (S.ideal i) A hd
    rw [heq] at hn
    rw [freePrimeRow_zero_at_prime I Q hI P _ hn,zero_mul]
  · have hz : (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_neg hd]
    rw [hz,mul_zero]

theorem markedCompletedT_free_overlap_zero {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : quadraticSupported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val)
    (φ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (φ*freePrimeRow I hI Q) W X
      (fun A => ∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  unfold markedCompletedT
  calc
    _ = ∑' n : Ideal Eis, ∑' b : Ideal Eis, (0:ℂ) := by
      apply tsum_congr
      intro n
      apply tsum_congr
      intro b
      rw [mul_comm φ (freePrimeRow I hI Q),summand_mul_fixed_twist]
      have hgen : primaryIdealGenerator (n*b^3)=primaryIdealGenerator n*(primaryIdealGenerator b)^3 := by
        rw [primaryIdealGenerator_mul,show primaryIdealGenerator (b^3)=primaryIdealGenerator b^3 from map_pow primaryIdealGeneratorHom b 3]
      rw [← hgen]
      have hz := free_row_whole_mark_overlap I Q hI S P i heq (n*b^3)
      calc
        _ = CompletedGauss.summand φ W X n b*(freePrimeRow I hI Q (primaryIdealGenerator (n*b^3))*
          (∏ j, if S.ideal j∣n*b^3 then (1:ℂ) else 0)) := by ring
        _ = 0 := by rw [hz,mul_zero]
    _ = 0 := by simp

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

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance

def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val

lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))

def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))

theorem marked_source [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := cubicIdealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply cubicIdealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := (Ideal.span {call}).finiteQuotientOfFreeOfNeBot (Ideal.span_singleton_eq_bot.not.mpr hcall)
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [span_cubicIdealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    (P.activeControlled hP c G N hN hNp) call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
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
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

variable {ι : Type*} [Fintype ι]
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)

omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]

omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl

omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm

lemma active_sum_eq_mixed (P : PrimeFamily ι) (j : ι→ℕ) (S : Finset ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    (∑ v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ,
      localActiveWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) A v *
      (activeStratumDatum P.generator P.generator_ne_zero P.generator_primary
        (P.activeControlled hP c G N hN hNp h) (hN h) (G h).denominator_ne_zero
        (G h).primary (G h).shape A v).smoothedKernel W X)=
    mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
      (P.restrict A).generator_product_primary (G h).primary (G h).shape
      (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) W X := by
  unfold mixedSmoothedValue
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
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
theorem finiteAdditiveFourierCoeff_zero_delta {R:Type*} [CommRing R] [Fintype R]
    (ψ:AddChar R ℂ) (h:R) :
    finiteAdditiveFourierCoeff ψ (fun x=>if x=0 then 1 else 0) h=(Fintype.card R:ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

theorem prime_zeroFourier_norm_formula (p:Eis) [hP:(Ideal.span {p}).IsMaximal]
    (hp:p≠0) (hg:lambda∉Ideal.span {p}) (hc:ringChar (Eis⧸Ideal.span {p})≠2)
    (j:ℕ) (hj:j<6) :
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 p hp)
      (fun x => (complexSexticChar (Ideal.span {p}) hg ^ j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_mulChar_zero]
  by_cases hz:j=0
  · subst j
    simp only [pow_zero,if_pos rfl,Nat.card_eq_fintype_card,Fintype.card_units]
    rw [Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos),Nat.cast_one,
      Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    have hq:(Fintype.card (Eis⧸Ideal.span {p}):ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · rw [if_neg hz,if_neg (complexSexticChar_pow_ne_one _ hg hc j hj hz)]
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
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mixed_inactive_coefficient (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) :
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (P.generator i) (P.generator_ne_zero i))
      (mixedPrimeFunction P.generator P.generator_good j S i) 0 =
    if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
      else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  change finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (P.generator i) (P.generator_ne_zero i))
    (fun x => if i∈S then zeroMark x else (complexSexticChar (Ideal.span {P.generator i}) (P.generator_good i)^j i) x) 0 = _
  by_cases hi : i∈S
  · simp only [hi,ite_true,zeroMark,finiteAdditiveFourierCoeff_zero_delta]
    have hcard : Fintype.card (Eis⧸Ideal.span {P.generator i})=Ideal.absNorm (P.ideal i) := by
      rw [← P.generator_span i,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    rw [hcard]
  · simp only [hi,ite_false]
    have ho : ringChar (Eis⧸Ideal.span {P.generator i})≠2 := by
      rw [P.generator_span]
      exact hodd i
    rw [prime_zeroFourier_norm_formula (P.generator i) (P.generator_ne_zero i)
      (P.generator_good i) ho (j i) (hj i),P.generator_span]

lemma mixed_inactive_weight (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A =
    ∏ i∈(Finset.univ:Finset ι)\A,
      if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
        else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  unfold localInactiveWeight
  apply Finset.prod_congr rfl
  intro i hi
  exact mixed_inactive_coefficient P hodd j hj S i

lemma mixed_inactive_zero_of_omitted (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) (i : ι) (hi : i∉S) (hji : j i≠0) (hiA : i∉A) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A=0 := by
  rw [mixed_inactive_weight P hodd j hj]
  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hiA⟩)
  simp only [hi,hji,ite_false]

lemma mixed_inactive_nonzero_requires (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι)
    (h : localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A≠0) :
    ∀ i, i∉S → j i≠0 → i∈A := by
  intro i hi hji
  by_contra hiA
  exact h (mixed_inactive_zero_of_omitted P hodd j hj S A i hi hji hiA)
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
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]

def joinedFiberEquiv (e : α⊕β≃γ) : α⊕(β⊕σ)≃γ⊕σ :=
  (Equiv.sumAssoc α β σ).symm.trans (Equiv.sumCongr e (Equiv.refl σ))

def markedActiveSet (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) : Finset (γ⊕σ) :=
  residualActivePrimes (joinedFiberEquiv (σ:=σ) e) ∪
    (B.disjSum T).image (fun x => joinedFiberEquiv e (Sum.inr x))

lemma inactive_product_disjSum (z : β⊕σ→ℂ) (B : Finset β) (T : Finset σ) :
    (∏ x∈(Finset.univ:Finset (β⊕σ))\B.disjSum T,z x)=
    (∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl b))*
    ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t) := by
  have hs : (Finset.univ:Finset (β⊕σ))\B.disjSum T=
      ((Finset.univ:Finset β)\B).disjSum ((Finset.univ:Finset σ)\T) := by
    ext x
    cases x <;> simp
  rw [hs,Finset.prod_disjSum]

theorem inactive_weight_three_blocks (e : α⊕β≃γ) (z : γ⊕σ→ℂ)
    (hz : ∀ a, z (Sum.inl (e (Sum.inl a)))=0) (F : Finset (γ⊕σ)→ℂ) :
    (∑ A : Finset (γ⊕σ), (∏ x∈(Finset.univ:Finset (γ⊕σ))\A,z x)*F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl (e (Sum.inr b))))*
        ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t))*F (markedActiveSet e B T) := by
  have he := inactive_weight_nonresidual_subsets (joinedFiberEquiv e) z hz F
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro x hx
    rfl
  · rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
    intro B
    have hB : B=B.toLeft.disjSum B.toRight := (Finset.toLeft_disjSum_toRight).symm
    conv_lhs => rw [hB]
    congr 1
    · refine Eq.trans ?_ (inactive_product_disjSum (fun x => z (joinedFiberEquiv e (Sum.inr x))) B.toLeft B.toRight)
      apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
      intro x hx
      rfl
    · apply congrArg F
      ext x
      simp only [markedActiveSet,Finset.sumEquiv,Equiv.coe_fn_mk,Finset.mem_union,Finset.mem_image]
end
end InverseReflectedPhase

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
