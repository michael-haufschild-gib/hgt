/-
Mixed reflected values adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.ControlledStratumReflection

/-!
# Mixed reflected values

Mixed reflected values, prime functions and active brackets of the marked phase; unmarked
sextic twists and inactive weights; smoothed and reflected mixed values agree.
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
namespace InverseMoment
open SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eisenstein.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop

omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    FirstPassCubeLabels.crossSymbol p hg i k ^ 4 *
      FirstPassCubeLabels.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : FirstPassCubeLabels.crossSymbol p hg i k ^ 2 =
      FirstPassCubeLabels.crossSymbol p hg k i ^ 2 :=
    FirstPassCubeLabels.cross_square_primary p hg hpr i k
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have hm : primeCoprimeMask p {i} (p k)=1 := by
    rw [primeCoprimeMask_indicator]
    apply if_pos
    intro j hj hd
    have hji := Finset.mem_singleton.mp hj
    subst j
    exact hnot (Ideal.mem_span_singleton.mpr hd)
  have h6 : FirstPassCubeLabels.crossSymbol p hg i k^6=1 := by
    simpa only [primeSubsetRow,Finset.prod_singleton,FirstPassCubeLabels.crossSymbol] using
      (row_sixth p hg {i} (p k)).trans hm

  calc
    _ = FirstPassCubeLabels.crossSymbol p hg i k ^ 6 := by rw [← hs]; ring
    _ = 1 := h6

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      FirstPassCubeLabels.crossSymbol p hg i k ^ 4 *
        FirstPassCubeLabels.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
def mixedActiveBracket [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) : ℂ :=
  if i ∈ S then
    (rootCard (Eis ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
      tau (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) 2 *
        (((complexSexticChar (Ideal.span {p i}) (hg i)) ^ 2)⁻¹)
          ((D.sigma i : Eis ⧸ Ideal.span {p i}) * (D.epsilon i : Eis ⧸ Ideal.span {p i}) *
            Ideal.Quotient.mk _ x)
  else (((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
    phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i) *
      bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

def markedActiveExponent (S : Finset ι) (j : ι → ℕ) (i : ι) : ℕ := if i ∈ S then 0 else j i

theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

theorem mixedActiveBracket_product [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode) (x : Eis) :
    (∏ i, mixedActiveBracket hp hg j S D i x) =
      (-1 : ℂ) ^ S.card * D.bracketProduct hp hg (markedActiveExponent S j) x := by
  simp_rw [mixedActiveBracket_eq_signed]
  rw [Finset.prod_mul_distrib]
  have hsign : (∏ i : ι, if i ∈ S then (-1 : ℂ) else 1) = (-1 : ℂ) ^ S.card := by
    rw [Finset.prod_ite]
    simp
  rw [hsign]
  rfl

theorem mixed_model_coefficient [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor * cuspBadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m I J)) =
    ((-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m) *
      ∑ e : ι → Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0
            (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg (markedActiveExponent S j) e
          (primaryIdealGenerator I) (primaryIdealGenerator J) := by
  rw [mixedActiveBracket_product]
  calc
    _ = (-1 : ℂ) ^ S.card * (s.amplitude u m I J *
      (star D.fixedFactor * cuspBadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      D.bracketProduct hp hg (markedActiveExponent S j) (s.modelDualNumerator u m I J)) := by ring
    _ = _ :=
      (congrArg ((-1 : ℂ) ^ S.card * ·)
        (D.model_coefficient s hp hc0 hg (markedActiveExponent S j) u m I J)).trans
          (mul_assoc _ _ _).symm

theorem marked_modelRowPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖(-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m‖ = 1 := by
  have hj' : ∀ i, markedActiveExponent S j i < 6 := by
    intro i
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact D.modelRowPhase_norm hN hr hbase s hp hg hchar _ hj' u m

end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
theorem actual_marked_active_formula
    (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) (hc:ringChar (Eis⧸P)≠2)
    (ψ:AddChar (Eis⧸P) ℂ) (hψ:ψ.IsPrimitive) (σ ε:(Eis⧸P)ˣ) (x:Eis⧸P) :
    localReflectionActive zeroMark (complexSexticChar P hg) ψ σ ε x=
      (rootCard (Eis⧸P):ℂ)⁻¹*tau (complexSexticChar P hg) ψ 2*
        (((complexSexticChar P hg)^2)⁻¹) ((σ:Eis⧸P)*(ε:Eis⧸P)*x) := by
  have he : localReflectionActive (fun t=>(1:MulChar (Eis⧸P) ℂ) t)
      (complexSexticChar P hg) ψ σ ε x =
      ∑h:(Eis⧸P)ˣ,frequencyRow (complexSexticChar P hg) ψ 0 σ ε x h := by
    simp only [localReflectionActive,localFourier,frequencyRow,frequencyMultiplier,
      finiteAdditiveFourierCoeff,pow_zero,Units.ne_zero,ite_false,
      Finset.mul_sum,Units.val_inv_eq_inv_val,div_eq_mul_inv,neg_mul]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [marked_active_eq_neg_trivial _ ψ hψ,he,
    canonical_frequencyRow_units P hg hc ψ hψ 0 (by decide)]
  simp only [phase,bracket,show (0:ℕ)≠4 by decide,↓reduceIte,inv_pow,map_mul]
  ring
section
variable {F:Type*} [Field F] [Fintype F]
def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    markedFrequencyRow χ ψ σ ε x 0 = (Fintype.card F : ℂ)⁻¹ := by
  simp [markedFrequencyRow, frequencyMultiplier, finiteAdditiveFourierCoeff, zeroMark]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end
noncomputable local instance markedStratumField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) :=
  Fintype.ofFinite _

theorem actual_mixed_frequency_units (P : Ideal Eis) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    (∑ h : (Eis ⧸ P)ˣ, mixedFrequencyRow (complexSexticChar P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (Eis ⧸ P) : ℂ)⁻¹ * tau (complexSexticChar P hg) ψ 2 *
          (((complexSexticChar P hg) ^ 2)⁻¹) ((σ : Eis ⧸ P) * (ε : Eis ⧸ P) * x)
      else (((complexSexticChar P hg)⁻¹) ^ 2) σ *
        phase (complexSexticChar P hg) ψ j ε * bracket (complexSexticChar P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]


end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein 
noncomputable section
noncomputable local instance activeQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (F i.val) (v i)

theorem primeFunction_fourier_by_active
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (n : Eis) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, residueTraceQuotientChar 1 (p i.val) (hp i.val)
              ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (Eis ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have h := finiteAdditiveFourier_active_inversion
    (fun i=>residueTraceQuotientChar 1 (p i) (hp i))
    (fun i=>residueTraceQuotientChar_primitive (p i) (hp i)) F (fun i=>Ideal.Quotient.mk _ n)
  rw [h]
  apply Finset.sum_congr rfl
  intro A hA
  have hz : (∏i:{i // i∉A},finiteAdditiveFourierCoeff
      (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (F i.val) 0)=localInactiveWeight p hp F A := by
    rw [localInactiveWeight,Finset.prod_subtype (p := fun i => i ∉ A) (Finset.univ \ A) (by simp)]
  rw [hz]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [localActiveWeight,Finset.prod_mul_distrib]

theorem activeStratum_function_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : Eis} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : Eis) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * tracePhase (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      tracePhase (-cuspFrequency n * (ringComplex a0 / ringComplex c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) :
      tracePhase (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      tracePhase (-cuspFrequency n * (ringComplex a0 / ringComplex c0)) *
        ∏ i : A, residueTraceQuotientChar 1 (p i.val) (hp i.val)
          ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (fun i => hp i.val) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro v hv
  ring

def fixedActiveFunctionWeight
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (φ : Eis →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

theorem fixedActiveFunction_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (φ : Eis →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : Eis) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      tracePhase (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [FixedActiveCuspIndex, Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : Eis ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      tracePhase (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * tracePhase (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment

theorem completed_summand_primary_support (Ψ:Eis→*ℂ) (W:ℝ→ℂ)
    (X:ℝ) (I J:Ideal Eis) (h:CompletedGauss.summand Ψ W X I J≠0) :
    primaryIdealGenerator (I*J^3)≠0 := by
  have hs:=CompletedGauss.summand_primary_support Ψ W X I J h
  change primaryIdealGeneratorHom (I*J^3)≠0
  rw [map_mul,map_pow]
  exact mul_ne_zero hs.1.2 (pow_ne_zero _ hs.2)

theorem markedCompletedT_congr_primary (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ)
    (d e:Ideal Eis→ℂ) (h:∀A,primaryIdealGenerator A≠0→d A=e A) :
    markedCompletedT Ψ W X d=markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz:CompletedGauss.summand Ψ W X I J=0
  · simp only [hz,zero_mul]
  · rw [h (I*J^3) (completed_summand_primary_support Ψ W X I J hz)]

theorem summand_mul_fixed_twist (Ψ φ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) (I J:Ideal Eis) :
    CompletedGauss.summand (φ*Ψ) W X I J=
      φ (primaryIdealGenerator I*primaryIdealGenerator J^3)*CompletedGauss.summand Ψ W X I J := by
  simp only [CompletedGauss.summand,columnWeight,cubeWeight,MonoidHom.coe_mk,
    OneHom.coe_mk,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
noncomputable section

theorem markedCompletedT_monoid (Ψ φ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun A => φ (primaryIdealGenerator A)) = completedIdealT (φ * Ψ) W X := by
  unfold markedCompletedT completedIdealT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  change CompletedGauss.summand Ψ W X I J * φ (primaryIdealGenerator (I * J ^ 3)) = _
  rw [summand_mul_fixed_twist, primaryIdealGenerator_mul,
    show primaryIdealGenerator (J ^ 3) = primaryIdealGenerator J ^ 3 from map_pow primaryIdealGeneratorHom J 3]
  exact mul_comm _ _

theorem whole_prime_mark_eq_mask_complement (p : Eis) (hp : Prime p)
    (A : Ideal Eis) (hA : primaryIdealGenerator A ≠ 0) :
    (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
      1 - coprimalityMask p (primaryIdealGenerator A) := by
  have hd : Ideal.span {p} ∣ A ↔ p ∣ primaryIdealGenerator A := by
    calc
      _ ↔ A ≤ Ideal.span {p} := Ideal.dvd_iff_le
      _ ↔ Ideal.span {primaryIdealGenerator A} ≤ Ideal.span {p} := by
        rw [(primaryIdealGenerator_spec A hA).1]
      _ ↔ _ := by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  change (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
    1 - (if IsCoprime p (primaryIdealGenerator A) then 1 else 0)
  rw [hp.coprime_iff_not_dvd]
  by_cases h : p ∣ primaryIdealGenerator A <;> simp [hd, h]

theorem markedCompletedT_prime_product_twists {ι : Type*}
    (S : Finset ι) (p : ι → Eis) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        completedIdealT ((∏ i ∈ T, coprimalityMask (p i)) * Ψ) W X := by
  have he : markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          (∏ i ∈ T, coprimalityMask (p i)) (primaryIdealGenerator A)) := by
    apply markedCompletedT_congr_primary
    intro A hA
    calc
      _ = ∏ i ∈ S, (1 - coprimalityMask (p i) (primaryIdealGenerator A)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (p i) (hp i hi) A hA
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  rw [he, markedCompletedT_finset_sum S.powerset Ψ W hW X hX]
  apply Finset.sum_congr rfl
  intro T hT
  rw [markedCompletedT_const_mul, markedCompletedT_monoid]

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section

variable {ι : Type*}

def markTwist (p : ι → Eis) (T : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ T, coprimalityMask (p i)

theorem markTwist_norm (p : ι → Eis) (T : Finset ι) (x : Eis) : ‖markTwist p T x‖ ≤ 1 := by
  simp only [markTwist, MonoidHom.finsetProd_apply, norm_prod]
  exact Finset.prod_le_one (fun i hi => norm_nonneg _) (fun i hi => coprimalityMask_norm _ _)

theorem markTwist_periodic (p : ι → Eis) (S T : Finset ι) (hTS : T ⊆ S) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i ∈ S, p i}) (markTwist p T) := by
  intro x y hxy
  simp only [markTwist, MonoidHom.finsetProd_apply]
  apply Finset.prod_congr rfl
  intro i hi
  apply coprimalityMask_periodic (p i) x y
  apply Ideal.mem_span_singleton.mpr
  exact (Finset.dvd_prod_of_mem p (hTS hi)).trans (Ideal.mem_span_singleton.mp hxy)

def markedThetaQuotient (p : ι → Eis) (S : Finset ι) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) : ℂ :=
  fixedThetaQuotient Ψ c x * ∏ i ∈ S, if p i ∣ Quotient.out x then 1 else 0

theorem markedThetaQuotient_twists (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i)) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) :
    markedThetaQuotient p S Ψ c x =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * fixedThetaQuotient (markTwist p T * Ψ) c x := by
  have hmark (i : ι) (hi : i ∈ S) :
      (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
        1 - coprimalityMask (p i) (Quotient.out x) := by
    change (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
      1 - (if IsCoprime (p i) (Quotient.out x) then 1 else 0)
    rw [(hp i hi).coprime_iff_not_dvd]
    by_cases h : p i ∣ Quotient.out x <;> simp [h]
  unfold markedThetaQuotient
  rw [Finset.prod_congr rfl hmark, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show markTwist p T * Ψ = Ψ * markTwist p T from mul_comm _ _]
  simp only [fixedThetaQuotient, fixedThetaTwist_mul, markTwist, MonoidHom.finsetProd_apply]
  ring


end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
noncomputable local instance mixedQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι]

def unmarkedSexticTwist (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) : Eis →* ℂ where
  toFun n := ∏ i ∈ (Finset.univ : Finset ι) \ S,
    (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

def mixedPrimeFunction (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (i : ι) (x : Eis ⧸ Ideal.span {p i}) : ℂ :=
  if i ∈ S then zeroMark x else (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i) x

theorem unmarkedSexticTwist_norm (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    ‖unmarkedSexticTwist p hg j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S,
    (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one (fun i hi => norm_nonneg _)
    (fun i hi => FiniteRayExpansion.norm_char_le_one _ _)

theorem unmarkedSexticTwist_periodic (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i, p i}) (unmarkedSexticTwist p hg j S) := by
  intro x y hxy
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (Ideal.span {p i}) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hxy)
  rw [he]

theorem mixedPrimeFunction_product (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    (∏ i, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      unmarkedSexticTwist p hg j S n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if p i ∣ n then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, zeroMark,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

omit [Fintype ι] in
theorem markedThetaQuotient_mk (p : ι → Eis) (S : Finset ι)
    (Ψ : Eis →* ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (n : Eis) :
    markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n) =
      fixedThetaTwist Ψ n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  unfold markedThetaQuotient
  have hcbase : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q :=
    hcQ.trans (Ideal.mul_mono_right Ideal.mul_le_right)
  rw [fixedThetaQuotient_mk Ψ Q hΨ c hcbase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hxy : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n ∈ Ideal.span {c} :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) n))
  have hp : p i ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n :=
    (Finset.dvd_prod_of_mem p hi).trans (Ideal.mem_span_singleton.mp
      (Ideal.mul_le_left (Ideal.mul_le_left (hcQ hxy))))
  simp only [dvd_iff_dvd_of_dvd_sub hp]

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
theorem cusp_kernel_sum_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ n : Eis,
      (∑ i, w i * tracePhase (-cuspFrequency n * (d i).point)) =
        ∑ k, z k * tracePhase (-cuspFrequency n * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) = ∑ k, z k * (e k).smoothedKernel W X := by
  have hcoeff:Summable (fun n:Eis=>‖sourceBarRadialCoefficient 0 n‖*
      sourceCuspRadialLength n^(-(3/2:ℝ))) := by
    simpa only [show (1/2:ℝ)-2=-(3/2) by norm_num] using sourceBarRadialCoefficient_summable 0 2 le_rfl
  have hsum:=weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceBarRadialCoefficient 0) (3/2) hcoeff (Vstar W) lo hi hlo
    (Vstar_support W lo hi hsupp) (Vstar_contDiff W lo hi hlo hsupp hW) X hX
  simp_rw [SourceCuspDatum.smoothedKernel_source _ W lo hi hlo hsupp hW X hX]
  rw [sourceBar_smoothed_phase_translation _ _ _ hsum,
    sourceBar_smoothed_phase_translation _ _ _ hsum]
  simp_rw [hmult]

end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
variable {ι:Type*}
theorem markedCompletedT_canonical_reflection (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Ψ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΨ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_left hxy),
      hperiod x y (Ideal.mul_le_right hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp Ψ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedIdealT (markTwist p T * Ψ) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).smoothedKernel W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedIdealT_eq_completedT _ W hWcompact X hX, completedT_canonical_smoothed_reflection _ (hnorm T) _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
theorem markedCompletedT_of_cusp_multiplier {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ n : Eis, (∑ k, w k * tracePhase (-cuspFrequency n * (d k).point)) =
      markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ k, w k * (d k).smoothedKernel W X := by
  rw [markedCompletedT_canonical_reflection p S hp Ψ hΨ Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply cusp_kernel_sum_congr (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc)
      (markedThetaQuotient p S Ψ c)) d w ?_ W lo hi hlo hsupp hW X hX
  intro n
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]

end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CubicEisenstein CanonicalRowCompletion
noncomputable section
noncomputable local instance activeReflectionQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem markedCompletedT_fixed_active_strata {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (φ * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).smoothedKernel W X := by
  have hnorm (n : Eis) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_right hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_left hxy)]
  apply markedCompletedT_of_cusp_multiplier p S (fun i _ => hprime i) _ hnorm _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein  CubicKubota
open CubicJacobi   NormalizedReflection
noncomputable section
noncomputable local instance controlledField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis ⧸ P) := Ideal.Quotient.field _
noncomputable local instance controlledFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_phase_product (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) (x : Eis) :
    star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      tracePhase (-(ringComplex (D.matrix v 1 1) * (ringComplex x / (ringComplex traceLambda) ^ 4)) /
        (ringComplex c0 * ringComplex (∏ i, p i))) =
    (star D.fixedFactor * cuspBadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, frequencyMultiplier (complexSexticChar (Ideal.span {p i}) (hg i))
        (residueTraceQuotientChar 1 (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) (v i) := by
  have hpair:Pairwise (Function.onFun IsCoprime p) := by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have ht (i:ι):∃t:Eis,p i∣cuspPrimeCofactor p i*t-1 := by
    have hc:IsCoprime (p i) (cuspPrimeCofactor p i):=
      IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
    obtain ⟨a,b,hab⟩:=hc
    exact ⟨b,⟨-a,by linear_combination hab⟩⟩
  choose t ht using ht
  have he:=cuspMatrix_inverse_phase_product p t hp hpair ht c0 D.U D.w x hc0
    D.bezout (D.matrix v) (by rw [D.denominator];exact dvd_mul_left _ _)
    D.sigma D.epsilon v (D.frequency_congruence v) D.epsilon_value
  rw [cuspInverse_fixed_phase_congr c0 _ _ D.U x hc0 (D.inverse_fixed hN v)] at he
  rw [D.relative_character hN hr hbase v,star_mul,cuspSymbol_sextic_product p hg]
  simp_rw [D.frequency_congruence v]
  have he':tracePhase (-(ringComplex (D.matrix v 1 1)*(ringComplex x/(ringComplex traceLambda)^4))/
      (ringComplex c0*ringComplex (∏i,p i)))=
      cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U x*
        ∏i,(residueTraceQuotientChar 1 (p i) (hp i))
          (((D.epsilon i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*
            ((v i : Eis⧸Ideal.span {p i})⁻¹)) := by
    simpa only [cuspBadPhase_eq,div_eq_mul_inv,mul_inv_rev,Units.val_inv_eq_inv_val,neg_mul,mul_neg,mul_assoc,mul_comm,mul_left_comm] using he
  rw [he']
  simp only [frequencyMultiplier,Units.ne_zero,ite_false,map_mul,
    Units.val_inv_eq_inv_val,Finset.prod_mul_distrib]
  ring

def fullLocalFourierWeight [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) : ℂ :=
  ∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (F i) (v i)

theorem controlled_local_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ, fullLocalFourierWeight hp F v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      tracePhase (-(ringComplex (D.matrix v 1 1) * (ringComplex x / (ringComplex traceLambda) ^ 4)) /
        (ringComplex c0 * ringComplex (∏ i, p i)))) =
    (star D.fixedFactor * cuspBadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, ∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (F i) v *
          frequencyMultiplier (complexSexticChar (Ideal.span {p i}) (hg i))
            (residueTraceQuotientChar 1 (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_assoc, controlled_phase_product D hN hr hbase hp hc0 hcop hg v x]
  simp only [fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

theorem mixedActiveBracket_eq_units [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (D : ControlledStratumArithmetic p N a0 c0 mode) (i : ι) (x : Eis) :
    (∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (mixedPrimeFunction p hg j S i) v *
        frequencyMultiplier (complexSexticChar (Ideal.span {p i}) (hg i))
          (residueTraceQuotientChar 1 (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v) =
      mixedActiveBracket hp hg j S D i x := by
  have hh := actual_mixed_frequency_units (Ideal.span {p i}) (hg i) (hc i)
    (residueTraceQuotientChar 1 (p i) (hp i))
    (residueTraceQuotientChar_primitive (p i) (hp i))
    (decide (i ∈ S)) (j i) (hj i) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x)
  have hfun : mixedPrimeFunction p hg j S i = fun t =>
      if i ∈ S then zeroMark t else (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i) t := rfl
  rw [hfun]
  by_cases hi : i ∈ S
  · simpa only [hi, decide_true, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      ite_true, markedFrequencyRow] using hh
  · simpa only [hi, decide_false, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      Bool.false_eq_true, ite_false, frequencyRow] using hh

theorem controlled_mixed_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      tracePhase (-(ringComplex (D.matrix v 1 1) * (ringComplex x / (ringComplex traceLambda) ^ 4)) /
        (ringComplex c0 * ringComplex (∏ i, p i)))) =
    (star D.fixedFactor * cuspBadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, mixedActiveBracket hp hg j S D i x := by
  rw [controlled_local_multiplier D hN hr hbase hp hc0 hcop hg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact mixedActiveBracket_eq_units hp hg hc j hj S D i x

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein  CubicKubota CompletedDyadic
open CubicJacobi   NormalizedReflection
noncomputable section
noncomputable local instance dualQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def mixedSmoothedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

def mixedReflectedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) *
    ∑' t : ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1 *
          Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ)) *
      paperKernel (Vstar W)
        ((X / (27 * (sourceCuspScale s.index) ^ 2 * (Ideal.absNorm (Ideal.span {c0 * ∏ i, p i}) : ℝ) ^ 2)) *
          (ramifiedScale 1 completedRamifiedStep t.2.1) ^ 3 *
          (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) ^ 3) *
      ((star D.fixedFactor * cuspBadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))) *
        ∏ i, mixedActiveBracket hp hg j S D i
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem mixed_smoothed_eq_reflected (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  have hden : c0 * (∏ i, p i) ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hmat (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      (D.sourceGamma hN hr hbase v : SL(2, Eis)) *
        ControlledStratumArithmetic.fixedCusp a0 c0 mode = D.matrix v :=
    D.sourceGamma_mul hN hr hbase v
  have hchar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      extendedComplexCharacter (D.sourceGamma hN hr hbase v) =
        complexCharacter (D.relativeGamma hN hr hbase v) :=
    D.sourceGamma_character hN hr hbase v
  have hC : ∀ v, ((D.sourceGamma hN hr hbase v : SL(2, Eis)) *
      ControlledStratumArithmetic.fixedCusp a0 c0 mode) 1 0 = c0 * ∏ i, p i := by
    intro v
    exact (congrArg (fun M : SL(2, Eis) => M 1 0) (hmat v)).trans (D.denominator v)
  have he := s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hden hC
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) W lo hi hlo hsupp hW X hX
  change mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X = _ at he
  rw [he]
  unfold mixedReflectedValue
  apply congrArg (fun z : ℂ => fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) * z)
  apply tsum_congr
  intro t
  congr 1
  simpa only [hchar, hmat, map_mul] using
    controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end
end InverseMoment

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace InverseMoment
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
theorem mixedReflectedValue_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    mixedReflectedValue D s hp hc0 hg j S W X =
      (-1 : ℂ) ^ S.card * D.reflectedValue s hp hc0 hg (markedActiveExponent S j) W X := by
  unfold mixedReflectedValue ControlledStratumArithmetic.reflectedValue
  simp_rw [mixedActiveBracket_product]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  ring


end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
