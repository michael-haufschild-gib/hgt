/-
Reopened cube families adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.GlobalScalesAndNormCaps

/-!
# Reopened cube families

Reopened cube families `reopenedCubeFamily` and their pair coefficients. Cutoff tails have
polynomial numerators and arbitrary decay; integration absorbs the polynomial frequency loss;
canonical child bounds for the global bins.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b ∈ s, w b * ∑ z ∈ T b, ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t b z‖^2

theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (T : GlobalFirstData ι → Finset O) (N : ℕ) :
    Integrable (fun t => firstLogDensity N t * globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side r T t) volume := by
  simp only [globalFirstFiniteEnergy, Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool \ (b.cube.support ∪ b.common))
    b.firstCommon b.cube.support (fun i => b.cube.leftExponent i + b.cube.rightExponent i)
    b.cube.leftBit b.cube.rightBit side r Ψ m
    (normalizedColumn p (fun S => g (columnLog p (globalFirstBlockColumnScale p ell side b) S)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (∏ i ∈ b.common, p i) (∏ i ∈ b.firstDivisor, p i) z (firstLogDensity_integrable N)
  simpa only [globalFirstCoreRow, mul_left_comm] using hi.const_mul (w b)

/-- The cutoff tail has a polynomial numerator and arbitrary decay in its truncation parameter. -/
def globalFirstTailCost (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool) : ℝ :=
  (∑ b ∈ s, ‖w b‖ * (globalFirstTailLength p ell M side b)^4 *
    globalFirstPooledRow p K ell B F side b *
    (1 + (globalFirstTailLength p ell M side b)^3 / globalFirstPooledRow p K ell B F side b)^2) /
    (1+H)^N

theorem globalFirstTailCost_nonneg (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H) :
    0 ≤ globalFirstTailCost p s w K ell B F M H N side := by
  unfold globalFirstTailCost
  apply div_nonneg _ (pow_nonneg (by linarith) _)
  apply Finset.sum_nonneg
  intro b hb
  have hY : 0 < globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  positivity

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff

/-- Integration absorbs the polynomial frequency loss in the two reflected tests. -/
theorem globalFirstCoreRows_integrated_transfer
    (ε : ℝ) (hε : 0 < ε) (g V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Ct : ℝ), 0 ≤ C ∧ 0 < Ct ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀ i u, windows i u ≠ 0 → |u| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda^2 ∣ p i-1)
        (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
        (Γ K ell B F H : ℝ) (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
        (T : GlobalFirstData ι → Finset O),
      0 ≤ Γ → (∀ b ∈ s, 0 ≤ w b ∧ w b ≤ Γ) → 0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ H →
      (∀ b ∈ s, GlobalFirstAdmissible b) → (∀ a, ‖Ψ a‖ ≤ 1) →
      (∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2 ≤ B) →
      (∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2 ≤ B) →
      (∀ b ∈ s, ∀ z ∈ T b, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ globalFirstPooledRow p K ell B F side b) →
      let source := globalFirstSupportedPool p pool s
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b * globalFirstCoefficient p K ell B F side b
      let I := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
      (∫ t, firstLogDensity (2*(J+2)) t *
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side r T t) ≤
      (∫ t, firstLogDensity 0 t) *
        (globalFirstDiagonalCost p hg pool s (fun b => (weight b : ℂ)) Ψ m
            (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
          globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F I A J side +
          Ct * globalFirstTailCost p s (fun b => (weight b : ℂ)) K ell B F M H N side) := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,hsource⟩ :=
    full_uniform_globalFirstTruncatedSource_bound g V rowMajorant M hM hgM side ε hε A J
  obtain ⟨Ct,hCt,htail⟩ := globalFirstSourceTail_bound N g V rowMajorant
  refine ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hc hpr pool s w Γ K ell B F H Ψ m r T
    hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT
  dsimp only
  let cutoff := globalFirstConcreteCutoff p K ell B F M H side
  let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
  let weight := fun b => w b * globalFirstCoefficient p K ell B F side b
  let I := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let Y := globalFirstPooledRow p K ell B F side
  let d := globalFirstDiagonalCost p hg pool s (fun b => (weight b : ℂ)) Ψ m
    (firstCoreBaseProfile g V side) rowMajorant ell side Y
  let c := globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F I A J side
  let q := Ct * globalFirstTailCost p s (fun b => (weight b : ℂ)) K ell B F M H N side
  have hY (b : GlobalFirstData ι) (_ : b ∈ s) : 0 < Y b :=
    globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hweight (b : GlobalFirstData ι) (hb : b ∈ s) : 0 ≤ weight b :=
    mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hI : ∀ x ∈ source, globalScaleIndex p side x ∈ I :=
    globalFirstSupportedPool_index_mem_box p hp pool s hs K ell B F M H hK hell hB hF hH side hb₁ hb₂
  have hd : 0 ≤ d := globalFirstDiagonalCost_nonneg p hp hg pool s _ Ψ m _ rowMajorant ell side Y
  have hq : 0 ≤ q := mul_nonneg hCt.le
    (globalFirstTailCost_nonneg p s _ K ell B F M H N side hK hell hB hF hH)
  have hpoint (t : ℝ) : globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side r T t ≤
      1 * (d + ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c + q) := by
    have hn := hsource p hp hg hinj hc hpr pool s (fun b => (w b : ℂ)) Ψ m Γ K ell B F t r
      cutoff I hΓ (fun b hb => by simpa only [Complex.norm_real, Real.norm_of_nonneg (hw b hb).1] using (hw b hb).2)
      hK hell hB hF hΨ hs hI
    have hz := globalFirstFiniteEnergy_le_nonzero_diagonal_tail p hp hg hinj pool s weight hweight
      Ψ m g V ell hell side r t Y hY T hT cutoff
      (fun b hb G hG E hE => zero_mem_secondTailCutoff _ _ _)
    have ht := htail p hp hg hinj pool s (fun b => (weight b : ℂ)) Ψ m ell M H side r t Y
      hΨ hell hH hgM hY
    have ht' : ‖globalFirstSourceTail p hp hg pool s (fun b => (weight b : ℂ)) Ψ m g V rowMajorant
        ell side r t Y cutoff‖ ≤ q := by
      exact ht.trans_eq (by dsimp only [q, globalFirstTailCost, Y]; ring)
    have hn' : ‖globalFirstTruncatedSource p hp hg pool s (fun b => (weight b : ℂ)) Ψ m g V rowMajorant
        ell side r t Y (fun b G E => (cutoff b G E).erase 0)‖ ≤
        ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c := by
      simpa only [weight, Complex.ofReal_mul, ← pow_add, show J+2+(J+2)=2*(J+2) by omega] using hn
    exact hz.trans ((add_le_add (add_le_add hn' (le_refl d)) ht').trans_eq (by ring))
  have hi := integral_pair_moment_bound J (globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side r T)
    (globalFirstFiniteEnergy_integrable p hg pool s weight Ψ m g V ell side r T (2*(J+2)))
    1 d c q (by norm_num) hd hq hpoint
  simpa only [mul_one] using hi

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem inputConjugateRow_zero_of_mass_zero (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (hm : (∑ S ∈ F.powerset, ‖secondInputCoefficient p χ Ψ m c d H S‖^2) = 0) (z : O) :
    inputConjugateRow p χ F Ψ m c d H z = 0 := by
  unfold inputConjugateRow supportConjugateSum
  apply Finset.sum_eq_zero
  intro S hS
  have hle : ‖secondInputCoefficient p χ Ψ m c d H S‖^2 ≤ 0 := by
    rw [← hm]
    exact Finset.single_le_sum (f := fun A => ‖secondInputCoefficient p χ Ψ m c d H A‖^2)
      (fun A _ => sq_nonneg _) hS
  have hz : secondInputCoefficient p χ Ψ m c d H S = 0 := by
    apply norm_eq_zero.mp
    nlinarith only [hle, norm_nonneg (secondInputCoefficient p χ Ψ m c d H S)]
  simp only [hz, mul_zero, zero_mul]

include hp in
/-- Outside the compact logarithmic support every first-pass coefficient vanishes. -/
theorem globalFirstCoreRow_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ)) (ell M U : ℝ) (hell : 0 < ell)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (hU : ell * Real.exp M ≤ U)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ) (z : O)
    (hoff : ¬(primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U)) :
    globalFirstCoreRow p hg pool Ψ m g V ell side r t b z = 0 := by
  have hbase : ∀ u, firstCoreBaseProfile g V side u ≠ 0 → |u| ≤ M := by
    intro u hu
    apply hgM u
    intro hz
    exact hu (by simp only [firstCoreBaseProfile_apply, hz, zero_mul])
  have hm := globalFirstInput_mass_le p hp hg pool b Ψ m g V ell hell side r t
  rw [globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m (firstCoreBaseProfile g V side)
    ell M U hell hbase hU side hoff, mul_zero] at hm
  rw [globalFirstCoreRow_eq_input]
  exact inputConjugateRow_zero_of_mass_zero p _ _ Ψ _ _ _ _
    (le_antisymm hm (Finset.sum_nonneg (fun S hS => sq_nonneg _))) z

include hp in
theorem globalFirstFiniteEnergy_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ))
    (ell M U : ℝ) (hell : 0 < ell) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (hU : ell * Real.exp M ≤ U) (side : Bool) (r : QuadraticRayRing)
    (T : GlobalFirstData ι → Finset O) (t : ℝ) :
    globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side r T t =
      globalFirstFiniteEnergy p hg pool
        (s.filter (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U))
        w Ψ m g V ell side r T t := by
  unfold globalFirstFiniteEnergy
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U) :=
    fun hh => hn (Finset.mem_filter.mpr ⟨hb, hh⟩)
  have hz (z : O) := globalFirstCoreRow_zero_off_support p hp hg pool b Ψ m g V
    ell M U hell hgM hU side r t z hoff
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
section
def globalFirstTailFactor (K ell B F U H : ℝ) (N : ℕ) : ℝ :=
  (1+U)^4*(1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2)))^2/(1+H)^N

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_lower_from_common (b : GlobalFirstData ι)
    (K ell B F U : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 0<U)
    (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    ell^2*B^2*F^2/(K*U^2)≤globalFirstPooledRow p K ell B F side b := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1≤U := (globalScaleIndex_bounds p hp side x one_ne_zero 1).1.trans hc
  have hJ := globalPooled_J_bound p hp B hB.le side x one_ne_zero hb1 hb2
  have hcp := globalLogRep_pos j 1
  have hjp := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  change _≤Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  calc
    _ = ell^2*B^4*F^2/(K*U^2*B^2) := by field_simp
    _ ≤ _ := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in
theorem globalFirstTailFactor_bound (b : GlobalFirstData ι)
    (K ell B F M U H : ℝ) (N : ℕ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 1≤U) (hH : 0≤H)
    (hellU : ell*Real.exp M≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    lengthScale^4*(1+lengthScale^3/Y)^2/(1+H)^N≤globalFirstTailFactor K ell B F U H N := by
  dsimp only
  let X := globalFirstBlockColumnScale p ell side b
  let Y := globalFirstPooledRow p K ell B F side b
  have ha := primeProductNorm_ge_one p hp (b.cube.sideDivisor side)
  have hc1 := primeProductNorm_ge_one p hp b.common
  have ht := primeProductNorm_ge_one p hp b.firstCommon
  have hX : 0<X := by
    dsimp [X,globalFirstBlockColumnScale]
    positivity
  have hXle : X≤ell := by
    dsimp [X,globalFirstBlockColumnScale]
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc1)
  have hL : 1+X*Real.exp M≤1+U := add_le_add le_rfl ((mul_le_mul_of_nonneg_right hXle (Real.exp_pos _).le).trans hellU)
  have hY : 0<Y := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hlower := globalFirstPooledRow_lower_from_common p hp b K ell B F U hK hell hB hF (by linarith) hc hb1 hb2 side
  have hinv : 1/Y≤K*U^2/(ell^2*B^2*F^2) := by
    have h := one_div_le_one_div_of_le (by positivity : 0<ell^2*B^2*F^2/(K*U^2)) hlower
    simpa only [one_div_div] using h
  have hratio : (1+X*Real.exp M)^3/Y≤(1+U)^3*(K*U^2/(ell^2*B^2*F^2)) := by
    calc
      _ = (1+X*Real.exp M)^3*(1/Y) := by ring
      _ ≤ _ := by gcongr
  change (1+X*Real.exp M)^4*(1+(1+X*Real.exp M)^3/Y)^2/(1+H)^N≤_
  unfold globalFirstTailFactor
  gcongr

end

open Eisenstein
open FirstPassCubeLabels (primeProduct cubeActiveSupport)


theorem globalFirstWeightedVolume_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,w b*globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  refine ⟨Cd*(Real.exp 1)^3*Cp,by positivity,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hC ht hb1 hb2
  have hB0 : 0<B := by linarith
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖ringComplex (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have hsum := hcount p hp hinj s B U hB hU hs hC ht hb1 hb2
  change (∑b∈s,θ b)≤_ at hsum
  have hterm (b : GlobalFirstData ι) (hb : b∈s) :
      w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤(Γ*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := primeProductNorm_pos p hp b.firstCommon
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = w b*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ Γ*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := mul_le_mul_of_nonneg_right (hw b hb).2 (by positivity)
      _ ≤ Γ*(((Real.exp 1)^3*ell*B^2*F)*θ b) := mul_le_mul_of_nonneg_left hsc' hΓ
      _ = _ := by ring
  calc
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*(∑b∈s,θ b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ = _ := by ring


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

/-- The common-divisor normalization costs at most its support bound in the coarse cutoff tail. -/
theorem globalFirstTailCost_parent_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F M U H : ℝ) (N : ℕ) (side : Bool),
      0 ≤ Γ → 0 < K → 0 < ell → 1 ≤ B → 0 < F → 1 ≤ U → 0 ≤ H → ell * Real.exp M ≤ U →
      (∀ b ∈ s, 0 ≤ w b ∧ w b ≤ Γ) → (∀ b ∈ s, GlobalFirstAdmissible b) →
      (∀ b ∈ s, primeProductNorm p b.common ≤ U) → (∀ b ∈ s, primeProductNorm p b.firstCommon ≤ U) →
      (∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2 ≤ B) →
      (∀ b ∈ s, ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2 ≤ B) →
      globalFirstTailCost p s (fun b => ((w b * globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        K ell B F M H N side ≤ C * Γ * (ell*B^3*F) * (B*U)^ε * (U * globalFirstTailFactor K ell B F U H N) := by
  obtain ⟨C,hC,hvolume⟩ := globalFirstWeightedVolume_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F M U H N side
    hΓ hK hell hB hF hU hH hellU hw hs hCnorm ht hb₁ hb₂
  have hB0 : 0 < B := by linarith
  have hfactor : 0 ≤ globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hv := hvolume p hp hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hCnorm ht hb₁ hb₂
  apply le_trans _ (mul_le_mul_of_nonneg_right hv (mul_nonneg (by linarith) hfactor))
  unfold globalFirstTailCost
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  have hc : 0 ≤ globalFirstCoefficient p K ell B F side b :=
    globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
  have hY : 0 < globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
  have hT := primeProductNorm_pos p hp b.firstCommon
  have hw0 := (hw b hb).1
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hw0 hc)]
  have h := globalFirstTailFactor_bound p hp b K ell B F M U H N hK hell hB0 hF hU hH
    hellU (hCnorm b hb) (hb₁ b hb) (hb₂ b hb) side
  change (globalFirstTailLength p ell M side b)^4 *
      (1 + (globalFirstTailLength p ell M side b)^3 / globalFirstPooledRow p K ell B F side b)^2 /
      (1+H)^N ≤ globalFirstTailFactor K ell B F U H N at h
  have h' := mul_le_mul_of_nonneg_left h
    (show 0 ≤ w b * globalFirstCoefficient p K ell B F side b * globalFirstPooledRow p K ell B F side b by positivity)
  have hTU : 1 ≤ (primeProductNorm p b.firstCommon)⁻¹ * U := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (one_le_div hT).mpr (ht b hb)
  calc
    _ ≤ (w b * globalFirstCoefficient p K ell B F side b * globalFirstPooledRow p K ell B F side b) *
        globalFirstTailFactor K ell B F U H N := by
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h'
    _ ≤ (w b * globalFirstCoefficient p K ell B F side b * globalFirstPooledRow p K ell B F side b) *
        globalFirstTailFactor K ell B F U H N * ((primeProductNorm p b.firstCommon)⁻¹ * U) :=
      le_mul_of_one_le_right (by positivity) hTU
    _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff

theorem globalFirstCoreRows_quantitative_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      let activeFamily := s.filter (fun b => primeProductNorm p b.common≤U ∧
        primeProductNorm p b.firstCommon≤U)
      let source := globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (Cd*Γ*(ell*B^3*F)*(B*U)^ε +
          globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F (globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)) A J side +
          Ct*Γ*(ell*B^3*F)*(B*U)^ε*(U*globalFirstTailFactor K ell B F U H N)) := by
  have hbase : ∀t,firstCoreBaseProfile g V side t≠0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    apply ht
    simp only [firstCoreBaseProfile_apply,hz,zero_mul]
  obtain ⟨windows,C,Ct0,hC,hCt0,hwc,hws,hwb,hrows⟩ :=
    globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  obtain ⟨Cd,hCd,hdiag⟩ := globalFirstDiagonalCost_parent_bound ε hε
    (firstCoreBaseProfile g V side) rowMajorant M hbase
  obtain ⟨Ct1,hCt1,htail⟩ := globalFirstTailCost_parent_bound ε hε
  refine ⟨windows,C,Cd,Ct0*Ct1,hC,hCd,mul_pos hCt0 hCt1,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hc hpr pool s w Γ K ell B F H U Ψ m r T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT
  dsimp only
  have hB0 : 0<B := by linarith
  let activeFamily := s.filter (fun b => primeProductNorm p b.common≤U ∧
    primeProductNorm p b.firstCommon≤U)
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  have hsub (b : GlobalFirstData ι) (hb : b∈activeFamily) : b∈s := (Finset.mem_filter.mp hb).1
  have hΓw := fun b hb => hw b (hsub b hb)
  have hsa := fun b hb => hs b (hsub b hb)
  have hba1 := fun b hb => hb1 b (hsub b hb)
  have hba2 := fun b hb => hb2 b (hsub b hb)
  have hr := hrows p hp hg hinj hc hpr pool activeFamily w Γ K ell B F H Ψ m r T
    hΓ hΓw hK hell hB0 hF hH hsa hΨ hba1 hba2
    (fun b hb => hT b (hsub b hb))
  dsimp only at hr
  have hd := hdiag p hp hg hinj pool activeFamily w Ψ m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨ hΓw hsa hba1 hba2
  have ht := htail p hp hinj activeFamily w Γ K ell B F M U H N side
    hΓ hK hell hB hF hU hH hellU hΓw hsa
    (fun b hb => (Finset.mem_filter.mp hb).2.1) (fun b hb => (Finset.mem_filter.mp hb).2.2) hba1 hba2
  have heq :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side r T t)=
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool activeFamily weight Ψ m g V ell side r T t) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [globalFirstFiniteEnergy_eq_supported p hp hg pool s weight Ψ m g V ell M U hell hgM hellU side r T t]
  rw [heq]
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun t => firstLogDensity_nonneg 0 t))
  have ht' := mul_le_mul_of_nonneg_left ht hCt0.le
  have h := add_le_add (add_le_add hd (le_refl
    (globalChildBudget p hg pool
      (globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side)
      Ψ m windows (Γ*C) ε K ell B F (globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)) A J side))) ht'
  convert h using 1 <;> (try dsimp only [weight]) <;> ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

def globalCubeCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalCubeBlock ι) : ℝ :=
  globalFirstCoefficient p K ell B F side (b.withCommon ∅)

theorem globalFirstCoefficient_block (K ell B F : ℝ) (side : Bool) (d : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side d = globalCubeCoefficient p K ell B F side d.block := by
  simp [globalFirstCoefficient, globalCubeCoefficient, globalBinFirstCoefficient, globalFirstIndex,
    globalScaleIndex, globalScaleVector, globalLogRep, GlobalFirstData.append,
    GlobalCubeBlock.withCommon, GlobalFirstData.block, globalCubeActiveRoot,
    Matrix.cons_val_zero, Matrix.cons_val_succ]

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem globalFirstFiniteEnergy_integral_sum
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool)
    (r : QuadraticRayRing) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    (∫ t, firstLogDensity J t * globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side r T t) =
      ∑ d ∈ s, w d * ∫ t, firstLogDensity J t * ∑ z ∈ T d,
        ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t d z‖^2 := by
  have hi (d : GlobalFirstData ι) : Integrable (fun t => firstLogDensity J t *
      ∑ z ∈ T d, ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t d z‖^2) := by
    simpa only [globalFirstFiniteEnergy, Finset.sum_singleton, one_mul] using
      globalFirstFiniteEnergy_integrable p hg pool {d} (fun _ => 1) Ψ m g V ell side r T J
  have he (t : ℝ) : firstLogDensity J t * globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side r T t =
      ∑ d ∈ s, w d * (firstLogDensity J t * ∑ z ∈ T d, ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t d z‖^2) := by
    simp only [globalFirstFiniteEnergy, Finset.mul_sum, mul_left_comm]
  simp_rw [he]
  rw [integral_finsetSum _ (fun d hd => (hi d).const_mul (w d))]
  simp only [integral_const_mul]

/-- Reindexing common divisors turns the first-pass family into integrated global rows. -/
theorem globalCubeInputFamilyEnergy_eq_integrated_rows
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (w : GlobalCubeBlock ι → ℝ)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ)) (K ell B F : ℝ) (side : Bool) (J : ℕ)
    (T : GlobalCubeBlock ι → Finset O) :
    (∑ b ∈ blocks, w b * globalCubeCoefficient p K ell B F side b *
      globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side J (T b)) =
    ∑ r : QuadraticRayRing × QuadraticRayRing, 2 *
      ∫ t, firstLogDensity J t * globalFirstFiniteEnergy p hg pool (globalFirstFamilySet pool blocks)
        (fun d => w d.block * globalFirstCoefficient p K ell B F side d)
        Ψ m g V ell side (if side then r.1 else r.2) (fun d => T d.block) t := by
  simp_rw [globalFirstFiniteEnergy_integral_sum, sum_globalFirstFamilySet]
  simp only [globalCubeInputFamilyEnergy, firstInputFamilyEnergy, Finset.mul_sum]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro D hD
  rw [globalFirstCoefficient_block]
  simp only [GlobalCubeBlock.withCommon, GlobalFirstData.block, globalFirstCoreRow,
    globalCubePool, globalCubeColumnScale, globalFirstBlockColumnScale]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff

theorem globalFirstPooledRow_block {ι : Type*} [DecidableEq ι] (p : ι → O)
    (K ell B F : ℝ) (side : Bool) (d : GlobalFirstData ι) :
    globalFirstPooledRow p K ell B F side d =
      globalFirstPooledRow p K ell B F side (d.block.withCommon ∅) := by
  simp [globalFirstPooledRow, globalPooledRowScale, globalFirstIndex, globalScaleIndex,
    globalScaleVector, globalLogRep, GlobalFirstData.append, GlobalCubeBlock.withCommon,
    GlobalFirstData.block, globalCubeJNorm, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- All first-pass residues share the same quantitative descendant bound. -/
theorem globalCubeInputFamilyEnergy_quantitative_transfer
    (ε : ℝ) (hε : 0 < ε) (g V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ), 0 ≤ C ∧ 0 < Cd ∧ 0 < Ct ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀ i u, windows i u ≠ 0 → |u| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda^2 ∣ p i-1)
        (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (w : GlobalCubeBlock ι → ℝ)
        (Γ K ell B F H U : ℝ) (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0 ≤ Γ → (∀ b ∈ blocks, 0 ≤ w b ∧ w b ≤ Γ) →
      0 < K → 0 < ell → 1 ≤ B → 0 < F → 0 ≤ H → 1 ≤ U → ell * Real.exp M ≤ U →
      (∀ b ∈ blocks, GlobalCubeAdmissible b) → (∀ a, ‖Ψ a‖ ≤ 1) →
      (∀ b ∈ blocks, ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2 ≤ B) →
      (∀ b ∈ blocks, ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2 ≤ B) →
      (∀ b ∈ blocks, ∀ z ∈ T b, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤
        globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      let family := (globalFirstFamilySet pool blocks).filter
        (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U)
      let source := globalFirstSupportedPool p pool family
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let I := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
      (∑ b ∈ blocks, w b * globalCubeCoefficient p K ell B F side b *
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b)) ≤
      (2 * (Fintype.card (QuadraticRayRing × QuadraticRayRing) : ℝ)) *
        (∫ t, firstLogDensity 0 t) *
        (Cd * Γ * (ell*B^3*F) * (B*U)^ε +
          globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F I A J side +
          Ct * Γ * (ell*B^3*F) * (B*U)^ε * (U * globalFirstTailFactor K ell B F U H N)) := by
  obtain ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,hrows⟩ :=
    globalFirstCoreRows_quantitative_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ m T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb₁ hb₂ hT
  dsimp only
  have hblock (d : GlobalFirstData ι) (hd : d ∈ globalFirstFamilySet pool blocks) : d.block ∈ blocks :=
    ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  have hrows' (r : QuadraticRayRing) := hrows p hp hg hinj hc hpr pool (globalFirstFamilySet pool blocks)
    (fun d => w d.block) Γ K ell B F H U Ψ m r (fun d => T d.block)
    hΓ (fun d hd => hw d.block (hblock d hd)) hK hell hB hF hH hU hellU
    (fun d hd => hs d.block (hblock d hd)) hΨ
    (fun d hd => hb₁ d.block (hblock d hd)) (fun d hd => hb₂ d.block (hblock d hd))
    (fun d hd z hz => by rw [globalFirstPooledRow_block p K ell B F side d]; exact hT d.block (hblock d hd) z hz)
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  apply (Finset.sum_le_sum (fun r _ =>
    mul_le_mul_of_nonneg_left (hrows' (if side then r.1 else r.2)) (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem globalCutoffRatio_le (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M≤U^8 := by
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hden : 1≤B^2*F^2 := by nlinarith [sq_nonneg (B-1),sq_nonneg (F-1)]
  have he : H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M =
      (H*K*ell^2*(Real.exp M)^4)/(B^2*F^2) := by
    unfold globalRowScaleFloor
    field_simp

  rw [he]
  calc
    _ ≤ H*K*ell^2*(Real.exp M)^4 := div_le_self (by positivity) hden
    _ ≤ U*U*U^2*U^4 := by gcongr
    _ = U^8 := by ring

theorem globalNormCaps_polynomial (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ∀i, 0≤globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i ∧
      globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i≤27*U^22 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hratio := globalCutoffRatio_le K ell B F M H U hU hK hell hB hF hH hKU hellU hHU heU
  have hY := globalRowScaleFloor_pos K ell B F M hK hell hB0 hF0
  have hrow : H*(ell*Real.exp M)^2*B^2*(1+ell*Real.exp M)^3 /
      globalRowScaleFloor K ell B F M ≤ 27*U^22 := by
    have hL' : 1+ell*Real.exp M ≤ 2*U^2 := by linarith [one_le_pow₀ hU (n:=2)]
    calc
      _ = (H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M)*B^2*(1+ell*Real.exp M)^3 := by ring
      _ ≤ U^8*U^2*(2*U^2)^3 := by gcongr
      _ = 8*U^16 := by ring
      _ ≤ 27*U^22 := by
        calc
          _ ≤ 8*U^22 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (by omega)) (by norm_num)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hU0.le _)
  have hpow2 : U^2≤27*U^22 := by
    calc
      U^2 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hpow4 : U^4≤27*U^22 := by
    calc
      U^4 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hB2 : B^2≤27*U^22 := (pow_le_pow_left₀ hB0.le hBU 2).trans hpow2
  have hLB : (ell*Real.exp M)*B^2≤27*U^22 := by
    calc
      _ ≤ U^2*U^2 := by gcongr
      _ = U^4 := by ring
      _ ≤ _ := hpow4
  have hL0 : 0 ≤ ell*Real.exp M := mul_nonneg hell.le (Real.exp_pos M).le
  have hLB0 : 0 ≤ (ell*Real.exp M)*B^2 := mul_nonneg hL0 (sq_nonneg B)
  have hrow0 : 0 ≤ H*(ell*Real.exp M)^2*B^2*(1+ell*Real.exp M)^3 /
      globalRowScaleFloor K ell B F M := by positivity
  intro i
  fin_cases i
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨sq_nonneg B, hB2⟩
  · exact ⟨hLB0, hLB⟩
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨hL0, hL.trans hpow2⟩
  · exact ⟨hrow0, hrow⟩
  · exact ⟨sq_nonneg B, hB2⟩

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0≤x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  by_cases hx0 : x=0
  · simpa [hx0, normLogBin] using Real.log_nonneg hY
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono (lt_of_le_of_ne hx (Ne.symm hx0)) hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

theorem globalLogBox_card_le_log (caps : Fin 10 → ℝ) (Y : ℝ) (hY : 1≤Y)
    (hcaps : ∀i,0≤caps i ∧ caps i≤Y) :
    ((globalLogBox caps).card:ℝ)≤(1+Real.log Y)^10 := by
  calc
    ((globalLogBox caps).card:ℝ) = ∏i : Fin 10,((normLogBin (caps i):ℝ)+1) := by
      rw [globalLogBox_card]
      push_cast
      rfl
    _ ≤ ∏_i : Fin 10,(1+Real.log Y) := by
      apply Finset.prod_le_prod (by intro i _; positivity)
      intro i _
      linarith [normLogBin_le_log_upper (caps i) Y (hcaps i).1 (hcaps i).2 hY]
    _ = (1+Real.log Y)^10 := by simp

theorem globalLogBox_card_polynomial_log (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤
      (1+Real.log 27+22*Real.log U)^10 := by
  have hU0 : 0<U := by linarith
  have hY : 1≤27*U^22 := by nlinarith [one_le_pow₀ hU (n:=22)]
  have hh := globalLogBox_card_le_log _ (27*U^22) hY
    (globalNormCaps_polynomial K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU)
  have he : 1+Real.log (27*U^22)=1+Real.log 27+22*Real.log U := by
    rw [Real.log_mul (by norm_num : (27:ℝ)≠0) (pow_ne_zero 22 hU0.ne'),Real.log_pow]
    norm_num
    ring
  rwa [he] at hh

theorem globalLogRep_le_upper (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1

def globalBinLossScale (B : ℝ) (j : GlobalLogIndex) : ℝ :=
  globalPooledLabelScale j*(B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4)

theorem globalBinLossScale_cancel (B : ℝ) (j : GlobalLogIndex) :
    globalBinLossScale B j = Real.exp 5*globalLogRep j 1*globalLogRep j 6*
      globalLogRep j 7*B*Real.sqrt (globalLogRep j 9) := by
  have hj := (globalLogRep_pos j 4).ne'
  have he : Real.exp 5=Real.exp 4*Real.exp 1 := by rw [←Real.exp_add]; norm_num
  rw [he]
  unfold globalBinLossScale globalPooledLabelScale
  field_simp

theorem globalBinLossScale_polynomial (ell B Y M H U : ℝ)
    (hU : 1≤U) (hell : 0<ell) (hB : 1≤B)
    (hellU : ell≤U) (hBU : B≤U) (heU : Real.exp M≤U)
    (j : GlobalLogIndex) (hj : j∈globalLogBox (globalNormCaps ell B Y M H)) :
    globalBinLossScale B j≤Real.exp 5*U^8 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hL0 : 0<ell*Real.exp M := by positivity
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hpow2 : 1≤U^2 := one_le_pow₀ hU
  have h1 : globalLogRep j 1≤U^2 := globalLogRep_le_upper _ j hj 1 (U^2) hL0 hL hpow2
  have h6 : globalLogRep j 6≤U^2 := globalLogRep_le_upper _ j hj 6 (U^2) hL0 hL hpow2
  have h7 : globalLogRep j 7≤U^2 := globalLogRep_le_upper _ j hj 7 (U^2) hL0 hL hpow2
  have h9 : globalLogRep j 9≤U^2 := globalLogRep_le_upper _ j hj 9 (U^2) (by simp [globalNormCaps]; positivity)
    (by simpa [globalNormCaps] using pow_le_pow_left₀ hB0.le hBU 2) hpow2
  have hsqrt : Real.sqrt (globalLogRep j 9)≤U := Real.sqrt_le_iff.mpr ⟨hU0.le,h9⟩
  rw [globalBinLossScale_cancel]
  calc
    _ ≤ Real.exp 5*U^2*U^2*U^2*U*U := by
      gcongr
      all_goals exact (globalLogRep_pos j _).le
    _ = Real.exp 5*U^8 := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem globalLogFactor_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1≤U →
      (1+Real.log 27+22*Real.log U)^10≤C*U^ε := by
  let deltaLoss := ε/10
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let C0 := 1+Real.log 27+22/deltaLoss
  have hlog : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  refine ⟨C0^10,by positivity,?_⟩
  intro U hU
  have hU0 : 0<U := by linarith
  have hR : 1≤U^deltaLoss := Real.one_le_rpow hU hδ.le
  have hb : Real.log U≤U^deltaLoss/deltaLoss := Real.log_le_rpow_div hU0.le hδ
  have hs : 1+Real.log 27+22*Real.log U≤C0*U^deltaLoss := by
    calc
      _ ≤ (1+Real.log 27)*U^deltaLoss+22*(U^deltaLoss/deltaLoss) := add_le_add
        (le_mul_of_one_le_right (by linarith) hR)
        (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = C0*U^deltaLoss := by dsimp [C0]; ring
  have hs0 : 0≤1+Real.log 27+22*Real.log U := by
    have hu := Real.log_nonneg hU
    positivity
  calc
    _ ≤ (C0*U^deltaLoss)^10 := pow_le_pow_left₀ hs0 hs 10
    _ = C0^10*U^ε := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
      dsimp [deltaLoss]
      congr 1
      ring

theorem globalLogBox_card_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  exact (globalLogBox_card_polynomial_log K ell B F M H U hU hK hell hB hF hH
    hKU hellU hBU hHU heU).trans (hbound U hU)

theorem globalLogBox_total_loss (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∑j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinLossScale B j)^η)≤C*U^(ε+8*η) := by
  obtain ⟨C,hC,hcard⟩ := globalLogBox_card_small_power ε hε
  refine ⟨C*(Real.exp 5)^η,by positivity,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  have hU0 : 0<U := by linarith
  let S := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  have hbound (j : GlobalLogIndex) (hj : j∈S) :
      (globalBinLossScale B j)^η≤(Real.exp 5)^η*U^(8*η) := by
    have hb := globalBinLossScale_polynomial ell B (globalRowScaleFloor K ell B F M) M H U
      hU hell hB hellU hBU heU j hj
    have hnonneg : 0≤globalBinLossScale B j := by
      rw [globalBinLossScale_cancel]
      have h1 := (globalLogRep_pos j 1).le
      have h6 := (globalLogRep_pos j 6).le
      have h7 := (globalLogRep_pos j 7).le
      positivity
    apply (Real.rpow_le_rpow hnonneg hb hη).trans_eq
    rw [Real.mul_rpow (Real.exp_pos _).le (by positivity)]
    congr 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
    norm_num
  calc
    _ ≤ ∑_j∈S,((Real.exp 5)^η*U^(8*η)) := Finset.sum_le_sum hbound
    _ = (S.card:ℝ)*((Real.exp 5)^η*U^(8*η)) := by simp
    _ ≤ (C*U^ε)*((Real.exp 5)^η*U^(8*η)) :=
      mul_le_mul_of_nonneg_right (hcard K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) (by positivity)
    _ = (C*(Real.exp 5)^η)*U^(ε+8*η) := by rw [Real.rpow_add hU0]; ring

theorem globalBinLossScale_nonneg (B : ℝ) (hB : 0≤B) (j : GlobalLogIndex) :
    0≤globalBinLossScale B j := by
  rw [globalBinLossScale_cancel]
  have h1 := (globalLogRep_pos j 1).le
  have h6 := (globalLogRep_pos j 6).le
  have h7 := (globalLogRep_pos j 7).le
  positivity

theorem globalLogBox_radial_decay (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U Z θ : ℝ, ∀ N : ℕ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/
          (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) ≤
        C*U^(ε+8*η)/Z^(θ*N) := by
  obtain ⟨C,hC,hall⟩ := globalLogBox_total_loss ε hε η hη
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ
  let box := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let radial := fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j
  have hbase : 0<Z^θ := Real.rpow_pos_of_pos hZ _
  have hden : 0<Z^(θ*N) := Real.rpow_pos_of_pos hZ _
  have hnum (j : GlobalLogIndex) : 0≤(globalBinLossScale B j)^η :=
    Real.rpow_nonneg (globalBinLossScale_nonneg B (by linarith) j) _
  have hp (j : GlobalLogIndex) (hj : Z^θ≤radial j) :
      Z^(θ*N)≤(1+radial j)^N := by
    rw [Real.rpow_mul hZ.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ hbase.le (by linarith) N
  calc
    _ ≤ ∑j∈box.filter (fun j => Z^θ≤radial j), (globalBinLossScale B j)^η/Z^(θ*N) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_left (hnum j) hden (hp j (Finset.mem_filter.mp hj).2)
    _ = (∑j∈box.filter (fun j => Z^θ≤radial j),(globalBinLossScale B j)^η)/Z^(θ*N) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (∑j∈box,(globalBinLossScale B j)^η)/Z^(θ*N) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hnum j)
    _ ≤ C*U^(ε+8*η)/Z^(θ*N) := div_le_div_of_nonneg_right
      (hall K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hden.le

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem secondChildColumn_norm_le_test
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondChildColumn p hg Ψ m f y H S‖ ≤ ‖H S‖ := by
  have hprime (i : ι) : Prime (p i) :=
    (Ideal.span_singleton_prime (hp i)).mp (inferInstance : (Ideal.span {p i}).IsPrime)
  have hcop : Pairwise (Function.onFun IsCoprime p) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  have he : secondChildColumn p hg Ψ m f y H S = secondColumnCoefficient p S *
      secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m f y H S := by
    simp only [secondChildColumn, secondInputCoefficient, mul_assoc]
  rw [he, norm_mul, secondColumnCoefficient_norm_one p hprime hpr hcop S, one_mul]
  exact secondInputCoefficient_norm_le_test p hg Ψ hΨ m f y H S

include hp in
theorem fixedChildRow_elementary
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (X M : ℝ) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hH : ∀ S, ‖H S‖ ≤ M) (hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ X) :
    ‖fixedChildRow p hg F Ψ m H f y‖ ≤ diagonalControl sieveCutoff * X * M := by
  have heq : fixedChildRow p hg F Ψ m H f y =
      ∑ S ∈ boundedPrimeSupports p F X, secondChildColumn p hg Ψ m f y H S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hz : H S = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hS, hSupp S h⟩)
    simp only [secondChildColumn, hz, mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, ‖secondChildColumn p hg Ψ m f y H S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, M := Finset.sum_le_sum
      (fun S hS => (secondChildColumn_norm_le_test p hp hg hinj hpr Ψ hΨ m f y H S).trans (hH S))
    _ = ((boundedPrimeSupports p F X).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F X hX) hM

/-- The label and row projections bound the number of pairs in a finite target family. -/
theorem finite_label_row_count (T : Finset (Ideal O × O)) (F K : ℝ) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hT : ∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ringComplex z.2‖^2 ≤ K) :
    (T.card : ℝ) ≤ (diagonalControl sieveCutoff)^2 * F * K := by
  let I := T.image Prod.fst
  let R := T.image Prod.snd
  have hI : (I.card : ℝ) ≤ diagonalControl sieveCutoff * F := by
    apply finite_ideal_card_bound I F hF
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact (hT z hz).1
  have hR : (R.card : ℝ) ≤ diagonalControl sieveCutoff * K := by
    apply finite_norm_ball_card_bound R K hK
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact (hT z hz).2
  have hsub : T ⊆ I ×ˢ R := fun z hz =>
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩, Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hn := Finset.card_le_card hsub
  rw [Finset.card_product] at hn
  have hcontrol := diagonalControl_nonneg sieveCutoff
  calc
    _ ≤ (I.card : ℝ) * R.card := by exact_mod_cast hn
    _ ≤ (diagonalControl sieveCutoff * F) * (diagonalControl sieveCutoff * K) :=
      mul_le_mul hI hR (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation FirstPassCubeLabels MeasureTheory
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- Counting supported columns and target pairs gives a uniform elementary energy estimate. -/
theorem childEnergy_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (H : Finset ι → ℂ) (hH : ∀ S, ‖H S‖ ≤ 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X F K A M a b : ℝ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hV : ∀ s, ‖V s‖ ≤ M) (hVsupp : ∀ s, V s ≠ 0 → |s| ≤ A)
    (hT : ∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ringComplex z.2‖^2 ≤ K)
    (testNegative rowNegative : Bool) :
    childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b / (X*F) ≤
      (Fintype.card Oˣ : ℝ) * (diagonalControl sieveCutoff)^4 * K *
        (max 1 (X*Real.exp A))^2 * M^2 / X := by
  let test := weightedSecondTest p H V X a b testNegative
  let Y := max 1 (X*Real.exp A)
  have hF0 : 0 < F := by linarith
  have hY : 1 ≤ Y := le_max_left _ _
  have htest (S : Finset ι) : ‖test S‖ ≤ M := by
    have hf : ‖fixedSecondTest p V X a b testNegative S‖ = ‖V (columnLog p X S)‖ := by
      cases testNegative <;> simp only [fixedSecondTest, Bool.false_eq_true, ite_false, ite_true,
        fixedColumnTest, norm_mul, norm_star, kernelLogPhase_norm, mul_one]
    change ‖H S * fixedSecondTest p V X a b testNegative S‖ ≤ M
    rw [norm_mul, hf]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH S)).trans (hV _)
  have hsupp (S : Finset ι) (hS : test S ≠ 0) : primeProductNorm p S ≤ Y := by
    have hv : V (columnLog p X S) ≠ 0 := by
      intro hz
      apply hS
      cases testNegative <;> simp only [test, weightedSecondTest, fixedSecondTest,
        Bool.false_eq_true, ite_false, ite_true, fixedColumnTest, hz, zero_mul, star_zero, mul_zero]
    exact (columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hVsupp _ hv))).trans (le_max_right _ _)
  have hrow (f y : O) : ‖fixedChildRow p hg pool Ψ m test f y‖ ≤ diagonalControl sieveCutoff * Y * M :=
    fixedChildRow_elementary p hp hg hinj hpr pool Ψ hΨ m f y test Y M hY hM htest hsupp
  have he : childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b ≤
      (Fintype.card Oˣ : ℝ) * ((T.card : ℝ) * (diagonalControl sieveCutoff * Y * M)^2) := by
    unfold childEnergy
    calc
      _ ≤ ∑ _u : Oˣ, ∑ _z ∈ T, (diagonalControl sieveCutoff * Y * M)^2 := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow _ _) 2
      _ = _ := by simp
  have ht := finite_label_row_count T F K hF hK hT
  apply (div_le_iff₀ (mul_pos hX hF0)).mpr
  calc
    _ ≤ (Fintype.card Oˣ : ℝ) * ((T.card : ℝ) * (diagonalControl sieveCutoff * Y * M)^2) := he
    _ ≤ (Fintype.card Oˣ : ℝ) * (((diagonalControl sieveCutoff)^2 * F * K) *
        (diagonalControl sieveCutoff * Y * M)^2) := by gcongr
    _ = _ := by dsimp only [Y]; field_simp

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

theorem childDensity_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (H₁ H₂ : Finset ι → ℂ) (hH₁ : ∀ S, ‖H₁ S‖ ≤ 1) (hH₂ : ∀ S, ‖H₂ S‖ ≤ 1)
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ringComplex z.2‖^2 ≤ K) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      ((Fintype.card Oˣ : ℝ)*(diagonalControl sieveCutoff)^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*
        (∫ t : ℝ,firstLogDensity 0 t)^3 := by
  let B := ((Fintype.card Oˣ : ℝ)*(diagonalControl sieveCutoff)^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F)
  have hcontrol := diagonalControl_nonneg sieveCutoff
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hXF : 0 < X*F := mul_pos hX (lt_of_lt_of_le zero_lt_one hF)
  have h₁ (a : ℝ) : childEnergy p hg H₁ pool Ψ₁ m T V₁ X true false a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hg hinj hpr H₁ hH₁ pool Ψ₁ hΨ₁ m T V₁
      X F K A M a 0 hX hF hK hM hV₁ hVs₁ (fun z hz => (hT z hz).2) true false
    have hh : childEnergy p hg H₁ pool Ψ₁ m T V₁ X true false a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have h₂ (a : ℝ) : childEnergy p hg H₂ pool Ψ₂ m T V₂ X false true a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hg hinj hpr H₂ hH₂ pool Ψ₂ hΨ₂ m T V₂
      X F K A M a 0 hX hF hK hM hV₂ hVs₂ (fun z hz => (hT z hz).2) false true
    have hh : childEnergy p hg H₂ pool Ψ₂ m T V₂ X false true a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have hd := densityChildEnergy_polynomial_bound p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X J B B hB hB h₁ h₂
  rw [Real.mul_self_sqrt hB] at hd
  apply (div_le_iff₀ hXF).mpr
  apply hd.trans_eq
  dsimp only [B]
  ring

theorem childDensity_elementary_supported {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (H₁ H₂ : Finset ι → ℂ) (hH₁ : ∀ S, ‖H₁ S‖ ≤ 1) (hH₂ : ∀ S, ‖H₂ S‖ ≤ 1)
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hscale : 1 ≤ X*Real.exp A)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ringComplex z.2‖^2 ≤ K) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      ((Fintype.card Oˣ : ℝ)*(diagonalControl sieveCutoff)^4*(Real.exp A*M)^2*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*X := by
  have h := childDensity_elementary_normalized p hp hg hinj hpr H₁ H₂ hH₁ hH₂ pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X F K A M J hX hF hK hA hM hV₁ hV₂ hVs₁ hVs₂ hT
  rw [max_eq_right hscale] at h
  convert h using 1
  field_simp

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem fixedSecondTest_subunit (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative : Bool) (S : Finset ι) : fixedSecondTest p V X a b negative S=0 := by
  have hz : V (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have h1 := primeProductNorm_ge_one p hp S
    linarith
  cases negative <;> simp [fixedSecondTest,JointLogSeparation.fixedColumnTest,hz]

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation SecondPassArithmetic MeasureTheory
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

include hp in
theorem childEnergy_subunit (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative rowNegative : Bool) :
    childEnergy p hg H pool Ψ m T V X negative rowNegative a b=0 := by
  have hrow (f y : O) : fixedChildRow p hg pool Ψ m (weightedSecondTest p H V X a b negative) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,weightedSecondTest,fixedSecondTest_subunit p hp V X A hX hV hsmall a b negative S,mul_zero]
  simp [childEnergy,idealChildRow,hrow]

include hp in
theorem densityChildEnergy_subunit (H₁ H₂ : Finset ι → ℂ) (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ A : ℝ) (J : ℕ) (hX : 0 < X₁)
    (hV : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hsmall : X₁*Real.exp A < 1) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J=0 := by
  unfold densityChildEnergy childGeometricMean
  simp only [childEnergy_subunit p hp hg H₁ pool Ψ₁ m T V₁ X₁ A hX hV hsmall,
    Real.sqrt_zero,zero_mul,mul_zero,integral_zero]

include hp in
theorem childDensity_elementary_all_scales
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
    (H₁ H₂ : Finset ι → ℂ) (hH₁ : ∀ S, ‖H₁ S‖ ≤ 1) (hH₂ : ∀ S, ‖H₂ S‖ ≤ 1)
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ringComplex z.2‖^2 ≤ K) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      ((Fintype.card Oˣ : ℝ)*(diagonalControl sieveCutoff)^4*(Real.exp A*M)^2*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*X := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · exact childDensity_elementary_supported p hp hg hinj hpr H₁ H₂ hH₁ hH₂ pool Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X F K A M J hX hF hK hA hM hscale hV₁ hV₂ hVs₁ hVs₂ hT
  · rw [densityChildEnergy_subunit p hp hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X A (2*J) hX hVs₁ (lt_of_not_ge hscale),zero_div]
    have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
      integral_nonneg (fun t => firstLogDensity_nonneg 0 t)
    positivity

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical

def globalDescentWeight (C ε K ell B F : ℝ) (A : ℕ) (j : GlobalLogIndex)
    (ray : QuadraticRayRing × QuadraticRayRing) (q : Ideal O × Ideal O × Ideal O) : ℝ :=
  C * globalBinFirstCoefficient K ell B F j *
    globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
    (globalPooledLabelScale j * Ideal.absNorm q.1)^ε /
    (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *
    (globalPooledColumnScale ell j * globalPooledLabelScale j)

theorem globalDescentWeight_nonneg (C ε K ell B F : ℝ) (A : ℕ) (j : GlobalLogIndex)
    (ray : QuadraticRayRing × QuadraticRayRing) (q : Ideal O × Ideal O × Ideal O)
    (hC : 0 ≤ C) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) :
    0 ≤ globalDescentWeight C ε K ell B F A j ray q := by
  have hc := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hr := globalBinRadial_pos ell _ hell hy j
  have hx := globalPooledColumnScale_pos ell hell j
  have hl := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).le
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  unfold globalDescentWeight globalPooledOuterBound
  positivity

def globalRayTripleConstant : ℝ :=
  ∑ ray : QuadraticRayRing × QuadraticRayRing,
    ∑ _s : QuadraticRayRing × QuadraticRayRing, ∑ _q : QuadraticRayRing × QuadraticRayRing,
      (diagonalControl sieveCutoff)^3 * (Real.exp 1)^18 * ‖rayQuadraticPair ray.1 ray.2‖

theorem globalRayTripleConstant_nonneg : 0 ≤ globalRayTripleConstant := by
  have hc := diagonalControl_nonneg sieveCutoff
  unfold globalRayTripleConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
/-- Summing a bin's arithmetic triples cancels its reciprocal column and label scales. -/
theorem globalDescentWeight_triple_sum
    (C ε K ell B F : ℝ) (A : ℕ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (side : Bool) (source : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x ∈ source, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (ray : QuadraticRayRing × QuadraticRayRing) :
    (∑ q ∈ globalBinTriples p source side j, globalDescentWeight C ε K ell B F A j ray q) ≤
      (C * (globalBinLossScale B j)^ε /
        (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
        globalBinChildCharge B F j * ‖rayQuadraticPair ray.1 ray.2‖ := by
  have hc := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hr := globalBinRadial_pos ell _ hell hy j
  have hx := globalPooledColumnScale_pos ell hell j
  have hl := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).le
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have houter : 0 ≤ globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j := by
    unfold globalPooledOuterBound
    positivity
  have hloss0 := globalBinLossScale_nonneg B hB.le j
  let base := C * (globalBinLossScale B j)^ε /
    (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A
  let factor := base * globalBinFirstCoefficient K ell B F j *
    globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
    (globalPooledColumnScale ell j * globalPooledLabelScale j)
  have hf : 0 ≤ factor := by dsimp only [factor, base]; positivity
  have ht (q : Ideal O × Ideal O × Ideal O) (hq : q ∈ globalBinTriples p source side j) :
      globalDescentWeight C ε K ell B F A j ray q ≤ factor := by
    have hloss : globalPooledLabelScale j * Ideal.absNorm q.1 ≤ globalBinLossScale B j :=
      mul_le_mul_of_nonneg_left
        (globalBinTriples_label_bound p hp B hB side source j hk hb₁ hb₂ q hq) hl
    have hpowers := Real.rpow_le_rpow (mul_nonneg hl (Nat.cast_nonneg _)) hloss hε
    have hfactor := globalDescentWeight_nonneg C ε K ell B F A j ray q hC hK hell hB hF
    unfold globalDescentWeight
    calc
      _ ≤ C * globalBinFirstCoefficient K ell B F j *
          globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
          (globalBinLossScale B j)^ε /
          (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *
          (globalPooledColumnScale ell j * globalPooledLabelScale j) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowers (mul_nonneg (mul_nonneg hC hc) houter))
            (pow_nonneg (by linarith) A)) (mul_nonneg hx.le hl)
      _ = factor := by dsimp only [factor, base]; ring
  calc
    _ ≤ ∑ _q ∈ globalBinTriples p source side j, factor := Finset.sum_le_sum ht
    _ = ((globalBinTriples p source side j).card : ℝ) * factor := by simp
    _ ≤ ((diagonalControl sieveCutoff)^3 * (Real.exp 1)^3 * globalBinTripleRange B j) * factor :=
      mul_le_mul_of_nonneg_right (globalBinTriples_count p hp B hB side source j hk hb₁ hb₂) hf
    _ = base * (globalBinFirstCoefficient K ell B F j *
        globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
        (globalPooledColumnScale ell j * globalPooledLabelScale j) *
        ((diagonalControl sieveCutoff)^3 * (Real.exp 1)^3 * globalBinTripleRange B j)) := by
      dsimp only [factor]; ring
    _ = _ := by rw [globalBin_complete_cost K ell B F hK hell hB hF]; dsimp only [base]; ring

include hp in
theorem globalDescentWeight_mass
    (C ε K ell B F : ℝ) (A : ℕ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (side : Bool) (source : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x ∈ source, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (∑ ray : QuadraticRayRing × QuadraticRayRing,
      ∑ _s : QuadraticRayRing × QuadraticRayRing, ∑ _q : QuadraticRayRing × QuadraticRayRing,
        ∑ q ∈ globalBinTriples p source side j, globalDescentWeight C ε K ell B F A j ray q *
          (globalPooledColumnScale ell j * globalPooledLabelScale j)) ≤
      (C * (globalBinLossScale B j)^ε /
        (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
        globalRayTripleConstant * ((ell*B^3)*F) := by
  unfold globalRayTripleConstant
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_mul]
  have hx := globalPooledColumnScale_pos ell hell j
  have hl := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).le
  have h := mul_le_mul_of_nonneg_right
    (globalDescentWeight_triple_sum p hp C ε K ell B F A hC hε hK hell hB hF side source j hk hb₁ hb₂ ray)
    (mul_nonneg hx.le hl)
  apply h.trans_eq
  calc
    _ = (C * (globalBinLossScale B j)^ε /
        (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
        (globalBinChildCharge B F j * (globalPooledColumnScale ell j * globalPooledLabelScale j)) *
        ‖rayQuadraticPair ray.1 ray.2‖ := by ring
    _ = _ := by rw [globalBin_mass_balance ell B F hB hF]; ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def globalTerminalConstant (A M : ℝ) : ℝ :=
  (Fintype.card Oˣ : ℝ) * (diagonalControl sieveCutoff)^4 *
    (Real.exp A * M)^2 * (∫ t, firstLogDensity 0 t)^3

theorem globalTerminalConstant_nonneg (A M : ℝ) : 0 ≤ globalTerminalConstant A M := by
  have hi : 0 ≤ ∫ t, firstLogDensity 0 t := integral_nonneg (firstLogDensity_nonneg 0)
  unfold globalTerminalConstant
  positivity

theorem radial_decay_step (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    R/(1+R)^(N+1) ≤ 1/(1+R)^N := by
  have h1 : 0 < 1+R := by linarith
  have hr : R/(1+R) ≤ 1 := (div_le_iff₀ h1).mpr (by linarith)
  calc
    R/(1+R)^(N+1) = (R/(1+R))/(1+R)^N := by rw [pow_succ]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr (pow_nonneg h1.le _)

/-- The pooled physical row is controlled by the radial parameter times the original row scale. -/
theorem globalPooledRow_radial_bound (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalLogRep j 8 * Real.exp 1 ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j * K := by
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hD := globalPooledDelta_pos B F hB0 hF0 j
  have hD1 : 1 ≤ globalPooledDelta B F j :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB hF)
          (globalLogRep_ge_one j 0)) (globalLogRep_ge_one j 2)) (globalLogRep_ge_one j 3)
  have hN : 0 < globalPooledNaturalRow K B F j := by
    unfold globalPooledNaturalRow
    exact div_pos (mul_pos hK (globalLogRep_pos j 4)) (mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hB0))
  have hNupper : globalPooledNaturalRow K B F j ≤ K := by
    unfold globalPooledNaturalRow
    calc
      _ ≤ K * B^2 / ((globalPooledDelta B F j)^2 * B^2) := by gcongr
      _ = K / (globalPooledDelta B F j)^2 := by field_simp
      _ ≤ K := div_le_self hK.le (one_le_pow₀ hD1)
  have hR := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have he : globalLogRep j 8 * Real.exp 1 =
      globalBinRadial ell (globalPooledRowScale K ell B F j) j * globalPooledNaturalRow K B F j := by
    rw [globalBinRadial, globalPooled_radial_ratio K ell B F hK hell hB0 hF0]
    field_simp
  exact he.trans_le (mul_le_mul_of_nonneg_left hNupper hR.le)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration MeasureTheory
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalBinDensityBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (C ε K ell B F : ℝ)
    (A J : ℕ) (side : Bool) (j : GlobalLogIndex) : ℝ :=
  ∑ ray : QuadraticRayRing × QuadraticRayRing,
    ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
      ∑ q₀ ∈ globalBinTriples p source side j,
        globalDescentWeight C ε K ell B F A j ray q₀ *
        (densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
          pool Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
          V₁ V₂ (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j * globalPooledLabelScale j))

/-- One radial power pays for the elementary physical-row count. -/
theorem globalRadialBin_terminal_bound
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t, ‖V₁ t‖ ≤ M) (hV₂ : ∀ t, ‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ A₀)
    (source : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x ∈ source, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hJ : globalLogRep j 4 ≤ B^2) :
    globalBinDensityBudget p hg pool source Ψ m V₁ V₂ C ε K ell B F (N+1) (2*J) side j ≤
      (C * (globalBinLossScale B j)^ε * (globalTerminalConstant A₀ M * globalRayTripleConstant) *
        K * ((ell*B^3)*F)) / (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  let X := globalPooledColumnScale ell j
  let L := globalPooledLabelScale j
  let R := globalBinRadial ell (globalPooledRowScale K ell B F j) j
  let K' := globalLogRep j 8 * Real.exp 1
  let Ct := globalTerminalConstant A₀ M
  let Q := C * (globalBinLossScale B j)^ε * (Ct * globalRayTripleConstant) * K * ((ell*B^3)*F)
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hX : 0 < X := globalPooledColumnScale_pos ell hell j
  have hL : 1 ≤ L := globalPooledLabelScale_ge_one j
  have hR : 0 < R := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hCt : 0 ≤ Ct := globalTerminalConstant_nonneg A₀ M
  have hrow : K' ≤ R*K := globalPooledRow_radial_bound K ell B F hK hell hB hF j hJ
  have hQ : 0 ≤ Q := by
    have hrc := globalRayTripleConstant_nonneg
    have hloss := globalBinLossScale_nonneg B hB0.le j
    dsimp only [Q]
    positivity
  have hterm (s q : QuadraticRayRing × QuadraticRayRing) (q₀ : Ideal O × Ideal O × Ideal O) :
      densityChildEnergy p hg
        (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
        (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
        pool Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
        V₁ V₂ X X (2*J)/(X*L) ≤ Ct*K'*(X*L) := by
    have h := childDensity_elementary_all_scales p hp hg hinj hpr
      (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
      (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
      (fun S => by simpa only [norm_one] using combinedFixedColumn_norm_le p hg side q.1 s.1 (fun _ => 1) S)
      (fun S => by simpa only [norm_one] using combinedFixedColumn_norm_le p hg side q.2 s.2 (fun _ => 1) S)
      pool Ψ Ψ hΨ hΨ (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
      V₁ V₂ X L K' A₀ M J hX hL hK' hA₀ hM hV₁ hV₂ hVs₁ hVs₂
      (globalArithmeticTargets_bounds p hp source side q₀ j hk)
    exact h.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hX.le hL)
      (mul_nonneg hCt (zero_le_one.trans hK')))
  let mass := ∑ ray : QuadraticRayRing × QuadraticRayRing,
    ∑ _s : QuadraticRayRing × QuadraticRayRing, ∑ _q : QuadraticRayRing × QuadraticRayRing,
      ∑ q₀ ∈ globalBinTriples p source side j,
        globalDescentWeight C ε K ell B F (N+1) j ray q₀ * (X*L)
  have hmass := globalDescentWeight_mass p hp C ε K ell B F (N+1) hC hε hK hell hB0 hF0
    side source j hk hb₁ hb₂
  have hm0 : 0 ≤ mass := by
    apply Finset.sum_nonneg
    intro ray _
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro q _
    apply Finset.sum_nonneg
    intro q₀ hq₀
    exact mul_nonneg (globalDescentWeight_nonneg C ε K ell B F (N+1) j ray q₀ hC hK hell hB0 hF0)
      (mul_nonneg hX.le (zero_le_one.trans hL))
  calc
    _ ≤ ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
          ∑ q₀ ∈ globalBinTriples p source side j,
            globalDescentWeight C ε K ell B F (N+1) j ray q₀ * (Ct*K'*(X*L)) := by
      apply Finset.sum_le_sum
      intro ray _
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro q₀ hq₀
      exact mul_le_mul_of_nonneg_left (hterm s q q₀)
        (globalDescentWeight_nonneg C ε K ell B F (N+1) j ray q₀ hC hK hell hB0 hF0)
    _ = Ct*K'*mass := by
      dsimp only [mass]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro q₀ _
      ring
    _ ≤ Ct*(R*K)*((C*(globalBinLossScale B j)^ε/(1+R)^(N+1))*globalRayTripleConstant*((ell*B^3)*F)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrow hCt) hmass hm0 (mul_nonneg hCt (mul_nonneg hR.le hK.le))
    _ = Q*(R/(1+R)^(N+1)) := by dsimp only [Q]; ring
    _ ≤ Q*(1/(1+R)^N) := mul_le_mul_of_nonneg_left (radial_decay_step R hR.le N) hQ
    _ = _ := by dsimp only [Q, R, Ct]; ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem globalChildBudget_eq_bin_sum (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ) (C ε K ell B F : ℝ)
    (I : Finset GlobalLogIndex) (A J : ℕ) (side : Bool) (hell : 0 < ell) :
    globalChildBudget p hg pool source Ψ m windows C ε K ell B F I A J side =
      ∑ j ∈ I, globalBinDensityBudget p hg pool source Ψ m (windows 5) (windows 6)
        C ε K ell B F A J side j := by
  unfold globalChildBudget globalBinDensityBudget
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (QuadraticRayRing × QuadraticRayRing))) (t := I)]
  apply Finset.sum_congr rfl
  intro j hj
  have hx := (globalPooledColumnScale_pos ell hell j).ne'
  have hl := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).ne'
  apply Finset.sum_congr rfl
  intro ray _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro q₀ hq₀
  unfold globalDescentWeight
  field_simp

theorem globalRadialBin_terminal_bound_all_bins
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t, ‖V₁ t‖ ≤ M) (hV₂ : ∀ t, ‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ A₀)
    (source : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x ∈ source, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalBinDensityBudget p hg pool source Ψ m V₁ V₂ C ε K ell B F (N+1) (2*J) side j ≤
      (C * (globalBinLossScale B j)^ε * (globalTerminalConstant A₀ M * globalRayTripleConstant) *
        K * ((ell*B^3)*F)) / (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  by_cases hs : (globalLogSector p source side j).Nonempty
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
    have hJ := globalPooled_J_bound p hp B (zero_le_one.trans hB) side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    rw [hj] at hJ
    exact globalRadialBin_terminal_bound p hg hp hinj hpr pool Ψ hΨ m V₁ V₂ C ε K ell B F A₀ M N J
      hC hε hK hell hB hF hA₀ hM hV₁ hV₂ hVs₁ hVs₂ source side j hk hb₁ hb₂ hJ
  · have he : globalBinTriples p source side j = ∅ := by
      simp only [globalBinTriples, Finset.not_nonempty_iff_eq_empty.mp hs, Finset.image_empty]
    simp only [globalBinDensityBudget, he, Finset.sum_empty, Finset.sum_const_zero]
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    have hR := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
    have hCt := globalTerminalConstant_nonneg A₀ M
    have hCr := globalRayTripleConstant_nonneg
    have hloss := globalBinLossScale_nonneg B hB0.le j
    positivity

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration MeasureTheory
open scoped Classical

theorem globalChild_large_radial_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (η : ℝ) (hη : 0<η) :
    ∃ Cbox : ℝ,0<Cbox ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda^2 ∣ p i-1)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ)
      (C K ell B F M H U Z θ A₀ Vmax : ℝ) (N J : ℕ)
      (source : Finset (GlobalSecondData ι)) (side : Bool),
      0≤C → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      0≤A₀ → 0≤Vmax → (∀ t,‖V₁ t‖≤Vmax) → (∀ t,‖V₂ t‖≤Vmax) →
      (∀ t,V₁ t≠0 → |t|≤A₀) → (∀ t,V₂ t≠0 → |t|≤A₀) →
      (∀ a,‖Ψ a‖≤1) → (∀ x∈source,x.source.frequency≠0) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        globalBinDensityBudget p hg pool source Ψ m V₁ V₂ C η K ell B F (N+1) (2*J) side j) ≤
      C*Cbox*(globalTerminalConstant A₀ Vmax*globalRayTripleConstant)*K*((ell*B^3)*F)*
        U^(deltaLoss+8*η)/Z^(θ*N) := by
  obtain ⟨Cbox,hCbox,hdecay⟩ := globalLogBox_radial_decay deltaLoss hδ η hη.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hg hinj hpr pool Ψ m V₁ V₂ C K ell B F M H U Z θ A₀ Vmax N J source side
    hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA₀ hVmax hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let Q := C*(globalTerminalConstant A₀ Vmax*globalRayTripleConstant)*K*((ell*B^3)*F)
  have hQ : 0≤Q := by
    have hc0 := globalTerminalConstant_nonneg A₀ Vmax
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    have hrc := globalRayTripleConstant_nonneg
    dsimp only [Q]
    positivity
  calc
    _ ≤ ∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        Q*((globalBinLossScale B j)^η/(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) := by
      apply Finset.sum_le_sum
      intro j hj
      have ht := globalRadialBin_terminal_bound_all_bins p hg hp hinj hpr pool Ψ hΨ m V₁ V₂
        C η K ell B F A₀ Vmax N J hC hη.le hK hell hB hF hA₀ hVmax hV₁ hV₂ hVs₁ hVs₂
        source side j hk hb₁ hb₂
      apply ht.trans_eq
      dsimp only [Q]
      ring
    _ = Q*(∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) := by
      rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*η)/Z^(θ*N)) := mul_le_mul_of_nonneg_left
      (hdecay K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ) hQ
    _ = _ := by dsimp [Q];ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
variable {ι : Type*} [DecidableEq ι]

def reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) : Finset (CubeCoordinates ι) :=
  (((v₁.support ∪ v₂.support).powerset).product
    ((v₁.support ∪ v₂.support).powerset)).image
    (fun A => ⟨v₁,v₂,A.2,A.1⟩)

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

def reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) : Finset (CubeCoordinates ι) :=
  (Q.product Q).biUnion (fun v => reopenedCubeFiber v.2 v.1)

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

lemma reopenedCubeFamily_support (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    ∀ b ∈ reopenedCubeFamily Q,b.support ⊆ pool := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  exact Finset.union_subset (hQ _ hl) (hQ _ hr)

theorem sum_reopenedCubeFamily {M : Type*} [AddCommMonoid M]
    (Q : Finset (ι →₀ ℕ)) (f : CubeCoordinates ι → M) :
    (∑ b ∈ reopenedCubeFamily Q,f b) =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ A₂ ∈ (v₁.support∪v₂.support).powerset,
        ∑ A₁ ∈ (v₁.support∪v₂.support).powerset,f ⟨v₁,v₂,A₁,A₂⟩ := by
  unfold reopenedCubeFamily
  rw [Finset.sum_biUnion]
  · change (∑ x ∈ Q ×ˢ Q,∑ i ∈ reopenedCubeFiber x.2 x.1,f i)=_
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v₂ hv₂
    apply Finset.sum_congr rfl
    intro v₁ hv₁
    unfold reopenedCubeFiber
    rw [Finset.sum_image]
    · change (∑ x ∈ (v₁.support∪v₂.support).powerset ×ˢ (v₁.support∪v₂.support).powerset,
        f ⟨v₁,v₂,x.2,x.1⟩)=_
      rw [Finset.sum_product]
    · intro A hA B hB he
      exact Prod.ext (congrArg CubeCoordinates.rightDivisor he) (congrArg CubeCoordinates.leftDivisor he)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨hbl,hbr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    obtain ⟨hcl,hcr,hc⟩ := (mem_reopenedCubeFiber w.2 w.1 b).mp hc
    exact hne (Prod.ext (hbr.symm.trans hcr) (hbl.symm.trans hcl))

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖ringComplex (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖ringComplex (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

def reopenedPairCoefficient (β : Ideal O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (_C : Finset ι) (I : Ideal O) : ℂ :=
  star (β I b.rightExponent)*β I b.leftExponent

omit [DecidableEq ι] in
lemma reopenedPairCoefficient_independent_common (β : Ideal O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (C D : Finset ι) (I : Ideal O) :
    reopenedPairCoefficient β b C I=reopenedPairCoefficient β b D I := rfl

lemma reopenedPairCoefficient_bound (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ) :
    ∀ b ∈ reopenedCubeFamily Q,∀ C,∀ I ∈ labels,
      ‖reopenedPairCoefficient β b C I‖ ≤ Γ^2 := by
  intro b hb C I hI
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  simp only [reopenedPairCoefficient,norm_mul,norm_star]
  simpa only [pow_two] using mul_le_mul (hβ I hI _ hr) (hβ I hI _ hl) (norm_nonneg _) hΓ

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- A common descendant-energy bound combines with the exact bin mass. -/
theorem globalBin_canonical_child_bound
    (hp : ∀ i, p i ≠ 0) (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (side : Bool) (j : GlobalLogIndex) (Ψ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ)
    (C E ε K ell B F : ℝ) (A J : ℕ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (hk : ∀ x ∈ source, x.source.frequency ≠ 0)
    (hb₁ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x ∈ source, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (he : ∀ s q : QuadraticRayRing × QuadraticRayRing, ∀ q₀ ∈ globalBinTriples p source side j,
      densityChildEnergy p hg
        (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
        (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
        pool Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
        V₁ V₂ (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J ≤
        E * (globalPooledColumnScale ell j * globalPooledLabelScale j)^2) :
    globalBinDensityBudget p hg pool source Ψ m V₁ V₂ C ε K ell B F A J side j ≤
      E * C * globalRayTripleConstant * ((ell*B^3)*F) * (globalBinLossScale B j)^ε /
        (1 + globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A := by
  let X := globalPooledColumnScale ell j * globalPooledLabelScale j
  have hX : 0 < X := mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  have hmass := globalDescentWeight_mass p hp C ε K ell B F A hC hε hK hell hB hF
    side source j hk hb₁ hb₂
  apply le_trans _ ((mul_le_mul_of_nonneg_left hmass hE).trans_eq (by ring))
  unfold globalBinDensityBudget
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray _
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum
  intro q₀ hq₀
  have hb : densityChildEnergy p hg
      (combinedFixedColumn p hg side q.1 s.1 (fun _=>1))
      (combinedFixedColumn p hg side q.2 s.2 (fun _=>1)) pool Ψ Ψ
      (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j) V₁ V₂
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J / X ≤ E*X := by
    apply (div_le_iff₀ hX).mpr
    exact (he s q q₀ hq₀).trans_eq (by dsimp only [X]; ring)
  exact (mul_le_mul_of_nonneg_left hb
    (globalDescentWeight_nonneg C ε K ell B F A j ray q₀ hC hK hell hB hF)).trans_eq (by dsimp only [X]; ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical

theorem globalSelected_canonical_child_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Cbox:ℝ,0<Cbox ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:O→*ℂ) (m:O) (V₁ V₂:ℝ→ℂ) (C E K ell B F M H U:ℝ) (A J:ℕ)
      (keep:GlobalLogIndex→Prop) [DecidablePred keep],
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∀s q:QuadraticRayRing×QuadraticRayRing,∀q₀∈globalBinTriples p source side j,
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _=>1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _=>1)) pool Ψ Ψ
          (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        globalBinDensityBudget p hg pool source Ψ m V₁ V₂ C ε K ell B F A J side j)≤
        E*C*globalRayTripleConstant*((ell*B^3)*F)*Cbox*U^(deltaLoss+8*ε) := by
  obtain ⟨Cbox,hCbox,hbox⟩:=globalLogBox_total_loss deltaLoss hδ ε hε.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hg pool source side Ψ m V₁ V₂ C E K ell B F M H U A J keep _
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let Q:=E*C*globalRayTripleConstant*((ell*B^3)*F)
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hQ:0≤Q:=by have hr := globalRayTripleConstant_nonneg; dsimp only [Q]; positivity
  have hloss (j:GlobalLogIndex):0≤(globalBinLossScale B j)^ε:=by
    unfold globalBinLossScale
    have hx:=globalLogRep_pos j 4
    have hl:=globalPooledLabelScale_ge_one j
    positivity
  calc
    _ ≤ ∑j∈S.filter keep,Q*(globalBinLossScale B j)^ε:=by
      apply Finset.sum_le_sum
      intro j hj
      have hb:=globalBin_canonical_child_bound p hg hp pool source side j Ψ m V₁ V₂ C E ε K ell B F A J
        hC hE hε.le hK hell hB0 hF0 hk hb₁ hb₂ (he j hj)
      apply hb.trans
      apply div_le_self (mul_nonneg hQ (hloss j))
      have hr:=globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
        (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
      exact one_le_pow₀ (by linarith)
    _ ≤ ∑j∈S,Q*(globalBinLossScale B j)^ε:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj hnot=>mul_nonneg hQ (hloss j))
    _ = Q*∑j∈S,(globalBinLossScale B j)^ε:=by rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*ε)):=mul_le_mul_of_nonneg_left
      (hbox K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hQ
    _ = _:=by dsimp [Q];ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical

theorem globalChildBudget_canonical_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i})) (hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:O→*ℂ) (m:O) (windows:Fin 7→ℝ→ℂ)
      (C E K ell B F M H U Z θ A₀ Vmax:ℝ) (N J:ℕ),
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) → (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀s q:QuadraticRayRing×QuadraticRayRing,∀q₀∈globalBinTriples p source side j,
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _=>1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _=>1)) pool Ψ Ψ
          (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalChildBudget p hg pool source Ψ m windows C ε K ell B F
        (globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)) (N+1) (2*J) side≤
        C*globalRayTripleConstant*((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,hClo,hlow⟩:=globalSelected_canonical_child_bound deltaLoss hδ ε hε
  obtain ⟨Chi,hChi,hhigh⟩:=globalChild_large_radial_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hg hinj hpr pool source side Ψ m windows C E K ell B F M H U Z θ A₀ Vmax N J
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂ he
  have hlo:=hlow p hp hg pool source side Ψ m (windows 5) (windows 6) C E K ell B F M H U (N+1) (2*J)
    (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ)
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  have hhi:=hhigh p hp hg hinj hpr pool Ψ m (windows 5) (windows 6) C K ell B F M H U Z θ A₀ Vmax N J
    source side hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let f:=fun j:GlobalLogIndex=>globalBinDensityBudget p hg pool source Ψ m
      (windows 5) (windows 6) C ε K ell B F (N+1) (2*J) side j
  have hsplit:(∑j∈S,f j)=
      (∑j∈S.filter (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),f j)+
      (∑j∈S.filter (fun j=>Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),f j):=by
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not S
      (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ) f).symm
  rw [globalChildBudget_eq_bin_sum p hg pool source Ψ m windows C ε K ell B F _ (N+1) (2*J) side hell]
  change (∑j∈S,f j)≤_
  rw [hsplit]
  apply (add_le_add hlo hhi).trans_eq
  ring

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
