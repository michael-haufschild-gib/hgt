/-
The quadratic large sieve adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.AnnularShellsAndSquareParts

/-!
# The quadratic large sieve

The quadratic large sieve for arbitrary finite families of admissible ideals
(`sieveNorm_sharp`), its transpose, reciprocal Cauchy bounds, and square-part fibers acting as
bounded coprimality masks.
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

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀x∈xs, x ≤ H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)

def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0 < η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη,
   2+1/(η*Real.log 2),
   2*diagonalControl sieveCutoff,
   (diagonalControl sieveCutoff) ^ 2,
   (Nat.card Oˣ : ℝ)*(2*diagonalControl sieveCutoff),
   ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ),
   divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   CD,
   CS,
   CT,
   CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   D ^ η]

theorem poissonPrimitiveConstants_nonneg
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0 ≤ CD) (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hCP : 0 ≤ CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0 < η)
    (D : ℝ) (hD : 0 ≤ D) (W : 𝓢(ℝ,ℂ)) :
    ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, 0 ≤ x := by
  have hd := (divisorConstant_pos η hη).le
  have he := (divisorExponentConstant_pos hexp η hη).le
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hdual := dualMiddleDecayConstant_nonneg (quadraticTransformedSquareProfile W)
  have hsource := originalMiddleDecayConstant_nonneg (quadraticSquareProfile W)
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hlog : 0  <  Real.log 2 := Real.log_pos (by norm_num)
  intro x hx
  simp only [poissonPrimitiveConstants,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals positivity

theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0 ≤ CD) (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hCP : 0 ≤ CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0 < η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hP : 1 ≤ P) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x ≤ H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0 ≤ x ∧ x ≤ D*P ^ 4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0 ≤ x ∧ x ≤ (H*P ^ (4*η)) ^ 8 := by
  let V := H*P ^ (4*η)
  have hP0 : 0 < P := by linarith
  have hR : 1 ≤ P ^ (4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1 ≤ V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0 ≤ x ∧ x ≤ V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0 ≤ x ^ η ∧ x ^ η ≤ V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D ^ η ≤ H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P ^ 4) ^ η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D ^ η*P ^ (4*η) := by
        rw [Real.mul_rpow (by linarith : 0 ≤ D) (by positivity : 0 ≤ P ^ 4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ) ^ η,K ^ η,N ^ η,((2*K)*N) ^ η,(N*N) ^ η,
      ((Ideal.absNorm G:ℝ)*(N*N)) ^ η,(K*N) ^ η]
  have hprims : ∀x∈prims, 0 ≤ x ∧ x ≤ V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length ≤ 8) : xs.prod ≤ V ^ 8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x ≤ V ^ 8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  have hd := (divisorConstant_pos η hη).le
  have he := (divisorExponentConstant_pos hexp η hη).le
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hdual := dualMiddleDecayConstant_nonneg (quadraticTransformedSquareProfile W)
  have hsource := originalMiddleDecayConstant_nonneg (quadraticSquareProfile W)
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hlog : 0  <  Real.log 2 := Real.log_pos (by norm_num)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ) ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K ^ η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N ^ η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [2*diagonalControl sieveCutoff,divisorConstant η hη,divisorConstant η hη,N ^ η,N ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N) ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [((idealDivisors (quadraticMaskIdeal 1)).card : ℝ),‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [((idealDivisors (quadraticMaskIdeal 1)).card : ℝ),‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [((idealDivisors (quadraticMaskIdeal 1)).card : ℝ),dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [(diagonalControl sieveCutoff) ^ 2,divisorConstant η hη,(N*N) ^ η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [(diagonalControl sieveCutoff) ^ 2,divisorConstant η hη,((Ideal.absNorm G:ℝ)*(N*N)) ^ η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [(Nat.card Oˣ : ℝ)*(2*diagonalControl sieveCutoff),CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  · refine ⟨by positivity, ?_⟩
    have hh := hp [divisorConstant η hη,N ^ η,CP,(K*N) ^ η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [V,List.prod_cons,List.prod_nil,mul_one,one_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh



theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4 ≤ C) (hCC : C ≤ C1) (hM : 1 ≤ M) (hX : 1 ≤ X)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    4 ≤ selectedPoissonT C M X η ∧
    (M*X) ^ η ≤ selectedPoissonT C M X η ∧
    selectedPoissonK C M X η ≤ C1*(M*X) ^ 3 := by
  have hC10 : 0 ≤ C1 := by linarith
  have hM0 : 0 < M := by linarith
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ M*X := by nlinarith
  have hP0 : 0 < M*X := by positivity
  have hR : 1 ≤ (M*X) ^ η := Real.one_le_rpow hP hη
  have hT : 4 ≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X ≤ M*X := by nlinarith
  have hfrac : X ^ 2/M ≤ (M*X) ^ 2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X) ^ η ≤ M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X) ^ η*(X ^ 2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X) ^ 2 := by gcongr
    _ = C1*(M*X) ^ 3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1 ≤ P) (hB : 1 ≤ B) (hC1 : 1 ≤ C1)
    (hg0 : 0 ≤ g) (hK0 : 0 ≤ K) (hN0 : 0 ≤ N)
    (hg : g ≤ B*P) (hK : K ≤ C1*P ^ 3) (hN : N ≤ P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0 ≤ x ∧ x ≤ (2*C1+B)*P ^ 4 := by
  have hP0 : 0 ≤ P := by linarith
  have hD : 1 ≤ 2*C1+B := by linarith
  have hp14 : P ≤ P ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 ≤ 4 by omega)
  have hp24 : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P ^ 4 := by gcongr
      _ ≤ (2*C1+B)*P ^ 4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P ^ 3 ≤ C1*P ^ 4 := by gcongr
      _ ≤ (2*C1+B)*P ^ 4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0 ≤ P ^ 4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P ^ 3)*P := by gcongr
      _ = (2*C1)*P ^ 4 := by ring
      _ ≤ (2*C1+B)*P ^ 4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P ^ 2 := by ring
      _ ≤ P ^ 4 := hp24
      _ ≤ (2*C1+B)*P ^ 4 := by nlinarith [show 0 ≤ P ^ 4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P ^ 3 := by ring
      _ ≤ B*P ^ 4 := by gcongr
      _ ≤ (2*C1+B)*P ^ 4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P ^ 3)*P := by gcongr
      _ = C1*P ^ 4 := by ring
      _ ≤ (2*C1+B)*P ^ 4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1 ≤ P) (hT : P ^ η ≤ T) (hpow : 4 ≤ η*l) :
    P ^ 4 ≤ T ^ l := by
  have hp0 : 0 < P := by linarith
  calc
    P ^ 4 = P ^ (4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P ^ (η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P ^ η) ^ l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T ^ l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1 ≤ P) (hT : P ^ η ≤ T) (hpow : 4 ≤ η*l)
    (_hK : 0 ≤ K) (hM : 0 ≤ M) (hN : 0 ≤ N) (hC1 : 0 ≤ C1)
    (hKP : K ≤ C1*P ^ 3) (hMP : M ≤ P) (hNP : N ≤ P) :
    K*M/T ^ l ≤ C1 ∧ K*N/T ^ l ≤ C1 := by
  have hp0 : 0 < P := by linarith
  have htpos : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0 ≤ Y) (hYP : Y ≤ P) : K*Y/T ^ l ≤ C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P ^ 3)*P := by gcongr
      _ = C1*P ^ 4 := by ring
      _ ≤ C1*T ^ l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1 ≤ B) (hP : 1 ≤ P) (hM : 0 ≤ M)
    (ht : 1/(B*P ^ 2) ≤ t) (hu : P ^ η ≤ 1+t*K) (hA : 4 ≤ η*A) :
    M/((min 1 t) ^ 2*(1+t*K) ^ A) ≤ B ^ 2*M := by
  have hB0 : 0 < B := by linarith
  have hP0 : 0 < P := by linarith
  have hBP : 1 ≤ B*P ^ 2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P ^ 2) ≤ min 1 t := le_min hinv ht
  have htpos : 0 < min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0 < 1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B ^ 2 ≤ (min 1 t) ^ 2*(1+t*K) ^ A := by
    calc
      1/B ^ 2 = (1/(B*P ^ 2)) ^ 2*P ^ 4 := by field_simp
      _ ≤ (min 1 t) ^ 2*(1+t*K) ^ A := by gcongr
  apply (div_le_iff₀ (by positivity : 0 < (min 1 t) ^ 2*(1+t*K) ^ A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ B ^ 2*M by positivity)
  have he : (B ^ 2*M)*(1/B ^ 2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B ≤ C) (hB : 1 ≤ B) (hM : 1 ≤ M) (hX : 1 ≤ X)
    (hq : 1 ≤ q) (_hη : 0 ≤ η) (hA : 4 ≤ η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q)))) ^ 2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η) ^ A) ≤ B ^ 2*M := by
  have hB0 : 0 < B := by linarith
  have hM0 : 0 < M := by linarith
  have hX0 : 0 < X := by linarith
  have hq0 : 0 < q := by linarith
  have hC0 : 0 < C := by linarith
  have hP : 1 ≤ M*X := by nlinarith
  have hXP : X ≤ M*X := by nlinarith
  have hMQ : 1 ≤ M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X ^ 2) := by field_simp
  have ht : 1/(B*(M*X) ^ 2) ≤ M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X ^ 2) ≤ B*(M*X) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X) ^ 2) := by nlinarith [show 0 ≤ B*(M*X) ^ 2 by positivity]
  have hu : (M*X) ^ η ≤ 1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0 ≤ (M*X) ^ η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X) ^ η ≤ selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X) ^ η*B = B*(M*X) ^ η := by ring
        _ ≤ C*(M*X) ^ η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X) ^ η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4 ≤ C) (hM : 1 ≤ M) (hX : 1 ≤ X) (hN : 0 ≤ N) (hNX : N ≤ X)
    (hη : 0 ≤ η) (hα : 1/2 ≤ α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η) ^ (α-1/2) ≤ 
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) := by
  have hM0 : 0 < M := by linarith
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ M*X := by nlinarith
  have hpow : 1 ≤ (M*X) ^ η := Real.one_le_rpow hP hη
  have hT : 1 ≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0 < selectedPoissonT C M X η := by linarith
  have hK0 : 0 < selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η ≤ (M/X) ^ 2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X) ^ 2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η) ≤ M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N ≤ M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η) ^ (α-1/2) ≤ 
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0 ≤ Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond



def poissonShape (M X α : ℝ) : ℝ := M+X+X ^ (2*α-1)*M ^ (1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1 ^ 3+B ^ 2+C1

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0 < P) :
    262144*((H*P ^ (4*η)) ^ 8) ^ 8*(C*P ^ (3*η)*Z) =
      (262144*H ^ 64*C)*P ^ (259*η)*Z := by
  have hp : (P ^ (4*η)) ^ 64*P ^ (3*η)=P ^ (259*η) := by
    calc
      _ = P ^ ((4*η)*64)*P ^ (3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P ^ ((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H ^ 64*C)*((P ^ (4*η)) ^ 64*P ^ (3*η))*Z := by ring
    _ = _ := by rw [hp]

theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (hα2 : α ≤ 2)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (l A : ℕ)
    (hl : 4 ≤ η*l) (hA : 4 ≤ η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0 ≤ CD) (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hCP : 0 ≤ CP)
    (B C1 : ℝ) (hB : 1 ≤ B) (hC1 : 1 ≤ C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0 < Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4 ≤ C → B ≤ C → C ≤ C1 →
        1 ≤ M → 1 ≤ X → 1 ≤ q → q ≤ X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1 ≤ selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤ 
        Cfinal*(M*X) ^ (259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1 ≤ D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0 ≤ C1 := le_trans zero_le_one hC1
  have hCs : 1 ≤ Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1 ≤ Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B ^ 2 ≤ Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1 ^ 3 ≤ Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H ^ 64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1 ≤ M*X := by nlinarith only [hM,hX]
  have hP0 : 0 < M*X := by positivity
  have hMP : M ≤ M*X := by nlinarith only [hM,hX]
  have hXP : X ≤ M*X := by nlinarith only [hM,hX]
  have hN : 1 ≤ X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q ≤ X := div_le_self hX0.le hq
  have hNP : X/q ≤ M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0 ≤ selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ) ≤ B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X) ^ (3*η)
  have hR : 1 ≤ R := Real.one_le_rpow hP (by positivity)
  let Z := X ^ (2*α-1)*M ^ (1-α)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1 ≤ poissonShape M X α := by
    change 1 ≤ M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0 ≤ poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M ≤ poissonShape M X α := by
    change M ≤ M+X+Z
    linarith only [hX,hZ]
  have hXshape : X ≤ poissonShape M X α := by
    change X ≤ M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z ≤ poissonShape M X α := by
    change Z ≤ M+X+Z
    linarith only [hM,hX]
  have hRshape : 1 ≤ R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α ≤ S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M ≤ S := hMshape.trans hshapeS
  have hNS : X/q ≤ S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) ≤ 
      4*C1 ^ 3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C ^ 3*R*Z ≤ 4*C1 ^ 3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) ≤ S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η) ^ (α-1/2) ≤ S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2)
 ≤ poissonShape M X α+4*C1 ^ 3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1 ^ 3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1 ^ 3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1 ≤ S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))) ^ 2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η) ^ A) ≤ S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B ^ 2*M ≤ B ^ 2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1 ≤ H*(M*X) ^ (4*η) := by
    have hh := Real.one_le_rpow hP (show 0 ≤ 4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1 ≤ (H*(M*X) ^ (4*η)) ^ 8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X) ^ (4*η)) ^ 8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (hα2 : α ≤ 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (η : ℝ) (hη : 0 < η), η ≤ 1 ∧ 259*η ≤ ρ ∧
    ∃ (l A : ℕ), 4 ≤ η*l ∧ 4 ≤ η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0 ≤ CD → 0 ≤ CS → 0 ≤ CT → 0 ≤ CP →
      ∀ (B C1 : ℝ), 1 ≤ B → 1 ≤ C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0 < Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4 ≤ C → B ≤ C → C ≤ C1 →
          1 ≤ M → 1 ≤ X → 1 ≤ q → q ≤ X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1 ≤ selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤ 
          Cfinal*(M*X) ^ ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηρ : 259*η ≤ ρ := by
    have hh : η ≤ ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4 ≤ η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1 ≤ M*X := by nlinarith
  have hshape : 0 ≤ poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein FiniteSieveRestriction
open scoped Classical

def coefficientScaleSupport (N X : ℝ) : Finset (QuadraticIdealRange N) :=
  Finset.univ.filter (fun J => (Ideal.absNorm J.val.val : ℝ) ≤ X)

def coefficientScaleColumn (N X : ℝ) (J : coefficientScaleSupport N X) : QuadraticIdealRange X :=
  ⟨J.val.val,(Finset.mem_filter.mp J.property).2⟩

lemma coefficientScaleColumn_injective (N X : ℝ) : Function.Injective (coefficientScaleColumn N X) := by
  intro I J h
  exact Subtype.ext (Subtype.ext (congrArg (fun Q : QuadraticIdealRange X => Q.val) h))

/-- Reindex coefficients by any norm ball containing their support. -/
def coefficientAtScale (N X : ℝ) (a : QuadraticIdealRange N → ℂ) : QuadraticIdealRange X → ℂ :=
  extendByZero Finset.univ (coefficientScaleColumn N X) (fun J : coefficientScaleSupport N X => a J.val)

theorem coefficientAtScale_row_sum (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val.val : ℝ) ≤ X) (z : O) :
    (∑ J, canonicalQuadraticRow J.val z*a J) =
      ∑ J, canonicalQuadraticRow J.val z*coefficientAtScale N X a J := by
  rw [coefficientAtScale,extendByZero_matrix Finset.univ (coefficientScaleColumn N X)
    (fun J : coefficientScaleSupport N X => a J.val)
    (fun (_ : Unit) (J : QuadraticIdealRange X) => canonicalQuadraticRow J.val z) ()]
  change _ = ∑ J : coefficientScaleSupport N X, canonicalQuadraticRow J.val.val z*a J.val
  rw [Finset.sum_coe_sort (coefficientScaleSupport N X)
    (fun J : QuadraticIdealRange N => canonicalQuadraticRow J.val z*a J)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro J _ hJ
  have hz : a J = 0 := by
    by_contra hn
    exact hJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha J hn⟩)
  rw [hz,mul_zero]

theorem coefficientAtScale_energy (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val.val : ℝ) ≤ X) :
    (∑ J, ‖coefficientAtScale N X a J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 := by
  rw [coefficientAtScale,extendByZero_energy _ _ _ (coefficientScaleColumn_injective N X).injOn]
  change (∑ J : coefficientScaleSupport N X, ‖a J.val‖ ^ 2) = _
  rw [Finset.sum_coe_sort (coefficientScaleSupport N X) (fun J : QuadraticIdealRange N => ‖a J‖ ^ 2)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro J _ hJ
  have hz : a J = 0 := by
    by_contra hn
    exact hJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha J hn⟩)
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem coefficientAtScale_shell (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell X X (coefficientAtScale N X a) := by
  intro J hJ
  have hm : J ∈ (Finset.univ : Finset (coefficientScaleSupport N X)).image (coefficientScaleColumn N X) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,_,rfl⟩ := Finset.mem_image.mp hm
  have he : coefficientAtScale N X a (coefficientScaleColumn N X I) = a I.val :=
    extendByZero_apply_image _ _ _ (coefficientScaleColumn_injective N X).injOn I (Finset.mem_univ I)
  rw [he] at hJ
  exact ha I.val hJ

theorem dyadicColumnCoefficient_at_scale_energy (N : ℝ) (lengthScale : ℕ)
    (hNL : N ≤ (2 : ℝ) ^ lengthScale) (a : QuadraticIdealRange N → ℂ) :
    (∑ j : Fin (lengthScale+1), ∑ J, ‖coefficientAtScale N ((2 : ℝ) ^ j.val)
      (dyadicColumnCoefficient N lengthScale hNL j a) J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 := by
  have he (j : Fin (lengthScale+1)) := coefficientAtScale_energy N ((2 : ℝ) ^ j.val)
    (dyadicColumnCoefficient N lengthScale hNL j a)
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)
  simp_rw [he]
  exact dyadicColumnCoefficient_energy N lengthScale hNL a

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M ≤ M') (a : QuadraticIdealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ ballQuadraticEnergy M' N a := by
  let f : QuadraticIdealRange M → QuadraticIdealRange M' := fun I => ⟨I.val,I.property.trans hM⟩
  have hf : Function.Injective f := fun I J h => Subtype.ext (congrArg (fun Q : QuadraticIdealRange M' => Q.val) h)
  let E : QuadraticIdealRange M' → ℝ := fun I =>
    ‖∑ J, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val)*a J‖ ^ 2
  change (∑ I, E (f I)) ≤ ∑ I, E I
  rw [← Finset.sum_image (f := E) (g := f) (fun _ _ _ _ h => hf h)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

theorem ballQuadraticEnergy_coefficientAtScale (M N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val.val : ℝ) ≤ X) :
    ballQuadraticEnergy M N a = ballQuadraticEnergy M X (coefficientAtScale N X a) := by
  unfold ballQuadraticEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem annularHighEnergy_coefficientAtScale (M N X K : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val.val : ℝ) ≤ X) :
    annularHighEnergy M N K a = annularHighEnergy M X K (coefficientAtScale N X a) := by
  unfold annularHighEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem ballQuadraticEnergy_column_shells (M N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : QuadraticIdealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1 : ℝ)*∑ j : Fin (lengthScale+1),
      ballQuadraticEnergy M N (dyadicColumnCoefficient N lengthScale hNL j a) := by
  simpa only [one_mul,ballQuadraticEnergy] using
    weighted_energy_column_shells N lengthScale hNL
      (fun I : QuadraticIdealRange M => fun J : QuadraticIdealRange N => canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val))
      (fun _ => (1 : ℝ)) (fun _ => by norm_num) a

theorem ballQuadraticEnergy_column_shells_at_scale (M N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : QuadraticIdealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1 : ℝ)*∑ j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2 : ℝ) ^ j.val)
        (coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale+1 : ℝ)*x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein FiniteSieveRestriction
open scoped Classical

theorem liftingFreeCoefficient_shell (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N X (liftingFreeCoefficient N a) := by
  intro J hJ
  have hj : a J≠0 := by
    intro hz
    exact hJ (by simp only [liftingFreeCoefficient,hz,ite_self])
  exact ha J hj

theorem liftingDividedCoefficient_shell (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2 < (Ideal.absNorm (quadraticIdealQuotient liftingPrime I.val.val.val):ℝ) ∧
    (Ideal.absNorm (quadraticIdealQuotient liftingPrime I.val.val.val):ℝ) ≤ X/7
  rw [quadraticIdealQuotient_norm liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

theorem coefficientOnShell_zero_or_scale (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : (∀J, a J=0) ∨ 1 ≤ X := by
  classical
  by_cases h : ∀J, a J=0
  · exact Or.inl h
  · push Not at h
    obtain ⟨J,hJ⟩ := h
    have hnorm : 1 ≤ (Ideal.absNorm J.val.val:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => (primaryIdealGenerator_ne_zero_ideal _ J.val.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
    exact Or.inr (hnorm.trans (ha J hJ).2)

theorem columnDyadicLength_scale_upper (N : ℝ) (hN : 1 ≤ N) :
    (2:ℝ) ^ columnDyadicLength N ≤ 2*N := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ) ^ ((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ) ^ (Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_one]
      have he : (2:ℝ) ^ (Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]

theorem columnDyadicScale_bounds (N : ℝ) (hN : 1 ≤ N) (j : Fin (columnDyadicLength N+1)) :
    1 ≤ (2:ℝ) ^ j.val ∧ (2:ℝ) ^ j.val ≤ 2*N := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  exact (pow_le_pow_right₀ (by norm_num) (by omega : j.val ≤ columnDyadicLength N)).trans
    (columnDyadicLength_scale_upper N hN)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein FiniteSieveRestriction
open scoped Classical

theorem improved_threshold_ge_column (α N M : ℝ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (hM : N ^ (2-1/α) ≤ M) : N ≤ M := by
  have hp : 1 ≤ 2-1/α := by
    have hh : 1/α ≤ 1 := (div_le_one (by linarith : 0 < α)).mpr hα
    linarith
  calc
    N = N ^ (1:ℝ) := (Real.rpow_one N).symm
    _ ≤ N ^ (2-1/α) := Real.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ M := hM

theorem improved_threshold_power (α N M : ℝ) (hα : 0 < α) (hN : 0 < N)
    (hM : N ^ (2-1/α) ≤ M) : N ^ (2*α-1) ≤ M ^ α := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hM hα.le
  rw [←Real.rpow_mul hN.le] at hh
  have he : (2-1/α)*α=2*α-1 := by field_simp
  rwa [he] at hh

theorem improved_threshold_main (α N M : ℝ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (hM : N ^ (2-1/α) ≤ M) : N ^ (2*α-1)*M ^ (1-α) ≤ M := by
  have hNM := improved_threshold_ge_column α N M hα hN hM
  have hM0 : 0 < M := by linarith
  have hh := improved_threshold_power α N M (by linarith) (by linarith) hM
  calc
    _ ≤ M ^ α*M ^ (1-α) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hM0.le _)
    _ = M := by rw [←Real.rpow_add hM0]; simp

theorem improved_threshold_shape (α N M : ℝ) (hα : 1 ≤ α) (hN : 1 ≤ N)
    (hM : N ^ (2-1/α) ≤ M) : M+N+N ^ (2*α-1)*M ^ (1-α) ≤ 3*M := by
  linarith [improved_threshold_main α N M hα hN hM,
    improved_threshold_ge_column α N M hα hN hM]

theorem improved_threshold_reciprocal (α N M : ℝ) (_hα : 0 < α) (hN : 0 < N) (hM0 : 0 < M)
    (hM : N ^ (2-1/α) ≤ M) : N ^ 2/M ≤ N ^ (1/α) := by
  apply (div_le_iff₀ hM0).mpr
  have he : N ^ 2=N ^ (2-1/α)*N ^ (1/α) := by
    rw [←Real.rpow_add hN]
    convert (Real.rpow_two N).symm using 1 ; ring_nf
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hN.le (1/α))

theorem improved_threshold_low (α C η N M : ℝ) (hα : 0 < α) (hC : 0 < C)
    (hN : 0 < N) (hM0 : 0 < M) (hM : N ^ (2-1/α) ≤ M) :
    (selectedPoissonK C M N η) ^ α ≤ C ^ α*(M*N) ^ (η*α)*N := by
  have hk : selectedPoissonK C M N η ≤ C*(M*N) ^ η*N ^ (1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0 ≤ selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N) ^ η*N ^ (1/α)) ^ α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ C*(M*N) ^ η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0 ≤ M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]

theorem sieveNorm_large_rows (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hlarge : N ^ 2 ≤ M) :
    sieveNorm M N ≤ 5*sieveNorm_initial.choose*M := by
  have hc := sieveNorm_initial.choose_spec.1
  have hb := sieveNorm_initial.choose_spec.2 M N hM hN
  nlinarith only [hb,hlarge,hc,hM]

theorem hasSieveExponent_of_threshold_band (β : ℝ) (_hβ1 : 1 ≤ β) (hβ2 : β ≤ 2)
    (hband : ∀ρ : ℝ, 0 < ρ → ∃C : ℝ, 0 < C ∧ ∀M N : ℝ,
      1 ≤ M → 1 ≤ N → N ^ β ≤ M → M ≤ N ^ 2 → sieveNorm M N ≤ C*(M*N) ^ ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0 < ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := sieveNorm_initial.choose
  have hI : 0 < I := sieveNorm_initial.choose_spec.1
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 1 ≤ M*N := by nlinarith
  have hpow : 1 ≤ (M*N) ^ ε := Real.one_le_rpow hMN hε.le
  have hNb : 0 ≤ N ^ β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N ^ 2 ≤ M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N) ^ ε*(M+N ^ β) := by gcongr <;> linarith
  · let R := max M (N ^ β)
    have hNβsq : N ^ β ≤ N ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1 ≤ R := hM.trans (le_max_left _ _)
    have hRM : M ≤ R := le_max_left _ _
    have hRN : N ^ β ≤ R := le_max_right _ _
    have hRsq : R ≤ N ^ 2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    have hM3 : M ≤ M ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ) ≤ 3 by decide)
    have hRN2 : R ≤ M*N ^ 2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N ≤ (M*N) ^ 3 := by
      calc
        _ ≤ (M*N ^ 2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N ^ 3 := by ring
        _ ≤ M ^ 3*N ^ 3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N) ^ (ε/3) ≤ (M*N) ^ ε := by
      calc
        _ ≤ ((M*N) ^ 3) ^ (ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0 ≤ M*N)]
          congr 1
          ring
    have hRadd : R ≤ M+N ^ β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))



theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2)
    (hshell : ∀ρ : ℝ, 0 < ρ → ∃C : ℝ, 0 < C ∧ ∀M X : ℝ,
      1 ≤ M → 1 ≤ X → X ^ β ≤ M → ∀a : QuadraticIdealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a ≤ C*(M*X) ^ ρ*M*∑J,‖a J‖ ^ 2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0 < lengthScale := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8 ^ (ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hprod : 0 < M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ) ^ j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ) ^ j.val) (a' j) ≤ 
        (4*C*8 ^ (ε/2)*(M*N) ^ (ε/2)*M)*∑J,‖a' j J‖ ^ 2 := by
    let X := (2:ℝ) ^ j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0 ≤ β := by linarith
    have hXpow : X ^ β ≤ 4*M := by
      calc
        _ ≤ (2*N) ^ β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2 ^ β*N ^ β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N ^ β := by
          have ht : (2:ℝ) ^ β ≤ 4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ) ≤ 2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X) ^ (ε/2) ≤ 8 ^ (ε/2)*(M*N) ^ (ε/2) := by
      calc
        _ ≤ (8*(M*N)) ^ (ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M ≤ 4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8 ^ (ε/2)*(M*N) ^ (ε/2))*(4*M)*∑J,‖a' j J‖ ^ 2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖ ^ 2)=∑J,‖a J‖ ^ 2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ) ≤ lengthScale*(M*N) ^ (ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N ^ (ε/2) ≤ lengthScale*(M*N) ^ (ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a ≤ _
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8 ^ (ε/2)*(M*N) ^ (ε/2)*M)*∑J,‖a' j J‖ ^ 2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8 ^ (ε/2)*(M*N) ^ (ε/2)*M)*(∑J,‖a J‖ ^ 2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N) ^ (ε/2))*(4*C*8 ^ (ε/2)*(M*N) ^ (ε/2)*M)*(∑J,‖a J‖ ^ 2) := by gcongr
    _ = _ := by
      have hp : (M*N) ^ (ε/2)*(M*N) ^ (ε/2)=(M*N) ^ ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8 ^ (ε/2)*lengthScale)*((M*N) ^ (ε/2)*(M*N) ^ (ε/2))*M*(∑J,‖a J‖ ^ 2) := by ring
        _ = _ := by rw [hp]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein UniqueFactorizationMonoid
open scoped Classical

lemma quadraticMaskIdeal_norm (D : Ideal O) (hD : quadraticIdealAdmissible D) :
    Ideal.absNorm (quadraticMaskIdeal D) = Ideal.absNorm (quadraticMaskIdeal 1)*Ideal.absNorm D := by
  have hn := (squarefree_iff_nodup_normalizedFactors
    (primaryIdealGenerator_ne_zero_ideal D hD.1)).mp hD.2.1
  have hv : (primeSupport D).val = normalizedFactors D := by
    simpa only [primeSupport,Multiset.toFinset_val] using hn.dedup
  have he : (∏ P ∈ primeSupport D, P) = D := by
    change ((primeSupport D).val.map id).prod = D
    rw [Multiset.map_id,hv]
    exact Ideal.prod_normalizedFactors_eq_self (primaryIdealGenerator_ne_zero_ideal D hD.1)
  rw [quadraticMaskIdeal_supported_factor D ⟨hD.1,hD.2.2⟩,he,map_mul]

def fixedBadNorm : ℝ := Ideal.absNorm (quadraticMaskIdeal 1)
def fixedCutoffBase : ℝ := max 4 fixedBadNorm

lemma fixedBadNorm_one_le : 1 ≤ fixedBadNorm := by
  unfold fixedBadNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (quadraticMaskIdeal_squarefree 1).ne_zero)

lemma fixedCutoffBase_bounds : 4 ≤ fixedCutoffBase ∧ fixedBadNorm ≤ fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem HasSieveExponent.annular_selected_bound {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (l A : ℕ) (hl : 4 ≤ η*l) (hA : 4 ≤ η*A) (C1 : ℝ) (hC1 : 1 ≤ C1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase ≤ c → c ≤ C1 → 1 ≤ M → 4 ≤ N → N ^ (2-1/α) ≤ M →
      1 ≤ selectedPoissonK c M N η →
      ∀ (a : QuadraticIdealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤ 
        C*(M*N) ^ (260*η)*M*∑J,‖a J‖ ^ 2 := by
  have hα : 1/2 ≤ α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 annularSieveCutoff
  have hdiv : 0 < divisorConstant η hη := divisorConstant_pos η hη
  let SD := (divisorConstant η hη) ^ 2
  have hSD : 0 < SD := sq_pos_of_pos (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2 ^ η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hP : 1 ≤ M*N := by nlinarith
  have hP0 : 0 < M*N := by positivity
  have hc4 : 4 ≤ c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm ≤ c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4 ≤ selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N ^ 2/M ≤ selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0 ≤ N ^ 2/M := by positivity
    nlinarith
  have hH := largeCommonFactorThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈commonFactorPool (fun J : QuadraticIdealRange N => J.val),
      (Ideal.absNorm D:ℝ) ≤ largeCommonFactorThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (quadraticMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        annularSieveCutoff ≤ 3*CF*(M*N) ^ (259*η)*M := by
    intro D hD hd
    have hadm := commonFactorPool_admissible (fun J : QuadraticIdealRange N => J.val)
      D hD
    have hd1 : 1 ≤ (Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (primaryIdealGenerator_ne_zero_ideal D hadm.1) (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (quadraticMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [quadraticMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (quadraticMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (quadraticMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α ≤ 3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N) ^ (259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeCommonFactorThreshold α N) (3*CF*(M*N) ^ (259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_commonFactor_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N ^ η ≤ (M*N) ^ η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N) ^ (259*η)*(M*N) ^ η=(M*N) ^ (260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N) ^ η*((M*N) ^ η) ^ 2=(M*N) ^ (3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N) ^ (3*η) ≤ (M*N) ^ (260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hunit : 1 ≤ (Nat.card Oˣ : ℝ) := by
    have hn : Nat.card Oˣ ≠ 0 := by
      intro h
      exact eisenstein_unit_card_ne_zero (by rw [h]; norm_num)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hfirst : (3*CF*(M*N) ^ (259*η)*M/(Nat.card Oˣ : ℝ))*(divisorConstant η hη*N ^ η) ≤ 
      (3*CF*divisorConstant η hη)*(M*N) ^ (260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N) ^ (259*η)*M)*(divisorConstant η hη*(M*N) ^ η) := by
        exact mul_le_mul (div_le_self (by positivity) hunit)
          (mul_le_mul_of_nonneg_left hn hdiv.le) (by positivity) (by positivity)
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeCommonFactorThreshold α N)) ^ η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeCommonFactorThreshold α N) ^ α))*
      SD*(N ^ η) ^ 2 ≤ (4*CH*2 ^ η*SD)*(M*N) ^ (260*η)*M := by
    calc
      _ ≤ ((4*CH*2 ^ η)*(M*N) ^ η*M)*SD*((M*N) ^ η) ^ 2 := by gcongr
      _ = (4*CH*2 ^ η*SD)*(M*N) ^ (3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N) ^ (260*η)*M+
      (4*CH*2 ^ η*SD)*(M*N) ^ (260*η)*M)*∑J,‖a J‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst (by simpa only [SD,mul_pow,mul_assoc] using hsecond)) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0 < η → ∃ α : ℝ, α ≤ 1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 1 ≤ M*N := by nlinarith
  have hNmn : N ≤ M*N := by nlinarith
  have hQ : 1 ≤ (M*N) ^ (ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N ^ α ≤ (M*N) ^ (ε/2)*N := by
    calc
      _ ≤ N ^ (1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N ^ (ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N) ^ (ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N ^ α ≤ (M*N) ^ (ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N) ^ (ε/2)*(M+N ^ α) := hbound M N hM hN
    _ ≤ C*(M*N) ^ (ε/2)*((M*N) ^ (ε/2)*(M+N)) := by gcongr
    _ = C*(M*N) ^ ε*(M+N ^ (1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N) ^ (ε/2)*(M*N) ^ (ε/2) = (M*N) ^ ε := by
        rw [← Real.rpow_add (by positivity : 0 < M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N) ^ (ε/2)*(M*N) ^ (ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

theorem bootstrapExponent_gt_one (n : ℕ) : 1 < bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n ≤ 2 := by
  have h : 1/((n:ℝ)+1) ≤ (1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1 < α → α ≤ 2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem lifting_annular_scale_bounds (j : Fin 7) : 1 ≤ (2:ℝ) ^ j.val ∧ (2:ℝ) ^ j.val ≤ 64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val ≤ 6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (l A : ℕ) (hl : 4 ≤ η*l) (hA : 4 ≤ η*A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℝ),
      1 ≤ M → 28 ≤ N → N ^ (2-1/α) ≤ M →
      1 ≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1 ≤ q → q ≤ 7 →
      ∀ (a : QuadraticIdealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ) ^ j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤ 
        C*(M*N) ^ (260*η)*M*∑J,‖a J‖ ^ 2 := by
  have hc0 : 0 < fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64 ^ (260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ) ^ j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hNq : 4 ≤ N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q ≤ N := div_le_self hN0.le hq
  have hβ : 0 ≤ 2-1/α := by
    have hfrac : 1/α ≤ 1 := (div_le_one (by linarith : 0 < α)).mpr hα1
    linarith
  have hth : (N/q) ^ (2-1/α) ≤ r*M := by
    calc
      _ ≤ N ^ (2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q)) ^ (260*η) ≤ 64 ^ (260*η)*(M*N) ^ (260*η) := by
    calc
      _ ≤ (64*(M*N)) ^ (260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a ≤ _
  apply hh.trans
  calc
    _ ≤ C*(64 ^ (260*η)*(M*N) ^ (260*η))*(64*M)*∑J,‖a J‖ ^ 2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (l A : ℕ) (hl : 4 ≤ η*l) (hA : 4 ≤ η*A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℝ),
      1 ≤ M → 28 ≤ N → N ^ (2-1/α) ≤ M →
      1 ≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : QuadraticIdealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤ 
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N) ^ (260*η)*M)*∑J,‖a J‖ ^ 2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖ ^ 2)+
      2*(7*(C*(M*N) ^ (260*η)*M*∑J,‖liftingFreeCoefficient N a J‖ ^ 2)+
        7*(C*(M*N) ^ (260*η)*M*∑J,‖liftingDividedCoefficient N a J‖ ^ 2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖ ^ 2)+
          (14*C)*(M*N) ^ (260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖ ^ 2)+
            (∑J,‖liftingDividedCoefficient N a J‖ ^ 2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 ≤ α) (hα2 : α ≤ 2) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (c : ℝ) (hc : 4 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → N ^ (2-1/α) ≤ M → M ≤ N ^ 2 →
      sieveNorm (selectedPoissonK c M N η) N ≤ C*(M*N) ^ (6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0 < c := by linarith
  refine ⟨C*c ^ η*(1+c ^ α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hP : 1 ≤ M*N := by nlinarith
  have hP0 : 0 < M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N ≤ M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N ≤ c*(M*N) ^ 4 := by
    calc
      _ ≤ (c*(M*N) ^ 3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N) ^ η ≤ c ^ η*(M*N) ^ (4*η) := by
    calc
      _ ≤ (c*(M*N) ^ 4) ^ η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η) ^ α ≤ c ^ α*(M*N) ^ (2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N) ^ (η*α) ≤ (M*N) ^ (2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1 ≤ (M*N) ^ (2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η) ^ α ≤ (1+c ^ α)*(M*N) ^ (2*η)*M := by
    calc
      _ ≤ M+c ^ α*(M*N) ^ (2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N) ^ (2*η)*M+c ^ α*(M*N) ^ (2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N) ^ (4*η)*(M*N) ^ (2*η)=(M*N) ^ (6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N) ^ η*(N+(selectedPoissonK c M N η) ^ α) := hrev _ _ hK hN
    _ ≤ C*(c ^ η*(M*N) ^ (4*η))*((1+c ^ α)*(M*N) ^ (2*η)*M) := by gcongr
    _ = C*c ^ η*(1+c ^ α)*((M*N) ^ (4*η)*(M*N) ^ (2*η))*M := by ring
    _ = _ := by rw [hpowers]


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hN28 : N ≤ 28) :
    sieveNorm M N ≤ 785*sieveNorm_initial.choose*M := by
  have hc := sieveNorm_initial.choose_spec.1
  have hb := sieveNorm_initial.choose_spec.2 M N hM hN
  have hs : N ^ 2 ≤ 784 := by nlinarith only [hN,hN28]
  nlinarith only [hb,hs,hc,hM]

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) :
    ∀ρ : ℝ, 0 < ρ → ∃C : ℝ, 0 < C ∧ ∀M N : ℝ,
      1 ≤ M → 1 ≤ N → N ^ (2-1/α) ≤ M →
      ∀a : QuadraticIdealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤ C*(M*N) ^ ρ*M*∑J,‖a J‖ ^ 2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηρ : η ≤ ρ/600 := min_le_right _ _
  have h6 : 6*η ≤ ρ := by linarith only [hηρ,hη]
  have h260 : 260*η ≤ ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4 ≤ η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := sieveNorm_initial.choose
  have hI : 0 < I := sieveNorm_initial.choose_spec.1
  let C := 790*I+CL+CH
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1 ≤ M*N := by nlinarith only [hM,hN]
  have hPρ : 1 ≤ (M*N) ^ ρ := Real.one_le_rpow hP hρ.le
  have hE : 0 ≤ ∑J,‖a J‖ ^ 2 := by positivity
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x ≤ y) :
      x*M*∑J,‖a J‖ ^ 2 ≤ y*M*∑J,‖a J‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a ≤ sieveNorm M N*∑J,‖a J‖ ^ 2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N ^ 2 ≤ M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖ ^ 2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖ ^ 2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I ≤ C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N ≤ 28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖ ^ 2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖ ^ 2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I ≤ C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M ≤ N ^ 2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N) ^ (6*η) ≤ (M*N) ^ ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N) ^ (260*η) ≤ (M*N) ^ ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N) ^ (260*η)*M)*∑J,‖a J‖ ^ 2 := hb
    _ ≤ (CL*(M*N) ^ (6*η)*M+CH*(M*N) ^ (260*η)*M)*∑J,‖a J‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N) ^ ρ*M+CH*(M*N) ^ ρ*M)*∑J,‖a J‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N) ^ ρ*M*∑J,‖a J‖ ^ 2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH ≤ C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) : HasSieveExponent (2-1/α) := by
  have hα : 0 < α := by linarith
  have hfrac : 1/α ≤ 1 := (div_le_one hα).mpr hα1
  have hpos : 0 ≤ 1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2



theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N) ^ ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

/-- The quadratic large sieve for arbitrary finite families of admissible ideals. -/
theorem finite_family_quadratic_large_sieve :
    ∀ ε : ℝ, 0  <  ε → ∃ C : ℝ, 0  <  C ∧
    ∀ (M N : ℝ), 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal),
      Function.Injective rows → Function.Injective cols →
      (∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M) →
      (∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val)*a j‖ ^ 2) ≤ 
        C*(M*N) ^ ε*(M+N)*∑ j, ‖a j‖ ^ 2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  have he := FiniteSieveOperator.energy_bound
    (fun i j => canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val)) a
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have hE : 0 ≤ ∑ j, ‖a j‖ ^ 2 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hn hE).trans
    (mul_le_mul_of_nonneg_right (hsharp M N hM hN) hE))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped Classical

/-- Transposing the real quadratic character matrix preserves the sharp sieve bound. -/
theorem finite_family_quadratic_hybrid_orientation :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal),
      Function.Injective rows → Function.Injective cols →
      (∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M) →
      (∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, canonicalQuadraticRow (rows i) (primaryIdealGenerator (cols j).val)*a j‖ ^ 2) ≤
        C*(M*N) ^ ε*(M+N)*∑ j, ‖a j‖ ^ 2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  let B : Matrix n m ℂ := fun j i => canonicalQuadraticRow (rows i) (primaryIdealGenerator (cols j).val)
  have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm N M :=
    family_squared_norm_le cols rows hc hr N M hcols hrows
  have hBT : B.conjTranspose =
      (fun i j => canonicalQuadraticRow (rows i) (primaryIdealGenerator (cols j).val)) := by
    ext i j
    exact canonicalQuadraticRow_star _ _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose a
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hE : 0 ≤ ∑ j, ‖a j‖ ^ 2 := by positivity
  apply he.trans
  calc
    _ ≤ sieveNorm N M*∑ j, ‖a j‖ ^ 2 := mul_le_mul_of_nonneg_right hB hE
    _ ≤ (C*(N*M) ^ ε*(N+M))*∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hsharp N M hN hM) hE
    _ = _ := by rw [mul_comm N M,add_comm N M]

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0) (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)) ≤
      (2*diagonalControl sieveCutoff)*(columnDyadicLength H+1 : ℝ) := by
  have hd := diagonalControl_nonneg sieveCutoff
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)) ≤ 2*diagonalControl sieveCutoff := by
    have hp : 0 < (2 : ℝ) ^ j.val := by positivity
    have hone : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ diagonalControl sieveCutoff*(2 : ℝ) ^ j.val := by
      apply finite_ideal_card_bound _ _ hone
      intro I hI
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
      simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ) ≤ 2/(2 : ℝ) ^ j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith only [hb]
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 2/(2 : ℝ) ^ j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ)*(2/(2 : ℝ) ^ j.val) := by simp
      _ ≤ (diagonalControl sieveCutoff*(2 : ℝ) ^ j.val)*(2/(2 : ℝ) ^ j.val) := by gcongr
      _ = _ := by field_simp
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 2*diagonalControl sieveCutoff :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0)
    (v : Ideal O → ℂ) :
    ‖∑ I ∈ S, v I‖ ^ 2 ≤ (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ))*
      (∑ I ∈ S, (Ideal.absNorm I : ℝ)*‖v I‖ ^ 2) := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped Classical

lemma quadraticSquarePart_norm_decomposition (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (quadraticSquarePart I) : ℝ) ^ 2 *
      (Ideal.absNorm (quadraticSquarefreePart I) : ℝ) = Ideal.absNorm I := by
  have h := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (quadraticParts_mul_square I hI)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,mul_comm] using h

def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => quadraticSquarePart I = A)

lemma columnSquareFiber_injective (S : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => quadraticSquarefreePart I.val) := by
  intro I J he
  change quadraticSquarefreePart I.val = quadraticSquarefreePart J.val at he
  apply Subtype.ext
  have hi := Finset.mem_filter.mp I.property
  have hj := Finset.mem_filter.mp J.property
  calc
    I.val = quadraticSquarefreePart I.val*A ^ 2 := by
      simpa only [hi.2] using (quadraticParts_mul_square I.val (hS I.val hi.1)).symm
    _ = quadraticSquarefreePart J.val*A ^ 2 := by rw [he]
    _ = J.val := by simpa only [hj.2] using quadraticParts_mul_square J.val (hS J.val hj.1)

lemma columnSquareFiber_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, quadraticSupported I ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    quadraticIdealAdmissible (quadraticSquarefreePart I.val) ∧
      (Ideal.absNorm (quadraticSquarefreePart I.val) : ℝ) ≤ X/(Ideal.absNorm A : ℝ) ^ 2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hI0 := primaryIdealGenerator_ne_zero_ideal I.val hi.1.1
  have hp := (quadraticSupported_parts I.val hI0).mp hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A ≠ 0 := by rw [← ha]; exact quadraticSquarePart_ne_zero I.val
  have hAn : 0 < (Ideal.absNorm A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨hp.1,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn := quadraticSquarePart_norm_decomposition I.val hI0
  rw [ha] at hn
  nlinarith only [hn,hi.2]

lemma columnSquareFiber_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, quadraticSupported I ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (hscale : 1 ≤ X/(Ideal.absNorm A : ℝ) ^ 2) :
    ((columnSquareFiber S A).card : ℝ) ≤ diagonalControl sieveCutoff*(X/(Ideal.absNorm A : ℝ) ^ 2) := by
  let T := (columnSquareFiber S A).image quadraticSquarefreePart
  have hcard : T.card = (columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩ : columnSquareFiber S A) = (⟨J,hJ⟩ : columnSquareFiber S A) :=
      columnSquareFiber_injective S (fun I hI => primaryIdealGenerator_ne_zero_ideal I (hS I hI).1.1) A he
    exact congrArg Subtype.val hh)
  rw [← hcard]
  apply finite_ideal_card_bound T _ hscale
  intro I hI
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2

/-- A fixed square part acts only as a bounded coprimality mask on quadratic rows. -/
theorem columnSquareFiber_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀ I ∈ S, quadraticSupported I ∧ (Ideal.absNorm I : ℝ) ≤ X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑ k : QuadraticIdealRange K, ‖∑ I ∈ columnSquareFiber S A,
      canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤
      sieveNorm (X/(Ideal.absNorm A : ℝ) ^ 2) K * ∑ I ∈ columnSquareFiber S A, ‖a I‖ ^ 2 := by
  let T := columnSquareFiber S A
  let rows : T → QuadraticIdeal := fun I =>
    ⟨quadraticSquarefreePart I.val,(columnSquareFiber_bounds S X hS A I).1⟩
  let B : Matrix T (QuadraticIdealRange K) ℂ := fun I k =>
    canonicalQuadraticRow k.val (primaryIdealGenerator (rows I).val)
  have hr : Function.Injective rows := by
    intro I J h
    exact columnSquareFiber_injective S (fun I hI => primaryIdealGenerator_ne_zero_ideal I (hS I hI).1.1) A
      (congrArg (fun Q : QuadraticIdeal => Q.val) h)
  have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm (X/(Ideal.absNorm A : ℝ) ^ 2) K :=
    family_squared_norm_le rows (fun k : QuadraticIdealRange K => k.val) hr Subtype.val_injective _ _
      (fun I => (columnSquareFiber_bounds S X hS A I).2) (fun k => k.property)
  have hBT : B.conjTranspose =
      (fun k I => canonicalQuadraticRow k.val (primaryIdealGenerator (quadraticSquarefreePart I.val))) := by
    ext k I
    exact canonicalQuadraticRow_star _ _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun I : T => a I.val)
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hm (k : QuadraticIdealRange K) :
      ‖∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val‖ ^ 2 ≤
        ‖∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator (quadraticSquarefreePart I.val))*a I.val‖ ^ 2 := by
    have hrow : (∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val) =
        quadraticIdealMask k.val (primaryIdealGenerator A)*
        ∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator (quadraticSquarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := Finset.mem_filter.mp I.property
      have hq := canonicalQuadraticRow_squarefree_argument k.val (quadraticSquarefreePart I.val) (quadraticSquarePart I.val)
      rw [quadraticParts_mul_square I.val (primaryIdealGenerator_ne_zero_ideal _ (hS I.val hi.1).1.1),hi.2] at hq
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖quadraticIdealMask k.val (primaryIdealGenerator A)‖ ^ 2 ≤ 1 := by
      rw [quadraticIdealMask_indicator]
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hsum (k : QuadraticIdealRange K) :
      (∑ I ∈ columnSquareFiber S A, canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I) =
      ∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hsum]
  rw [← Finset.sum_coe_sort T (fun I => ‖a I‖ ^ 2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))

lemma columnSquareParts_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, quadraticSupported I ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (hA : A ∈ S.image quadraticSquarePart) :
    A ≠ 0 ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧ (Ideal.absNorm A : ℝ) ≤ X ∧ 1 ≤ X/(Ideal.absNorm A : ℝ) ^ 2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hi.1.1
  have hAz := quadraticSquarePart_ne_zero I
  have hDz := (quadraticSquarefreePart_squarefree I).ne_zero
  have ha : 1 ≤ (Ideal.absNorm (quadraticSquarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1 ≤ (Ideal.absNorm (quadraticSquarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hDz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn := quadraticSquarePart_norm_decomposition I hI0
  refine ⟨hAz,ha,by nlinarith only [ha,hd,hn,hi.2],?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (quadraticSquarePart I) : ℝ) ^ 2)).mpr
  nlinarith only [ha,hd,hn,hi.2]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped Classical

/-- Square-part fibers extend the sharp quadratic sieve to bounded supported columns. -/
theorem bounded_supported_quadratic_norm :
    ∀ε : ℝ, 0 < ε → ∃C : ℝ, 0 < C ∧ ∀K X lengthScale : ℝ,
      1 ≤ K → 1 ≤ X → 0 ≤ lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,quadraticSupported I ∧ (Ideal.absNorm I:ℝ) ≤ X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖ ≤ lengthScale) →
      (∑k : QuadraticIdealRange K,‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ 
        C*(K*X) ^ ε*(K+X)*X*lengthScale ^ 2 := by
  intro ε hε
  have hdiag := diagonalControl_nonneg sieveCutoff
  let deltaLoss := ε/3
  have hδ : 0 < deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := (2*(diagonalControl sieveCutoff+1))*(2+1/(deltaLoss*Real.log 2))
  have hD : 0 < D := by have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨(diagonalControl sieveCutoff+1)*C*D ^ 2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image quadraticSquarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0 < K := by linarith
  have hX0 : 0 < X := by linarith
  have hP0 : 0 < K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRL : R ≤ D*X ^ deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    have hp := Real.rpow_nonneg hX0.le deltaLoss
    have hlog : 0  <  Real.log 2 := Real.log_pos (by norm_num)
    have hc : 0  ≤  2+1/(deltaLoss*Real.log 2) := by positivity
    nlinarith only [hh,hdiag,hp,mul_nonneg hc hp]
  let F : ℝ := (diagonalControl sieveCutoff+1)*C*(K*X) ^ deltaLoss*(K+X)*X*lengthScale ^ 2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : QuadraticIdealRange K,‖∑I∈columnSquareFiber S A,
        canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0 < (Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ) ^ 2
    have hY : 1 ≤ Y := hp.2.2.2
    have hYX : Y ≤ X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K ≤ C*(K*X) ^ deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K ≤ K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0 ≤ Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖ ^ 2) ≤ (diagonalControl sieveCutoff+1)*Y*lengthScale ^ 2 := by
      calc
        _  ≤  ∑_I∈columnSquareFiber S A,lengthScale ^ 2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale ^ 2 := by simp
        _  ≤  diagonalControl sieveCutoff*Y*lengthScale  ^  2 :=
          mul_le_mul_of_nonneg_right (columnSquareFiber_card S X hS A hY) (sq_nonneg _)
        _  ≤  _ := by gcongr; linarith
    have he := columnSquareFiber_energy S X K hS A a
    calc
      _  ≤  (Ideal.absNorm A:ℝ)*(sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _  ≤  (Ideal.absNorm A:ℝ)*((C*(K*X) ^ deltaLoss*(K+X))*((diagonalControl sieveCutoff+1)*Y*lengthScale ^ 2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : QuadraticIdealRange K) :
      (∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem quadraticSquarePart hI) _).symm
  have hcauchy (k : QuadraticIdealRange K) :
      ‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 ≤ 
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : QuadraticIdealRange K,‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ F*R ^ 2 := by
    calc
      _  ≤  ∑k : QuadraticIdealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : QuadraticIdealRange K,‖∑I∈columnSquareFiber S A,
          canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _  ≤  R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R ^ 2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X) ^ deltaLoss*(X ^ deltaLoss) ^ 2 ≤ (K*X) ^ ε := by
    have hXP : X ≤ K*X := by nlinarith
    calc
      _  ≤  (K*X) ^ deltaLoss*((K*X) ^ deltaLoss) ^ 2 := by gcongr
      _ = (K*X) ^ ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _  ≤  F*(D*X ^ deltaLoss) ^ 2 := by gcongr
    _ = ((diagonalControl sieveCutoff+1)*C*D ^ 2)*((K*X) ^ deltaLoss*(X ^ deltaLoss) ^ 2)*(K+X)*X*lengthScale ^ 2 := by dsimp [F]; ring
    _  ≤  _ := by gcongr


end SchwartzPlanePoisson.CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
