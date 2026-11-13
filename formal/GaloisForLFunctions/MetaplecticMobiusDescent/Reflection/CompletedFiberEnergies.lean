/-
Completed fiber energies adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.OriginalResidualControl
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.ActualPeriodicRows
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.UnitTensorCoefficients

/-!
# Completed fiber energies

Completed representative aggregation and the uniform-degree completed fiber, row and original
energies; the powerful budget of row masks; actual puncture primes coprime to the period.
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
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe v

theorem canonical_completed_fiber_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤ cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F : Ideal Eis) (_hJ : J≠0) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → hhat≤ L →
      (Ideal.absNorm J:ℝ)≤ Z^M → (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hhat≤ d+η → d≤ cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,P∉reflectionExcludedPrimes q) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈representativeRowFiber parents J (ActualFiber.maskIdeal q m F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
            (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/16)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨degree,hu⟩ := canonical_original_frozen_energy_uniform_degree lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,?_⟩
  intro q hq
  let Q := CanonicalCoefficientClass.fixedBaseConductor q
  have hQ : Q≠0 := CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq
  let c := reflectionConductor q
  have hc : c≠0 := reflectionConductor_ne_zero q hq
  let : Finite (Eis⧸Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc)))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let b := excludedGenerator (reflectionExcludedPrimes q)
  let B : Ideal Eis := Ideal.span {b}
  have hb : b≠0 := reflectionExcludedGenerator_ne_zero q
  have hB : B≠0 := Ideal.span_singleton_eq_bot.not.mpr hb
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode)
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime) B hB
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J F hJ hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let mfull := ActualFiber.maskElement q m
  have hmfull : mfull≠0 := ActualFiber.maskElement_ne_zero q m hm
  let mask := Ideal.span {mfull}*F
  let Q₀ := Q*Ideal.span {(72:Eis)}
  have hmask : mask=B*F*Ideal.span {m} := by
    dsimp only [mask,mfull,ActualFiber.maskElement,B,b]
    rw [←Ideal.span_singleton_mul_span_singleton]
    ring
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hmfull) hF.ne_zero
  have hbad : ∀ P∈fixedBadPrimes,P∣mask := ActualFiber.mask_bad q m F
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F mfull hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact residual_coprime_free_base q hq m F I
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := reflectionConductor_ideal q
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLP : ∀ i,∀ P∈lists i,IsCoprime Q₀ P := by
    intro i P hP
    let : P.IsMaximal := hmax i P hP
    have hh := reflectionConductor_coprime_of_not_excluded q hq P (hexcluded i P hP)
    rw [reflectionConductor_ideal] at hh
    exact hh.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0< Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤ O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := descentIdealNorm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  have hOM : O≤ M := by
    have hh := Real.logb_le_logb_of_le hz hPowPos ((original_powerful_norm_le J hJ).trans hJn)
    rwa [Real.logb_rpow hzp (ne_of_gt hz)] at hh
  have hOn : Z^O≤(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    dsimp [O,normWidth]
    rw [Real.rpow_logb hzp (ne_of_gt hz) hPowPos]
  have ha := he (σ:=σ) J F (Ideal.span {m}) Q₀ hJ hF.ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm)
  rw [←hmask] at ha
  obtain ⟨D,hD⟩ := ha Z N V M z₀ margin O hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hmLam : lambda∣mfull :=
    ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
  have hm2 : (2:Eis)∣mfull := ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF mfull hmfull hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(N-3*hhat)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (ActualFiber.maskIdeal q m F) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (cubicIdealGenerator F)
        (u.val*cubicIdealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (cubicIdealGenerator F)
        (u.val*cubicIdealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O/2)=
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/16)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show N+V-cstar/16-O/2=(N+V-cstar/16)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (cubicIdealGenerator F)
        (u.val*cubicIdealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhasePowerfulBudget
open Eisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
local notation "O" => Eisenstein.O

theorem powerful_half_norm_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ),1≤ X →
      (∀ I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤ X) →
      ∑ I∈S,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ C*X^ε := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hcount⟩ := powerful_ideal_count δ hδ
  let C := D*(2:ℝ)^(1/2+δ)*(2+1/(δ*Real.log 2))
  have hl : 0< Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro S X hX hS
  have hx : 0< X := zero_lt_one.trans_le hX
  have hnorm (I : Ideal O) (hI : I∈S) :
      1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤ X :=
    ⟨descentIdealNorm_one_le (hS I hI).1.1,(hS I hI).2⟩
  have hbin (j : Fin (columnDyadicLength X+1)) :
      ∑ I∈divisorDyadicBin S X j,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤
        D*(2:ℝ)^(1/2+δ)*X^δ := by
    let R := divisorDyadicScale j.val
    have hR : 1≤ R := divisorDyadicScale_ge_one _
    have hr : 0< R := zero_lt_one.trans_le hR
    by_cases he : (divisorDyadicBin S X j).Nonempty
    · have hRX : R≤ X := divisorDyadicBin_scale_le S X hnorm j he
      have hc : ((divisorDyadicBin S X j).card:ℝ) ≤ D*(2*R)^(1/2+δ) := by
        apply hcount _ _ (by linarith)
        intro I hI
        exact ⟨(hS I (Finset.mem_filter.mp hI).1).1,
          (divisorDyadicBin_bounds S X hnorm j I hI).2⟩
      have hw (I : Ideal O) (hI : I∈divisorDyadicBin S X j) :
          (Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ R^(-1/2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr (divisorDyadicBin_bounds S X hnorm j I hI).1
          (by norm_num)
      calc
        _ ≤ ((divisorDyadicBin S X j).card:ℝ)*R^(-1/2:ℝ) := by
          apply (Finset.sum_le_sum hw).trans_eq
          simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ (D*(2*R)^(1/2+δ))*R^(-1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _)
        _ = (D*(2:ℝ)^(1/2+δ))*(R^(1/2+δ)*R^(-1/2:ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le]
          ring
        _ = D*(2:ℝ)^(1/2+δ)*R^δ := by
          rw [←Real.rpow_add hr]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hRX hδ.le) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [sum_divisorDyadicBins S X]
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength X+1),D*(2:ℝ)^(1/2+δ)*X^δ :=
      Finset.sum_le_sum (fun j _=> hbin j)
    _ = (columnDyadicLength X+1:ℝ)*(D*(2:ℝ)^(1/2+δ)*X^δ) := by simp
    _ ≤ ((2+1/(δ*Real.log 2))*X^δ)*(D*(2:ℝ)^(1/2+δ)*X^δ) :=
      mul_le_mul_of_nonneg_right (columnDyadicLength_small_power δ hδ X hX) (by positivity)
    _ = C*X^ε := by
      calc
        _ = C*(X^δ*X^δ) := by dsimp [C];ring
        _ = _ := by rw [←Real.rpow_add hx,show δ+δ=ε by dsimp [δ];ring]

lemma rowPowerful_norm_le (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowPowerfulPart I):ℝ) ≤ Ideal.absNorm I := by
  apply descentIdealNorm_le_of_dvd hI
  exact ⟨rowSimplePart I,(row_powerful_simple_product I hI).symm⟩

theorem row_mask_powerful_budget (L ε : ℝ) (hL : 0≤ L) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (Z : ℝ),2≤ Z → ∀ (S : Finset (Ideal O)) (Q : Ideal O),
      (∀ I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤ Z^L →
      ((S.image (fun I=> rowMaskPart I Q)).card:ℝ)*
        (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ C*Z^ε := by
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cp,hCp,hpower⟩ := powerful_half_norm_sum δ hδ
  obtain ⟨Cd,hCd,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨Cd*Cp,mul_pos hCd hCp,?_⟩
  intro Z hZ S Q hS hQ hQN
  have hz : 0< Z := by linarith
  have hX : 1≤ Z^L := Real.one_le_rpow (by linarith) hL
  have hp : (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ Cp*(Z^L)^δ := by
    apply hpower _ _ hX
    intro A hA
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨rowPowerfulPart_powerful I,(rowPowerful_norm_le I (hS I hI).1).trans (hS I hI).2⟩
  have hm : ((S.image (fun I=> rowMaskPart I Q)).card:ℝ) ≤ Cd*(Z^L)^δ :=
    ((Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)).trans (hdiv Q hQ)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hQN hδ.le) hCd.le)
  have he : L*(δ+δ) ≤ ε := by
    have heq : δ*(2*(L+1))=ε := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ (Cd*(Z^L)^δ)*(Cp*(Z^L)^δ) :=
      mul_le_mul hm hp (Finset.sum_nonneg (fun A _=> Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = (Cd*Cp)*((Z^L)^δ*(Z^L)^δ) := by ring
    _ = (Cd*Cp)*Z^(L*(δ+δ)) := by
      rw [←Real.rpow_add (Real.rpow_pos_of_pos hz L),←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (mul_pos hCd hCp).le

end InverseReflectedPhasePowerfulBudget

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤ L) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (Z : ℝ),2≤ Z → ∀ (parents : Finset (Ideal Eis)) (Q : Ideal Eis),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤ Z^L →
      ∀ (E : ℝ) (f : Ideal Eis→ℝ),0≤ E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤ C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal Eis) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      exact mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun T _ => hblocks A T))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe v

theorem canonical_completed_rows_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤ cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → hhat≤ L →
      (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hhat≤ d+η → d≤ cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,P∉reflectionExcludedPrimes q) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
            (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
  obtain ⟨degree,hu⟩ := canonical_completed_fiber_energy_uniform_degree lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation (2*L+1) (cstar/32) (by linarith) (by positivity)
  let B : Ideal Eis := Ideal.span {excludedGenerator (reflectionExcludedPrimes q)}
  let Z₁ := max Z₀ (max 2 (Ideal.absNorm B:ℝ))
  refine ⟨D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤ Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0< Z := by linarith
  have hz1 : 1≤ Z := by linarith
  have hBn : (Ideal.absNorm B:ℝ)≤ Z := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hZ
  have hmask : ActualFiber.maskIdeal q m F=B*F*Ideal.span {m} := by
    dsimp only [ActualFiber.maskIdeal,ActualFiber.maskElement,B]
    rw [←Ideal.span_singleton_mul_span_singleton]
    ring
  have hmaskn : (Ideal.absNorm (ActualFiber.maskIdeal q m F):ℝ)≤ Z^(2*L+1) := by
    rw [hmask]
    exact canonical_mask_norm_cap B F (Ideal.span {m}) Z V L L hz1 hBn hFn hRn hVc le_rfl
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(2*L+1) := by
    intro I hI
    exact ⟨(hparents I hI).1,(hparents I hI).2.trans
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))⟩
  have hh := ha Z hZ2 parents (ActualFiber.maskIdeal q m F) hparentn
    (ActualFiber.maskIdeal_ne_zero q m hm F hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^(N+V-cstar/16))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
        (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J F (hparents J hJ).1 hF m hm Z N V M z₀ margin hhat d
      hZZ hN hM hMc hVc hzc hhc (hparents J hJ).2 hFn hRn hinv hmargin hVd hhd hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/32)*Z^(N+V-cstar/16)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe v

theorem canonical_original_completed_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤ cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → hhat≤ L →
      (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hhat≤ d+η → d≤ cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
            (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
  obtain ⟨degree,hu⟩ := canonical_completed_rows_energy_uniform_degree lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := reflectionExcludedPrimes q
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hh := he (σ:=σ) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    (fun i P hP => (Finset.mem_filter.mp hP).2) hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_puncture_lists lists hprime S Ψ m
    (cubicIdealGenerator F) (u.val*cubicIdealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w)
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe v

theorem canonical_cube_shifted_completed_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤ L) (hcstar : 0< cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤ cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤ Z → 0≤ N → 0≤ M → M≤ L → V≤ L → z₀≤ L → hhat≤ L →
      (Ideal.absNorm F:ℝ)≤ Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤ d → hhat≤ d+η → d≤ cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,lambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (Hcube : Ideal Eis),Hcube≠0 → (Ideal.absNorm Hcube:ℝ)≤ Z^hhat →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
            (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣Hcube^3*A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64) := by
  obtain ⟨degree,hu⟩ := canonical_original_completed_energy_uniform_degree lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  let ε := cstar/(64*(L+1))
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨D,hD,hcube⟩ := original_cube_shifted_tuple_energy rmax ε hε
  refine ⟨D*C,Z₀,mul_pos hD hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod Hcube hcube0 hcuben u θ w hw
  have hz1 : 1≤ Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hz1
  have hremain (T : Finset σ) :
      (∑ I∈parents,‖∑ a : ∀ i : T,cubeAwayList Hcube (lists i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT (rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
            (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
            (Z^(N-3*hhat)) (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
    have hsub (i : T) : cubeAwayList Hcube (lists i.val)⊆lists i.val := Finset.filter_subset _ _
    have hcardT : Fintype.card T≤ rmax := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ T).trans hcard
    have hprodT : (∏ i : T,H i.val)≤ Z^z₀ := by
      apply le_trans ?_ hprod
      rw [Finset.prod_coe_sort]
      exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ T)
        (fun i hi => (hH1 i).trans' (by norm_num)) (fun i hi hnot => hH1 i)
    exact he (σ:=T) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
      hFn hRn hinv hmargin hVd hhd hd parents hparents hcardT
      (fun i : T => cubeAwayList Hcube (lists i.val)) (fun i : T => H i.val)
      (fun i j hij => (hdis (fun he => hij (Subtype.ext he))).mono (hsub i) (hsub j))
      (fun i P hP => hmax i.val P (hsub i hP)) (fun i P hP => hgood i.val P (hsub i hP))
      (fun i P hP => hprime i.val P (hsub i hP)) (fun i P hP => hodd i.val P (hsub i hP))
      (fun i => hH1 i.val) (fun i P hP => hH i.val P (hsub i hP)) hprodT
      Ψ hΨnorm hΨperiod u θ (fun i P => w i.val ⟨P.val,hsub i P.property⟩)
      (fun i P => hw i.val ⟨P.val,hsub i P.property⟩)
  have hh := hcube Hcube hcube0 lists hmax hgood w hw hcard parents
    (fun I => rowTwist Ψ (ActualFiber.maskElement q m) (cubicIdealGenerator F)
      (u.val*cubicIdealGenerator I)) (CompletedHeight.normTwistedSource W θ)
    (Z^(N-3*hhat)) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) (by positivity) hremain
  have hεcap : hhat*ε≤ cstar/64 := by
    have hhε : ε*(64*(L+1))=cstar := by dsimp [ε];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hhc hε.le]
  have hn : (Ideal.absNorm Hcube:ℝ)^ε≤ Z^(cstar/64) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hcuben hε.le).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 hεcap
  apply hh.trans
  calc
    _ ≤ D*Z^(cstar/64)*(C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) := by gcongr
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/64)*Z^(N+V-cstar/32)) := by ring
    _ = _ := by rw [←Real.rpow_add hz];congr 2;ring
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : quadraticSupported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

lemma markedCompletedT_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0)
    (W : ℝ→ℂ) (X : ℝ) (mark : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ (m*B) f z) W X mark=
      markedCompletedT (rowTwist Ψ m f z) W X mark := by
  rw [rowTwist_absorb_puncture Ψ m B f z hmLam hm2 hΨzero]

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

lemma rowResidualPart_coprime_enlarged_period (I F Q : Ideal Eis) (m B : Eis)
    (hQ : Q∣Ideal.span {B}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m*B}*F)) := by
  apply rowResidualPart_coprime_period I F Q (m*B)
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_of_dvd_right hQ _

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hA))
  exact mul_eq_zero_of_right _ hz
end
end InverseReflectedPhase

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
