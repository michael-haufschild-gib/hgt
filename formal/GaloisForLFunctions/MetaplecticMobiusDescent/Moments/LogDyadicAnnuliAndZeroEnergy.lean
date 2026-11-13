/-
Logarithmic annuli and zero energy adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondCanonicalFamilies

/-!
# Logarithmic annuli and zero energy

Smooth compact logarithmic annuli, first whole-kernel windows and the global amplification
error; zero energies of first localizations and of smooth subset sources.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentScale
open CenteredMomentSmooth SchwartzPlanePoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

theorem normalized_kernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K : ℂ) / ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ)) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) =
    (K : ℂ) / ((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) *
      wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
        (Real.log (K / K₀)) (Real.log (H / H₀))
        (Real.log (A / A₀)) (Real.log (B / B₀)) := by
  rw [wholeKernel_actual W V K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  have ha : (Real.sqrt A₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hb : (Real.sqrt B₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

end CenteredMomentScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentFirstWholeKernel
def windows (V : Fin 4 → ℝ → ℂ) (K H A B K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  V 0 (Real.log (K/K₀))*V 1 (Real.log (H/H₀))*
    V 2 (Real.log (A/A₀))*V 3 (Real.log (B/B₀))


end CenteredMomentFirstWholeKernel

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4< Real.exp x := lt_of_not_ge (fun h=> hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=> hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=> by
    by_contra hn
    exact hx (logAnnulus_support hn))

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log (q H : ℝ) (hq : 0< q) (hH : 0< H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0< q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0< k) (hH : 0< H) (ha : 0< a) (hb : 0< b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=> logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end CenteredMomentLogDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstLocalization
open Eisenstein  SchwartzPlanePoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open TruncatedPrincipalPoisson
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => Eisenstein.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0< k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤ B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0< k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤ B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [if_neg hh]
    have hp : 0< normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

theorem reducedFirstSum_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      canonicalRetainedPair I J hI hJ W K Tsec Z ξ+canonicalDiscardedPair I J hI hJ W K Tsec Z ξ := by
  unfold reducedFirstSum canonicalZeroPair canonicalRetainedPair canonicalDiscardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem finiteHeckeEnergy_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0< K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K Tsec Z ξ+
        discardedEnergy η m A t S c W K Tsec Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_split _ _ _ _ W K Tsec Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end CenteredMomentFirstLocalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNonprincipalGate
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open  CenteredMomentRestrictedEnergy CenteredMomentChildRows RayFourExpansion
local notation "O" => Eisenstein.O

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (O⧸(⊤:Ideal O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim

theorem unitCharacter_ideal (I:Ideal O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_cubicIdealGenerator I,idealCoeff_span _ (cubicIdealGenerator_ne_zero I hI)]
  change (1:MulChar (O⧸(⊤:Ideal O)) ℂ) (Ideal.Quotient.mk _ (cubicIdealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal O) (cubicIdealGenerator I)=1 from Subsingleton.elim _ _]
  exact map_one _

theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn:=cubicIdealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_cubicIdealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (cubicIdealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {cubicIdealGenerator I}) χ.modulus
    · rw [if_pos hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [if_neg hc]
      exact MulChar.map_nonunit _ (fun h=> hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=> hex (principal_row_fixed η χ Q m A z hrow h)

theorem nonexceptional_row_nonprincipal (η χ:Character) (ξ:RayCharacter)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom (childCharacter η ξ)) m 1 (A*z) n)
    (hex:nonexceptional η ξ Q m A z) : χ.residue≠1 :=
  actual_row_nonprincipal (childCharacter η ξ) χ Q m A z hrow hex.2

end CenteredMomentNonprincipalGate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplification
open Eisenstein CompletedGauss  CanonicalRowCompletion
open CanonicalQuadraticSieve  ProbePrimePower ProbePhysical
open CenteredMomentUnequal
local notation "O" => Eisenstein.O

theorem gauss_prime_power_one (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) 1 =
      if n = 0 then primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg]
  have ht := complexSexticChar_primePowerGauss_at_pow p hp hg hc (n+1) n 0
  simp only [pow_zero] at ht
  rw [ht]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn0 : ¬0 = n := Ne.symm hn
    have hpos : ¬n ≤ 0 := by omega
    simp only [if_neg hn,if_neg hn0,if_neg hpos,show ¬n+1 ≤ 0 by omega,ite_false,sub_self]
    split_ifs <;> rfl

theorem gauss_prime_power_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^6) =
      if n = 5 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^5 *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1)
      else if n = 6 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^6 *
        primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg,complexSexticChar_primePowerGauss_at_pow p hp hg hc]
  have h6 : complexSexticChar (Ideal.span {p}) hg ^ 6 = 1 :=
    (complexSexticChar_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl
  by_cases hn5 : n = 5
  · subst n
    norm_num
    ring
  · by_cases hn6 : n = 6
    · subst n
      simp only [hn5,show ¬6 ∣ 6+1 by decide,ite_false,ite_true,
        pow_succ (complexSexticChar (Ideal.span {p}) hg) 6,h6,one_mul]
    · rw [if_neg hn5,if_neg hn6]
      by_cases hd : 6 ∣ n+1
      · have hlarge : 6 < n := by omega
        simp only [hd,ite_true,show ¬n+1 ≤ 6 by omega,ite_false,
          show ¬n ≤ 6 by omega,sub_self]
      · simp only [hd,ite_false,show ¬6=n from Ne.symm hn6]

theorem gauss_prime_power_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn0 : n ≠ 0) (hn5 : n ≠ 5) (hn6 : n ≠ 6) (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (h*p^6) =
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h := by
  have hcop : IsCoprime h (p^(n+1)) :=
    (hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right
  have hsp := supported_power p hs (n+1)
  rw [sexticGauss_unit_scale _ hsp h (p^6) hcop,
    ← mul_one h, sexticGauss_unit_scale _ hsp h 1 hcop,
    gauss_prime_power_six p hp hg hc,gauss_prime_power_one p hp hg hc]
  simp only [hn0,hn5,hn6,ite_false,mul_zero]

theorem gauss_sixth_frequency (a : O) (ha : Supported (Ideal.span {a}))
    (p h : O) (hcop : IsCoprime p a) :
    sexticGauss a (CenteredMomentSupportedCorrelation.supported_element_ne_zero a ha) (p^6*h) =
      sexticGauss a (CenteredMomentSupportedCorrelation.supported_element_ne_zero a ha) h := by
  rw [sexticGauss_unit_scale a ha (p^6) h hcop.pow_left,
    idealRowHom_sixth_eq_mask p a ((supported_iff_native _).mp ha)]
  change (if IsCoprime p a then (1 : ℂ) else 0)⁻¹ * _ = _
  rw [if_pos hcop, inv_one, one_mul]

theorem twelfth_power_mask (p : O) (hs : Supported (Ideal.span {p})) (u : O) :
    idealRowHom u (Ideal.span {p}) ^ 12 = coprimalityMask u p := by
  rw [show 12=6*2 by decide,pow_mul,← idealRowHom_argument_pow u 6 _ (supported_primaryIdealGenerator_ne_zero _ hs),
    idealRowHom_sixth_eq_mask u p ((supported_iff_native _).mp hs)]
  change (if IsCoprime u p then (1 : ℂ) else 0)^2 = if IsCoprime u p then 1 else 0
  split_ifs <;> norm_num

end CenteredMomentAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationLocal
open Eisenstein CompletedGauss  CanonicalRowCompletion
open CanonicalQuadraticSieve  ProbePrimePower ProbePhysical
open CenteredMomentUnequal CenteredMomentAmplification CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

def centralLocal (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  sexticGauss (p^(n+1)) (pow_ne_zero _ hp) h / (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1)

theorem gauss_unit_scale_norm (a : O) (ha : Supported (Ideal.span {a}))
    (b h : O) (hcop : IsCoprime b a) :
    ‖sexticGauss a (supported_element_ne_zero a ha) (b*h)‖ =
      ‖sexticGauss a (supported_element_ne_zero a ha) h‖ := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero a ha)
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := CenteredMomentCommonSupport.isUnit_residue_of_coprime a b hcop.symm
  have hn : ‖idealRowHom b (Ideal.span {a})‖ = 1 := by
    change ‖supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit _ u
  rw [sexticGauss_unit_scale a ha b h hcop,norm_mul,norm_inv,hn,inv_one,one_mul]

theorem primeGauss_actual_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1‖^2 =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp.ne_zero
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hχ : complexSexticChar (Ideal.span {p}) hg ≠ 1 := by
    intro he
    have ho := CenteredMomentCanonical.complexSexticChar_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht : (CenteredMomentFourier.primitiveTrace p hp.ne_zero).IsPrimitive :=
    residueTraceQuotientChar_primitive p hp.ne_zero
  have he : primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 =
      gaussSum (complexSexticChar (Ideal.span {p}) hg) (CenteredMomentFourier.primitiveTrace p hp.ne_zero) := by
    simp [primeGauss,tsum_fintype,gaussSum]
  rw [he,ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card hχ ht,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_cast
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem centralLocal_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 5 (p^6) = 1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_seven (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 6 (p^6) =
      primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 /
        (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [show ¬(6:ℕ)=5 by decide,ite_false,ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_unit_norm (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (n : ℕ) (h k : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero n (h*k)‖ = ‖centralLocal p hp.ne_zero n k‖ := by
  unfold centralLocal
  rw [norm_div,norm_div,gauss_unit_scale_norm _ (supported_power p hs (n+1)) h k
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right)]

theorem centralLocal_one_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [← mul_one h,centralLocal_unit_norm p hp hs 0 h 1 hph,centralLocal,
    gauss_prime_power_one p hp hg hc]
  simp only [ite_true,zero_add,pow_one,norm_div,Complex.norm_natCast,div_pow,
    primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_seven_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 6 (h*p^6)‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [centralLocal_unit_norm p hp hs 6 h (p^6) hph,centralLocal_seven p hp hg hc,
    norm_div,Complex.norm_natCast,div_pow,primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_six_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 5 (h*p^6)‖^2 =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 := by
  rw [centralLocal_unit_norm p hp hs 5 h (p^6) hph,centralLocal_six p hp hg hc]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end CenteredMomentAmplificationLocal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationGlobal
open CanonicalQuadraticSieve CanonicalRowCompletion 
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentGaussEnergy
open CenteredMomentAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem full_column_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn1 : n ≠ 1) (hn6 : n ≠ 6) (hn7 : n ≠ 7)
    (a : O) (ha : Supported (Ideal.span {a})) (hcop : IsCoprime p a)
    (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha))
      (p^6*h) =
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha)) h := by
  cases n with
  | zero =>
    simp only [pow_zero,one_mul]
    exact gauss_sixth_frequency a ha p h hcop
  | succ n =>
    rw [sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      gauss_sixth_frequency a ha p h hcop,
      mul_comm (p^6) h,gauss_prime_power_unchanged p hp hs hg hc n
        (by omega) (by omega) (by omega) h hph]

def amplificationError {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (ν : α → ℕ) (p : O) (k : ℕ) (h : O) : ℂ :=
  ∑ i ∈ S, if ν i = k then c i *
    (gaussRow (a i) (ha i) h - gaussRow (a i) (ha i) (p^6*h)) else 0

theorem polynomial_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c ν p 1 h + amplificationError S a ha c ν p 6 h +
      amplificationError S a ha c ν p 7 h := by
  simp only [gaussPolynomial,amplificationError,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h1 : ν i = 1
  · simp only [h1,ite_true,show ¬(1:ℕ)=6 by decide,show ¬(1:ℕ)=7 by decide,ite_false]
    ring
  · by_cases h6 : ν i = 6
    · simp only [h6,ite_true,show ¬(6:ℕ)=1 by decide,show ¬(6:ℕ)=7 by decide,ite_false]
      ring
    · by_cases h7 : ν i = 7
      · simp only [h7,ite_true,show ¬(7:ℕ)=1 by decide,show ¬(7:ℕ)=6 by decide,ite_false]
        ring
      · simp only [h1,h6,h7,ite_false,add_zero]
        congr 1
        unfold gaussRow
        congr 1
        have he := full_column_unchanged p hp hs hg hc (ν i) h1 h6 h7
          (r i) (hr i) (hcop i hi) h hph
        simpa only [hfactor i hi] using he.symm

def primeRemainder (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_spec (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) :
    a = p^(multiplicity p a)*primeRemainder p hp a ha ∧ ¬p ∣ primeRemainder p hp a ha :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_supported (p : O) (hp : Prime p) (a : O)
    (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {primeRemainder p hp a (supported_element_ne_zero a ha)}) := by
  have hs := ha
  rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1,
    ← Ideal.span_singleton_mul_span_singleton,supported_mul_iff] at hs
  exact hs.2

theorem polynomial_amplification_actual {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h := by
  apply polynomial_amplification S a ha c p hp hs hg hc _
    (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
    (fun i => primeRemainder_supported p hp (a i) (ha i))
  · exact fun i _ => (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
  · exact fun i _ => hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
  · exact hph

theorem norm_four_sum_sq (a b c d : ℂ) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have hn : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ ≤ ‖a+b+c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le a b) le_rfl) le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖d‖)]

theorem polynomial_amplification_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ 4*(‖gaussPolynomial S a ha c (p^6*h)‖^2 +
      ‖amplificationError S a ha c ν p 1 h‖^2 +
      ‖amplificationError S a ha c ν p 6 h‖^2 +
      ‖amplificationError S a ha c ν p 7 h‖^2) := by
  rw [polynomial_amplification S a ha c p hp hs hg hc ν r hr hfactor hcop h hph]
  exact norm_four_sum_sq _ _ _ _

theorem eligible_pool_average {β : Type*} (P : Finset β) (hP : P.Nonempty)
    (H : ℂ) (A E₁ E₆ E₇ : β → ℂ)
    (hid : ∀ p ∈ P, H = A p + E₁ p + E₆ p + E₇ p) :
    ‖H‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
  have hc : (0 : ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hb : (P.card : ℝ)*‖H‖^2 ≤ 4 *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
    have hb := Finset.sum_le_sum (s := P) (fun p hp => show ‖H‖^2 ≤
      4*(‖A p‖^2+‖E₁ p‖^2+‖E₆ p‖^2+‖E₇ p‖^2) by
        rw [hid p hp]
        exact norm_four_sum_sq _ _ _ _)
    simpa only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] using hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  convert hb using 1 <;> first | rfl | ring

theorem polynomial_pool_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hP : P.Nonempty) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hgood : ∀ p ∈ P, lambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (h : O) (hph : ∀ p ∈ P, ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  apply eligible_pool_average P hP
  intro p hpP
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hp p hpP).irreducible
  exact polynomial_amplification_actual S a ha c p (hp p hpP) (hs p hpP)
    (hgood p hpP) (hc p hpP) h (hph p hpP)

end CenteredMomentAmplificationGlobal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationCount
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => Eisenstein.O

theorem primeDivisors_product_dvd (S : Finset (Ideal O))
    (hP : ∀ P ∈ S, Prime P) (I : Ideal O) (hd : ∀ P ∈ S, P ∣ I) :
    (∏ P ∈ S, P) ∣ I := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro P hPS Q hQS hPQ
  let : P.IsMaximal := (Ideal.isPrime_of_prime (hP P hPS)).isMaximal (hP P hPS).ne_zero
  let : Q.IsMaximal := (Ideal.isPrime_of_prime (hP Q hQS)).isMaximal (hP Q hQS).ne_zero
  exact Ideal.isCoprime_of_isMaximal hPQ

theorem large_prime_divisor_count (S : Finset (Ideal O)) (hP : ∀ P ∈ S, Prime P)
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ P ∈ S, P ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ P ∈ S, Z^ℓ ≤ (Ideal.absNorm P : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hpow : Z ^ (ℓ * (S.card : ℝ)) ≤ Z^B := by
    calc
      _ = (Z^ℓ)^S.card := Real.rpow_mul_natCast (zero_lt_one.trans hZ).le ℓ S.card
      _ = ∏ _P ∈ S, Z^ℓ := (Finset.prod_const _).symm
      _ ≤ ∏ P ∈ S, (Ideal.absNorm P : ℝ) := Finset.prod_le_prod
        (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hlower
      _ = (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by simp only [map_prod,Nat.cast_prod]
      _ ≤ (Ideal.absNorm I : ℝ) := norm_le_of_dvd hI (primeDivisors_product_dvd S hP I hd)
      _ ≤ _ := hupper
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hpow
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using he

theorem indexed_large_prime_divisor_count {α : Type*} (S : Finset α) (P : α → Ideal O)
    (hinj : Set.InjOn P S) (hp : ∀ i ∈ S, Prime (P i))
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ i ∈ S, P i ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, Z^ℓ ≤ (Ideal.absNorm (P i) : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hb := large_prime_divisor_count (S.image P) (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hp i hi) I hI (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hd i hi) Z ℓ B hZ hℓ (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hlower i hi) hupper
  simpa only [Finset.card_image_of_injOn hinj] using hb

theorem amplified_row_fiber_count (F : Finset (O × O)) (y : O) (hy : y ≠ 0)
    (hprime : ∀ x ∈ F, Prime x.2)
    (hprimary : ∀ x ∈ F, lambda^2 ∣ x.2-1)
    (hrow : ∀ x ∈ F, x.2^6*x.1 = y)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ x ∈ F, Z^ℓ ≤ (Ideal.absNorm (Ideal.span {x.2}) : ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Z^B) : (F.card : ℝ) ≤ B/ℓ := by
  apply indexed_large_prime_divisor_count F (fun x => Ideal.span {x.2}) ?_
    (fun x hx => CubicEisenstein.gaussPrimeIdeal_prime x.2 (hprime x hx))
    (Ideal.span {y}) (Ideal.span_singleton_eq_bot.not.mpr hy) ?_ Z ℓ B hZ hℓ hlower hupper
  · intro x hx z hz heq
    have hp : x.2 = z.2 := by
      rw [← primaryIdealGenerator_span x.2 (hprime x hx).ne_zero (hprimary x hx),
        ← primaryIdealGenerator_span z.2 (hprime z hz).ne_zero (hprimary z hz)]
      exact congrArg primaryIdealGenerator heq
    have hh : x.1 = z.1 := by
      apply mul_left_cancel₀ (pow_ne_zero 6 (hprime x hx).ne_zero)
      rw [hrow x hx,hp,hrow z hz]
    exact Prod.ext hh hp
  · intro x hx
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton,← hrow x hx]
    exact (dvd_pow_self x.2 (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem positive_pushforward_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (C : ℝ)
    (hg : ∀ y ∈ S.image f, 0 ≤ g y)
    (hf : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ C) :
    (∑ x ∈ S, g (f x)) ≤ C * ∑ y ∈ S.image f, g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ = ((S.filter (fun x => f x = y)).card : ℝ) * g y := by
      rw [← nsmul_eq_mul,← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hf y hy) (hg y hy)

end CenteredMomentAmplificationCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentZeroMeanBridge
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CanonicalQuadraticSieve CanonicalRowCompletion 
open TruncatedPrincipalPoisson CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentFirstDiscardedEnergy CenteredMomentFirstLocalization
local notation "O" => Eisenstein.O

def quotientMean (a : O) (F : Residue a → ℂ) : ℂ :=
  (normValue a : ℂ)⁻¹ * ∑' x : Residue a, F x

lemma normValue_ne_zero (a : O) (ha : a ≠ 0) : normValue a ≠ 0 :=
  by
    rw [normValue_eq_embedding]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (ringComplex_ne_zero ha))

theorem quotientMean_pullback (a m : O) (ha : a ≠ 0) (hm : m ≠ 0)
    (h : a ∣ m) (F : Residue a → ℂ) :
    quotientMean m (fun x => F (frequencyReduction a m h x)) = quotientMean a F := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := right_ne_zero_of_mul hm
  have hh := conductorFourier_lift a b ha hb F 0
  simp only [mul_zero, conductorFourier, map_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one] at hh
  have he : frequencyReduction a (a*b) (dvd_mul_right a b) = conductorReduction a b := rfl
  unfold quotientMean
  rw [he, hh, normValue_mul, Complex.ofReal_mul]
  have ha' : (normValue a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero a ha)
  have hb' : (normValue b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero b hb)
  change ((normValue a : ℂ) * (normValue b : ℂ))⁻¹ *
    ((normValue b : ℂ) * _) = _
  field_simp

def dilationMask (e d : O) (F : Residue d → ℂ) (x : Residue (d*e)) : ℂ :=
  if frequencyReduction e (d*e) (dvd_mul_left e d) x = 0 then
    F (frequencyReduction d (d*e) (dvd_mul_right d e) x) else 0

@[simp] theorem dilationMask_mk (e d : O) (F : Residue d → ℂ) (z : O) :
    dilationMask e d F (Ideal.Quotient.mk _ z) =
      if e ∣ z then F (Ideal.Quotient.mk _ z) else 0 := by
  simp only [dilationMask, frequencyReduction_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem dilationMask_sum (e d : O) (he : e ≠ 0) (F : Residue d → ℂ) :
    (∑' x : Residue (d*e), dilationMask e d F x) =
      ∑' y : Residue d, F (Ideal.Quotient.mk _ e * y) := by
  have hi := scaledResidue_injective d e (d*e) rfl he
  have hz (x : Residue (d*e)) (hx : x ∉ Set.range (scaledResidue d e (d*e) rfl)) :
      dilationMask e d F x = 0 := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [dilationMask_mk]
    split_ifs with h
    · obtain ⟨y,rfl⟩ := h
      exact False.elim (hx ⟨Ideal.Quotient.mk _ y, rfl⟩)
    · rfl
  have hs : Function.support (dilationMask e d F) ⊆ Set.range (scaledResidue d e (d*e) rfl) := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro y
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, dilationMask_mk, if_pos (dvd_mul_right e z), map_mul]

theorem quotientMean_dilation (e d : O) (he : e ≠ 0) (_hd : d ≠ 0)
    (F : Residue d → ℂ) (hF : ∀ x y, F (x*y) = F x * F y) :
    quotientMean (d*e) (dilationMask e d F) =
      (normValue e : ℂ)⁻¹ * F (Ideal.Quotient.mk _ e) * quotientMean d F := by
  rw [quotientMean, dilationMask_sum e d he]
  simp_rw [hF]
  rw [tsum_mul_left, normValue_mul, Complex.ofReal_mul, quotientMean]
  ring

theorem quotientMean_finite_sum {ι : Type*} [Fintype ι]
    (a : O) (ha : a ≠ 0) (F : Residue a → ℂ)
    (d : ι → O) (hd : ∀ i, d i ≠ 0) (G : (i : ι) → Residue (d i) → ℂ)
    (c : ι → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      ∑ i, c i * G i (Ideal.Quotient.mk _ z)) :
    quotientMean a F = ∑ i, c i * quotientMean (d i) (G i) := by
  let m := a * ∏ i, d i
  have hm : m ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have haM : a ∣ m := dvd_mul_right _ _
  have hdM (i : ι) : d i ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) a
  let := finiteEisensteinQuotientOfNonzero hm
  let : Fintype (Residue m) := Fintype.ofFinite _
  rw [← quotientMean_pullback a m ha hm haM F]
  have hh (x : Residue m) : F (frequencyReduction a m haM x) =
      ∑ i, c i * G i (frequencyReduction (d i) m (hdM i) x) := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [frequencyReduction_mk] using h z
  simp_rw [quotientMean, hh, tsum_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl := quotientMean_pullback (d i) m (hd i) hm (hdM i) (G i)
  rw [quotientMean, tsum_fintype] at hl
  rw [← Finset.mul_sum, mul_left_comm, hl]
  rfl

theorem row_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (z : O) (v : ℂ) :
    rowCoprimeMask P S z * v =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (if primeSubsetGenerator P E ∣ z then v else 0) := by
  rw [rowCoprimeMask, primeCoprimeMask_divisor_expansion _ (generator_pairwise_coprime P hinj),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  have hp (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_product_moebius P hp hinj E]
  by_cases h : primeSubsetGenerator P E ∣ z <;>
    simp only [primeSubsetGenerator] at h ⊢ <;>
    simp only [h, ite_true, ite_false, mul_one, zero_mul, mul_zero]


theorem quotientMean_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (a d : O) (ha : a ≠ 0) (hd : d ≠ 0)
    (F : Residue a → ℂ) (G : Residue d → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y)
    (hFG : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      rowCoprimeMask P S z * G (Ideal.Quotient.mk _ z)) :
    quotientMean a F =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
          G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G := by
  have h := quotientMean_finite_sum a ha F
    (fun E : S.powerset => d * primeSubsetGenerator P E.val)
    (fun E => mul_ne_zero hd (primeSubsetGenerator_ne_zero P E.val))
    (fun E => dilationMask (primeSubsetGenerator P E.val) d G)
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i∈E.val,P i) : ℂ)) (by
      intro z
      rw [hFG, row_mask_expansion P hinj S z]
      simp only [dilationMask_mk]
      exact (Finset.sum_coe_sort S.powerset _).symm)
  simp_rw [quotientMean_dilation _ _ (primeSubsetGenerator_ne_zero P _) hd G hG] at h
  simp only [← mul_assoc] at h
  exact h.trans (Finset.sum_coe_sort S.powerset (fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
      (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
        G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G))

theorem tripleResidue_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y) (x y : Residue (a*(b*r))) :
    tripleResidue a b r χa χb G (x*y) =
      tripleResidue a b r χa χb G x * tripleResidue a b r χa χb G y := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, tripleResidue_mk, tripleResidue_mk, tripleResidue_mk]
  exact tripleRow_mul a b r χa χb G hG u v

theorem original_pair_reduced_mask (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (z : O) :
    idealRowHom z I * star (idealRowHom z J) =
      rowCoprimeMask (fun P : CommonIndex I J => P.val)
        (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) z := by
  rw [original_pair_factor I J hI hJ]
  rw [common_ideal_pair_active (fun P : CommonIndex I J => P.val) (common_good I J hI)
    (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => (leftExponent_pos I J P).ne') (fun P _ => (rightExponent_pos I J P).ne')]
  have hactive : activeFunction I J hI (Ideal.Quotient.mk _ z) =
      finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z :=
    principalSexticRow_mk (activePrime I J) (activeCoprime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) (activeConductor I J)
      (span_finitePrimeModulus _) z
  simp only [tripleRow, hactive]
  convert mul_left_comm
    ((residualCharacter I J hI) (Ideal.Quotient.mk _ z) *
      (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z))
    (rowCoprimeMask (fun P : CommonIndex I J => P.val)
      (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z)
    (finiteSexticRow (activePrime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) z) using 1
  congr 2

theorem original_pair_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let hi : Supported (Ideal.span {primaryIdealGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {primaryIdealGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    quotientMean (primaryIdealGenerator I * primaryIdealGenerator J)
      (CenteredMomentRowNorm.pairResidue _ _ hi hj) =
    ∑ E ∈ inactiveSubsets I J,
      (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)) := by
  dsimp only
  have h := quotientMean_mask_expansion (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (principalSupport Finset.univ (leftExponent I J) (rightExponent I J))
    (primaryIdealGenerator I * primaryIdealGenerator J)
    (residualGenerator I J * (residualGenerator J I * activeConductor I J))
    (mul_ne_zero (supported_primaryIdealGenerator_ne_zero I hI) (supported_primaryIdealGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
        (finitePrimeModulus_ne_zero _)))
    (CenteredMomentRowNorm.pairResidue _ _
      ((CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI)
      ((CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ))
    (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (tripleResidue_mul _ _ _ _ _ _ (principalSexticRow_mul _ _ _ _ _ _)) (by
      intro z
      rw [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
        CenteredMomentSourceRow.primary_span_supported J hJ, tripleResidue_mk]
      exact original_pair_reduced_mask I J hI hJ z)
  simpa only [inactiveSubsets, tripleResidue_mk] using h

theorem canonicalZeroTerm_eq_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroTerm I J hI hJ E W K = (K : ℂ) *
      ((UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))) *
      paperRadialFourier W 0 := by
  simp only [canonicalZeroTerm, tripleFourier, map_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, quotientMean, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem canonicalZeroPair_eq_original (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let hi : Supported (Ideal.span {primaryIdealGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {primaryIdealGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖ringComplex (primaryIdealGenerator I * primaryIdealGenerator J)‖^2 : ℝ) : ℂ) *
        CenteredMomentRowNorm.pairFourier (primaryIdealGenerator I) (primaryIdealGenerator J)
          hi hj 0) * paperRadialFourier W 0 := by
  dsimp only
  rw [canonicalZeroPair]
  simp_rw [canonicalZeroTerm_eq_mean]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← original_pair_mean I J hI hJ]
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem quotientMean_congr (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : Residue a → ℂ) (G : Residue b → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) = G (Ideal.Quotient.mk _ z)) :
    quotientMean a F = quotientMean b G := by
  have hh := quotientMean_finite_sum a ha F (fun _ : Unit => b) (fun _ => hb)
    (fun _ => G) (fun _ => (1 : ℂ)) (by intro z; simpa using h z)
  simpa using hh

theorem scaled_pairFourier_eq_mean (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (K : ℝ) :
    (((K / ‖ringComplex (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) =
      (K : ℂ) * quotientMean (a*b) (CenteredMomentRowNorm.pairResidue a b ha hb) := by
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem canonicalZeroPair_eq_generators (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (haI : Ideal.span {a} = I) (hbJ : Ideal.span {b} = J) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖ringComplex (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) *
        paperRadialFourier W 0 := by
  rw [canonicalZeroPair_eq_original, scaled_pairFourier_eq_mean, scaled_pairFourier_eq_mean]
  congr 2
  apply quotientMean_congr
    _ _ (mul_ne_zero (supported_primaryIdealGenerator_ne_zero I hI) (supported_primaryIdealGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
  intro z
  simp only [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ, haI, hbJ]

theorem canonical_ideal_zero_sum (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      canonicalZeroPair I.val J.val (hS I.val I.property) (hS J.val J.property) W K) =
      CenteredMomentZeroMode.idealZeroEnergy S hS c K * paperRadialFourier W 0 := by
  rw [CenteredMomentZeroMode.idealZeroEnergy]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [canonicalZeroPair_eq_generators I.val J.val (hS I.val I.property) (hS J.val J.property)
    (CenteredMomentZeroMode.idealColumn S I) (CenteredMomentZeroMode.idealColumn S J)
    (CenteredMomentZeroMode.idealColumn_supported S hS I) (CenteredMomentZeroMode.idealColumn_supported S hS J)
    (CenteredMomentZeroMode.idealColumn_span S I) (CenteredMomentZeroMode.idealColumn_span S J)]
  ring

theorem zeroEnergy_eq_original (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) W K

theorem productColumnCoefficient_mul_whole (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (w : Ideal O → ℂ) (I : Ideal O) :
    CompletedGauss.productColumnCoefficient S T (fun J L => β J L * w (J*L)) I =
      CompletedGauss.productColumnCoefficient S T β I * w I := by
  rw [CompletedGauss.productColumnCoefficient, CompletedGauss.productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem zeroEnergy_product_eq (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S T : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
      (CompletedGauss.productColumnCoefficient S T β) W K =
    CenteredMomentZeroMode.productZeroEnergy S T hS hT
      (fun I J => β I J * CenteredMomentHeckeExpansion.rowWeight η m A 1 t (I*J)) K *
      paperRadialFourier W 0 := by
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2)
  have hp := CenteredMomentZeroMode.productColumns_supported S T hS hT
  have hs : CenteredMomentSourceRow.supportedColumns P = P := Finset.filter_eq_self.mpr hp
  have hh := zeroEnergy_eq_original η m A t P (CompletedGauss.productColumnCoefficient S T β) W K
  simp only [hs] at hh
  rw [hh]
  congr 1
  unfold CenteredMomentZeroMode.productZeroEnergy
  congr 1
  funext I
  exact (productColumnCoefficient_mul_whole S T β
    (CenteredMomentHeckeExpansion.rowWeight η m A 1 t) I).symm

theorem normalized_zeroEnergy_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeFamily.Character) (m A : O) (t : ℝ)
      (S T : Finset (Ideal O)) (_hS : ∀ I ∈ S, Supported I) (_hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I*J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
          (CompletedGauss.productColumnCoefficient S T β) W K‖ ≤
        C * K * B^2 * ‖paperRadialFourier W 0‖ * X^ε := by
  obtain ⟨C,hC,hc⟩ := CenteredMomentZeroMode.normalized_product_zero_mode_bound ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S T hS hT β W X K B hX hK hB hN hβ
  rw [zeroEnergy_product_eq η m A t S T hS hT]
  apply hc S T hS hT _ W X K B hX hK hB hN
  intro I hi J hj
  rw [norm_mul]
  exact (mul_le_mul (hβ I hi J hj)
    (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t (I*J)
      (mul_ne_zero (hS I hi).1 (hT J hj).1)) (norm_nonneg _) hB).trans_eq (mul_one B)

end CenteredMomentZeroMeanBridge

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSupportedZeroEnergy
open Eisenstein  CanonicalQuadraticSieve CanonicalRowCompletion 
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge SchwartzPlanePoisson HeckeFamily
local notation "O" => Eisenstein.O

theorem idealZeroEnergy_filter (S : Finset (Ideal O)) (hS : ∀ I∈S,Supported I)
    (c : Ideal O → ℂ) (K : ℝ) (p : Ideal O → Prop) [DecidablePred p]
    (hc : ∀ I∈S, ¬p I → c I=0) :
    idealZeroEnergy S hS c K =
      idealZeroEnergy (S.filter p) (fun I h => hS I (Finset.mem_filter.mp h).1) c K := by
  let e : S.filter p → S := fun I => ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  let ep : (S.filter p) × (S.filter p) → S × S := fun q => (e q.1,e q.2)
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  have hep : Function.Injective ep := by
    intro q r h
    exact Prod.ext (he (congrArg Prod.fst h)) (he (congrArg Prod.snd h))
  let f : S × S → ℂ := fun q => (c q.1.val * star (c q.2.val)) *
    (((K / ‖ringComplex (idealColumn S q.1 * idealColumn S q.2)‖^2 : ℝ) : ℂ) *
      CenteredMomentRowNorm.pairFourier (idealColumn S q.1) (idealColumn S q.2)
        (idealColumn_supported S hS q.1) (idealColumn_supported S hS q.2) 0)
  have hs : Function.support f ⊆ Set.range ep := by
    intro q hq
    have hi : p q.1.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.1.val q.1.property hn,zero_mul])
    have hj : p q.2.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.2.val q.2.property hn,star_zero,mul_zero,zero_mul])
    exact ⟨(⟨q.1.val,Finset.mem_filter.mpr ⟨q.1.property,hi⟩⟩,
      ⟨q.2.val,Finset.mem_filter.mpr ⟨q.2.property,hj⟩⟩),rfl⟩
  have ht := hep.tsum_eq hs
  simpa only [tsum_fintype,Fintype.sum_prod_type,f,ep,e,idealZeroEnergy,idealColumn] using ht.symm

def activeColumns (S : Finset (Ideal O)) (c : Ideal O → ℂ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => c I≠0)

lemma activeColumns_supported (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (I : Ideal O) (hI : I∈activeColumns S c) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem zeroEnergy_eq_active_original (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem zeroEnergy_eq_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K = zeroEnergy η m A t (activeColumns S c) c W K := by
  rw [zeroEnergy_eq_active_original,zeroEnergy_eq_original]
  have he : supportedColumns (activeColumns S c)=activeColumns S c :=
    Finset.filter_eq_self.mpr (activeColumns_supported S c)
  simp only [he]

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤ B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤ B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤ X → 0≤ K → 0≤ B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤ B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤ X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0< X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤ X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤ X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

theorem normalized_active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤ X → 0≤ K → 0≤ B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤ B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤ X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  have hX0 : 0< X := zero_lt_one.trans_le hX
  have hb := hc hi η m A t S β W X K B hX hK hB hβ hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hX0)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hX0.le)).trans_eq
  rw [Real.rpow_add hX0,Real.rpow_one]
  field_simp

theorem normalized_supported_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤ X → 0≤ K → 0≤ B →
      (∀ v∈S,‖β v‖≤ B) →
      (∀ v∈S,β v≠0 → (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := normalized_active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  apply hc hi η m A t S β W X K B hX hK hB (fun v hv _ => hβ v hv)
  intro I _ hI
  obtain ⟨v,hv,hne,he⟩ := finiteColumnCoefficient_witness S β I hI
  rw [←he]
  exact hN v hv hne

end CenteredMomentSupportedZeroEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSourceZeroEnergy
open Eisenstein HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤ D j) (hD₁ : 0≤ D₁) (hD₂ : 0≤ D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤ D j)
    (h₁ : ∀ x,‖W₁ x‖≤ D₁) (h₂ : ∀ x,‖W₂ x‖≤ D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤ b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤ b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤ b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤ Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem smooth_source_zero_energy {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0< a j) (hb : ∀ j,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (X K : ℝ),
      0< X → 0≤ K → (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤ X →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K‖≤
        C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤ B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  have hend : 0≤(∏ j,b j)*b₁*b₂ := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂
  let L := 1+(∏ j,b j)*b₁*b₂
  have hL : 0< L := by dsimp only [L]; linarith
  have hendL : (∏ j,b j)*b₁*b₂≤ L := by dsimp only [L]; linarith
  obtain ⟨C₀,hC₀,hbound⟩ := active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let C := C₀*(1+B^2)*L^(1+ε)
  have hC : 0< C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos hL _)
  refine ⟨C,hC,?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK hscale
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤ B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) :=
    mul_nonneg (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ L*X := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ = ((∏ j,b j)*b₁*b₂)*((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)) := by ring
      _ ≤ L*X := mul_le_mul hendL hscale hraw hL.le
  by_cases hsmall : L*X<1
  · have he := zeroEnergy_eq_zero_of_subunit η m A t S β Φ K (L*X) hsmall
      (fun v _ hv => hN v hv)
    change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤ _
    rw [he,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (norm_nonneg _)) (Real.rpow_nonneg hXX.le _)
  have hradius : 1≤ L*X := le_of_not_gt hsmall
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ (L*X) K B hradius hK hB
    (fun v _ _ => hβ v) (fun I _ hI => by
      obtain ⟨v,hv,hne,hprod⟩ := finiteColumnCoefficient_witness S β I hI
      rw [←hprod]
      exact (hN v hne).2)
  have hpower : X⁻¹*(L*X)^(1+ε)=L^(1+ε)*X^ε := by
    rw [Real.mul_rpow hL.le hXX.le,Real.rpow_add hXX,Real.rpow_one]
    field_simp
  change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hXX)]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXX.le)).trans
  calc
    _ = C₀*B^2*L^(1+ε)*K*‖paperRadialFourier Φ 0‖*X^ε := by
      calc
        _ = C₀*B^2*K*‖paperRadialFourier Φ 0‖*(X⁻¹*(L*X)^(1+ε)) := by ring
        _ = _ := by rw [hpower];ring
    _ ≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX.le _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hK
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le)
        (Real.rpow_nonneg hL.le _)

theorem smooth_source_zero_energy_at_radius {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0< a j) (hb : ∀ j,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0≤ K →
      let X := (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (X<1 → E=0) ∧ ‖((X⁻¹:ℝ):ℂ)*E‖≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤ B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  obtain ⟨C₀,hC₀,hbound⟩ := normalized_supported_tuple_zero_energy_bound (Fintype.card ι) ε hε
  refine ⟨C₀*(1+B^2),mul_pos hC₀ (by positivity),?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK X E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤ B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ X :=
    profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
  have hzero (hx : X<1) : E=0 :=
    zeroEnergy_eq_zero_of_subunit η m A t S β Φ K X hx (fun v _ hv => hN v hv)
  refine ⟨hzero,?_⟩
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hXX : 0≤ X := by
    dsimp only [X]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂)
      (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  by_cases hx : X<1
  · rw [hzero hx,mul_zero,norm_zero]
    positivity
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ X K B
    (le_of_not_gt hx) hK hB (fun v _ => hβ v) (fun v _ hv => (hN v hv).2)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    C₀*K*B^2 = C₀*B^2*K := by ring
    _ ≤ C₀*(1+B^2)*K := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le) hK

theorem smooth_subset_source_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0< a j) (hb : ∀ j∈F,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0≤ K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let ρ := (∏ j∈J,b j)*b₁*b₂*H
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (ρ<1 → E=0) ∧
      ‖((ρ⁻¹:ℝ):ℂ)*E‖≤ C*K*‖paperRadialFourier Φ 0‖*ρ^ε ∧
      ∀ X : ℝ,0< X → H≤ X → ‖((X⁻¹:ℝ):ℂ)*E‖≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  have hraw (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  have hrad (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy_at_radius
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  let D (J : Finset α) : ℝ := if hJ : J⊆F then (hraw J hJ).choose+(hrad J hJ).choose else 1
  have hD (J : Finset α) : 0< D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact add_pos (hraw J hJ).choose_spec.1 (hrad J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈F.powerset,D J
  have hC : 0< C := by
    have hsum := Finset.sum_nonneg (fun J (_ : J∈F.powerset) => (hD J).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK H ρ E
  have hDC : D J≤ C := by
    have hle := Finset.single_le_sum (fun L (_ : L∈F.powerset) => (hD L).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hde : D J=(hraw J hJ).choose+(hrad J hJ).choose := by simp only [D,dif_pos hJ]
  have hrawC : (hraw J hJ).choose≤ C := by
    rw [hde] at hDC
    linarith [(hrad J hJ).choose_spec.1]
  have hradC : (hrad J hJ).choose≤ C := by
    rw [hde] at hDC
    linarith [(hraw J hJ).choose_spec.1]
  have hr := (hrad J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK
  have heq : (∏ j : J,b j.val)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j : J,P j.val)=ρ := by
    rw [Finset.prod_coe_sort,Finset.prod_coe_sort]
    dsimp only [ρ,H]
    ring
  dsimp only at hr
  rw [heq] at hr
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hprodB : 0≤∏ j∈J,b j := Finset.prod_nonneg (fun j hj => hb j (hJ hj))
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hρ : 0≤ρ := by dsimp only [ρ,H]; positivity
  refine ⟨hr.1,hr.2.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hradC hK) (norm_nonneg _))
      (Real.rpow_nonneg hρ _)
  · intro X hXX hscale
    have hx := (hraw J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
      (fun j I => hν j.val j.property I) (fun j : J => P j.val)
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
      hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK
      (by simpa only [Finset.prod_coe_sort] using hscale)
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrawC hK) (norm_nonneg _))
      (Real.rpow_nonneg hXX.le _))

end CenteredMomentSourceZeroEnergy

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
