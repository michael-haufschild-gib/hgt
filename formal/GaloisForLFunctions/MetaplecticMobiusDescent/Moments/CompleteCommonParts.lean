/-
Complete common parts adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.ReflectionMass

/-!
# Complete common parts

Prime-slot pools, radial comparison energies and Rankin radicals; smooth column phases and
whole kernels; common parts and residual parts with their norm bounds.
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

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=> hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=> hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

lemma annular_inverse_frequency_norm (χ : Character) (X v : ℝ) (hX : 0< X) :
    ‖polynomial χ.inverse false
      (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
      X 0 (2*Real.pi*v)‖=
    ‖polynomial χ false (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v)‖ := by
  rw [actual_log_window]
  have hh := HeckeInverseAmplification.polynomial_inverse_norm χ false
    (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v) hX
  simpa only [Complex.conj_ofReal,neg_mul,neg_neg] using hh

theorem actual_one_rowwise_scales (a b : ℝ) (ha : 0< a) (A J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0< C ∧ ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)
      (s t lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤ d → Function.support Wshort⊆Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤ hi → low≤ high → (∀i,lx i∈Icc lo hi) → (∀i,ly i∈Icc low high) →
      (∀i,0< s i) → 0≤ E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Icc lo hi,∀y∈Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong A n (s i) (t i))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤ Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionEnergy.actual_one_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) a b hlog hwindow ha A J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hbound⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P s t lx ly omega Wshort c d lo hi low high E hd hshort hshortsmooth
    hlh hlw hlx hly hspos hE henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i).inverse false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=> hlx i) (fun i _=> hly i) (henergy v)
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by
      rw [←pow_mul,Nat.mul_comm J 2]
    calc
      _ = ∑i,‖polynomial (χ i) false (fun z : ℝ=>(annulus z:ℂ))
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul,annular_inverse_frequency_norm (χ i) _ v (Real.exp_pos _)]
      _ ≤ (1+2*(hi-lo))*((1+2*(high-low))*(E*(1+‖v‖)^(2*J))) := hh
      _ = _ := by rw [hp];ring
  have hh := hbound (fun i=>(χ i).inverse) χ P s t (fun i=> Real.exp (lx i))
    (fun i=> Real.exp (ly i)) omega Wshort hspos (fun i=> Real.exp_pos _)
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) (mul_nonneg hdx (mul_nonneg hdy hE)) hfixed
  convert hh using 1 ; ring

end CenteredMomentOneReflectionScaleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => Eisenstein.O

theorem actual_independent_profile_choices (a b : ℝ) (ha : 0< a) (B J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0< C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (t ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤ hi → low≤ high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0< s i u) → (∀i u,keep i u → 0< X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0≤ E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong B n (s i (u i)) (t i))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionScaleEnergy.actual_one_rowwise_scales a b ha B J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ α χ P s X keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hE henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤ E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb χ P' (fun i=> s i (u i)) t lx ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=> hspos i (u i)) hE he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0< C) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤ C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0< Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤ dyadicScale u.2*Y ∧
      0≤ Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=> hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤ C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0< Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end CenteredMomentReflectedChoiceEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace CenteredMomentRetainedComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedChoiceEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_retained_fixed_profile_energy (a b epsilon : ℝ)
    (ha : 0< a) (hepsilon : 0< epsilon) (B J : ℕ) (hB : 2≤ B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0< C ∧ ∀{ι : Type}[Fintype ι],
      ∀(χ ψ : ι→Character)(P : ι→ℂ)(X R t ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high E T Rcap : ℝ),
      (∀i,0< X i) → 0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤ hi → low≤ high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0< dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0≤ E → 0≤ T → (∀i,‖t i‖≤ T) → 1≤ Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤ Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (X i) (R i) (t i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := actual_independent_profile_choices a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cp,hCp,hp⟩ := hn Wlong hs hW
  refine ⟨Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ χ ψ P X R t ly omega Wshort c d lo hi low high E T Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hE hT ht hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp χ P s Y keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=> dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hE henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) Wlong (X i) (R i) (t i) (hX i) B n (P' i) (u i)‖^2)≤
        Cp*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun _=> Wlong) X R t hX (fun _=> B) n P' (fun _=> hB)
    T Rcap _ hT ht hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [P',←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end CenteredMomentRetainedComparisonEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace CenteredMomentNaturalRetainedEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentRetainedComparisonEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (a b epsilon Cscale xi : ℝ)
    (ha : 0< a) (hepsilon : 0< epsilon) (hscale : 0< Cscale) (hxi : 0< xi)
    (B J : ℕ) (hB : 2≤ B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤ Cscale*Z^M) →
      0≤ E → 0≤ T → (∀i,‖t i‖≤ T) → 1≤ Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤ Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (Z^along) (Z^(xi/4)) (t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨n,hn⟩ := actual_retained_fixed_profile_energy a b epsilon ha hepsilon B J hB
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ ψ P t omega Wshort c d M along bshort E T Rcap hd hshort hshortsmooth
    hnatural hmod hE hT ht hRcap hcap henergy
  have hz : 0< Z := by linarith [hZ.1]
  have hlog : 0≤ Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0< dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤ Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb χ ψ P (fun _=> Z^along) (fun _=> Z^(xi/4)) t (fun _=> bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    E T Rcap (fun _=> Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hE hT ht hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end CenteredMomentNaturalRetainedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace CenteredMomentOriginalComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentNaturalRetainedEnergy CenteredMomentOriginalReflectionEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0< a) (hepsilon : 0< epsilon) (hscale : 0< Cscale) (hxi : 0< xi)
    (B J : ℕ) (hB : 2≤ B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0< C ∧ 0< D ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤ L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤ Cscale*Z^M) →
      0≤ E → 0≤ T → (∀i,‖t i‖≤ T) → 1≤ Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤ Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false Wlong (Z^along) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_natural_retained_energy a b epsilon Cscale xi ha hepsilon hscale hxi B J hB
  obtain ⟨ne,hne⟩ := actual_original_energy_to_retained a b (xi/2) saving L Cscale epsilon
    ha (by positivity) hscale hepsilon
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hr⟩ := hn Wlong hs hW
  obtain ⟨D,hD,ho⟩ := hne Wlong hs hW
  refine ⟨2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ P t omega Wshort c d M along bshort E T Rcap hχ hd hshort hshortsmooth
    hML hmod hE hT ht hRcap hcap henergy
  have hz : 0< Z := by linarith [hZ.1]
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤ Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal (fun _=> Z^along) t Q T Z Rcap hT hZ.1.le hRcap
    (fun _=> Real.rpow_pos_of_pos hz _) ht hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 χ ψ P t omega Wshort c d M along bshort E T Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hE hT ht hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 <;> first | rfl | ring

end CenteredMomentOriginalComparisonEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace CenteredMomentOriginalRadialComparison
open HeckeFamily HeckeDyadic 
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalComparisonEnergy CenteredMomentRadialPolynomialEnergy
local notation "O" => Eisenstein.O

def radialEnergy (F : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖F z‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0

lemma sqrt_weight (a p : ℂ) (u : ℝ) (hu : 0≤ u) :
    ‖a*(p*(Real.sqrt u:ℂ))‖^2=‖a*p‖^2*u := by
  rw [←mul_assoc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hu]

lemma finite_weighted (rows : Finset O) (keep : O→Prop) (F : O→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀z:O,0≤(Φ (‖ringComplex z‖^2/K)).re) :
    (∑z : ↥(rows.filter keep),‖F z*(Real.sqrt ((Φ (‖ringComplex z‖^2/K)).re):ℂ)‖^2)=
    ∑z∈rows,if keep z then ‖F z‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0 := by
  simp_rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
  rw [Finset.sum_coe_sort (rows.filter keep) (fun z:O=>‖F z‖^2*(Φ (‖ringComplex z‖^2/K)).re),Finset.sum_filter]

theorem actual_original_radial_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0< a) (_hb : 0≤ b) (hepsilon : 0< epsilon) (hscale : 0< Cscale) (hxi : 0< xi)
    (B J : ℕ) (hB : 2≤ B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0< C ∧ 0< D ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀(χ : O→Character)(P : O→ℂ)(t omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0< K → (∀z,0≤(Φ (‖ringComplex z‖^2/K)).re) → (∀z,‖P z‖≤ Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤ L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤ Cscale*Z^M) →
      0≤ E → 0≤ T → (∀z,keep z → ‖t z‖≤ T) → 1≤ Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤ Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=> polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤ E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=> polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          radialEnergy (fun z=> polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨n,ne,h⟩:=actual_original_comparison a b epsilon Cscale xi saving L ha hepsilon hscale hxi B J hB
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,D,hC,hD,h⟩:=h Wlong hs hW
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ P t omega keep Φ K Pbound Wshort c d M along bshort E T Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hT ht hRcap hcap henergy
  have hz : 0< Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖ringComplex z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>χ z) weightedP (fun z=> t z) (fun z=> omega z)
    Wshort c d M along bshort E T Rcap (fun z=> hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=> hmod z (hmem z)) hE hT (fun z=> ht z (hmem z)) hRcap
    (fun z=> hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=> polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
      finite_weighted rows keep (fun z=> polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ] at hh
    apply hh.trans
    apply add_le_add
    · apply le_of_eq;ring
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hshortsum.sum_le_tsum rows (fun z _=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  · intro v j k x hx
    have hschild:=pair_radial_summable χ P (fun _=>-2*Real.pi*v) omega
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (scaleTest Wshort k)
      (1/4) 1 c d (Real.exp x) (Z^bshort) Pbound (by norm_num) hd
      (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j)
      (scaleTest_support _ _ _ hshort k) hP keep Φ K hK
    simp only [weightedP,←mul_assoc]
    rw [finite_weighted rows keep (fun z=> polynomial (χ z) false (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) Φ K hΦ]
    exact (hschild.sum_le_tsum rows (fun z _=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (henergy v j k x hx)

end CenteredMomentOriginalRadialComparison

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap BigOperators
namespace CenteredMomentPlainPositiveEnergy
open HeckeFamily HeckeDyadic CenteredMomentPlainPositiveScale CenteredMomentPlainGlobalEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentRadialEligibleEnergy (Radial)
open InversePrincipalEnergy 
local notation "O"=> Eisenstein.O

 theorem actual_radial_pair_bound (a b:ℝ)(ha:0< a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(χ:O→Character)(r:Radial)(R X₁ X₂ freq₁ freq₂:ℝ),0≤ R→0< X₁→0< X₂→
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤ R)→
    radialEnergy (fun z=> polynomial (χ z) false W₁ X₁ 0 freq₁*
      polynomial (χ z) false W₂ X₂ 0 freq₂) r.keep r.profile r.scale≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*R^4*
        (3+|freq₁|)^4*(3+|freq₂|)^4:=by
  obtain ⟨S,C,hC,hg⟩:=global_positive_scale a b ha
  refine ⟨S,C ^ 4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R X₁ X₂ freq₁ freq₂ hR hX₁ hX₂ hχ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤ B₁:=apply_nonneg _ _
  have hB₂:0≤ B₂:=apply_nonneg _ _
  let B:=C ^ 2*(B₁*B₂)*R^2*(3+|freq₁|)^2*(3+|freq₂|)^2
  have hB:0≤ B:=by dsimp [B];positivity
  have hp (z:O)(hz:r.keep z):
      ‖polynomial (χ z) false W₁ X₁ 0 freq₁*polynomial (χ z) false W₂ X₂ 0 freq₂‖≤ B:=by
    rw [norm_mul]
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 freq₁‖≤ C*B₁*R*(3+|freq₁|)^2:=
      (hg W₁ hs₁ (χ z) (hχ z hz) X₁ freq₁ hX₁).trans (by gcongr;exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 freq₂‖≤ C*B₂*R*(3+|freq₂|)^2:=
      (hg W₂ hs₂ (χ z) (hχ z hz) X₂ freq₂ hX₂).trans (by gcongr;exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hh:=radial_bound_on_keep _ r B hB hp
  exact hh.trans_eq (by dsimp [B];ring)

end CenteredMomentPlainPositiveEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentFirstPoisson
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma principalCRT_scaled_left (a b : O) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : O) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

theorem coprime_character_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          primitiveTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        CenteredMomentFourier.residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        CenteredMomentFourier.residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    primitiveTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    primitiveTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, CenteredMomentFourier.residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem residueGauss_inverse (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    CenteredMomentFourier.residueGauss d hd χ⁻¹ h = star (CenteredMomentFourier.residueGauss d hd χ (-h)) := by
  let := finiteEisensteinQuotientOfNonzero hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  have htrace (x : Residue d) : star (primitiveTrace d hd x) = primitiveTrace d hd (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((primitiveTrace d hd).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [CenteredMomentFourier.residueGauss, tsum_fintype, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem coprime_pair_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x)) *
          primitiveTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a)) *
        CenteredMomentFourier.residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        star (CenteredMomentFourier.residueGauss b hb χb (-(frequencyReduction b (a * b) (dvd_mul_left b a) h))) := by
  simp only [MulChar.star_apply']
  rw [coprime_character_fourier a b ha hb hcop χa χb⁻¹ h, residueGauss_inverse]

theorem coprime_pair_poisson (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, χa (Ideal.Quotient.mk _ z) * star (χb (Ideal.Quotient.mk _ z)) *
      W (‖ringComplex z‖ ^ 2 / K)) =
      ((K / ‖ringComplex (a * b)‖ ^ 2 : ℝ) : ℂ) *
        (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
      ∑' j : O, CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) *
        paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (a * b)‖ ^ 2) := by
  let := finiteEisensteinQuotientOfNonzero ha
  let := finiteEisensteinQuotientOfNonzero hb
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P := fun x : Residue (a * b) =>
    χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
      star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hcoeff (j : O) :
      (∑ r : Residue (a * b), P r * primitiveTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) =
      (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
        (CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    have h := coprime_pair_fourier a b ha hb hcop χa χb (Ideal.Quotient.mk _ j)
    simpa only [P, frequencyReduction_mk, map_neg, mul_assoc] using h
  have hpoisson := actual_radial_poisson_trace W K hK (a * b) (mul_ne_zero ha hb) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖ringComplex z‖ ^ 2 / K)) =
    (K / ‖ringComplex (a * b)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (a * b), P r * primitiveTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (a * b)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson
  rw [hpoisson]
  change (K / ‖ringComplex (a * b)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (a * b), P r * primitiveTrace (a * b) (mul_ne_zero ha hb)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (a * b)‖ ^ 2)) = _
  simp_rw [hcoeff, mul_assoc]
  simp_rw [tsum_mul_left]
  rw [Complex.real_smul]

end CenteredMomentFirstPoisson
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace CenteredMomentSmooth
open JointLogSeparation SchwartzPlanePoisson

def rootWindow (V : ℝ → ℂ) (u : ℝ) : ℂ := V u / (Real.sqrt (Real.exp u) : ℂ)

def wholeKernel (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (R ρ x u v : ℝ) : ℂ :=
  V 0 ρ * V 1 x * rootWindow (V 2) u * rootWindow (V 3) v *
    paperRadialFourier W (R * Real.exp (ρ + x - u - v))

def rowPhase (V : Fin 4 → ℝ → ℂ) (ρ x t : ℝ) : ℂ :=
  (V 0 ρ * kernelLogPhase t ρ) * (V 1 x * kernelLogPhase t x)

def columnPhase (V : ℝ → ℂ) (u t : ℝ) : ℂ :=
  rootWindow V u * kernelLogPhase t (-u)

def separatedKernel (V : Fin 4 → ℝ → ℂ) (ρ x u v t : ℝ) : ℂ :=
  rowPhase V ρ x t * columnPhase (V 2) u t * columnPhase (V 3) v t

theorem whole_kernel_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  let U : Fin 4 → ℝ → ℂ := ![V 0, V 1, rootWindow (V 2), rootWindow (V 3)]
  let a : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hU : ∀ i y, U i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i
    · exact hV 0 y hy
    · exact hV 1 y hy
    · apply hV 2 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
    · apply hV 3 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope U a M hM hU W A J
  refine ⟨C, hC.le, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  refine ⟨b, ?_, by simpa only [Real.norm_eq_abs] using hi,
    by simpa only [Real.norm_eq_abs] using hm,
    by simpa only [Real.norm_eq_abs] using hp⟩
  intro ρ x u v
  have h := hb ![ρ, x, u, v]
  simpa [U, a, wholeKernel, separatedKernel, rowPhase, columnPhase,
    Fin.prod_univ_succ, Fin.sum_univ_succ, sub_eq_add_neg, mul_assoc, add_assoc] using h

lemma separated_integrable (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (ρ x u v : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => c * separatedKernel V ρ x u v t * b t) := by
  let K : ℝ := ‖c‖ * ‖V 0 ρ‖ * ‖V 1 x‖ * ‖rootWindow (V 2) u‖ * ‖rootWindow (V 3) v‖
  apply (b.integrable.norm.const_mul K).mono'
  · have hρ := kernelLogPhase_continuous_left ρ
    have hx := kernelLogPhase_continuous_left x
    have hu := kernelLogPhase_continuous_left (-u)
    have hv := kernelLogPhase_continuous_left (-v)
    exact (by unfold separatedKernel rowPhase columnPhase; fun_prop : Continuous (fun t : ℝ =>
      c * separatedKernel V ρ x u v t * b t)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [separatedKernel, rowPhase, columnPhase, norm_mul, kernelLogPhase_norm, mul_one]
    dsimp only [K]
    ring_nf
    exact le_rfl

theorem finite_pair_separation {α β : Type*}
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
      ∫ t : ℝ, separatedKernel V ρ x u v t * b t)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
      ∫ t : ℝ, rowPhase V ρ x t *
        (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
        (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ t : ℝ,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsep, ← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, ∑ i ∈ S, ∑ j ∈ T,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum T
        (fun j _ => separated_integrable b V ρ x (u i) (v j) (c i * star (d j))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ =>
        separated_integrable b V ρ x (u i) (v j) (c i * star (d j)))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.sum_mul, Finset.mul_sum, separatedKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem whole_product_pair_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ {α β : Type*} (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
        (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ),
        (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
          ∫ t : ℝ, rowPhase V ρ x t *
            (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
            (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hs⟩ := whole_kernel_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  exact ⟨b, fun S T c d u v ρ x => finite_pair_separation W V R b hb S T c d u v ρ x,
    hi, hm, hp⟩

theorem kernelLogPhase_norm_ratio (q X θ : ℝ) (hq : 0 < q) (hX : 0 < X) :
    kernelLogPhase θ (-Real.log (q / X)) =
      kernelLogPhase θ (Real.log X) * (q : ℂ) ^ (Complex.I * (-(2 * Real.pi * θ))) := by
  have hlog : -Real.log (q / X) = Real.log X + -Real.log q := by
    rw [Real.log_div hq.ne' hX.ne']
    ring
  rw [hlog, kernelLogPhase_add]
  congr 1
  have hθ : (-(2 * Real.pi * θ)) / (2 * Real.pi) = -θ := by
    have hp := Real.pi_ne_zero
    field_simp
  have hn := CenteredMomentLattice.logPhase_eq_normPower (-(2 * Real.pi * θ)) q hq
  rw [hθ] at hn
  push_cast at hn
  rw [← hn]
  unfold kernelLogPhase
  congr 1
  push_cast
  ring

open CenteredMomentRectangle
local notation "O" => Eisenstein.O

theorem idealWeight_height_add (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t v : ℝ) :
    idealWeight c χ R (t + v) I =
      idealWeight c χ R t I * (Ideal.absNorm I : ℂ) ^ (Complex.I * v) := by
  have hn : (Ideal.absNorm I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [idealWeight, Complex.ofReal_add, mul_add, Complex.cpow_add _ _ hn]
  ring

theorem idealWeight_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t θ X : ℝ) (hX : 0 < X) :
    idealWeight c χ R t I * kernelLogPhase θ (-Real.log ((Ideal.absNorm I : ℝ) / X)) =
      kernelLogPhase θ (Real.log X) * idealWeight c χ R (t - 2 * Real.pi * θ) I := by
  have hn : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  rw [kernelLogPhase_norm_ratio _ X θ hn hX, sub_eq_add_neg, idealWeight_height_add c χ R I hI]
  push_cast
  ring

theorem centered_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R Qslot I J : Ideal O) (hQslot : Qslot ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ t θ X : ℝ) (hX : 0 < X) :
    (idealWeight c χ R t (Qslot * I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) *
      kernelLogPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X)) =
      kernelLogPhase θ (Real.log X) *
        (idealWeight c χ R (t - 2 * Real.pi * θ) (Qslot * I * J) *
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
  calc
    _ = (idealWeight c χ R t (Qslot * I * J) *
        kernelLogPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X))) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by ring
    _ = _ := by
      rw [idealWeight_whole_phase c χ R (Qslot * I * J) (mul_ne_zero (mul_ne_zero hQslot hI) hJ) t θ X hX]
      ring

end CenteredMomentSmooth
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace CenteredMomentCauchy
open CenteredMomentSmooth JointLogSeparation

theorem bounded_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) * Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

def leftColumn {α : Type*} (S : Finset α) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * columnPhase V (u i) t

def rightColumn {β : Type*} (T : Finset β) (d : β → ℂ)
    (V : ℝ → ℂ) (v : β → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ T, star (d j) * columnPhase V (v j) t

lemma paired_columns_integrable {α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (ρ x : ℝ)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => z * (rowPhase V ρ x t *
      leftColumn S c (V 2) u t * rightColumn T d (V 3) v t * b t)) := by
  have hi := integrable_finsetSum S (fun i _ => integrable_finsetSum T
    (fun j _ => separated_integrable b V ρ x (u i) (v j) (z * c i * star (d j))))
  convert hi using 1
  all_goals try rfl
  funext t
  simp only [leftColumn, rightColumn, Finset.mul_sum, Finset.sum_mul, separatedKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem common_density_cauchy {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, kernelLogPhase_norm, kernelLogPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := bounded_row_cauchy rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    CanonicalCubeSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_cauchy b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end CenteredMomentCauchy
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => Eisenstein.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=> Prime I ∧ I∈RayQuotient.identityClass M H)

def slotProfile (W:ℝ→ℂ) (D σ:ℝ) (I:Ideal O) : ℂ := annularWeight W D σ 0 I

lemma norm_height_split (N D σ t:ℝ) (hN:0< N) (hD:0< D) :
    (((N/D:ℝ):ℂ)^(-shift σ 0))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_zero,zero_mul,sub_zero]
  ring

lemma sqrt_inverse_cpow (D:ℝ) (hD:0< D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0< D) :
    normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ t := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0< D) :
    ‖normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ t‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end CenteredMomentPrimeSlot

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => Eisenstein.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0< N) (hD:0< D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0< D) :
    normalizedSlot η m A z (CenteredMomentPrimeSlot.primePool M H b D) (annularWeight W D σ v) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial CenteredMomentPrimeSlot.primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0< D) :
    ‖normalizedSlot η m A z (CenteredMomentPrimeSlot.primePool M H b D) (annularWeight W D σ v) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ (t+v)‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t v hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end CenteredMomentPrimeSlotShift

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => Eisenstein.O

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0< X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hP : ∀i,0< P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem positiveSlotRow_eq_polynomials
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P σp tp : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hP : ∀i,0< P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t)
      (fun i=> primePool M H (b i) (P i))
      (fun i=> HeckePrimeAnnular.annularWeight (V i) (P i) (σp i) (tp i)) P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,HeckePrimeRay.rayPrimePolynomial M H χ (V i) (b i) (P i) (σp i) (tp i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  have hslot (i : ι) := CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H η χ m A z hrow
    (V i) (b i) (P i) (σp i) 0 (tp i) (hP i)
  simp_rw [hslot]
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,zero_add]
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem oriented_twist_support (reverse : Bool) (W : ℝ→ℂ) (σ t : ℝ) :
    Function.support (twistProfile (HeckeDetectorCoefficientTransfer.orientedProfile reverse W) σ t)
      ⊆Function.support W := by
  apply (twistProfile_support _ _ _).trans
  cases reverse <;> simp only [HeckeDetectorCoefficientTransfer.orientedProfile,ite_true]
  · exact Set.Subset.rfl
  · intro x hx hzero
    exact hx (by simp only [hzero,map_zero])

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinRadical
open  UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => Eisenstein.O

def commonRadical (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I ∩ primeSupport J,P

theorem commonRadical_ne_zero (I J : Ideal O) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

theorem commonRadical_squarefree (I J : Ideal O) : Squarefree (commonRadical I J) :=
  squarefree_support_product Finset.inter_subset_left

theorem commonRadical_support (I J : Ideal O) :
    primeSupport (commonRadical I J)=primeSupport I∩primeSupport J := by
  unfold primeSupport commonRadical
  rw [factors_support_product Finset.inter_subset_left]
  simp [primeSupport]

theorem old_mask_dvd_commonRadical (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J := by
  apply (squarefree_dvd_iff s _ hs).mpr
  intro P hP
  have hp := support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  have hi : P ∈ primeSupport I := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hI,hp,true_and]
      using hd.trans hsI
  have hj : P ∈ primeSupport J := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hJ,hp,true_and]
      using hd.trans hsJ
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hi,hj⟩)


end CenteredMomentRankinRadical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentCompleteCommon
open UniqueFactorizationMonoid  CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def commonSupport (I J : Ideal O) : Finset (Ideal O) := primeSupport I ∩ primeSupport J

def commonPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ commonSupport I J, P ^ valuation I P

def residualPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I \ primeSupport J, P ^ valuation I P

theorem commonSupport_comm (I J : Ideal O) : commonSupport I J = commonSupport J I :=
  Finset.inter_comm _ _

theorem supportExtract_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportExtract I S = ∏ P ∈ primeSupport I ∩ S, P ^ valuation I P := by
  unfold supportExtract
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I ∩ S) (by
    intro P hP
    exact Finset.mem_inter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_inter.mp hP).2, ↓reduceIte]
  rfl

theorem supportResidual_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportResidual I S = ∏ P ∈ primeSupport I \ S, P ^ valuation I P := by
  unfold supportResidual
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I \ S) (by
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_sdiff.mp hP).2]
  rfl

theorem commonPart_eq_supportExtract (I J : Ideal O) :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem residualPart_eq_supportResidual (I J : Ideal O) :
    residualPart I J = supportResidual I (commonSupport I J) := by
  rw [supportResidual_eq_power_product]
  have he : primeSupport I \ commonSupport I J = primeSupport I \ primeSupport J := by
    ext P
    simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
    tauto
  rw [he]
  rfl

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem residualPart_ne_zero (I J : Ideal O) : residualPart I J ≠ 0 := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonPart_support (I J : Ideal O) :
    primeSupport (commonPart I J) = commonSupport I J := by
  rw [commonPart_eq_supportExtract, supportExtract_support]
  simp only [commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem commonParts_equal_support (I J : Ideal O) :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]

theorem residualPart_support (I J : Ideal O) :
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J := by
  rw [residualPart_eq_supportResidual, supportResidual_support]
  ext P
  simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
  tauto

theorem commonPart_valuation (I J P : Ideal O) :
    valuation (commonPart I J) P = if P ∈ commonSupport I J then valuation I P else 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_count I P _

theorem residualPart_valuation (I J P : Ideal O) :
    valuation (residualPart I J) P = if P ∈ commonSupport I J then 0 else valuation I P := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_count I P _

theorem commonPart_residualPart_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart J I) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact extracted_residual_coprime I J _

theorem commonPart_own_residual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart I J) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact extracted_residual_coprime I I _

theorem commonProduct_leftResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) :=
  (commonPart_own_residual_coprime I J).mul_left (commonPart_residualPart_coprime J I)

theorem commonProduct_rightResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) :=
  (commonPart_residualPart_coprime I J).mul_left (commonPart_own_residual_coprime J I)

theorem residualParts_coprime (I J : Ideal O) :
    IsCoprime (residualPart I J) (residualPart J I) := by
  rw [residualPart_eq_supportResidual, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact common_support_residual_coprime I J

theorem canonical_complete_extraction (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = commonPart I J * residualPart I J ∧
    J = commonPart J I * residualPart J I ∧
    commonPart I J ≠ 0 ∧ commonPart J I ≠ 0 ∧
    residualPart I J ≠ 0 ∧ residualPart J I ≠ 0 ∧
    primeSupport (commonPart I J) = commonSupport I J ∧
    primeSupport (commonPart J I) = commonSupport I J ∧
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J ∧
    primeSupport (residualPart J I) = primeSupport J \ primeSupport I ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) ∧
    IsCoprime (residualPart I J) (residualPart J I) := by
  exact ⟨reconstruct I J hI, reconstruct J I hJ,
    commonPart_ne_zero I J, commonPart_ne_zero J I,
    residualPart_ne_zero I J, residualPart_ne_zero J I,
    commonPart_support I J, (commonPart_support J I).trans (commonSupport_comm J I),
    residualPart_support I J, residualPart_support J I,
    commonProduct_leftResidual_coprime I J, commonProduct_rightResidual_coprime I J,
    residualParts_coprime I J⟩

theorem commonPart_dvd (I J : Ideal O) (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem residualPart_dvd (I J : Ideal O) (hI : I ≠ 0) : residualPart I J ∣ I :=
  ⟨commonPart I J, (reconstruct I J hI).trans (mul_comm _ _)⟩

theorem residualPart_original_coprime (I J : Ideal O) (hJ : J ≠ 0) :
    IsCoprime (residualPart I J) J := by
  conv_rhs => rw [reconstruct J I hJ]
  exact (commonPart_residualPart_coprime J I).symm.mul_right (residualParts_coprime I J)

theorem commonPart_eq_one_of_empty (I J : Ideal O) (h : commonSupport I J = ∅) :
    commonPart I J = 1 := by simp only [commonPart, h, Finset.prod_empty]

theorem residualPart_eq_of_empty (I J : Ideal O) (hI : I ≠ 0)
    (h : commonSupport I J = ∅) : residualPart I J = I := by
  have he := reconstruct I J hI
  rw [commonPart_eq_one_of_empty I J h, one_mul] at he
  exact he.symm

theorem commonSupport_empty_iff (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    commonSupport I J = ∅ ↔ IsCoprime I J := by
  rw [← CenteredMomentSupport.primeSupport_disjoint_iff hI hJ,
    Finset.disjoint_iff_inter_eq_empty]
  rfl

theorem commonPart_one_right (I : Ideal O) : commonPart I 1 = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem commonPart_one_left (J : Ideal O) : commonPart 1 J = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_inter]

theorem residualPart_one_right (I : Ideal O) (hI : I ≠ 0) : residualPart I 1 = I := by
  apply residualPart_eq_of_empty I 1 hI
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem residualPart_one_left (J : Ideal O) : residualPart 1 J = 1 := by
  simp only [residualPart, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_sdiff, Finset.prod_empty]

theorem extracted_commonRadical (I J : Ideal O) :
    commonRadical (commonPart I J) (commonPart J I) = commonRadical I J := by
  unfold commonRadical
  rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
  rfl

theorem commonRadical_dvd_commonPart (I J : Ideal O) : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

theorem squarefree_mask_survives (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J ∧ s ∣ commonPart I J ∧ s ∣ commonPart J I ∧
      IsCoprime s (residualPart I J) ∧ IsCoprime s (residualPart J I) := by
  have hR := old_mask_dvd_commonRadical s I J hs hI hJ hsI hsJ
  have hC := hR.trans (commonRadical_dvd_commonPart I J)
  have hD : s ∣ commonPart J I := by
    have he : commonRadical I J = commonRadical J I := by
      simp only [commonRadical, Finset.inter_comm]
    exact (he ▸ hR).trans (commonRadical_dvd_commonPart J I)
  exact ⟨hR, hC, hD,
    (commonPart_own_residual_coprime I J).of_isCoprime_of_dvd_left hC,
    (commonPart_own_residual_coprime J I).of_isCoprime_of_dvd_left hD⟩

theorem commonPart_supported (I J : Ideal O) (hI : Supported I) : Supported (commonPart I J) := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_supported I hI _

theorem residualPart_supported (I J : Ideal O) (hI : Supported I) : Supported (residualPart I J) := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_supported I hI _

theorem primaryIdealGenerator_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    primaryIdealGenerator I =
      primaryIdealGenerator (commonPart I J) *
        primaryIdealGenerator (residualPart I J) := by
  rw [← primaryIdealGenerator_mul, ← reconstruct I J hI]

theorem primary_complete_extraction (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let C := primaryIdealGenerator (commonPart I J)
    let D := primaryIdealGenerator (commonPart J I)
    let a := primaryIdealGenerator (residualPart I J)
    let b := primaryIdealGenerator (residualPart J I)
    primaryIdealGenerator I = C * a ∧
    primaryIdealGenerator J = D * b ∧
    IsCoprime (C * D) a ∧ IsCoprime (C * D) b ∧ IsCoprime a b := by
  dsimp only
  have hC := commonPart_supported I J hI
  have hD := commonPart_supported J I hJ
  have ha := residualPart_supported I J hI
  have hb := residualPart_supported J I hJ
  have hpC := primaryIdealGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryIdealGenerator_ne_zero _ hC)
  have hpD := primaryIdealGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryIdealGenerator_ne_zero _ hD)
  have hpa := primaryIdealGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryIdealGenerator_ne_zero _ ha)
  have hpb := primaryIdealGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryIdealGenerator_ne_zero _ hb)
  refine ⟨primaryIdealGenerator_reconstruct I J hI.1, primaryIdealGenerator_reconstruct J I hJ.1, ?_, ?_, ?_⟩
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpa.1]
    exact commonProduct_leftResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpb.1]
    exact commonProduct_rightResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpa.1, hpb.1]
    exact residualParts_coprime I J

theorem common_valuations_pos (I J P : Ideal O) (hP : P ∈ commonSupport I J) :
    0 < valuation I P ∧ 0 < valuation J P := by
  obtain ⟨hI, hJ⟩ := Finset.mem_inter.mp hP
  exact ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hI),
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)⟩

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

theorem absNorm_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm I = Ideal.absNorm (commonPart I J) * Ideal.absNorm (residualPart I J) := by
  have h := congrArg Ideal.absNorm (reconstruct I J hI)
  simpa only [map_mul] using h

theorem absNorm_commonPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))

theorem absNorm_residualPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (residualPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (residualPart_dvd I J hI))

end CenteredMomentCompleteCommon

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
