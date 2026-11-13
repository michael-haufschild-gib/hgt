/-
Zero reflection support adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.ZeroReferenceStates

/-!
# Zero reflection support

Deleted short lengths, live deleted growth and endpoint defects of the zero reflection support;
balanced and unbalanced original states from zero low data; natural retained errors and short
radial masses.
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
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroReferenceBounded
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=> Eisenstein.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ e → 0≤ K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤ Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0< X₁ →0< X₂ →s.width/4≤ Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤ s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 <;> first | rfl | ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 <;> first | rfl | ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> first | rfl | ((try dsimp only [E,A]) <;> ring)
  · dsimp only [E,A]
    ring

end CenteredMomentEnergyZeroReferenceBounded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroUnbalancedOriginalPower
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroUnbalancedOriginalSource CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=> Eisenstein.O

theorem original_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ e → 0≤ K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤ Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0< X₁ →0< X₂ →Real.logb Z X₁≤ s.width/4 →1≤ X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hxiM:xi≤ s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 <;> first | rfl | ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 <;> first | rfl | ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> first | rfl | ((try dsimp only [E,A]) <;> ring)
  · dsimp only [E,A]
    ring

end CenteredMomentEnergyZeroUnbalancedOriginalPower

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

namespace CenteredMomentEnergyZeroUnbalancedOriginalGates
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBranchGeometry

lemma original_long_positive (Z M X₁ X₂:ℝ)(hZ:1< Z)(hM:0< M)
    (_hX₁:0< X₁)(hX₂:0< X₂)
    (hshort:length Z X₁≤ M/4)
    (hlarge:5*M/6≤ length Z X₁+length Z X₂):
    0< Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤ X₂:=by
  have hpos:0< length Z X₂:=by linarith
  have he:=CenteredMomentEnergyInputParentCapacity.length_eq_max_log Z X₂ hZ hX₂
  have hl:0< Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma raw_short_bound (Z M X:ℝ)(hZ:1< Z)(hX:0< X)
    (hshort:length Z X≤ M/4):Real.logb Z X≤ M/4:=by
  rw [CenteredMomentEnergyInputParentCapacity.length_eq_max_log Z X hZ hX] at hshort
  exact (le_max_right _ _).trans hshort

end CenteredMomentEnergyZeroUnbalancedOriginalGates

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroUnbalancedOriginal
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroUnbalancedOriginalPower
open CenteredMomentEnergyZeroUnbalancedOriginalGates
local notation "O"=> Eisenstein.O

theorem original_unbalanced_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ e → 0≤ K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤ Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0< X₁ →0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hshort hlarge
  have hordered (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)
      (hshort:length Z X₁≤ s.width/4)
      (hlarge:5*s.width/6≤ length Z X₁+length Z X₂):
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
    have hlong:=original_long_positive Z s.width X₁ X₂ hZ.1
      (hrho.trans_le hslo) hX₁ hX₂ hshort hlarge
    exact hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂
      (raw_short_bound Z s.width X₁ hZ.1 hX₁ hshort) hlong.2.2
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hordered p X₁ X₂ hX₁ hX₂ hshort hlarge
  · let p':Profiles a b:={
      profile:=![p.profile 1,p.profile 0]
      support:=by
        intro i
        fin_cases i
        · simpa using p.support 1
        · simpa using p.support 0 }
    have hpcontrol:p'.control U=p.control U:=by
      simp [p',Profiles.control,mul_comm]
    have hswap:s.plainEnergy p' t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
      unfold NaturalState.plainEnergy CenteredMomentInductionEnergy.energy
      apply tsum_congr
      intro z
      have hh:CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p'.profile 0) (p'.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₂ X₁=
          CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₁ X₂:=by
        simp only [p',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
        unfold CenteredMomentRetainedEnergy.positiveSlotRow
        rw [mul_comm X₂ X₁]
        ring
      rw [hh]
    have hh:=hordered p' X₂ X₁ hX₂ hX₁ hshort (by linarith)
    simpa only [hswap,hpcontrol] using hh

end CenteredMomentEnergyZeroUnbalancedOriginal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroReferenceLiveBounded
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceBounded CenteredMomentFiniteProfileExceptional
local notation "O"=> Eisenstein.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧0< xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ e → 0≤ K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤ Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0< X₁ →0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end CenteredMomentEnergyZeroReferenceLiveBounded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroReferencePhysicalBounded
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=> Eisenstein.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroReferencePhysical

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hB:0≤ B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧0< xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ e → 0≤ K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤ Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),X₁*X₂≤ Z^B →
      5*s.width/6≤ length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤ _+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end CenteredMomentEnergyZeroReferencePhysicalBounded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyOriginalProfileControl
local notation "O"=> Eisenstein.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤ Z)(hL:L'≤ L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

theorem actual_high_from_physical
    (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hB:0≤ B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤ e→0≤ K→0≤ Cmass→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      ZeroLowAt Q a b bΦ Bmask (Mcap+Bmask+rho/100) Mcap e Z degree S K→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q→ rho≤ s.width→s.width≤ Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),X₁*X₂≤ Z^B→
      5*s.width/6≤ length Z X₁+length Z X₂→
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
          Cmass*(p.control Smass)^2*(1+|t|)^Jmass*
            Z^(max s.width (length Z X₁+length Z X₂)+emass))→
      s.plainEnergy p t X₁ X₂≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^Jout*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuCap,hLu,hLuCap,huStage⟩:=
    CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirCap,hLr,hLrCap,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrStage⟩:=
    CenteredMomentEnergyZeroReferencePhysicalBounded.actual_positive_source_entry
      a b bΦ rho ε Mcap Bmask B εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,huBound⟩:=huStage S
  obtain ⟨Jr,Ur,Cr,hCr,hrBound⟩:=hrStage S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=1
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤ P:=by norm_num [P]
  have hD:0≤ D:=by dsimp [D];positivity
  have hT:0≤ T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0< Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [huBound,hrBound] with Z hZu hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂ hvolume hlarge
  dsimp only
  intro hphysical
  let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
  have hlowU:=low_restrict Q a b bΦ Bmask _ Lu Mcap e Z degree S K hZ.1.le hLuCap hlow
  have hlowR:=low_restrict Q a b bΦ Bmask _ Lr Mcap e Z degree S K hZ.1.le hLrCap hlow
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|:=by exact le_add_of_nonneg_right (abs_nonneg t)
  let Mout:ℝ:=max s.width (length Z X₁+length Z X₂)
  have hwm:s.width≤ Mout:=le_max_left _ _
  let F:ℝ:=(p.control U)^2*(1+|t|)^Jout*Z^(Mout+efinal)
  have hF:0≤ F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤ Jout)(hej:ej≤ efinal):
      (p.control Sj)^2*(1+|t|)^jj*Z^(s.width+ej)≤ F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (add_le_add hwm hej)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤ Jout:=by dsimp [Jout];omega
  have hjr:Jr≤ Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤ Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤ Cfixed*(K+Cmass+1):=by
    have hCuC : Cu ≤ Cfixed := by
      dsimp only [Cfixed]
      linarith only [hCr, hD, hT]
    exact mul_le_mul hCuC (by linarith only [hCmass])
      (by linarith only [hK]) hCfixed.le
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · have hunbalanced:=hZu.2 e Q degree K he hK hlowU s hQ hwidthLo hwidth
      p t X₁ X₂ hX₁ hX₂ hshort hlarge
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤ Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hfour':=balanced_four_scale_gates Z s.width X₁ X₂ hZ.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_not_ge hshort)
    have hfour:Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂:=
      ⟨hfour'.1,hfour'.2.1,hfour'.2.2.1,hfour'.2.2.2.1⟩
    rcases hZ.2 e Q degree K he hK hlowR s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂
      hvolume hlarge with hzero|hsource
    · rw [hzero]
      positivity
    have hmass:=hphysical hfour
    have hmEnv:(p.control Smass)^2*(1+|t|)^Jmass*Z^(Mout+emass)≤ F:=by
      have hp:=profile_control_mono p hm
      have hp0:=p.control_nonneg Smass
      have hj:=pow_le_pow_right₀ hbase hjm
      have hx:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show Mout+emass≤ Mout+efinal by linarith only [hmassFinal])
      dsimp [F]
      gcongr
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        (X₁*X₂)≤ Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 <;> first | rfl | ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤ P*(p.control U)^2:=by
      have hc:=plain_control_sq_le inp p U 0 1 (by norm_num) (by simp) (by intro i;exact Fin.elim0 i)
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [P,Finset.insert_eq_of_mem h00,one_pow,one_mul] using hc
    have hheight1:1≤(1+|t|)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤ efinal):s.radial.scale*Z^x≤ Z^(Mout+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by have hh:=hwm;unfold NaturalState.width at hh;linarith only [hh, hx, s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤ A)(hx:x≤ efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(Mout+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          dsimp [F]
          nlinarith only [mul_nonneg (show 0≤ c*P*A*(p.control U)^2*Z^(Mout+efinal) by positivity)
            (sub_nonneg.mpr hheight1)]
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤ Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu, hCr, hD, hT, hK, hCmass, mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤ Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|)^Jout*Z^(Mout+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤ _ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+(e+ε)))≤ _ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+e+ε)≤ _
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end CenteredMomentEnergyZeroGrowthHighBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroGrowthSourceControlled
open HeckeFamily InversePrincipalEnergy CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroGrowthSource (PhysicalGrowthAt)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hB:0≤ B)(hLB:2*L≤ B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass Cprevious:ℝ),
      0≤ e→0≤ K→0≤ Cmass→0≤ Cprevious→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z degree S Cprevious→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+Cprevious+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0< Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass Cprevious he hK hCm hCp hef hmf hdf htf hold hlow hmass
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hCout:0≤ Cfixed*(K+Cmass+Cprevious+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  by_cases hsmall:s.width≤ rho
  · have hh:=zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z degree S
      Cprevious hCp hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤ Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ (show 1≤1+‖t‖ by linarith [norm_nonneg t]) hj
    have hcoeff:Cprevious≤ Cfixed*(K+Cmass+Cprevious+1):=by
      dsimp [Cfixed]
      nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    gcongr
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤ Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤ max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤ Cfixed*(K+Cmass+Cprevious+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤ Z^B:=by
    calc
      _≤ Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤ Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤ Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤ Cfixed:=by dsimp [Cfixed];linarith
  have hcoefFull:Ch*(K+Cmass+1)≤ Cfixed*(K+Cmass+Cprevious+1):=
    mul_le_mul hcoeff (by linarith) (by positivity) hCfixed.le
  have hfront:=mul_le_mul_of_nonneg_right hcoefFull
    (show 0≤ diagonalControl s.radial.profile*(p.control Uh)^2*(1+|t|)^Jh*
      Z^(max s.width (length Z X₁+length Z X₂)+efinal) by positivity)
  have hmid:s.plainEnergy p t X₁ X₂≤
      Cfixed*(K+Cmass+Cprevious+1)*diagonalControl s.radial.profile*(p.control Uh)^2*
        (1+|t|)^Jh*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
    apply hh.trans
    convert hfront using 1 <;> first | rfl | ring
  apply hmid.trans
  rw [Real.norm_eq_abs]
  gcongr

end CenteredMomentEnergyZeroGrowthSourceControlled

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive SchwartzPlanePoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => Eisenstein.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*CenteredMomentReflectionDeletion.norm H.val)

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0< X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0< naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=> redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := CenteredMomentReflectionDeletion.norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0< C) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤ C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0< naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤ M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0< C) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤ C*Z^M → M+xi< a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0< naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0< naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dif_pos hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1< Z)(_hb : 0< b)(hshort : 0< Xshort)(hlong : Xshort≤ Xlong)
    (hN : 1≤ Nshort)(hsupport : 1≤ b*Xlong) :
    length Z (Xshort/Nshort)≤ Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0< Xlong := hshort.trans_le hlong
  have hn : 0< Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤ Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤ max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [CenteredMomentEnergyInputParentCapacity.length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem live_deleted_growth (Z b M xi Xshort Xlong Nshort Nlong : ℝ)
    (hZ : 1< Z)(hb : 0< b)(_hM : 0≤ M)(hshort : 0< Xshort)(hlong : Xshort≤ Xlong)
    (hNs : 1≤ Nshort)(hNl : 1≤ Nlong)(hsupport : 1≤ b*Xlong)
    (hlive : 0≤ M-Real.logb Z (Xlong/Nlong)+xi)
    (x : ℝ)(hx : x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/Nshort)≤
      M+Real.logb Z Nlong+Real.logb Z (max 1 b)+xi := by
  have hxlong : 0< Xlong := hshort.trans_le hlong
  have hnlong : 0< Nlong := zero_lt_one.trans_le hNl
  have hwindow := (reflection_window_length Z _ x hZ (le_max_left _ _) hx).1
  rw [max_eq_right hlive,Real.logb_div hxlong.ne' hnlong.ne'] at hwindow
  have hshortbound := deleted_short_length Z b Xshort Xlong Nshort hZ hb hshort hlong hNs hsupport
  linarith

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0< epsilon) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ Real.logb Z (max 1 b)≤ epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

theorem actual_deleted_growth {Z Bmask bΦ : ℝ}(s : NaturalState Z Bmask bΦ)
    (b xi Xshort Xlong : ℝ)(hZ : 1< Z)(hb : 0< b)
    (hshort : 0< Xshort)(hlong : Xshort≤ Xlong)(hsupport : 1≤ b*Xlong)
    (Dshort Dlong : Finset (Ideal O))
    (hDs : Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset)
    (hDl : Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset)
    (hlive : 0≤ s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)
    (x : ℝ)(hx : x∈Set.Icc 0
      (max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
      s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+Real.logb Z (max 1 b)+xi := by
  exact live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ hb s.width_nonneg
    hshort hlong (divisor_norm s Dshort hDs).1 (divisor_norm s Dlong hDl).1 hsupport hlive x hx

theorem eventually_actual_source_zero (bΦ xi : ℝ)(hbΦ : 0< bΦ)(hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀a : ℝ,s.width+xi< a →
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0< C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_source_zero C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap a hfar
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤ C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  exact (hZ.2 (naturalCharacter s.character z) ψ s.width a hcap hm hfar).2.2

theorem eventually_actual_deleted_growth (b epsilon : ℝ)(hb : 0< b)(hepsilon : 0< epsilon) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(Bmask bΦ : ℝ)(s : NaturalState Z Bmask bΦ)
      (xi Xshort Xlong : ℝ),0< Xshort → Xshort≤ Xlong → 1≤ b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset →
      Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset →
      0≤ s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  filter_upwards [eventually_endpoint_defect b epsilon hepsilon] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask bΦ s xi Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl hlive x hx
  have h := actual_deleted_growth s b xi Xshort Xlong hZ.1 hb hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx
  linarith [hZ.2]

theorem eventually_actual_retained_deleted_growth (b bΦ xi epsilon : ℝ)
    (hb : 0< b)(hbΦ : 0< bΦ)(hxi : 0< xi)(hepsilon : 0< epsilon) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀(Xshort Xlong : ℝ),0< Xshort → Xshort≤ Xlong → 1≤ b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset →
      Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset →
      ∀(E : Finset (Ideal O)),E∈(redundantSet χ.modulus ψ.modulus).powerset →
      ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0< naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4))
        (naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H) hY →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0< C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_choice_range C xi hC hxi,
    eventually_actual_deleted_growth b epsilon hb hepsilon] with Z hZ hgrowth
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl E hE H hY n hn x hx
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤ C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hL : 0< Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    div_pos (hshort.trans_le hlong) (zero_lt_one.trans_le (divisor_norm s Dlong hDl).1)
  have hexp : Z^(Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))=
      Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' hL
  have hrange := hZ.2 (naturalCharacter s.character z) ψ s.width
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))) hcap hm E hE H
  rw [hexp] at hrange
  have hlive := hrange hY n hn
  exact hgrowth.2 Bmask bΦ s xi Xshort Xlong hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx

end CenteredMomentEnergyZeroReflectionSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyZeroGrowthChild
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=> Eisenstein.O

theorem independent_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤ Bmask)(ha:0< a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤ Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    :
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤ Bmask)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤ Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    :
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  have hh:=independent_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end CenteredMomentEnergyZeroGrowthChild

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyZeroGrowthMoments
open HeckeFamily HeckeDyadic  InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroGrowthChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O

theorem reflected_uniform (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0< D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤ C →
    ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤ Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤ Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0< X₁ → 0< X₂ → X₁≤ Z^L → X₂≤ Z^L →
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(max s.width (length Z X₁+length Z X₂)+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hh:=reflected_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤ C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤ Z^(max s.width (length Z X₁+length Z X₂)+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 <;> first | rfl | ring

lemma actual_growth_power (Z b M xi epsilon loss Xshort Xlong Nshort Nlong x:ℝ)
    (hZ:1< Z)(hb:0< b)(hM:0≤ M)(he:0≤ epsilon)(hxi:0≤ xi)
    (hshort:0< Xshort)(hlong:Xshort≤ Xlong)(hNs:1≤ Nshort)(hNl:1≤ Nlong)
    (hsupport:1≤ b*Xlong)(hdef:Real.logb Z (max 1 b)≤ epsilon)
    (hlive:0≤ M-Real.logb Z (Xlong/Nlong)+xi)
    (hx:x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)):
    Z^(max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss)≤
      Nlong*Z^(M+loss+epsilon+xi):=by
  have hg:=live_deleted_growth Z b M xi Xshort Xlong Nshort Nlong
    hZ hb hM hshort hlong hNs hNl hsupport hlive x hx
  have hN:=Real.logb_nonneg hZ hNl
  have hemax:max M (length Z (Real.exp x)+length Z (Xshort/Nshort))≤
      M+Real.logb Z Nlong+epsilon+xi:=max_le (by linarith) (by linarith)
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le (show max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss≤ M+Real.logb Z Nlong+epsilon+xi+loss by linarith)
  apply hp.trans_eq
  rw [show M+Real.logb Z Nlong+epsilon+xi+loss=
    Real.logb Z Nlong+(M+loss+epsilon+xi) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hNl)]

end CenteredMomentEnergyZeroGrowthMoments

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentEnergyZeroGrowthWindow
open CenteredMomentFiniteProfileExceptional
open HeckeFamily HeckeDyadic InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthMoments CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=> Eisenstein.O

theorem actual_reflected_window (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0< D ∧
    ∀(bΦ Bmask L Mcap loss Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤ C→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S C→0≤ Bmask→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤ Mcap→
    ∀(Wshort:𝓢(ℝ,ℂ)),Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀xi epsilon Xshort Xlong:ℝ,0≤ xi→0≤ epsilon→1< Z→
    Real.logb Z (max 1 b)≤ epsilon→Mcap+Bmask+epsilon+xi≤ L→
    0< Xshort→Xshort≤ Xlong→Xshort≤ Z^L→1≤ b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset→
    Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset→
    let Nshort:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nlong:ℝ:=(∏P∈Dlong,P).absNorm;
    0≤ s.width-Real.logb Z (Xlong/Nlong)+xi→
    ∀(j k:Fin 2)(v t x:ℝ),
    x∈Set.Icc 0 (max 0 (s.width-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)→
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Xshort/Nshort) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+loss+epsilon+xi)*Nlong)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hu⟩:=reflected_uniform a b ha hlo hhi S
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    xi epsilon Xshort Xlong hxi he hZ hdef hL hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive j k v t x hx
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:0<((∏P∈Dshort,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
  have hpL:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ hpL).mpr hNlcap
  have hlen:=live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ (by linarith)
    s.width_nonneg hshort hlong hNs hNl hsupport hlive x hx
  have hn:=length_nonneg Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ)) hZ
  have hlenx:length Z (Real.exp x)≤ L:=by linarith
  have hlogx:Real.logb Z (Real.exp x)≤ length Z (Real.exp x):=by
    rw [CenteredMomentEnergyInputParentCapacity.length_eq_max_log Z _ hZ (Real.exp_pos _)]
    exact le_max_right _ _
  have hxc:Real.exp x≤ Z^L:=(Real.logb_le_iff_le_rpow hZ (Real.exp_pos _)).mp (hlogx.trans hlenx)
  have hsc:Xshort/((∏P∈Dshort,P).absNorm:ℝ)≤ Z^L:=
    (div_le_self hshort.le hNs).trans hshortcap
  have hh:=hu bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    j k v t (Real.exp x) (Xshort/((∏P∈Dshort,P).absNorm:ℝ))
    (Real.exp_pos _) (div_pos hshort hpS) hxc hsc
  have hp:=actual_growth_power Z b s.width xi epsilon loss Xshort Xlong _ _ x
    hZ (by linarith) s.width_nonneg he hxi hshort hlong hNs hNl hsupport hdef hlive hx
  have hcoef:0≤ C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*(1+|t|)^(2*n):=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  apply hh.trans
  have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef)
    (show 0≤(1+‖v‖)^(2*n) by positivity)
  convert hbnd using 1 <;> first | rfl | ring
end CenteredMomentEnergyZeroGrowthWindow

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroGrowthReflection
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=> Eisenstein.O

theorem live_deleted_reflection (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hepsilon:0< epsilon)(hxi:0< xi)(hdefect:0< defect)
    (B:ℕ)(hB:2≤ B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤ Bmask→
    Mcap+Bmask+defect+xi≤ L→Mcap+Bmask+defect≤ Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤ Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0< Xshort→Xshort≤ Xlong→Xshort≤ Z^L→1≤ b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset→
    Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
          (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=actual_reflected_window a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hz:=zero_lt_one.trans hZ.1
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:=zero_lt_one.trans_le hNs
  have hpL:=zero_lt_one.trans_le hNl
  have hxl:=hshort.trans_le hlong
  have hlogs:=deleted_short_length Z b Xlong Xlong 1 hZ.1 (by linarith) hxl le_rfl le_rfl hsupport
  simp only [div_one] at hlogs
  have hn:=length_nonneg Z Xlong hZ.1
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ.1 hpL).mpr hNlcap
  have hlength:s.width≤ Lreflect+Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)):=by
    rw [Real.logb_div hxl.ne' hpL.ne']
    linarith [hendpoint.2]
  have hpowL:=Real.rpow_logb hz hZ.1.ne' (div_pos hxl hpL)
  have hpowS:=Real.rpow_logb hz hZ.1.ne' (div_pos hshort hpS)
  let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*((∏P∈Dlong,P).absNorm:ℝ)
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))
    (Real.logb Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))) E hlength
  simp only [Finset.prod_empty,mul_one,hpowL,hpowS] at hh
  apply hh
  · dsimp [E]
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  · intro v j k x hx
    exact hchild bΦ Bmask L Mcap loss Z Q degree K hK hgrowth hBmask s hQ hs Wshort hsShort
      xi defect Xshort Xlong hxi.le hdefect.le hZ.1 hendpoint.2 hL
      hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive j k v t x hx
end CenteredMomentEnergyZeroGrowthReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=> Eisenstein.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1< Z)(hb:0< b)(hx:0< Xlong)(hsupport:1≤ b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤ defect)
    (hL:Mcap+Bmask+defect+xi≤ L)(hL0:0≤ L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤ Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤ L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0< C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0< X→X≤ Z^L→
      ∀D:Finset (Ideal O),D∈(CubicEisenstein.primeSupport s.puncture).powerset→
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end CenteredMomentEnergyZeroGrowthBounds

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroGrowthBounded
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic InversePrincipalEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=> Eisenstein.O

open CenteredMomentEnergyZeroGrowthReflection CenteredMomentEnergyZeroGrowthBounds

theorem live_deleted_bounded (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hepsilon:0< epsilon)(hxi:0< xi)(hdefect:0< defect)
    (B:ℕ)(hB:2≤ B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤ Bmask→
    Mcap+Bmask+defect+xi≤ L→Mcap+Bmask+defect≤ Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤ Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0< Xshort→Xshort≤ Xlong→Xshort≤ Z^L→1≤ b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CubicEisenstein.primeSupport s.puncture).powerset→
    Dlong∈(CubicEisenstein.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(L*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L :=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=live_deleted_reflection
    a b bΦ epsilon xi defect saving Lreflect ha hlo hhi hbΦ hepsilon hxi hdefect B hB S
  obtain ⟨Cshort,hCs,hshortmass⟩:=actual_deleted_short_mass b
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cshort,hC,mul_pos hD hCs,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive
  have hL0:0≤ L:=by linarith [s.width_nonneg]
  have hw:=actual_window_cap Z b Bmask bΦ Mcap defect xi L Xlong hZ.1 (by linarith)
    (hshort.trans_le hlong) hsupport hendpoint.2 hL hL0 s hs Dlong hDl
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hwindow:1+2*(max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)
      ≤1+2*(L*Real.log Z):=by nlinarith
  have hmass:=hshortmass Z Bmask bΦ L s Wshort (fun x hx=>(hsShort hx).2)
    t Xshort hshort hshortcap Dshort hDs
  have hd:=diagonalControl_nonneg s.radial.profile
  have hN:0≤((∏P∈Dlong,P).absNorm:ℝ):=Nat.cast_nonneg _
  have hZ0:0< Z:=zero_lt_one.trans hZ.1
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hwindow (by positivity)
    · positivity
  · have he:=mul_le_mul_of_nonneg_left hmass
      (show 0≤ D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity)
    convert he using 1 <;> first | rfl | ring

end CenteredMomentEnergyZeroGrowthBounded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic 
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentEnergyReferenceReflection
local notation "O" => Eisenstein.O

theorem finite_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0< xi)(hscale : 0< Cscale)(hepsilon : 0< epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0< C ∧ 1< Z₀ ∧
      ∀{ι : Type}[Fintype ι],∀χ : ι→Character,(∀i,(χ i).residue≠1) →
      ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
      ∀(G : ι→𝓢(ℝ,ℂ))(P : ι→ℂ)(Z M along Src Rcap : ℝ),Z₀≤ Z →
        M+xi< along → 0< Src → 1≤ Rcap →
        (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤ Src) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤ Cscale*Z^M) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤ Rcap) →
        (∀i,retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0) ∧
        (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
          C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=CenteredMomentUniformOriginalEnergy.actual_original_energy_to_retained
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp (eventually_natural_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hχ
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hχ
  refine ⟨ψ,hψ,?_⟩
  intro G P Z M along Src Rcap hZ₀ hfar hSrc hR hGS hmod hcap
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0:=
    (hZ.2 (χ i) (ψ i) M along (hψ i).2.2 (hmod i) hfar).2.2.2 (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤ Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=> Z^along) P Src Z Rcap hSrc hZ.1.le hR
    (fun _=> Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simp only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
    mul_zero,zero_add] at hh
  exact ⟨hzero,hh⟩

theorem radial_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0< xi)(hscale : 0< Cscale)(hepsilon : 0< epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0< C ∧ 1< Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤ Z → 0< K → (∀z,0≤(Φ (‖ringComplex z‖^2/K)).re) →
      (∀z,‖P z‖≤ Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤ d → Function.support Wshort⊆Set.Icc c d → 0< Xshort →
      M+xi< along → 0< Src → 1≤ Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤ Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤ Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤ Rcap) →
      radialEnergy (fun z=> polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=> polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,Z₀,hC,hZ₀,hfinite⟩:=finite_original_error xi saving Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,Z₀,hC,hZ₀,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d Z M along Xshort Src Rcap
    hZ hK hΦ hP hχ hd hshort hXshort hfar hSrc hR hGS hmod hcap
  have hz:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hshortsum:=single_radial_summable χ P omega Wshort c d Xshort Pbound hd hXshort
    hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  have hmem(z:↥S):keep (z:O):=(Finset.mem_filter.mp z.property).2
  obtain ⟨ψ,hψ,hf⟩:=hfinite (fun z:↥S=>χ z) (fun z=> hχ z (hmem z))
  let Q(z:↥S):ℂ:=
    (polynomial (χ z) false Wshort Xshort 0 (omega z)*P z)*
      (Real.sqrt ((Φ (‖ringComplex z‖^2/K)).re):ℂ)
  have hh:=(hf (fun z:↥S=> G z) Q Z M along Src Rcap hZ hfar hSrc hR
    (fun z=> hGS z (hmem z)) (fun z=> hmod z (hmem z)) (fun z=> hcap z (hmem z))).2
  simp only [Q,←mul_assoc] at hh
  rw [finite_weighted rows keep
      (fun z=> polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ,
    finite_weighted rows keep
      (fun z=> polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (hshortsum.sum_le_tsum rows (fun z _=> by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl))
    (by positivity))

theorem natural_polynomials_summable {Z Bmask bΦ:ℝ}(state:NaturalState Z Bmask bΦ)
    (Wlong Wshort:𝓢(ℝ,ℂ))(a b Xlong Xshort t omega:ℝ)
    (hb:0≤ b)(hXlong:0< Xlong)(hXshort:0< Xshort)
    (hsLong:Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b)
    (hsShort:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b):
    Summable (fun z:O=> if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wlong Xlong 0 t*
        polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖ringComplex z‖^2/state.radial.scale)).re else 0) ∧
    Summable (fun z:O=> if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖ringComplex z‖^2/state.radial.scale)).re else 0):=by
  constructor
  · simpa only [mul_one] using pair_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=> t) (fun _=> omega) Wlong Wshort a b a b Xlong Xshort 1
      hb hb hXlong hXshort hsLong hsShort (fun _=> by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos
  · simpa only [mul_one] using single_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=> omega) Wshort a b Xshort 1 hb hXshort hsShort (fun _=> by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos

theorem natural_original_error (a b bΦ epsilon xi saving:ℝ)
    (ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0< Xshort → state.width+xi< along →
      radialEnergy (fun z=> polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        (effectiveState state).radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        radialEnergy (fun z=> polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
          (effectiveState state).radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨H,C,Z₀,hC,hZ₀,hr⟩:=radial_original_error xi saving
    ((fixedConductorFactor:ℝ)*bΦ) epsilon hxi (mul_pos conductorFactor_pos hbΦ) hepsilon
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hz:1< Z:=hZ₀.trans_le hZ
  refine ⟨hz,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,HeckeDyadic.summand,radialEnergy]
  have hpos:0< sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0< Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤ sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤ Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  have hh:=hr (fun _=> G) (naturalCharacter state.character) (fun _=>1) (fun _=> omega)
    (effectiveState state).radial.keep state.radial.profile state.radial.scale 1
    Wshort a b Z state.width along Xshort Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width)) hZ state.radial.scale_pos
    state.radial.nonneg (fun _=> by simp) (effective_character_nonprincipal state)
    hb hsShort hXshort hfar hSrc (le_max_left _ _) (fun _ _=> hnorm)
    (effective_character_cap state hbΦ.le)
    (fun z hz=>(effective_character_cap state hbΦ.le z hz).trans (le_max_right _ _))
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t,mul_one] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

theorem short_radial_mass (χ:O→Character)(W:𝓢(ℝ,ℂ))(a b X:ℝ)
    (hb:0≤ b)(hX:0< X)(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (omega:O→ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K):
    radialEnergy (fun z=> polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (128*max 1 b)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
        SchwartzPlanePoisson.diagonalControl Φ*max 1 K*X:=by
  let A:=((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)
  let V:=(128*max 1 b*A)^2*X
  have hV:0≤ V:=by dsimp [V];positivity
  have hp(z:O):‖polynomial (χ z) false W X 0 (omega z)‖^2≤ V:=by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound (χ z) W b A X (omega z)
        (apply_nonneg _ _) hX (SchwartzMap.norm_le_seminorm ℝ W) (fun y hy=>(hs hy).2)) 2
    simpa only [mul_pow,Real.sq_sqrt hX.le,V] using hh
  have hsum:=single_radial_summable χ (fun _=>1) omega W a b X 1 hb hX hs
    (fun _=> by simp) keep Φ K hK
  simp only [mul_one] at hsum
  have hweight:=CenteredMomentAbsoluteEnergy.radial_norm_summable Φ K hK
  have hh:radialEnergy (fun z=> polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (∑'z:O,‖Φ (‖ringComplex z‖^2/K)‖)*V:=by
    rw [←tsum_mul_right]
    apply hsum.tsum_le_tsum _ (hweight.mul_right V)
    intro z
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    · exact mul_nonneg (norm_nonneg _) hV
  apply (hh.trans (mul_le_mul_of_nonneg_right
    (CenteredMomentAbsoluteEnergy.radial_weight_lattice_bound_all Φ K hK) hV)).trans_eq
  dsimp [V,A]
  ring

theorem natural_original_error_mass (a b bΦ epsilon xi saving:ℝ)
    (ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0< Xshort → state.width+xi< along →
      radialEnergy (fun z=> polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        state.radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        SchwartzPlanePoisson.diagonalControl state.radial.profile*max 1 state.radial.scale*Xshort:=by
  obtain ⟨n,S,C,hC,h⟩:=natural_original_error a b bΦ epsilon xi saving ha hb hbΦ hepsilon hxi
  refine ⟨n,S,C*(128*max 1 b)^2,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have hh:=hZ.2 Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have he(f:O→ℂ):radialEnergy f (effectiveState state).radial.keep
      state.radial.profile state.radial.scale=
      radialEnergy f state.radial.keep state.radial.profile state.radial.scale:=
    radialEnergy_effective state.radial f
  rw [he,he] at hh
  have hm:=short_radial_mass (naturalCharacter state.character) Wshort a b Xshort
    hb hXshort hsShort (fun _=> omega) state.radial.keep state.radial.profile
    state.radial.scale state.radial.scale_pos
  have hz:0< Z:=zero_lt_one.trans hZ.1
  apply (hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_eq
  ring

end CenteredMomentEnergyZeroRetainedError

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
