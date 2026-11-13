/-
Basics of centered moments adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DyadicHeckePolynomials

/-!
# Basics of centered moments

Quotients by nonzero Eisenstein elements are finite; centered-moment coefficients, scale
suprema, norm-power lattice profiles and masked characters; primary ideal characters and the
twisted rectangle saving.
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
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def scaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ inv W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ inv W S) (scaleSum χ inv (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ inv J) using 1 <;> try rfl
    dsimp only [Pi.neg_apply, id_eq]
    rw [Complex.real_smul]
    push_cast
    ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  all_goals
    solve
    | ext x y <;> rfl
    | ext t; simp only [scaleSum, Pi.mul_apply, Finset.sum_apply]
    | simp only [scaleSum, scaleProfile, Finset.sum_apply]
      simp_rw [Finset.mul_sum]
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro J hJ
      push_cast
      ring

theorem scaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ inv W S l=polynomial χ inv W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤ b) (hd : 0≤ d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤ hi) (hlw : low≤ high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤ E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 0 *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 0 * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    scaleSum (χ i) false (scaleTest W j) S x *
      scaleSum (ψ i) false (scaleTest V k) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) false (scaleTest W j) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    scaleSum_eq_polynomial (ψ i) false (scaleTest V k) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((scaleSum_continuous (χ i) false _ S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((scaleSum_continuous (ψ i) false _ T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=> F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (scaleSum_deriv (χ i) false W S (hW.differentiable (by simp)) x).mul_const
        (scaleSum (ψ i) false (scaleTest V k) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((scaleSum_deriv (ψ i) false V T (hV.differentiable (by simp)) y).const_mul
        (scaleSum (χ i) false (scaleTest W j) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=> hc j k i)
    (fun k i _ x y=> hx k i x y) (fun j i _ x y=> hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤ b) (hd : 0≤ d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤ hi) (hlw : low≤ high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤ E) :
    ∃ B : ι→ℝ,(∀i,0≤ B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 0 *
          polynomial (ψ i) false V (Real.exp y) 0 0 * P i‖^2≤ B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    scaleSum (χ i) false W S p.1 * scaleSum (ψ i) false V T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((scaleSum_continuous (χ i) false W S hW.continuous).comp continuous_fst).mul
      ((scaleSum_continuous (ψ i) false V T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      F i (x,y)=polynomial (χ i) false W (Real.exp x) 0 0 *
        polynomial (ψ i) false V (Real.exp y) 0 0 * P i := by
    dsimp only [F]
    rw [scaleSum_eq_polynomial (χ i) false W S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      scaleSum_eq_polynomial (ψ i) false V T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=> sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end CenteredMomentScaleSupremum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


open scoped BigOperators NNReal
namespace CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def ofResidueMask {S : Type*} [CommRing S] (ρ : M →* R)
    (χ : MulChar R ℂ) (puncture : M →* S) : MaskedCharacter M R where
  residue := ρ
  character := χ
  keep a := IsUnit (puncture a)
  keep_mul a b := by
    rw [map_mul]
    exact (Commute.all _ _).isUnit_mul_iff

@[simp] theorem ofResidueMask_keep_one {S : Type*} [CommRing S]
    (ρ : M →* R) (χ : MulChar R ℂ) (puncture : M →* S) :
    (ofResidueMask ρ χ puncture).keep 1 := by
  change IsUnit (puncture 1)
  simp only [map_one, isUnit_one]

def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0

@[simp] theorem MaskedCharacter.value_mul (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all

def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)

@[simp] theorem normTwist_mul (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by
  simp only [normTwist, map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (N a).coe_nonneg (N b).coe_nonneg _

def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a

@[simp] theorem coefficient_mul (d : MaskedCharacter M R) (N : M →* ℝ≥0)
    (t : ℝ) (a b : M) :
    coefficient d N t (a * b) = coefficient d N t a * coefficient d N t b := by
  simp only [coefficient, MaskedCharacter.value_mul, normTwist_mul]
  ring

def plainSum (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s : Finset M) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ a ∈ s, coefficient d N t a * W ((N a : ℝ) / X)

def rectangle (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂) -
    W₁ ((N a : ℝ) / Y₁) * W₂ ((N b : ℝ) / Y₂)

theorem rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by
  simp only [plainSum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [coefficient_mul, rectangle]
  ring

theorem slot_rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (p : M) (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (p * (a * b)) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      coefficient d N t p *
        (plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
          plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂) := by
  rw [← rectangle_sum_eq]
  simp only [coefficient_mul, Finset.mul_sum, mul_assoc]

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

theorem volume_products_eq (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  calc
    _ = c ^ 2 * I₁ * I₂ *
      ((X₁ : ℂ) ^ (1 + Complex.I * t) * (X₂ : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [hpow]; ring

theorem centered_error_identity (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    A₁ * A₂ - B₁ * B₂ =
      (A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) -
        (B₁ - b₁) * B₂ - b₁ * (B₂ - b₂) := by
  linear_combination hmain

theorem norm_centered_le (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [norm_mul]

theorem norm_centered_le_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith

theorem scale_le_product_div {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX

theorem sum_scales_le {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  have a := scale_le_product_div (le_trans hL.le hX₁) hL hX₂ hprodX
  have b := scale_le_product_div (le_trans hL.le hX₂) hL hX₁
    (by simpa only [mul_comm] using hprodX)
  have c := scale_le_product_div (le_trans hL.le hY₁) hL hY₂ hprodY
  have d := scale_le_product_div (le_trans hL.le hY₂) hL hY₁
    (by simpa only [mul_comm] using hprodY)
  linarith

theorem centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring

theorem extracted_volume_phase (X D t : ℝ) (hX : 0 ≤ X) (hD : 0 < D) :
    (D : ℂ) ^ (Complex.I * t) * ((X / D : ℝ) : ℂ) ^ (1 + Complex.I * t) =
      (X : ℂ) ^ (1 + Complex.I * t) / (D : ℂ) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hp : (D : ℂ) ^ (Complex.I * t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [positive_div_cpow X D hX hD,
    Complex.cpow_add _ _ hDc, Complex.cpow_one]
  field_simp

theorem extracted_volume_sum {D : Type*} (s : Finset D) (a : D → ℂ)
    (norm : D → ℝ) (hnorm : ∀ d ∈ s, 0 < norm d)
    (c I : ℂ) (t X : ℝ) (hX : 0 ≤ X) :
    (∑ d ∈ s, a d * (norm d : ℂ) ^ (Complex.I * t) *
      volumeTerm c I t (X / norm d)) =
      volumeTerm (c * ∑ d ∈ s, a d / (norm d : ℂ)) I t X := by
  unfold volumeTerm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := extracted_volume_phase X (norm d) t hX (hnorm d hd)
  calc
    _ = a d * c * I * ((norm d : ℂ) ^ (Complex.I * t) *
        ((X / norm d : ℝ) : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [h]; ring

theorem centered_volume_fallback (A₁ A₂ B₁ B₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T C : ℝ)
    (hA₁ : ‖A₁‖ ≤ C * X₁) (hA₂ : ‖A₂‖ ≤ C * X₂)
    (hB₁ : ‖B₁‖ ≤ C * Y₁) (hB₂ : ‖B₂‖ ≤ C * Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 2 * C ^ 2 * T := by
  have hA := mul_le_mul hA₁ hA₂ (norm_nonneg A₂) ((norm_nonneg A₁).trans hA₁)
  have hB := mul_le_mul hB₁ hB₂ (norm_nonneg B₂) ((norm_nonneg B₁).trans hB₁)
  have h := norm_sub_le (A₁ * A₂) (B₁ * B₂)
  rw [norm_mul, norm_mul] at h
  have heX : C * X₁ * (C * X₂) = C ^ 2 * T := by rw [← hprodX]; ring
  have heY : C * Y₁ * (C * Y₂) = C ^ 2 * T := by rw [← hprodY]; ring
  rw [heX] at hA
  rw [heY] at hB
  linarith

theorem normalized_centered_saving (D : ℂ) (T L C E : ℝ)
    (hT : 0 < T) (hbound : ‖D‖ ≤ 4 * E * C * (T / L)) :
    ‖(Real.sqrt T : ℂ)⁻¹ * D‖ ≤ 4 * E * C * (Real.sqrt T / L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (4 * E * C * (T / L)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)
    _ = 4 * E * C * ((T / Real.sqrt T) / L) := by ring
    _ = _ := by
      have hdiv : T / Real.sqrt T = Real.sqrt T :=
        (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt hT.le).symm
      rw [hdiv]

end
end CenteredMoment

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => Eisenstein.O
/-- Quotients by nonzero Eisenstein elements are finite. -/
theorem finiteEisensteinQuotientOfNonzero {c : O} (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) :=
  Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)

namespace CenteredMomentLattice
open Eisenstein  SchwartzPlanePoisson
open InversePrincipalEnergy

theorem radial_zero_mode_error (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t)
    (A : O → ℂ) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ h, ‖A h‖ ≤ B) :
    ‖t • (∑' h : O, A h * paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)) -
      t • (A 0 * paperRadialFourier W 0)‖ ≤ B * pvControl W := by
  let F : O → ℂ := fun h => A h * paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hF (h : O) : ‖F h‖ ≤ B * ‖paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA h) (norm_nonneg _)
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF (hs.mul_left B)
  have hsplit := hFs.of_norm.tsum_eq_add_tsum_ite 0
  have hzero : F 0 = A 0 * paperRadialFourier W 0 := by simp only [F, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have htail : (∑' h : O, if h = 0 then 0 else F h) =
      ∑' h : {h : O // h ≠ 0}, F h := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [if_neg h.property]
  have heq : (∑' h : O, F h) - F 0 = ∑' h : {h : O // h ≠ 0}, F h := by
    rw [hsplit, htail]
    ring
  have hn : ‖∑' h : {h : O // h ≠ 0}, F h‖ ≤
      B * (∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖) := by
    calc
      _ ≤ ∑' h : {h : O // h ≠ 0}, ‖F h‖ := norm_tsum_le_tsum_norm (hFs.subtype _)
      _ ≤ ∑' h : {h : O // h ≠ 0}, B *
          ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖ :=
        (hFs.subtype _).tsum_le_tsum (fun h => hF h) ((hs.subtype _).mul_left B)
      _ = _ := tsum_mul_left
  change ‖t • (∑' h : O, F h) - t • (A 0 * paperRadialFourier W 0)‖ ≤ _
  rw [← hzero, ← smul_sub, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ t * (B * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖) :=
      mul_le_mul_of_nonneg_left hn ht.le
    _ = B * (t * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖) := by ring
    _ ≤ B * pvControl W := mul_le_mul_of_nonneg_left (pv_lattice_bound W t ht) hB

theorem periodic_lattice_volume_error (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finiteEisensteinQuotientOfNonzero hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        W (‖ringComplex z‖ ^ 2 / X)) -
      (X / ‖ringComplex c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, P r) * paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖P r‖) * pvControl W := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := residueTraceQuotientChar 1 c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c},
    P r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hA (h : O) : ‖A h‖ ≤ B := by
    apply (norm_sum_le _ _).trans
    dsimp only [B]
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul, ψ.norm_apply, mul_one]
  have hA0 : A 0 = ∑ r : O ⧸ Ideal.span {c}, P r := by
    simp only [A, map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
  have hnorm : 0 < ‖ringComplex c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hc))
  have h := radial_zero_mode_error W (X / ‖ringComplex c‖ ^ 2)
    (div_pos hX hnorm) A B hB hA
  rw [actual_radial_poisson_trace W X hX c hc P]
  rw [hA0] at h
  simpa only [A, B, ψ, div_mul_eq_mul_div] using h

theorem logPhase_eq_normPower (t x : ℝ) (hx : 0 < x) :
    kernelLogPhase (t / (2 * Real.pi)) (Real.log x) =
      (x : ℂ) ^ (Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  unfold kernelLogPhase
  rw [← Complex.ofReal_log hx.le]
  congr 1
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  push_cast
  field_simp

def normPowerProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) : 𝓢(ℝ, ℂ) :=
  CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (t / (2 * Real.pi))

theorem normPowerProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t x : ℝ) :
    normPowerProfile W a b ha hs hW t x = (x : ℂ) ^ (Complex.I * t) * W x := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply]
  unfold CompletedHeight.normTwistedSource
  by_cases hx : W x = 0
  · simp only [hx, mul_zero]
  · rw [logPhase_eq_normPower t x (lt_of_lt_of_le ha (hs hx).1)]

theorem normPowerProfile_zero_mode (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
      (2 * Real.pi / Real.sqrt 3 : ℂ) *
        ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (Complex.I * t) * W y := by
  rw [paperRadialFourier_zero_eq_halfline]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y _
  exact normPowerProfile_apply W a b ha hs hW t y

theorem normPowerProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) ≤
        C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha S
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hn W hs hW
  exact ⟨C, hC, fun t => hbound (t / (2 * Real.pi))⟩

theorem periodic_twisted_lattice_volume_error (a b : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∀ c : O, ∀ hc : c ≠ 0,
      ∀ P : O ⧸ Ideal.span {c} → ℂ,
      letI : Finite (O ⧸ Ideal.span {c}) := finiteEisensteinQuotientOfNonzero hc
      letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
      ∃ C : ℝ, 0 < C ∧ ∀ t X : ℝ, 0 < X →
        ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
            (((‖ringComplex z‖ ^ 2 / X : ℝ) : ℂ) ^ (Complex.I * t) *
              W (‖ringComplex z‖ ^ 2 / X))) -
          (X / ‖ringComplex c‖ ^ 2 : ℝ) •
            ((∑ r : O ⧸ Ideal.span {c}, P r) *
              paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)‖ ≤
          C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  refine ⟨n, ?_⟩
  intro W hs hW c hc P
  let : Finite (O ⧸ Ideal.span {c}) := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  obtain ⟨D, hD, hbound⟩ := hn W hs hW
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨(1 + B) * pvConstant * D, mul_pos (mul_pos (by linarith) pvConstant_pos) hD, ?_⟩
  intro t X hX
  have h := periodic_lattice_volume_error (normPowerProfile W a b ha hs hW t) X hX c hc P
  simp only [normPowerProfile_apply] at h
  apply h.trans
  change B * (pvConstant * _) ≤ _
  calc
    _ ≤ B * (pvConstant * (D * (1 + ‖t / (2 * Real.pi)‖) ^ n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound t) pvConstant_pos.le) hB
    _ ≤ (1 + B) * pvConstant * D * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
      nlinarith [mul_nonneg pvConstant_pos.le hD.le,
        mul_nonneg (mul_nonneg pvConstant_pos.le hD.le)
          (show 0 ≤ (1 + ‖t / (2 * Real.pi)‖) ^ n by positivity)]

end CenteredMomentLattice
end

end

namespace CenteredMomentPrimary
open Eisenstein
abbrev PrimaryLower := {z : O // (3 : O) ∣ z - 1}

/-- Primary generators identify unramified ideals with the primary lattice. -/
def primaryLowerIdealEquiv : PrimaryLower ≃ GoodIdeal where
  toFun z := ⟨Ideal.span {z.val}, by
    rw [primaryIdealGenerator_span z.val
      (primary_ne_zero z.val (lambda_sq_dvd_three.trans z.property))
      (lambda_sq_dvd_three.trans z.property)]
    exact primary_ne_zero z.val (lambda_sq_dvd_three.trans z.property)⟩
  invFun I := ⟨primaryIdealGenerator I.val,
    three_dvd_lambda_sq.trans (primaryIdealGenerator_spec I.val I.property).2⟩
  left_inv z := Subtype.ext (primaryIdealGenerator_span z.val
    (primary_ne_zero z.val (lambda_sq_dvd_three.trans z.property))
    (lambda_sq_dvd_three.trans z.property))
  right_inv I := Subtype.ext (primaryIdealGenerator_spec I.val I.property).1
end CenteredMomentPrimary

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => Eisenstein.O
namespace CenteredMomentPrimary
open Eisenstein  CompletedGauss



def primaryIdealCharacter (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    Ideal O →* ℂ :=
  χ.toMonoidHom.comp ((Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom.comp
    primaryIdealGeneratorHom.toMonoidHom)

@[simp] theorem primaryIdealCharacter_apply (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    primaryIdealCharacter c χ I =
      χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator I)) := rfl

theorem primaryIdealCharacter_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    ‖primaryIdealCharacter c χ I‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one χ _

theorem primaryIdealCharacter_zero_of_bad (c : O)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O)
    (hI : primaryIdealGenerator I = 0) : primaryIdealCharacter c χ I = 0 := by
  rw [primaryIdealCharacter_apply, hI, map_zero, χ.map_zero]

theorem tsum_primaryIdealCharacter_all (c : O)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (f : Ideal O → ℂ) :
    (∑' I : GoodIdeal, primaryIdealCharacter c χ I.val * f I.val) =
      ∑' I : Ideal O, primaryIdealCharacter c χ I * f I := by
  apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0})
    (f := fun I => primaryIdealCharacter c χ I * f I)
  intro I hI
  change primaryIdealGenerator I ≠ 0
  intro hz
  apply hI
  change primaryIdealCharacter c χ I * f I = 0
  rw [primaryIdealCharacter_zero_of_bad c χ I hz, zero_mul]

theorem primaryIdealCharacter_ray_trivial (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (a : O)
    (ha : (3 * c : O) ∣ a - 1) :
    primaryIdealCharacter c χ (Ideal.span {a}) = 1 := by
  have h3 : (3 : O) ∣ a - 1 := (dvd_mul_right (3 : O) c).trans ha
  have hc : c ∣ a - 1 := (dvd_mul_left c (3 : O)).trans ha
  have hp := lambda_sq_dvd_three.trans h3
  have ha0 := Eisenstein.primary_ne_zero a hp
  have hq : Ideal.Quotient.mk (Ideal.span {c}) a = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hc)
  rw [primaryIdealCharacter_apply, primaryIdealGenerator_span a ha0 hp, hq, map_one]

theorem primaryIdealCharacter_mul (c : O)
    (χ ξ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    primaryIdealCharacter c (χ * ξ) = primaryIdealCharacter c χ * primaryIdealCharacter c ξ := by
  ext I
  rfl

def primaryResidueValue (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3 : O) ∣ Quotient.out r - 1 then χ r else 0

theorem primaryResidueValue_mk (c : O) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (x : O) :
    primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3 : O) ∣ x - 1 then χ (Ideal.Quotient.mk (Ideal.span {c}) x) else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x) - x :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))
  have hd := h3.trans hc
  have hp : (3 : O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x) - 1 ↔
      (3 : O) ∣ x - 1 := by
    constructor
    · intro h
      convert dvd_sub h hd using 1 ; ring
    · intro h
      convert dvd_add hd h using 1 ; ring
  simp only [primaryResidueValue, hp]

theorem primary_lattice_eq_ideal_sum (c : O) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : O, primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖ringComplex z‖ ^ 2 / X)) =
      ∑' I : GoodIdeal, primaryIdealCharacter c χ I.val *
        W ((Ideal.absNorm I.val : ℝ) / X) := by
  let f : O → ℂ := fun z => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖ringComplex z‖ ^ 2 / X)
  have hleft : (∑' z : O, primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖ringComplex z‖ ^ 2 / X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : O, ({z : O | (3 : O) ∣ z - 1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [primaryResidueValue_mk c h3 χ z]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, f]
        split_ifs <;> simp only [zero_mul]
      _ = _ := (tsum_subtype {z : O | (3 : O) ∣ z - 1} f).symm
  rw [hleft, ← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator I.val)) *
      W (‖ringComplex (primaryIdealGenerator I.val)‖ ^ 2 / X) = _
  rw [primaryIdealGenerator_norm_sq I.val I.property]
  rfl

theorem primary_ideal_volume_error (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : GoodIdeal, primaryIdealCharacter c χ I.val *
          W ((Ideal.absNorm I.val : ℝ) / X)) -
      (X / ‖ringComplex c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) *
          SchwartzPlanePoisson.paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) *
        InversePrincipalEnergy.pvControl W := by
  rw [← primary_lattice_eq_ideal_sum c h3 χ W X]
  exact CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (primaryResidueValue c χ)

theorem primary_ideal_volume_error_all (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O, primaryIdealCharacter c χ I *
          W ((Ideal.absNorm I : ℝ) / X)) -
      (X / ‖ringComplex c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) *
          SchwartzPlanePoisson.paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) *
        InversePrincipalEnergy.pvControl W := by
  rw [← tsum_primaryIdealCharacter_all c χ (fun I => W ((Ideal.absNorm I : ℝ) / X))]
  exact primary_ideal_volume_error c hc h3 χ W X hX

end CenteredMomentPrimary
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => Eisenstein.O
namespace CenteredMomentMask
open Eisenstein CompletedGauss
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, if_neg hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

theorem masked_ideal_sum_eq (R : Ideal O) (hR : R ≠ 0)
    (f : Ideal O → ℂ) (hf : Summable f) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) * f I) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * ∑' J : Ideal O, f (D * J) := by
  have hterm (I : Ideal O) : (if IsCoprime I R then (1 : ℂ) else 0) * f I =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * (if D ∣ I then f I else 0) := by
    rw [ideal_coprime_mobius I R hR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    by_cases h : D ∣ I <;> simp only [h, ite_true, ite_false, zero_mul, mul_zero]
  have hsum (D : Ideal O) :
      Summable (fun I : Ideal O => (moebius D : ℂ) * (if D ∣ I then f I else 0)) := by
    have h := (hf.indicator {I : Ideal O | D ∣ I}).mul_left (moebius D : ℂ)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using h
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun D _ => hsum D)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [tsum_mul_left, tsum_ideal_divisible D (ne_zero_of_dvd_ne_zero hR
    ((mem_idealDivisors hR).mp hD))]

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOf_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

theorem masked_plain_ideal_sum (R : Ideal O) (hR : R ≠ 0)
    (χ : Ideal O →* ℂ) (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (χ I * W ((Ideal.absNorm I : ℝ) / X))) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * χ D *
        ∑' J : Ideal O, χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D)) := by
  rw [masked_ideal_sum_eq R hR _ (annular_ideal_sum_summable χ W b X hX hs)]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  have hnD : (Ideal.absNorm D : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm D ≠ 0 by
      intro hz
      exact hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hterms (J : Ideal O) :
      χ (D * J) * W ((Ideal.absNorm (D * J) : ℝ) / X) =
        χ D * (χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D))) := by
    rw [map_mul, map_mul, Nat.cast_mul]
    have harg : (Ideal.absNorm D : ℝ) * Ideal.absNorm J / X =
        (Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D) := by field_simp
    rw [harg]
    ring
  simp_rw [hterms]
  rw [tsum_mul_left]
  ring

theorem polynomial_mask_divisor_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ((idealDivisors R).card : ℝ) ≤ C * Z ^ ε := by
  let δ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hcount⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm
  have hexp : B * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm R : ℝ) ^ δ := hcount R hR
    _ ≤ C * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnorm hδ.le) hC.le
    _ = C * Z ^ (B * δ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexp) hC.le

end CenteredMomentMask
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => Eisenstein.O
namespace CenteredMomentMaskedVolume
open Eisenstein  SchwartzPlanePoisson
open CompletedGauss UniqueFactorizationMonoid InversePrincipalEnergy
open CenteredMomentPrimary CenteredMomentMask

theorem masked_primary_ideal_volume_error
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryIdealCharacter c χ
    let v := (1 / (‖ringComplex c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryIdealCharacter c χ
  let v := (1 / (‖ringComplex c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) * paperRadialFourier W 0)
  let B := (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (pvControl_nonneg W)
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := primary_ideal_volume_error_all c hc h3 χ W
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryIdealCharacter_norm_le_one c hc χ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end CenteredMomentMaskedVolume
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentCancellation
open Eisenstein  SchwartzPlanePoisson
open CompletedGauss UniqueFactorizationMonoid InversePrincipalEnergy
open CenteredMomentPrimary CenteredMomentMaskedVolume

def maskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (primaryIdealCharacter c χ I * W ((Ideal.absNorm I : ℝ) / X))

def maskedDensity (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) : ℂ :=
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D : ℂ) * primaryIdealCharacter c χ D /
    (Ideal.absNorm D : ℂ)) * (1 / (‖ringComplex c‖ ^ 2 : ℂ)) *
      ∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r

def maskedError (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hc)
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  ((idealDivisors R).card : ℝ) *
    ((∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W)

lemma maskedError_nonneg (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : 0 ≤ maskedError c hc χ R W := by
  unfold maskedError
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (pvControl_nonneg W))

theorem maskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    ‖maskedSum c χ R W X - (X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier W 0)‖ ≤ maskedError c hc χ R W := by
  have h := masked_primary_ideal_volume_error c hc h3 χ R hR W b X hX hs
  convert h using 1
  unfold maskedSum maskedDensity
  congr 1
  ring
  all_goals rfl

theorem masked_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : 𝓢(ℝ, ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
    let C := ‖maskedDensity c hc χ R * paperRadialFourier W₁ 0‖ +
      ‖maskedDensity c hc χ R * paperRadialFourier W₂ 0‖ + E
    ‖maskedSum c χ R W₁ X₁ * maskedSum c χ R W₂ X₂ -
      maskedSum c χ R W₁ Y₁ * maskedSum c χ R W₂ Y₂‖ ≤ 4 * E * C * (T / L) := by
  let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
  let v₁ := maskedDensity c hc χ R * paperRadialFourier W₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier W₂ 0
  let C := ‖v₁‖ + ‖v₂‖ + E
  have hE₁ := maskedError_nonneg c hc χ R W₁
  have hE₂ := maskedError_nonneg c hc χ R W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE
  have hL0 : 0 < L := by linarith
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₁ X - (X : ℂ) * v₁‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₁ b₁ X (lt_of_lt_of_le hL0 hX) hs₁).trans
      (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X - (X : ℂ) * v₂‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₂ b₂ X (lt_of_lt_of_le hL0 hX) hs₂).trans
      (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X : ℂ) * v₁‖ ≤ C * X := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg v₂]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X‖ ≤ C * X := by
    have hb := norm_le_norm_sub_add (maskedSum c χ R W₂ X) ((X : ℂ) * v₂)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E * X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    dsimp only [C]
    nlinarith [mul_nonneg (norm_nonneg v₁) (le_trans hL0.le hX)]
  have hmain : ((X₁ : ℂ) * v₁) * ((X₂ : ℂ) * v₂) =
      ((Y₁ : ℂ) * v₁) * ((Y₂ : ℂ) * v₂) := by
    have hp : (X₁ : ℂ) * X₂ = (Y₁ : ℂ) * Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁ : ℂ) * X₂) * (v₁ * v₂) := by ring
      _ = ((Y₁ : ℂ) * Y₂) * (v₁ * v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end CenteredMomentCancellation
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentCounting
open CenteredMomentCancellation CenteredMomentPrimary
open InversePrincipalEnergy

theorem norm_tsum_ideal_ball (f : Ideal O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOf_absNorm_le (S := O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal O, f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := EisensteinLatticeCount.finite_ideal_count_real S H hH1
      (fun J hJ hz => (hmem J).mp hJ (hz ▸ hzero))
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

theorem masked_coefficient_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R I : Ideal O) :
    ‖(if IsCoprime I R then (1 : ℂ) else 0) * primaryIdealCharacter c χ I‖ ≤ 1 := by
  split_ifs
  · simpa only [one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [zero_mul, norm_zero, zero_le_one]

theorem maskedSum_absolute (c : O) (hc : c ≠ 0)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O)
    (W : ℝ → ℂ) (b M X : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖maskedSum c χ R W X‖ ≤ (128 * b * M) * X := by
  have hzero : primaryIdealCharacter c χ (⊥ : Ideal O) = 0 := by
    apply primaryIdealCharacter_zero_of_bad
    exact map_zero primaryIdealGeneratorHom
  have h := norm_tsum_ideal_ball
    (fun I => (if IsCoprime I R then (1 : ℂ) else 0) *
      (primaryIdealCharacter c χ I * W ((Ideal.absNorm I : ℝ) / X)))
    (b * X) M (mul_nonneg hb hX.le) hM
    (by simp only [hzero, zero_mul, mul_zero])
    (by
      intro I
      rw [← mul_assoc, norm_mul]
      exact (mul_le_mul (masked_coefficient_norm_le_one c hc χ R I)
        (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by
      intro I hI
      have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
        intro hz
        exact hI (by simp only [hz, mul_zero])
      exact (div_le_iff₀ hX).mp (hs hw))
  change ‖maskedSum c χ R W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem norm_linear_coefficient_le (S : ℝ → ℂ) (v : ℂ) (C E : ℝ) (hE : 0 ≤ E)
    (herror : ∀ X : ℝ, 0 < X → ‖S X - (X : ℂ) * v‖ ≤ E)
    (habsolute : ∀ X : ℝ, 0 < X → ‖S X‖ ≤ C * X) : ‖v‖ ≤ C := by
  by_contra hn
  have hδ : 0 < ‖v‖ - C := sub_pos.mpr (lt_of_not_ge hn)
  let X := (E + 1) / (‖v‖ - C)
  have hX : 0 < X := div_pos (by linarith) hδ
  have heq : X * (‖v‖ - C) = E + 1 := div_mul_cancel₀ _ hδ.ne'
  have h := norm_le_norm_sub_add ((X : ℂ) * v) (S X)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX.le, norm_sub_rev] at h
  have ha := habsolute X hX
  have hb := herror X hX
  nlinarith

end CenteredMomentCounting
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => Eisenstein.O
namespace CenteredMomentTwist
open Eisenstein SchwartzPlanePoisson
open CenteredMomentLattice CenteredMomentCancellation CenteredMomentCounting

def twistedMaskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (CenteredMomentPrimary.primaryIdealCharacter c χ I *
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I : ℝ) / X))

lemma normPowerProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerProfile W a b ha hs hW t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [normPowerProfile_apply, hz, mul_zero])

lemma normPowerProfile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    ‖normPowerProfile W a b ha hs hW t x‖ = ‖W x‖ := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply,
    CompletedHeight.normTwistedSource, norm_mul, kernelLogPhase_norm, one_mul]

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

theorem twistedMaskedSum_scale (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedMaskedSum c χ R W t X = (X : ℂ) ^ (Complex.I * t) *
      maskedSum c χ R (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedMaskedSum maskedSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedMaskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      maskedError c hc χ R (normPowerProfile W a b ha hs hW t) := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_volume c hc h3 χ R hR _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedMaskedSum_absolute (c : O) (hc : c ≠ 0)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_absolute c hc χ R _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_volumeCoefficient_norm_le (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => maskedSum c χ R V X)
    _ (128 * b * M) (maskedError c hc χ R V) (maskedError_nonneg c hc χ R V)
    (fun X hX => maskedSum_volume c hc h3 χ R hR V b X hX hV)
    (fun X hX => maskedSum_absolute c hc χ R V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem twisted_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      maskedError c hc χ R (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
      twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := maskedError c hc χ R V₁ + maskedError c hc χ R V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := maskedDensity c hc χ R * paperRadialFourier V₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := maskedError_nonneg c hc χ R V₁
  have hE₂ := maskedError_nonneg c hc χ R V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_volumeCoefficient_norm_le c hc h3 χ R hR W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute c hc χ R W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end CenteredMomentTwist
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
