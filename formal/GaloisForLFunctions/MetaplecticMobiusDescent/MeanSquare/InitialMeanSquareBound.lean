/-
The initial mean-square bound adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CuspBadPhases

/-!
# The initial mean-square bound

The retained radial inequality discharges the canonical density hypotheses for the initial
mask; retained sources have harmonic decay in their residual prime support, and the complete
retained sum gives `initial_mean_square_bound`.
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

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration
open CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The retained radial inequality discharges the canonical density hypotheses for the initial mask. -/
theorem retained_initial_fixed_density
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (ε : ℝ) (hε : 0 < ε) (A : ℝ) (hA : 0 ≤ A) :
    ∃d : ℕ,∀(V₁ V₂ : ℝ→ℂ),ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s| ≤ A) → (∀s,V₂ s≠0→|s| ≤ A) →
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ)
      (R : Finset (primePool (outsideSquarefreeIdeals S D)))
      (negative₁ negative₂ : Bool) (r₁ s₁ r₂ s₂ : QuadraticRayRing)
      (j : SecondLogIndex) (T : Finset (Ideal O×O)) (σ θ : ℝ),
      Z₀ ≤ Z → Real.exp (radiusIter A 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      θ ≤ σ-(1:ℝ)/20 → initialRadial Z (Z^(1+σ))
        (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) R) j ≤ Z^θ →
      (∀t∈T,t.1≠0 ∧ Squarefree t.1 ∧ IsCoprime t.1 (∏P∈S,P) ∧
        (Ideal.absNorm t.1:ℝ) ≤ initialLogLabel j ∧ t.2≠0 ∧
        ‖ringComplex t.2‖^2 ≤ secondLogK j*Real.exp 2) →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      let X:=initialLogColumn Z (primeProductNorm (poolPrimary P) R) j
      densityChildEnergy (poolPrimary P) (poolPrimary_good P hP)
        (combinedFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative₁ r₁ s₁ (fun _=>1))
        (combinedFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative₂ r₂ s₂ (fun _=>1))
        Finset.univ Ψ Ψ (∏i∈R,poolPrimary P i) T V₁ V₂ X X (2*d) ≤ 
        C*Z^ε*(X*initialLogLabel j)^2 := by
  obtain ⟨d,hd⟩:=outsideCanonicalDensity_fixed_residues_small_power S hSp hbad base hbase
    Qbase h4 c hc hspan hsupport hperiod ε hε A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hV₁ hV₂ hs₁ hs₂
  obtain ⟨C,Z₁,hC,hZ₁,hbound⟩:=hd V₁ V₂ hV₁ hV₂ hs₁ hs₂
  refine ⟨C,max Z₁ (Real.exp 2),hC,hZ₁.trans (le_max_left _ _),?_⟩
  intro D Z Ψ R negative₁ negative₂ r₁ s₁ r₂ s₂ j T σ θ hZ hD hΨ hmargin hrad hT
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hZold : Z₁ ≤ Z:=(le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z:=hZ₁.trans hZold
  have hexp : Real.exp 2 ≤ Z:=(le_max_right _ _).trans hZ
  have hgeom:=initial_retained_geometry Z (primeProductNorm p R) 1 σ θ 0 j hZ1 hexp
    (primeProductNorm_ge_one p hp R) (by norm_num) (by simp only [Real.rpow_zero,le_refl])
    (by simpa only [zero_add] using hmargin) hrad
  have hm : (∏i∈R,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hinv : (secondLogK j*Real.exp 2)*‖ringComplex (∏i∈R,p i)‖^2 ≤ 
      initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j*Z^(-(1:ℝ)/20) := by
    simpa only [one_mul,primeProductNorm] using hgeom.2.2.2.2
  exact hbound D Z Ψ Ψ (∏i∈R,p i) negative₁ negative₂ r₁ s₁ r₂ s₂ T
    (initialLogColumn Z (primeProductNorm p R) j) (initialLogLabel j) (secondLogK j*Real.exp 2)
    hZold hD hΨ hΨ hm hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hinv hT

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration
open CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The initial source in a retained bin has harmonic decay in its residual prime support. -/
theorem retained_initial_fixed_source
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (hgA : ∀u,g u≠0→|u| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ)
      (R : Finset (primePool (outsideSquarefreeIdeals S D)))
      (negative : Bool) (r : QuadraticRayRing) (ray a b : QuadraticRayRing×QuadraticRayRing)
      (j : SecondLogIndex) (s : Finset (SecondExpansionData (primePool (outsideSquarefreeIdeals S D))))
      (σ θ : ℝ),
      Z₀ ≤ Z → Real.exp (radiusIter (A+2+1) 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      θ ≤ σ-(1:ℝ)/20 →
      (∀x∈s,InSourceSector R x) → (∀x∈s,x.frequency≠0) →
      (∀x∈s,initialLogIndex (poolPrimary (outsideSquarefreeIdeals S D)) x=j) →
      initialRadial Z (Z^(1+σ)) (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) R) j ≤ Z^θ →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      (1+initialRadial Z (Z^(1+σ)) (primeProductNorm (poolPrimary P) R) j)^N*
        ‖∑x∈s,secondFixedExpansionTerm (poolPrimary P) (poolPrimary_good P hP) Finset.univ Ψ 1 1 1
          (normalizedColumn (poolPrimary P) (fun T=>g (columnLog (poolPrimary P) Z T))) W (Z^(1+σ))
          negative r ray a b x‖ ≤ 
        C*Z^(1+σ)/primeProductNorm (poolPrimary P) R*‖rayQuadraticPair ray.1 ray.2‖*
          (initialLogLabel j)^ε*Z^ε := by
  obtain ⟨d,hd⟩:=retained_initial_fixed_density S hSp hbad base hbase Qbase h4 c hc hspan hsupport
    hperiod ε hε (A+2+1) (by linarith)
  obtain ⟨windows,Ct,hCt,hwc,hws,hwb,ht⟩:=initial_sector_density_bound g W A hA hgA ε hε N (2*d)
  obtain ⟨Ce,Z₀,hCe,hZ₀,he⟩:=hd (windows 5) (windows 6) (hws 5) (hws 6) (hwb 5) (hwb 6)
  refine ⟨(Ct+1)*Ce*Real.exp 4,Z₀,by positivity,hZ₀,?_⟩
  intro D Z Ψ R negative r ray a b j s σ θ hZ hD hΨ hmargin hs hk hj hrad
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hinj : Function.Injective (fun i=>Ideal.span {p i}):=by
    intro i k hh
    apply Subtype.ext
    simpa only [p,poolPrimary_span P hP] using hh
  have hpr : ∀i,lambda^2∣p i-1:=fun i=>(primaryIdealPrime_spec i.val (hp i)).2.2.2
  have hZ1 : 1 ≤ Z:=hZ₀.trans hZ
  have hZp : 0 < Z:=zero_lt_one.trans_le hZ1
  have hHp : 0 < Z^(1+σ):=Real.rpow_pos_of_pos hZp _
  have hBp:=primeProductNorm_pos p hp R
  let X:=initialLogColumn Z (primeProductNorm p R) j
  let T:=initialSourceTargets p s
  have htarget:=initial_source_target_geometry p hp (∏P∈S,P)
    (outside_pool_coprime_excluded S D hbad hSp) s j hk hj
  have hcoords (x : SecondExpansionData (primePool P)) (hx : x∈initialSquarefreeSector p s) := by
    have hxs:=(Finset.mem_filter.mp hx).1
    have hh:=initial_log_coordinates p hp Z hZp R x (hs x hxs) (hk x hxs)
    dsimp only at hh
    rw [hj x hxs] at hh
    exact hh
  have hdensity:=he D Z Ψ R negative negative b.1 a.1 b.2 a.2 j T σ θ hZ hD hΨ hmargin hrad htarget
  have hsource:=ht p hp (poolPrimary_good P hP) hinj hpr Finset.univ R
    (initialSquarefreeSector p s) T Ψ 1 Z (Z^(1+σ)) (secondLogE j) (secondLogV j) X
    (secondLogK j) (initialLogLabel j) negative r ray a b hZp hHp
    (normLogScale_pos _) (normLogScale_pos _) (initialLogColumn_pos _ _ _ hZp hBp)
    (normLogScale_pos _) (by unfold initialLogLabel secondLogE secondLogV normLogScale; positivity)
    (hΨ.norm_le hbase) (fun x hx=>hs x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hk x (Finset.mem_filter.mp hx).1)
    (fun x hx=>(hcoords x hx).1) (fun x hx=>(hcoords x hx).2.1)
    (fun x hx=>(hcoords x hx).2.2.1) (fun x hx=>(hcoords x hx).2.2.2)
    (fun x hx=>Finset.mem_image_of_mem _ hx) (fun t ht=>(htarget t ht).1)
    (fun t ht=>(htarget t ht).2.2.2.1)
  dsimp only [X] at hsource
  rw [initial_log_radial Z (Z^(1+σ)) _ hZp.ne' hBp.ne' j] at hsource
  simp only [one_mul] at hsource
  rw [initial_fixed_source_squarefree p (poolPrimary_good P hP) hinj Finset.univ Ψ 1
    (normalizedColumn p (fun T=>g (columnLog p Z T))) W (Z^(1+σ)) negative r ray a b s
    (fun x hx=>(hs x hx).1)]
  have hL : 0 ≤ initialLogLabel j:=by unfold initialLogLabel secondLogE secondLogV normLogScale; positivity
  have hf : 0 ≤ Ct*Z^(1+σ)*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*(initialLogLabel j)^ε:=by positivity
  refine hsource.trans ((mul_le_mul_of_nonneg_left hdensity hf).trans ?_)
  have heq : (Real.exp (2:ℝ))^2=Real.exp 4:=by rw [pow_two,←Real.exp_add]; norm_num
  rw [initial_log_mass Z _ hBp.ne' j]
  calc
    _=Ct*Ce*Real.exp 4*Z^(1+σ)/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*
        (initialLogLabel j)^ε*Z^ε:=by rw [mul_pow,div_pow,heq]; field_simp <;> ring
    _ ≤ ((Ct+1)*Ce*Real.exp 4)*Z^(1+σ)/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*
        (initialLogLabel j)^ε*Z^ε:=by gcongr; linarith

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration
open CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The complete retained source sum has arbitrarily small loss over the row length. -/
theorem retained_initial_source_sum
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S) [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (g W : 𝓢(ℝ,ℂ)) (A Ccap ε : ℝ) (hA : 0 ≤ A) (hcap : 1 ≤ Ccap)
    (hgA : ∀u,g u≠0→|u| ≤ A) (hε : 0 < ε) :
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ)
      (K : Finset (primePool (outsideSquarefreeIdeals S D))→
        Finset (primePool (outsideSquarefreeIdeals S D))→Finset O)
      (Kmax σ θ : ℝ) (negative : Bool) (r : QuadraticRayRing)
      (a b : QuadraticRayRing×QuadraticRayRing),
      Z₀ ≤ Z → Real.exp (radiusIter (A+2+1) 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      0 < Kmax → Z*Real.exp A ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 → θ ≤ σ-(1:ℝ)/20 →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      (∑ray : QuadraticRayRing×QuadraticRayRing,
        ∑R∈boundedPrimeSupports (poolPrimary P) Finset.univ (Z*Real.exp A),
        ∑j∈secondLogBinBox (Z*Real.exp A) Kmax,
          if initialRadial Z (Z^(1+σ)) (primeProductNorm (poolPrimary P) R) j ≤ Z^θ then
            ‖∑x∈initialLogSector (poolPrimary P) Finset.univ R K Z A j,
              secondFixedExpansionTerm (poolPrimary P) (poolPrimary_good P hP) Finset.univ Ψ 1 1 1
                (normalizedColumn (poolPrimary P) (fun T=>g (columnLog (poolPrimary P) Z T))) W
                (Z^(1+σ)) negative r ray a b x‖ else 0) ≤ C*Z^(1+σ)*Z^ε := by
  let δ:=ε/52
  have hδ : 0 < δ:=by dsimp [δ]; positivity
  obtain ⟨Cb,Z₀,hCb,hZ₀,hbin⟩:=retained_initial_fixed_source S hSp hbad base hbase Qbase h4 c hc
    hspan hsupport hperiod g W A hA hgA δ hδ 0
  obtain ⟨Cl,hCl,hlog⟩:=initial_label_log_budget δ Ccap hδ hcap
  have hmass:=initialRayMass_nonneg
  let C0:=Cb*initialRayMass*Cl
  have hC0 : 0 ≤ C0:=by dsimp [C0]; positivity
  refine ⟨C0+1,Z₀,by linarith,hZ₀,?_⟩
  intro D Z Ψ K Kmax σ θ negative r a b hZ hD hΨ hK hUcap hKcap hmargin
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hinj : Function.Injective (fun i=>Ideal.span {p i}):=by
    intro i k hh
    apply Subtype.ext
    simpa only [p,poolPrimary_span P hP] using hh
  have hZ1 : 1 ≤ Z:=hZ₀.trans hZ
  have hZp:=zero_lt_one.trans_le hZ1
  let U:=Z*Real.exp A
  have hU : 1 ≤ U:=one_le_mul_of_one_le_of_one_le hZ1 (Real.one_le_exp hA)
  have hUp:=zero_lt_one.trans_le hU
  let H:=Z^(1+σ)
  let B:=Cb*H*(U^2*Real.exp 2)^δ*Z^δ
  have hB : 0 ≤ B:=by dsimp [B,H]; positivity
  let f:=fun (ray : QuadraticRayRing×QuadraticRayRing) (R : Finset (primePool P)) (j : SecondLogIndex)=>
    if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
      ‖∑x∈initialLogSector p Finset.univ R K Z A j,
        secondFixedExpansionTerm p (poolPrimary_good P hP) Finset.univ Ψ 1 1 1
          (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖ else 0
  have hpoint (ray : QuadraticRayRing×QuadraticRayRing) (R : Finset (primePool P))
      (hR : R∈boundedPrimeSupports p Finset.univ U) (j : SecondLogIndex)
      (hj : j∈secondLogBinBox U Kmax) : f ray R j ≤ B/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖ := by
    dsimp only [f]
    split_ifs with hrad
    · have hs:=initialLogSector_geometry p Finset.univ R K Z A j
      have hb:=hbin D Z Ψ R negative r ray a b j (initialLogSector p Finset.univ R K Z A j)
        σ θ hZ hD hΨ hmargin (fun x hx=>(hs x hx).1) (fun x hx=>(hs x hx).2.1)
        (fun x hx=>(hs x hx).2.2.1) hrad
      simp only [pow_zero,one_mul] at hb
      have hl:=Real.rpow_le_rpow (zero_le_one.trans (initialLogLabel_ge_one j))
        (initialLogLabel_cap U Kmax hU j hj) hδ.le
      calc
        _ ≤ Cb*H/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*(initialLogLabel j)^δ*Z^δ:=hb
        _ ≤ Cb*H/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*(U^2*Real.exp 2)^δ*Z^δ:=by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
          exact mul_le_mul_of_nonneg_left hl (by have hRp:=(primeProductNorm_pos p hp R).le; dsimp [H]; positivity)
        _= _:=by dsimp [B]; ring
    · have hRp:=(primeProductNorm_pos p hp R).le
      positivity
  have hsum:=initial_harmonic_aggregation p hinj Finset.univ U Kmax B hB f hpoint
  have hlogs:=hlog Z U Kmax hZ1 hUp hK hUcap hKcap
  have he : δ+51*δ=ε:=by dsimp [δ]; ring
  calc
    _ ≤ B*initialRayMass*((secondLogBinBox U Kmax).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)):=hsum
    _=(Cb*initialRayMass)*H*Z^δ*((U^2*Real.exp 2)^δ*((secondLogBinBox U Kmax).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ))):=by dsimp [B]; ring
    _ ≤ (Cb*initialRayMass)*H*Z^δ*(Cl*Z^(51*δ)):=mul_le_mul_of_nonneg_left hlogs (by dsimp [H]; positivity)
    _=C0*H*Z^ε:=by rw [←he,Real.rpow_add hZp]; dsimp [C0]; ring
    _ ≤ (C0+1)*H*Z^ε:=by gcongr; linarith

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The nonzero-frequency initial source is bounded by the row length with arbitrarily small loss. -/
theorem initial_truncated_source_bound
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S) [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (g W : 𝓢(ℝ,ℂ)) (A Ccap σ ε : ℝ) (hA : 0 ≤ A) (hcap : 1 ≤ Ccap)
    (hgA : ∀u,g u≠0→|u| ≤ A) (hσ : (1:ℝ)/20 < σ) (hε : 0 < ε) :
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ)
      (K : Finset (primePool (outsideSquarefreeIdeals S D))→
        Finset (primePool (outsideSquarefreeIdeals S D))→Finset O)
      (Kmax : ℝ) (negative : Bool) (r : QuadraticRayRing),
      Z₀ ≤ Z → Real.exp (radiusIter (A+2+1) 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      0 < Kmax → Z*Real.exp A ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (∀x∈initialSupportedPool (poolPrimary (outsideSquarefreeIdeals S D)) Finset.univ K Z A,
        elementNorm (sourceRow (poolPrimary (outsideSquarefreeIdeals S D)) x) ≤ Kmax) →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      ‖truncatedSecondSource (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_good P hP)
        Finset.univ Ψ 1 1 1
        (firstFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative r
          (normalizedColumn (poolPrimary P) (fun T=>g (columnLog (poolPrimary P) Z T))))
        W (Z^(1+σ)) (fun G E=>(K G E).erase 0)‖ ≤ C*Z^(1+σ)*Z^ε := by
  let θ:=(σ-(1:ℝ)/20)/2
  have hθ : 0 < θ:=by dsimp [θ]; linarith
  have hmargin : θ ≤ σ-(1:ℝ)/20:=by dsimp [θ]; linarith
  obtain ⟨Cr,Z₀,hCr,hZ₀,hret⟩:=retained_initial_source_sum S hSp hbad base hbase Qbase h4 c hc
    hspan hsupport hperiod g W A Ccap ε hA hcap hgA hε
  obtain ⟨Ch,hCh,hhigh⟩:=initial_high_radial_sum g W A Ccap θ 0 hA hcap hgA hθ
  let C0:=(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ)^2*(Cr+Ch)
  have hC0 : 0 ≤ C0:=by dsimp [C0]; positivity
  refine ⟨C0+1,Z₀,by linarith,hZ₀,?_⟩
  intro D Z Ψ K Kmax negative r hZ hD hΨ hK hUcap hKcap hrow
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  let hg:=poolPrimary_good P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hinj : Function.Injective (fun i=>Ideal.span {p i}):=by
    intro i k hh
    apply Subtype.ext
    simpa only [p,poolPrimary_span P hP] using hh
  have hpr : ∀i,lambda^2∣p i-1:=fun i=>(primaryIdealPrime_spec i.val (hp i)).2.2.2
  have hZ1 : 1 ≤ Z:=hZ₀.trans hZ
  have hZp:=zero_lt_one.trans_le hZ1
  let H:=Z^(1+σ)
  have hH1 : 1 ≤ H:=Real.one_le_rpow hZ1 (by linarith)
  have hHp:=zero_lt_one.trans_le hH1
  have hHZ : 1 ≤ H*Z^ε:=one_le_mul_of_one_le_of_one_le hH1 (Real.one_le_rpow hZ1 hε.le)
  let U:=Z*Real.exp A
  let f:=fun (ray a b : QuadraticRayRing×QuadraticRayRing) (R : Finset (primePool P)) (j : SecondLogIndex)=>
    ‖∑x∈initialLogSector p Finset.univ R K Z A j,
      secondFixedExpansionTerm p hg Finset.univ Ψ 1 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖
  have hfixed (a b : QuadraticRayRing×QuadraticRayRing) :
      (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p Finset.univ U,
        ∑j∈secondLogBinBox U Kmax,f ray a b R j) ≤ (Cr+Ch)*H*Z^ε := by
    have hlo:=hret D Z Ψ K Kmax σ θ negative r a b hZ hD hΨ hK hUcap hKcap hmargin
    have hhi:=hhigh p hp hg hinj hpr Finset.univ K Ψ Z H Kmax negative r a b
      hZ1 hHp hK (hΨ.norm_le hbase) hUcap hKcap
    simp only [neg_zero,Real.rpow_zero,mul_one] at hhi
    have he : (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p Finset.univ U,
        ∑j∈secondLogBinBox U Kmax,f ray a b R j)=
        (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p Finset.univ U,
          ∑j∈secondLogBinBox U Kmax,
            if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then f ray a b R j else 0)+
        (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p Finset.univ U,
          ∑j∈secondLogBinBox U Kmax,
            if Z^θ < initialRadial Z H (primeProductNorm p R) j then f ray a b R j else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ray hray
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro R hR
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ
      · rw [if_pos hlow,if_neg (not_lt_of_ge hlow),add_zero]
      · rw [if_neg hlow,if_pos (lt_of_not_ge hlow),zero_add]
    rw [he]
    exact (add_le_add hlo hhi).trans (by nlinarith only [mul_le_mul_of_nonneg_left hHZ hCh.le])
  let F:=fun ray a b : QuadraticRayRing×QuadraticRayRing=>
    ∑x∈secondExpansionPool Finset.univ (fun G E=>(K G E).erase 0),
      secondFixedExpansionTerm p hg Finset.univ Ψ 1 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x
  have hterm (ray a b : QuadraticRayRing×QuadraticRayRing) :
      ‖F ray a b‖ ≤ ∑R∈boundedPrimeSupports p Finset.univ U,∑j∈secondLogBinBox U Kmax,f ray a b R j := by
    dsimp only [F]
    rw [initial_fixed_source_eq_bins p hp hg Finset.univ K Ψ g W Z H A Kmax hZp hgA
      negative r ray a b hrow]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun R hR=>norm_sum_le _ _))
  rw [truncatedSecondSource_eq_fixed_residues p hg hp hinj (poolPrimary_odd P hP) hpr]
  change ‖∑ray : QuadraticRayRing×QuadraticRayRing,∑a : QuadraticRayRing×QuadraticRayRing,
    ∑b : QuadraticRayRing×QuadraticRayRing,F ray a b‖ ≤ (C0+1)*H*Z^ε
  calc
    _ ≤ ∑ray : QuadraticRayRing×QuadraticRayRing,∑a : QuadraticRayRing×QuadraticRayRing,
        ∑b : QuadraticRayRing×QuadraticRayRing,
          ∑R∈boundedPrimeSupports p Finset.univ U,∑j∈secondLogBinBox U Kmax,f ray a b R j := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ray hray
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b hb=>hterm ray a b))
    _=∑a : QuadraticRayRing×QuadraticRayRing,∑b : QuadraticRayRing×QuadraticRayRing,
        ∑ray : QuadraticRayRing×QuadraticRayRing,
          ∑R∈boundedPrimeSupports p Finset.univ U,∑j∈secondLogBinBox U Kmax,f ray a b R j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ ≤ ∑_a : QuadraticRayRing×QuadraticRayRing,∑_b : QuadraticRayRing×QuadraticRayRing,(Cr+Ch)*H*Z^ε:=
      Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>hfixed a b))
    _=C0*H*Z^ε:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [C0]; ring
    _ ≤ _:=by gcongr; linarith

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The exact Poisson decomposition bounds the mean square by its three frequency pieces. -/
theorem initial_mean_square_triangle
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O→*ℂ) (col : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
    (H : ℝ) (hH : 0 < H) (K : Finset ι→Finset ι→Finset O) :
    ‖∑'z : O,W (‖ringComplex z‖^2/H)*
      (‖inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ 1 1 1 col z‖^2:ℝ)‖ ≤ 
      (‖truncatedSecondSource p hp hg pool Ψ 1 1 1 col W H (fun G E=>(K G E).erase 0)‖+
        ‖truncatedSecondZero p hg pool Ψ 1 1 1 col W H K‖)+
        ‖secondSourceTail p hp hg pool Ψ 1 1 1 col W H K‖ := by
  rw [inputConjugateRow_eq_truncated_add_tail p hp hg hinj pool Ψ 1 1 1 col W H hH K,
    truncatedSecondSource_eq_nonzero_add_zero p hg hp pool Ψ 1 1 1 col W H K]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- The complete initial mean square, including the zero frequency and complementary lattice tail. -/
theorem initial_fixed_mean_square_bound
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S) [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (g W : 𝓢(ℝ,ℂ)) (A σ ε : ℝ) (hA : 0 ≤ A)
    (hgA : ∀u,g u≠0→|u| ≤ A) (hσ : (1:ℝ)/20 < σ) (hε : 0 < ε) :
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ)
      (negative : Bool) (r : QuadraticRayRing),
      Z₀ ≤ Z → Real.exp (radiusIter (A+2+1) 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      ‖∑'z : O,W (‖ringComplex z‖^2/(Z^(1+σ)))*
        (‖inputConjugateRow (poolPrimary P) (fun i=>complexSexticChar (Ideal.span {poolPrimary P i})
          (poolPrimary_good P hP i)) Finset.univ Ψ 1 1 1
          (firstFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative r
            (normalizedColumn (poolPrimary P) (fun T=>g (columnLog (poolPrimary P) Z T)))) z‖^2:ℝ)‖ ≤ 
        C*Z^(1+σ)*Z^ε := by
  have hcap : 1 ≤ Real.exp (4*A):=Real.one_le_exp (by linarith)
  obtain ⟨Ct,Z₀,hCt,hZ₀,htrunc⟩:=initial_truncated_source_bound S hSp hbad base hbase Qbase h4 c hc
    hspan hsupport hperiod g W A (Real.exp (4*A)) σ ε hA hcap hgA hσ hε
  obtain ⟨Cz,hCz,hzero⟩:=initial_zero_frequency_bound g W A hgA
  obtain ⟨Ce,hCe,htail⟩:=initial_source_tail_bound g W A hA hgA
  refine ⟨Ct+Cz+Ce,Z₀,by positivity,hZ₀,?_⟩
  intro D Z Ψ negative r hZ hD hΨ
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  let hg:=poolPrimary_good P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hinj : Function.Injective (fun i=>Ideal.span {p i}):=by
    intro i k hh
    apply Subtype.ext
    simpa only [p,poolPrimary_span P hP] using hh
  have hZ1 : 1 ≤ Z:=hZ₀.trans hZ
  have hZp:=zero_lt_one.trans_le hZ1
  let H:=Z^(1+σ)
  have hH : 1 ≤ H:=Real.one_le_rpow hZ1 (by linarith)
  have hHp:=zero_lt_one.trans_le hH
  have hεpow : 1 ≤ Z^ε:=Real.one_le_rpow hZ1 hε.le
  let K:=fun _ _ : Finset (primePool P)=>initialFrequencyCutoff A Z H
  let col:=firstFixedColumn p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T)))
  have hcaps:=initial_polynomial_caps A Z hA hZ1
  have hrow:=initial_frequency_cutoff_row_bound p hp Finset.univ A Z H hA hZ1 hH
  have ht:=htrunc D Z Ψ K (initialRowCutoff A Z) negative r hZ hD hΨ hcaps.2.1
    hcaps.2.2 le_rfl hrow
  have hz:=hzero p hp hg hinj Finset.univ Ψ Z H negative r hZp hHp.le (hΨ.norm_le hbase)
  have he:=htail p hp hg hinj Finset.univ Ψ Z H negative r hZ1 hH (hΨ.norm_le hbase)
  calc
    _ ≤ (‖truncatedSecondSource p hp hg Finset.univ Ψ 1 1 1 col W H (fun G E=>(K G E).erase 0)‖+
        ‖truncatedSecondZero p hg Finset.univ Ψ 1 1 1 col W H K‖)+
        ‖secondSourceTail p hp hg Finset.univ Ψ 1 1 1 col W H K‖:=
      initial_mean_square_triangle p hp hg hinj Finset.univ Ψ col W H hHp K
    _ ≤ (Ct*H*Z^ε+Cz*H)+Ce*H:=add_le_add (add_le_add ht hz) he
    _ ≤ (Ct+Cz+Ce)*H*Z^ε:=by
      have hz':=le_mul_of_one_le_right (mul_nonneg hCz.le hHp.le) hεpow
      have he':=le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεpow
      nlinarith only [hz',he']

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Initial unmasked rows satisfy the near-linear mean-square bound on every finite norm ball. -/
theorem initial_mean_square_bound
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖ ≤ 1)
    (Qbase : Ideal O) (h4 : Qbase ≤ Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S) [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (g : 𝓢(ℝ,ℂ)) (A σ ε : ℝ) (hA : 0 ≤ A)
    (hgA : ∀u,g u≠0→|u| ≤ A) (hσ : (1:ℝ)/20 < σ) (hε : 0 < ε) :
    ∃C Z₀ : ℝ,0 < C ∧ 1 ≤ Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ) (R : Finset O),
      Z₀ ≤ Z → Real.exp (radiusIter (A+2+1) 3000)*Z^3 ≤ D → IsBaseRayTwist base Ψ →
      (∀z∈R,‖ringComplex z‖^2 ≤ Z^(1+σ)) →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      (∑z∈R,‖inputConjugateRow (poolPrimary P)
        (fun i=>complexSexticChar (Ideal.span {poolPrimary P i}) (poolPrimary_good P hP i))
        Finset.univ Ψ 1 1 1 (normalizedColumn (poolPrimary P) (fun T=>g (columnLog (poolPrimary P) Z T))) z‖^2) ≤ 
        C*Z^(1+σ)*Z^ε := by
  obtain ⟨Cf,Z₀,hCf,hZ₀,hfixed⟩:=initial_fixed_mean_square_bound S hSp hbad base hbase Qbase h4 c hc
    hspan hsupport hperiod g sieveCutoff A σ ε hA hgA hσ hε
  let C0:=(Fintype.card QuadraticRayRing:ℝ)^2*Cf
  have hC0 : 0 ≤ C0:=by dsimp [C0]; positivity
  refine ⟨C0+1,Z₀,by linarith,hZ₀,?_⟩
  intro D Z Ψ R hZ hD hΨ hR
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  let hg:=poolPrimary_good P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  have hpr : ∀i,lambda^2∣p i-1:=fun i=>(primaryIdealPrime_spec i.val (hp i)).2.2.2
  have hZp : 0 < Z:=zero_lt_one.trans_le (hZ₀.trans hZ)
  have hHp : 0 < Z^(1+σ):=Real.rpow_pos_of_pos hZp _
  let col:=normalizedColumn p (fun T=>g (columnLog p Z T))
  let row:=fun r : QuadraticRayRing=>inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
    Finset.univ Ψ 1 1 1 (firstFixedColumn p hg false r col)
  have hr (r : QuadraticRayRing) : (∑z∈R,‖row r z‖^2) ≤ Cf*Z^(1+σ)*Z^ε:=
    (initial_input_finite_majorant p hg Finset.univ Ψ (firstFixedColumn p hg false r col)
      (Z^(1+σ)) hHp R hR).trans (hfixed D Z Ψ false r hZ hD hΨ)
  calc
    _ ≤ ∑z∈R,(Fintype.card QuadraticRayRing:ℝ)*∑r : QuadraticRayRing,‖row r z‖^2:=
      Finset.sum_le_sum (fun z hz=>initial_row_residue_norm_sq p hg (poolPrimary_odd P hP) hpr
        Finset.univ Ψ col z)
    _=(Fintype.card QuadraticRayRing:ℝ)*∑r : QuadraticRayRing,∑z∈R,‖row r z‖^2:=by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card QuadraticRayRing:ℝ)*∑_r : QuadraticRayRing,Cf*Z^(1+σ)*Z^ε:=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _=>hr r)) (Nat.cast_nonneg _)
    _=C0*Z^(1+σ)*Z^ε:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [C0]; ring
    _ ≤ (C0+1)*Z^(1+σ)*Z^ε:=by gcongr; linarith

end InitialMeanSquare

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
