/-
Canonical long sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.MarkedReopenedCubeBins

/-!
# Canonical long sources

Fixed cusp shapes `FixedCuspShape`, marked short completed sums and tuple divisibility marks;
long filters, long coefficients and active local reflections.
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

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem marked_column_zero_of_subunit (Ψ : O→*ℂ) (W : ℝ→ℂ) (b Y : ℝ)
    (hY : 0<Y) (hW : ∀ t,W t≠0→t≤ b) (hsub : b*Y<1) (mark : Ideal O→ℂ) :
    (∑' I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I)=0 := by
  suffices hz : ∀ I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I=0 by
    simp only [hz,tsum_zero]
  intro I
  by_cases hI : I=0
  · simp only [hI,columnWeight_zero,zero_mul]
  have hw : W ((Ideal.absNorm I:ℝ)/Y)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hY).mp (hW _ hn)
    have hone := norm_at_least_one I hI
    linarith
  simp only [hw,mul_zero,zero_mul]

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)

theorem markedReopenedCubeBin_eq_active (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) :
    markedReopenedCubeBin S D
      ((outsideIdealsUpTo S D).image (cubeIndex (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ slots lists a =
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X<(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)^3 := by
    exact lt_of_not_ge (fun hh=>hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0<(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)^3)<1 := by
    rw [←mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [marked_column_zero_of_subunit _ W b _ (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem markedReopenedCubeBin_log_bins :
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a =
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

def markedShortCompletedSum (Ψrow : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) : ℂ :=
  ∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
      markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0

theorem original_marked_reopened_binned (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D) :
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
    markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a) +
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  rw [original_marked_split_to_bins S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [markedReopenedCubeBin_eq_active S D Ψ m f z W b X H₀ slots lists a hX hW,
    markedReopenedCubeBin_log_bins]
  rfl

theorem original_marked_binned_energy (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤ b) (hD : b*X≤ D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a))
    (fun j=>markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a)
  rw [←original_marked_reopened_binned S D Ψ m f z W b X H₀ slots lists a hbad hSp hWc hX hW hD] at hs
  have hn : ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 =
      X*‖(Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  simpa only [mul_assoc, mul_left_comm X 2] using mul_le_mul_of_nonneg_left hs hX.le

end
end InverseMoment

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation CompletedHeight
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem long_frequency_profile
    {ι:Type*}(p:ι→O)(hp:∀i,p i≠0)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤ A)
    (Z r ξ:ℝ)(hZ:0<Z)(T:Finset ι) :
    frequencyTwist V ξ (columnLog p (Z^r) T)=
      normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
        (primeProductNorm p T/Z^r) := by
  rw [normTwistedSource,radialFromLog_column p hp V (V.smooth ⊤) A hV _ (Real.rpow_pos_of_pos hZ r)]
  simp only [frequencyTwist_apply,columnLog]

theorem long_marked_source_eq
    {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(β:(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m f z:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤ A)(Z r ξ:ℝ)(hZ:0<Z) :
    varyingReopenedRow p hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (T∪v.support)*
        frequencyTwist V ξ (columnLog p (Z^r) T)) z =
    varyingReopenedRow p hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (v.support∪T)*
        normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
          (primeProductNorm p T/Z^r)) z := by
  congr 1
  funext v T
  rw [long_frequency_profile p hp V A hV Z r ξ hZ T,Finset.union_comm T v.support]

theorem marked_long_filter
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (weights:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights=
      markedReopenedCubeBin S D (progressingCubes S D H₀ Q) Ψ m f z W X H₀ slots lists weights := by
  unfold markedReopenedCubeBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hz:largeCubeCoefficient H₀ (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hv,(largeCubeCoefficient_support H₀ _ hh).2⟩)
  simp only [hz,zero_mul]

theorem long_cube_progress
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell:ℝ)(hZ:1<Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-1/Real.log Z≤ ell+V := by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨hv,hlower⟩:=Finset.mem_filter.mp hv
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:=Real.log_le_log (Real.rpow_pos_of_pos hz _) (hlower.trans (hupper v hv))
  rw [Real.log_rpow hz,Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz] at he
  have hlog:=Real.log_pos hZ
  have hd: (cutoff-ell-V)*Real.log Z≤1:=by nlinarith
  have hh:cutoff-ell-V≤1/Real.log Z:=(le_div_iff₀ hlog).mpr hd
  linarith

theorem long_cube_progress_with_slack
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell eta:ℝ)(hZ:1<Z)(hlog:1≤ eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-eta≤ ell+V := by
  have h:=long_cube_progress S D Q Z cutoff V ell hZ hne hupper
  have hh:1/Real.log Z≤ eta:=(div_le_iff₀ (Real.log_pos hZ)).mpr (by simpa only [mul_comm] using hlog)
  linarith

theorem short_sum_zero_of_label_large
    (Ψ:O→*ℂ)(W:ℝ→ℂ)(mark:Ideal O→ℂ)(X Z cutoff V:ℝ)
    (hZ:1≤ Z)(hV:cutoff≤ V) :
    markedShortCompletedSum Ψ W X (Z^(cutoff-V)) mark=0 := by
  have ht:Z^(cutoff-V)≤1:=by
    have he:=Real.rpow_le_rpow_of_exponent_le hZ (show cutoff-V≤0 by linarith)
    simpa only [Real.rpow_zero] using he
  unfold markedShortCompletedSum
  trans ∑' _ : Ideal O,(0:ℂ)
  · apply tsum_congr
    intro I
    by_cases hi:I=0
    · subst I
      simp
    rw [if_neg (not_lt.mpr (ht.trans (norm_at_least_one I hi)))]
  · exact tsum_zero

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers InverseInitialClippedColumns
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem child_ball_unit_mem (u:Oˣ)(R:ℝ)(k:O) :
    (u:O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    map_mul,norm_mul,norm_ringComplex_unit,one_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:Oˣ)(R:ℝ)(f:O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · intro x hx y hy he
    exact mul_left_cancel₀ u.ne_zero he
  · intro y hy
    refine ⟨((u⁻¹:Oˣ):O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    rw [←mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  · intros
    rfl

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(I:Ideal O)(hI:primaryIdealGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (cubicIdealGenerator I) (span_cubicIdealGenerator I) hI
  let P:O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:O):
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X‖^2=
      P (((u^4:Oˣ):O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  simp only [he]
  exact hrot.symm

theorem normalized_energy_le_actual_family
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryIdealGenerator I≠0)
    (weight:Ideal O→ℝ)(C:ℝ)(hC:0≤ C)(hw:∀I∈labels,0≤ weight I ∧ weight I≤ C)
    (W:ℝ→ℂ)(X Z F K:ℝ)(hZ:0<Z)(hK:0<K) :
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 K) weight W X Z F ≤
      Z^(-F)*C*rowFamilyEnergy labels (fun I k=>
        finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X) K := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  have he : (∑ I∈labels,weight I*(Z^(-F)*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator I) k slots lists a W X‖^2))=
      Z^(-F)*(∑ I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator I) k slots lists a W X‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  rw [canonical_ball_generator_energy p hg pool Ψ m I (hlabels I hI)]
  have hball:=finite_nonzero_row_energy_le_majorant
    (fun k=>finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X)
    (nonzeroChildFrequencyBall 1 K) K hK
    (by intro k hk
        rw [←ringComplex_norm_sq_eq_absNorm_span]
        simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).2)
    (by intro k hk hn
        have hh:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).1
        simp only [hn,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh)
  exact (mul_le_mul_of_nonneg_right (hw I hI).2 (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hball hC)

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers InverseInitialClippedColumns
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤ Z→V≤ L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤ Z^V→secondLabelWeight K I≤ C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤ eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤ C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤ C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤ C*Z^eps:=by gcongr

theorem normalized_second_energy_le_actual_family (K:ℕ)(L eps:ℝ)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (W:ℝ→ℂ)(X Z F V R:ℝ),1≤ Z→0<R→V≤ L→
      (∀I∈labels,(I.absNorm:ℝ)≤ Z^V)→
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W X Z F≤
        C*Z^(-F+eps)*rowFamilyEnergy labels (fun I k=>
          finiteCanonicalMarkedRow p hg pool Ψ m (cubicIdealGenerator I) k slots lists a W X) R := by
  obtain ⟨C,hC,hh⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg pool Ψ m slots lists a labels hlabels W X Z F V R hZ hR hV hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=normalized_energy_le_actual_family p hg pool Ψ m slots lists a labels
    (fun I hI=>((CanonicalQuadraticSieve.admissible_iff_native I).mp (hlabels I hI)).1)
    (secondLabelWeight K) (C*Z^eps) (by positivity)
    (fun I hI=>⟨by unfold secondLabelWeight;positivity,
      hh Z V hZ hV I (hlabels I hI).1 (hnorm I hI)⟩) W X Z F R hz hR
  convert hb using 1
  rw [Real.rpow_add hz]
  ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers InverseInitialClippedColumns
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem actual_marked_family_binned
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(hWc:HasCompactSupport W)
    (b X H₀ K:ℝ)(hX:0<X)(hK:0<K)(hW:∀t,W t≠0→t≤ b)(hD:b*X≤ D)
    (slots:Finset σ)(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    rowFamilyEnergy labels (fun I z=>outsideCanonicalMarkedRow S D hbad Ψ m
      (cubicIdealGenerator I) z slots lists a W X) K ≤
    2*X*(rowFamilyEnergy labels (fun I z=>
      markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a)) K+
      (cubeLogRange b X).card*∑j∈cubeLogRange b X,
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a) K) := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK]
  have he:∀I z,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (cubicIdealGenerator I) z slots lists a W X‖^2 ≤
      2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a‖^2) := by
    intro I z
    have hh:=original_marked_binned_energy S D Ψ m (cubicIdealGenerator I) z W b X H₀ slots lists a
      hbad hSp hWc hX hW hD
    have hs:(∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a‖^2)=
        ∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a‖^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [marked_long_filter S D (activeCubeLogBin S D b X j) Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a]
    rw [hs] at hh
    exact hh
  calc
    _≤∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
      (rowMajorant (‖ringComplex z‖^2/K)).re *
      (2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (he I z) (rowMajorant_nonneg _)
    _=_ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_left_comm _ _ _
      · simp_rw [Finset.sum_comm (s:=(firstFrequencyDisk (2*K)).erase 0) (t:=cubeLogRange b X)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open CanonicalRowCompletion SecondPassArithmetic

theorem actual_cube_bin_count (b L eps:ℝ)(hb:0≤ b)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀X Z:ℝ,0≤ X→1≤ Z→X≤ Z^L→
      ((cubeLogRange b X).card:ℝ)^2≤ C*Z^eps := by
  have hLp:0<L+1:=by linarith
  have hd:0<3*eps/(L+1):=by positivity
  obtain ⟨C,hC,hh⟩:=cubeLogRange_sq_small_power b (3*eps/(L+1)) hb hd
  refine ⟨C,hC,?_⟩
  intro X Z hX hZ hXL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hscale:(Z^((L+1)/3))^3=Z^(L+1) := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  have hpow:(Z^((L+1)/3))^(3*eps/(L+1))=Z^eps := by
    rw [←Real.rpow_mul hz.le]
    congr 1
    field_simp
  have hbnd:=hh X (Z^((L+1)/3)) hX (Real.one_le_rpow hZ (by positivity))
    (by rw [hscale];exact hXL.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
  simpa only [hpow] using hbnd

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

def actualLongCoefficient {ι:Type*}(p:ι→O)(Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)
    (I:Ideal O)(v:ι→₀ℕ) : ℂ :=
  separatedCubeCoefficient
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (cubicIdealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ v

theorem actualLongCoefficient_uniform (eps:ℝ)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}(p:ι→O)(_hp:∀i,p i≠0)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)
      (m:O)(H₀ B ξ:ℝ)(I:Ideal O)(v:ι→₀ℕ),0<B→
      B≤‖ringComplex (primeProduct p v.support v)‖^2→
      ‖ringComplex (primeProduct p v.support v)‖^2≤ Real.exp 1*B→
      ‖actualLongCoefficient p Ψ m H₀ B ξ I v‖≤ C*(Real.exp 1*B)^eps := by
  obtain ⟨C,hC,hbound⟩:=reopenedCubeCoefficient_small_power eps heps
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro ι p hp Ψ hΨ m H₀ B ξ I v hB hlo hhi
  have hne:Ideal.span {primeProduct p v.support v}≠0 := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i hi=>pow_ne_zero _ (hp i))
  rw [ringComplex_norm_sq_eq_absNorm_span] at hlo hhi
  have hh:=hbound H₀ (rowTwist Ψ m (cubicIdealGenerator I) 1)
    (rowTwist_norm Ψ hΨ m (cubicIdealGenerator I) 1) _ hne
  have hb:‖reopenedCubeCoefficient H₀ (rowTwist Ψ m (cubicIdealGenerator I) 1)
      (Ideal.span {primeProduct p v.support v})‖≤ C*(Real.exp 1*B)^eps :=
    hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi heps.le) hC.le)
  have hs:=separatedCubeCoefficient_bound
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (cubicIdealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ
    (C*(Real.exp 1*B)^eps) hB (by positivity) v hlo hhi hb
  unfold actualLongCoefficient
  convert hs using 1 ; ring

theorem actualLongCoefficient_complete
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)(I:Ideal O)
    (v:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ) :
    actualLongCoefficient (poolPrimary (CanonicalRowCompletion.outsideSquarefreeIdeals S D))
      Ψ (m*excludedGenerator S) H₀ B ξ I v=
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1)
        (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v := by
  simp only [actualLongCoefficient,cubeIdeal_eq_primeProduct_span _
    (CanonicalRowCompletion.outsideSquarefree_admissible S D hbad)]

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem actual_long_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤ Lcap)(hMmax:0≤ Mmax)(hb:0≤ b)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃Ccoef C Czero Ctail:ℝ,0<Ccoef ∧ 0≤ C ∧ 0≤ Czero ∧ 0≤ Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ Benergy:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hbinExp:Real.exp 1≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Lcap)(_hMcap:M≤ Mmax)(_hell:0≤ ell)(_hV:0≤ V)(_hr: -eta≤ r)
      (_hbZ:b≤ Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖ringComplex (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Real.exp 1*Z^ell)
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hB:0≤ Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (cubicIdealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Benergy*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(-saving) := by
  obtain ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=
    original_dyadic_full_energy om a b ha hs Lcap Mmax eta tau saving hcap hMmax hb heta heta1 htau htau1
  refine ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform eps heps
  obtain ⟨C,Czero,Ctail,hC,hCzero,hCtail,hfull⟩:=he eps heps J
  refine ⟨Ccoef,C,Czero,Ctail,hCcoef,hC,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ Benergy hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hΨ hB hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤ Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤ Ccoef*(Real.exp 1*Z^ell)^eps := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^eps) ξ Benergy hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hΨ (by positivity) hB hsf hn hβ hlabels hslots hweights hleft hright

end InverseMoment

end

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem actual_long_bin_normalized_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤ b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Z r cubeLength Vheight H₀ K E : ℝ) (d : ℕ)
    (hZ : 0 < Z) (hD : b*(Z^(r+3*cubeLength))≤ D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, (Z^cubeLength) ≤ (Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (CanonicalRowCompletion.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*(Z^cubeLength))
    (slots : Finset σ)
    (lists : σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ) :
    let F := CanonicalRowCompletion.outsideSquarefreeIdeals S D
    let hF := CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, Z^(-r-2*cubeLength-Vheight)*rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ) Ψ m (cubicIdealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    Z^(-Vheight)*rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (cubicIdealGenerator I) z W (Z^(r+3*cubeLength)) H₀ slots lists weights) K ≤
      E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β:=fun I v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hcancel:Z^(r+2*cubeLength+Vheight)*Z^(-r-2*cubeLength-Vheight)=1 := by
    rw [←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hpoint:∀ξ:ℝ,rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ Q (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ)
        Ψ m (cubicIdealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K≤
      (Z^(r+2*cubeLength+Vheight)*E)*(1+|ξ|)^(2*d) := by
    intro ξ
    have hh:=mul_le_mul_of_nonneg_left (hsource ξ) (Real.rpow_nonneg hZ.le (r+2*cubeLength+Vheight))
    rw [←mul_assoc,hcancel,one_mul] at hh
    simpa only [mul_assoc] using hh
  have hX:Z^(r+3*cubeLength)=(Z^cubeLength)^3*Z^r := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  have hbnd:=markedReopenedCubeBin_energy S D hbad hSp Q labels Ψ m W a b ha hb hs hW V hV
    (Z^cubeLength) (Z^r) (Z^(r+3*cubeLength)) H₀ K (Z^(r+2*cubeLength+Vheight)*E) d
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hX hD hK (by positivity)
    hn hn' slots lists weights hpoint
  have hc:Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight)=1 := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ,←Real.rpow_neg hZ.le,
      ←Real.rpow_add hZ,←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hh:=mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hZ.le (-Vheight))
  apply hh.trans_eq
  calc
    _=(Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight))*
      E*(∫ξ:ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by ring
    _=_:=by rw [hc,one_mul]

end
end InverseMoment

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers InverseInitialClippedColumns
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem normalized_complete_marked_split (K:ℕ)(L eps:ℝ)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤ Z→0<R→V≤ L→(∀I∈labels,(I.absNorm:ℝ)≤ Z^V)→
      (∀t,W t≠0→t≤ b)→b*Z^N≤ D→
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W (Z^N) Z (N+V)≤
      2*C*Z^(-V+eps)*(
        rowFamilyEnergy labels (fun I z=>markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W (Z^N) H₀
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)) R+
        (cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
          rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
            (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
            Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a) R) := by
  obtain ⟨C,hC,hh⟩:=normalized_second_energy_le_actual_family K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀
    hZ hR hV hnorm hW hD
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=hh (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels hlabels W
    (Z^N) Z (N+V) V R hZ hR hV hnorm
  have hsplit:=actual_marked_family_binned S D hbad hSp labels Ψ m W hWc
    b (Z^N) H₀ R (Real.rpow_pos_of_pos hz _) hR hW hD slots lists a
  have hcost: C*Z^(-(N+V)+eps)*(2*Z^N)=2*C*Z^(-V+eps) := by
    calc
      _=2*C*(Z^(-(N+V)+eps)*Z^N):=by ring
      _=2*C*Z^(-V+eps):=by rw [←Real.rpow_add hz];congr 2;ring
  apply hb.trans
  have he:=mul_le_mul_of_nonneg_left hsplit (show 0≤ C*Z^(-(N+V)+eps) by positivity)
  rw [←mul_assoc,hcost] at he
  exact he

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

 theorem actual_marked_bin_empty
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (he:¬(progressingCubes S D H₀ Q).Nonempty) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a=0 := by
  rw [marked_long_filter,Finset.not_nonempty_iff_eq_empty.mp he]
  simp only [markedReopenedCubeBin,Finset.sum_empty]

theorem actual_large_bins_aggregate
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(b X H₀ R Z V E:ℝ)
    (slots:Finset σ)(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (hbin:∀j∈cubeLogRange b X,
      (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty→
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a) R≤ E)
    (hE:0≤ E) :
    Z^(-V)*((cubeLogRange b X).card*∑j∈cubeLogRange b X,
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a) R)≤
      ((cubeLogRange b X).card:ℝ)^2*E := by
  have hj (j:ℕ)(hj:j∈cubeLogRange b X) :
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a) R≤ E := by
    by_cases hn:(progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · exact hbin j hj hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simpa only [markedReopenedCubeBin,Finset.sum_empty,rowFamilyEnergy,
        nonzeroRowMajorantSum,norm_zero,zero_pow (by decide:2≠0),Complex.ofReal_zero,
        mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hE
  calc
    _=(cubeLogRange b X).card*∑j∈cubeLogRange b X,
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (cubicIdealGenerator I) z W X H₀ slots lists a) R := by rw [←Finset.mul_sum];ring
    _≤(cubeLogRange b X).card*∑_j∈cubeLogRange b X,E := by
      gcongr
      exact hj _ ‹_›
    _=_ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem actual_complete_finite_split (K:ℕ)(L eps:ℝ)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤ Z → 0<R → V≤ L → (∀I∈labels,(I.absNorm:ℝ)≤ Z^V) →
      (∀t,W t≠0 → t≤ b) → b*Z^N≤ D →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (cubicIdealGenerator I) z slots lists a W (Z^N)‖^2) ≤
      2*(Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2))+
      2*C*Z^(-V+eps)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a) R := by
  obtain ⟨C,hC,hweight⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let bins:=cubeLogRange b (Z^N)
  let short:=fun I z=>markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z)
    W (Z^N) H₀ (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  let long:=fun j I z=>markedReopenedCubeBin S D
    (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
    Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a
  let ball:=nonzeroChildFrequencyBall 1 R
  have hpoint (I:Ideal O)(z:O):
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (cubicIdealGenerator I) z slots lists a W (Z^N)‖^2≤
      2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2) := by
    have hh:=original_marked_binned_energy S D Ψ m (cubicIdealGenerator I) z W b (Z^N) H₀ slots lists a
      hbad hSp hWc (Real.rpow_pos_of_pos hz _) hW hD
    convert hh using 1
    congr 2
    apply congrArg (fun x:ℝ=>(bins.card:ℝ)*x)
    apply Finset.sum_congr rfl
    intro j hj
    rw [marked_long_filter S D (activeCubeLogBin S D b (Z^N) j) Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a]
  have hlong (j:ℕ):
      (∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2)≤
      C*Z^eps*rowFamilyEnergy labels (long j) R := by
    rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hb:=finite_nonzero_row_energy_le_majorant (long j I) ball R hR
      (by intro z hz;rw [←ringComplex_norm_sq_eq_absNorm_span]
          simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).2)
      (by intro z hz he
          have hn:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).1
          simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hn)
    exact (mul_le_mul_of_nonneg_right (hweight Z V hZ hV I (hlabels I hI) (hnorm I hI))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hsum:=Finset.sum_le_sum (s:=labels) (fun I hI=>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=ball) (fun z hz=>hpoint I z))
      (show 0≤ secondLabelWeight K I by unfold secondLabelWeight;positivity))
  have he:=mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le (-(N+V)))
  have hc:Z^(-(N+V))*Z^N=Z^(-V):=by rw [←Real.rpow_add hz];congr 1;ring
  have rearrange:
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈ball,
        2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2))=
      2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)+
      2*Z^(-V)*bins.card*∑j∈bins,∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2 := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp_rw [Finset.sum_comm (s:=ball) (t:=bins)]
    rw [Finset.sum_comm (s:=labels) (t:=bins)]
    simp only [←Finset.mul_sum,mul_assoc,mul_left_comm]
    rw [←hc]
    ring
  rw [rearrange] at he
  apply he.trans
  have hj:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=bins) (fun j hj=>hlong j))
    (show 0≤2*Z^(-V)*(bins.card:ℝ) by positivity)
  rw [←Finset.mul_sum] at hj
  have hpow:Z^(-V)*Z^eps=Z^(-V+eps):=(Real.rpow_add hz _ _).symm
  convert add_le_add_left hj (2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)) using 1 <;>
    dsimp [bins,short,long,ball] <;> (try rw [←hpow]) <;> ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O"=>Eisenstein.O

theorem actual_complete_energy_from_live_bins (K:ℕ)(b L eps:ℝ)
    (hb:0≤ b)(hL:0≤ L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(Z N V R H₀ Eshort Elong:ℝ),
      1≤ Z → 0<R → N≤ L → V≤ L → (∀I∈labels,(I.absNorm:ℝ)≤ Z^V) →
      (∀t,W t≠0 → t≤ b) → b*Z^N≤ D → 0≤ Elong →
      Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2)≤ Eshort →
      (∀j∈cubeLogRange b (Z^N),
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a) R≤ Elong) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (cubicIdealGenerator I) z slots lists a W (Z^N)‖^2)≤
      2*Eshort+C*Z^eps*Elong := by
  obtain ⟨Cw,hCw,hw⟩:=actual_complete_finite_split K L (eps/2) hL (by positivity)
  obtain ⟨Cb,hCb,hbnd⟩:=actual_cube_bin_count b L (eps/2) hb hL (by positivity)
  refine ⟨2*Cw*Cb,by positivity,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc Z N V R H₀ Eshort Elong
    hZ hR hN hV hnorm hW hD hE hshort hlong
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:=hw S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have ha:=actual_large_bins_aggregate S D labels Ψ m W b (Z^N) H₀ R Z V Elong slots lists a hlong hE
  have hc:=hbnd (Z^N) Z (Real.rpow_nonneg hz.le _) hZ (Real.rpow_le_rpow_of_exponent_le hZ hN)
  have hh:Z^(eps/2)*Z^(eps/2)=Z^eps := by rw [←Real.rpow_add hz];congr 1;ring
  have hp:Z^(-V+eps/2)=Z^(-V)*Z^(eps/2):=Real.rpow_add hz _ _
  have ha':2*Cw*Z^(-V+eps/2)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
        Ψ m (cubicIdealGenerator I) z W (Z^N) H₀ slots lists a) R≤
      (2*Cw*Cb)*Z^eps*Elong := by
    have h1:=mul_le_mul_of_nonneg_left ha (show 0≤2*Cw*Z^(eps/2) by positivity)
    have h2:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE)
      (show 0≤2*Cw*Z^(eps/2) by positivity)
    have ht:=h1.trans h2
    simpa only [hp, ←hh, mul_assoc, mul_left_comm, mul_comm] using ht
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_left hshort (by norm_num:0≤(2:ℝ))) ha')

end InverseMoment

end

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CanonicalRowCompletion IdealDivisorBound
local notation "O" => Eisenstein.O

theorem markedShortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) :
    markedShortCompletedSum Ψ W X H₀ mark = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) := by
  unfold markedShortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => if_pos ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact if_neg hn

theorem marked_short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (mark : κ→Ideal O→ℂ) (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤ A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2)≤ A) :
    (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤
      A*((2*(1+diagonalControl sieveCutoff))*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤ lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
    rw [markedShortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤ A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤(2*(1+diagonalControl sieveCutoff))*(columnDyadicLength H₀+1:ℝ) :=
    (finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end
end InverseMoment

namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedHeight
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson
local notation "Eis"=>Eisenstein.O
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

theorem completed_tuple_mark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ)
    (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (hW:HasCompactSupport W)
    (X:ℝ) (hX:0<X) (H:Ideal Eis):
    markedCompletedT Ψ W X (fun A=>tupleDivisibilityMark lists w (H^3*A))=
      ∑p:∀i,lists i,(∏i,w i (p i))*markedCompletedT Ψ W X
        (fun A=>∏i,if (p i).val∣H^3*A then (1:ℂ) else 0) := by
  unfold tupleDivisibilityMark
  rw [markedCompletedT_finset_sum Finset.univ Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

theorem short_cube_exact_scale (Z N:ℝ) (hZ:1<Z) (H:Ideal Eis) (hH:H≠0):
    Z^(N-3*Real.logb Z (Ideal.absNorm H:ℝ))=Z^N/(Ideal.absNorm H:ℝ)^3 := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(Ideal.absNorm H:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hH (Ideal.absNorm_eq_zero_iff.mp hn))
  rw [Real.rpow_sub hz,show 3*Real.logb Z (Ideal.absNorm H:ℝ)=Real.logb Z (Ideal.absNorm H:ℝ)*3 by ring,
    show Z^(Real.logb Z (Ideal.absNorm H:ℝ)*3)=(Z^(Real.logb Z (Ideal.absNorm H:ℝ)))^3 from
      Real.rpow_mul_natCast hz.le _ 3,Real.rpow_logb hz (ne_of_gt hZ) hn]


end InverseMoment

namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedHeight SchwartzPlanePoisson.CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson
local notation "Eis"=>Eisenstein.O
universe v

theorem short_harmonic_small_power (L e:ℝ) (hL:0≤ L) (he:0<e):
    ∃C:ℝ,0<C ∧ ∀Z h:ℝ,1≤ Z → 0≤ h → h≤ L →
      ((2*(1+diagonalControl sieveCutoff))*(columnDyadicLength (Z^h)+1:ℝ))^2≤ C*Z^e := by
  have hdc := diagonalControl_nonneg sieveCutoff
  let a:=e/(2*(L+1))
  have ha:0<a:=by dsimp [a]; positivity
  let B:=(2*(1+diagonalControl sieveCutoff))*(2+1/(a*Real.log 2))
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have hB:0<B:=by dsimp [B]; positivity
  refine ⟨B^2,pow_pos hB _,?_⟩
  intro Z h hZ hh hhL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hZh:1≤ Z^h:=Real.one_le_rpow hZ hh
  have hb:=mul_le_mul_of_nonneg_left (columnDyadicLength_small_power a ha (Z^h) hZh)
    (by positivity:(0:ℝ)≤(2*(1+diagonalControl sieveCutoff)))
  have hs:((2*(1+diagonalControl sieveCutoff))*(columnDyadicLength (Z^h)+1:ℝ))^2≤ B^2*Z^(h*a*2):=by
    calc
      _≤(B*(Z^h)^a)^2:=pow_le_pow_left₀ (by positivity) (by simpa [B,mul_assoc] using hb) 2
      _=B^2*Z^(h*a*2):=by rw [mul_pow,←Real.rpow_mul hz.le,←Real.rpow_mul_natCast hz.le (h*a) 2]; norm_num
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have heq:a*(2*(L+1))=e:=by dsimp [a]; field_simp
  nlinarith


end InverseMoment

namespace InverseCanonicalShortAttachment
open Eisenstein CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InverseMoment CompletedHeight
open InverseInitialRayAttachment InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson
local notation "Eis" => Eisenstein.O
universe u v

def idealLists {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (j : σ) : Finset (Ideal Eis) :=
  (lists j).image Subtype.val

def transportCoeff {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (P : Ideal Eis) : ℂ :=
  if h:P∈primePool F then a j ⟨P,h⟩ else 0

@[simp] theorem transportCoeff_val {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (i : primePool F) :
    transportCoeff F a j i.val=a j i := by simp [transportCoeff]

def idealWeights {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (j : σ) (P : idealLists F lists j) : ℂ := transportCoeff F a j P.val

lemma tuple_mark_product {σ : Type u} [Fintype σ] [DecidableEq σ]
    (lists : σ→Finset (Ideal Eis)) (w : ∀j,lists j→ℂ) (A : Ideal Eis) :
    tupleDivisibilityMark lists w A=
      ∏j,∑P:lists j,if P.val∣A then w j P else 0 := by
  unfold tupleDivisibilityMark
  calc
    _ = ∑p:∀j,lists j,∏j,if (p j).val∣A then w j (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = _ := (Fintype.prod_sum (fun j (P : lists j)=>if P.val∣A then w j P else 0)).symm

theorem indexed_mark_eq_tuple {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (a : σ→primePool F→ℂ) (A : Ideal Eis) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a A=
      tupleDivisibilityMark (fun j:slots=>idealLists F lists j.val)
        (fun j:slots=>idealWeights F lists a j.val) A := by
  rw [tuple_mark_product]
  unfold indexedIdealMark
  rw [←Finset.prod_coe_sort slots]
  apply Finset.prod_congr rfl
  intro j hj
  change _ = ∑P:idealLists F lists j.val,if P.val∣A then transportCoeff F a j.val P.val else 0
  rw [Finset.sum_coe_sort (idealLists F lists j.val) (fun P : Ideal Eis=>if P∣A then transportCoeff F a j.val P else 0)]
  change (∑i∈lists j.val,if i.val∣A then a j.val i else 0)=
    ∑P∈(lists j.val).image Subtype.val,if P∣A then transportCoeff F a j.val P else 0
  rw [Finset.sum_image (fun i hi k hk h=>Subtype.ext h)]
  simp only [transportCoeff_val]

lemma idealLists_disjoint {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (h : (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k))) :
    Pairwise (fun j k:slots=>Disjoint (idealLists F lists j.val) (idealLists F lists k.val)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hP
  obtain ⟨i',hi',he'⟩:=Finset.mem_image.mp hQ
  have hii : i=i' := Subtype.ext (he.trans he'.symm)
  have hjk' : j.val≠k.val := fun he=>hjk (Subtype.ext he)
  exact Finset.disjoint_left.mp (h j.property k.property hjk') hi (hii.symm ▸ hi')

lemma idealLists_prime_data {σ : Type u} (F : Finset (Ideal Eis))
    (hF : ∀I∈F,quadraticIdealAdmissible I) (lists : σ→Finset (primePool F))
    (j : σ) (P : Ideal Eis) (hP : P∈idealLists F lists j) :
    P.IsMaximal ∧ lambda∉P ∧ Prime P ∧ ringChar (Eis⧸P)≠2 := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  refine ⟨inferInstance,poolGood F hF i,?_,poolOdd F hF i⟩
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

lemma idealLists_capacity {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (H : σ→ℝ)
    (hH : ∀j,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤ H j) :
    ∀j,∀P∈idealLists F lists j,(Ideal.absNorm P:ℝ)≤ H j := by
  intro j P hP
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  exact hH j i hi

lemma idealWeights_norm {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (ha : ∀j,∀i∈lists j,‖a j i‖≤1) :
    ∀j,∀P:idealLists F lists j,‖idealWeights F lists a j P‖≤1 := by
  intro j P
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp P.property
  change ‖transportCoeff F a j P.val‖≤1
  rw [←he,transportCoeff_val]
  exact ha j i hi


end InverseCanonicalShortAttachment

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
lemma integralComplexMatrix_apply (M : SL(2,Eis)) (i j : Fin 2) :
    integralComplexMatrix M i j = ringComplex (M i j) := rfl

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : rationalExtension
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:rationalExtension)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:rationalExtension):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group

def datum (h:((g:SL(2,Eis))*H) 1 0≠0) : SourceCuspDatum where
  gamma := g*s.gamma
  index := s.index
  lower_ne_zero := by
    rw [←map_mul,←s.removed_eq g,integralComplexMatrix_apply,
      upper_right_removed_bottom _ _ s.lower_zero,map_mul]
    exact mul_ne_zero (ringComplex_ne_zero h) (ringComplex_ne_zero s.lower_unit.ne_zero)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_point (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).point=
      ringComplex (((g:SL(2,Eis))*H) 0 0)/ringComplex (((g:SL(2,Eis))*H) 1 0) := by
  rw [SourceCuspDatum.point,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,
    upper_right_removed_top _ _ s.lower_zero,upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_mul]
  exact mul_div_mul_right _ _ (ringComplex_ne_zero s.lower_unit.ne_zero)

lemma datum_heightScale (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).heightScale=‖ringComplex (((g:SL(2,Eis))*H) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul,norm_mul]
  have hn:‖ringComplex (s.upper 1 1)‖=1 := by
    rcases s.lower_unit with ⟨u,hu⟩
    rw [←hu]
    exact norm_ringComplex_unit u
  rw [hn,mul_one]

lemma datum_dualPoint (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).dualPoint=
      ringComplex (s.upper 0 0*s.upper 0 1)-
        ringComplex (s.upper 0 0)^2*
          (ringComplex (((g:SL(2,Eis))*H) 1 1)/ringComplex (((g:SL(2,Eis))*H) 1 0)) := by
  rw [SourceCuspDatum.dualPoint,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,upper_right_removed_last,
    upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_add,map_neg,map_mul]
  have hd:ringComplex (s.upper 0 0)*ringComplex (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hc:=ringComplex_ne_zero h
  have ht:=ringComplex_ne_zero s.lower_unit.ne_zero
  field_simp [hc,ht]
  linear_combination (ringComplex (s.upper 0 0)*ringComplex (((g:SL(2,Eis))*H) 1 1)-
    ringComplex (((g:SL(2,Eis))*H) 1 0)*ringComplex (s.upper 0 1))*hd

lemma datum_multiplier (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).multiplier=
      -star (extendedComplexCharacter g)*star (extendedComplexCharacter s.gamma)*
        ringComplex (s.upper 0 0)^2/ringComplex (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [SourceCuspDatum.multiplier,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul]
  change -star (extendedComplexCharacter (g*s.gamma))/
    (ringComplex (((g:SL(2,Eis))*H) 1 0)*ringComplex (s.upper 1 1))^2=_
  rw [map_mul,star_mul]
  have hc:=ringComplex_ne_zero h
  have ht:=ringComplex_ne_zero s.lower_unit.ne_zero
  have hd:ringComplex (s.upper 0 0)*ringComplex (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hp:ringComplex (s.upper 0 0)^2*ringComplex (s.upper 1 1)^2=1 := by
    rw [←mul_pow,hd,one_pow]
  field_simp [hc,ht]
  linear_combination (star (extendedComplexCharacter g)*star (extendedComplexCharacter s.gamma))*hp

lemma datum_additive_phase (h:((g:SL(2,Eis))*H) 1 0≠0) (freq:ℂ) (scale:ℂ) :
    tracePhase (-freq*(s.datum g h).dualPoint/scale)=
      tracePhase (-freq*ringComplex (s.upper 0 0*s.upper 0 1)/scale)*
      tracePhase (freq*ringComplex (s.upper 0 0)^2*
        (ringComplex (((g:SL(2,Eis))*H) 1 1)/ringComplex (((g:SL(2,Eis))*H) 1 0))/scale) := by
  rw [s.datum_dualPoint]
  rw [show -freq*(ringComplex (s.upper 0 0*s.upper 0 1)-
      ringComplex (s.upper 0 0)^2*(ringComplex (((g:SL(2,Eis))*H) 1 1)/
        ringComplex (((g:SL(2,Eis))*H) 1 0)))/scale=
    -freq*ringComplex (s.upper 0 0*s.upper 0 1)/scale+
      freq*ringComplex (s.upper 0 0)^2*ringComplex (((g:SL(2,Eis))*H) 1 1)/
        ringComplex (((g:SL(2,Eis))*H) 1 0)/scale by ring]
  simp only [AddChar.map_add_eq_mul,mul_div_assoc]

end FixedCuspShape
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))

theorem localFourier_zeroMark (ψ : AddChar F ℂ) (h : F) :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

omit [Fintype F] in
theorem zeroMark_complement (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · simp [zeroMark, hx, MulChar.map_zero]
  · rw [zeroMark, if_neg hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    ring

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

theorem marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring

theorem marked_inactive_coefficient (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by
  rw [localFourier_zeroMark, mul_one]

end

end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
