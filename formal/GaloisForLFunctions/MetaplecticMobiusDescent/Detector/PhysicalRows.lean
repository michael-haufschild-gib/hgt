/-
Physical rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.MixedRightTransport
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.GaussianWindows
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorRawFibers

/-!
# Physical rows

Count parameters of the final assembly; selected slots and physical row indices, low outer
cutoffs and row weights; low calibration data and the low Mellin ratio of physical radial
rows.
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
open scoped Classical BigOperators ContDiff
open Set Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤ q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds (2*a-1) q hδ.le
  have hc' := hcount a ε (cutoff (2*a-1) q) T allowance Δ ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf B hq hmom
  have he : max (shortExponent (2*a-1) (q/(2*a-1)) (cutoff (2*a-1) q))
      (longExponent (2*a-1) (cutoff (2*a-1) q)) =
      Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1)) := by
    rw [cutoff_eq_balanced (2*a-1) q hδ hd hqb.1 hqb.2]
    exact HeckeDetectorRowCount.balanced_count_identity hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

theorem high_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1< U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff_eq_high (2*a-1) q ha]
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0< cB
  cB_one : cB≤1
  kB_pos : 0< kB
  cH_pos : 0< cH
  cH_one : cH≤1
  kH_pos : 0< kH
  balanced : ∃K₀ : ℝ,0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν)
  high : ∃K₀ : ℝ,0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1< U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ := balanced_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ := high_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB,kB,cH,kH,hcB,hcB1,hkB,hcH,hcH1,hkH,⟨KB,hKB,hbalanced⟩,⟨KH,hKH,hhigh⟩⟩⟩

end ProbeFinalAssembly

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted ProbeRow _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma gaussian_selected_tuple_sum {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→ Id) (Ψ : α→ O→*ℂ)
    (Z : ℝ) (hZ : 0< Z) (j : ℕ) (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0< q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
      ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hi (k : α) : Integrable (fun t : ℝ=> a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simpa only [mul_assoc] using (gaussian_selected_completed_integrable W (q k) _ S (D k) (Ψ k) _ (by positivity)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _=> hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := gaussian_selected_completed W V hV hsep S (D k) (Ψ k) Z hZ j (q k) (hq k hk)
  calc
    _ = a k*((∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) := by ring
    _ = a k*∫t : ℝ,correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
      (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i)))*
        gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=> by dsimp only; ring)

lemma gaussian_selected_scale {ι : Type*} [Fintype ι]
    (Z : ℝ) (P Q : ι→ℝ) (hP : ∀i,0< P i) :
    (Z*∏i,P i)*(∏i,Q i/P i)=Z*∏i,Q i := by
  rw [Finset.prod_div_distrib]
  have hp : (∏i,P i)≠0 := ne_of_gt (Finset.prod_pos (fun i _=> hP i))
  field_simp

theorem gaussian_selected_tuple_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤ M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤ C*R^(-A)) ∧
      (∀F : Finset α,∀a : α→ℂ,∀S : Finset Id,∀D : α→ Id,∀Ψ : α→ O→*ℂ,
        ∀Z : ℝ,0< Z→∀j : ℕ,∀q : α→ι→ℝ,(∀k∈F,∀i,0< q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
          (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
          ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
            (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_selected_slot_family W M hM hwindow
  exact ⟨V,hV,hbound,fun F a S D Ψ Z hZ j q hq=>
    gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq⟩

lemma gaussianFixedWindow_twist_compact (t : ℝ) :
    HasCompactSupport (CompletedHeight.normTwistedSource gaussianFixedWindow t) := by
  exact gaussianFixedWindow_compact.mul_left

lemma correctedGaussian_dyadic_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0< Z) :
    Summable (fun j : ℕ=> correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j)) := by
  have hh := (annular_reassembly_summable
    (fun p : Id×Id=> correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2)
    (fun p : Id×Id=>(Ideal.absNorm p.1:ℝ)*(Ideal.absNorm p.2:ℝ)^3)
    (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=> gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).prod_symm.prod
  simpa only [correctedCompletedT,gaussian_dyadic_correctedSummand S D Ψ Z hZ,Prod.swap] using hh

theorem gaussian_selected_tuple_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→ Id) (Ψ : α→ O→*ℂ)
    (hΨ : ∀k∈F,∀n,‖Ψ k n‖≤1) (Z : ℝ) (hZ : 0< Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0< q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      gaussianCompletedProfile (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hp (k : α) (hk : k∈F) : 0< Z*∏i,q k i :=
    mul_pos hZ (Finset.prod_pos (fun i _=> hq k hk i))
  have hd (k : α) (hk : k∈F) : Summable (fun j : ℕ=> a k*(∏i,W i (q k i))*
      correctedCompletedT S (D k) (Ψ k) (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) :=
    (correctedGaussian_dyadic_summable S (D k) (Ψ k) (hΨ k hk) _ (hp k hk)).mul_left _
  calc
    _ = ∑k∈F,∑'j : ℕ,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [correctedGaussian_eq_tsum_dyadic S (D k) (Ψ k) (hΨ k hk) _ (hp k hk),tsum_mul_left]
    _ = ∑'j : ℕ,∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := (Summable.tsum_finsetSum hd).symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeCompleted ProbeRow _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

/-- A supported ideal and a lattice frequency index each physical row. -/
abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryIdealGenerator r.1.val)
    ((supported_span_primaryIdealGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryIdealGenerator r.1.val
    let ha := supported_primaryIdealGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0< X)
    (s : {I : Id // Supported I}) : 0< elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0< elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)< Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0< X) (hY : 0< Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=> s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=> hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

lemma physicalRowWeight_mul_summable (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0< X) (hY : 0< Y) (F : PhysicalRowIndex→ℂ) :
    Summable (fun r=> physicalRowWeight C W0 W1 X Y r*F r) := by
  apply summable_of_hasFiniteSupport
  apply (physicalRowWeight_finite_support C W0 W1 hW0 hW1 X Y hX hY).subset
  intro r hr hz
  exact hr (by dsimp only; rw [hz,zero_mul])

theorem markedPhysicalProbe_eq_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=> verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [if_pos hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [if_neg hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0< X k) (hY : ∀k∈F,0< Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→ physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (hX k.val k.property) (hY k.val k.property)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hn⟩

theorem physical_selected_gaussian_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0< X k) (hY : ∀k∈F,0< Y k) (Z : ℝ) (hZ : 0< Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0< q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=> by rw [hR k hk r hr,zero_mul])
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=> D p.1) (fun p=> physicalRowMonoid η C p.2)
    (fun p _=> physicalRowMonoid_norm η C p.2) Z hZ (fun p=> q p.1)
    (fun p hp=> hq p.1 (Finset.mem_product.mp hp).1)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (physicalRowMonoid η C p.2) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [markedPhysicalProbe_eq_gaussian_rows η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (hX k hk) (hY k hk) (mul_pos hZ (Finset.prod_pos (fun i _=> hq k hk i))),hs k hk]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [A]
        ring
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [A]
      ring

theorem physical_selected_gaussian_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤ M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀J : ℕ,∀s : ℝ,0< s→∃B : ℝ,0< B ∧ ∀Z : ℝ,0< Z→
        Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤ B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→ HasCompactSupport W1→
        ∀F : Finset α,∀a : α→ℂ,∀D : α→ Id,∀X Y : α→ℝ,
        (∀k∈F,0< X k)→(∀k∈F,0< Y k)→∀Z : ℝ,0< Z→
        ∀q : α→ι→ℝ,(∀k∈F,∀i,0< q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
          (X k) (Y k) (Z*∏i,q k i))=
          ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
            (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
              correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
                (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
            (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,_⟩ := gaussian_selected_slot_family W M hM hwindow
  refine ⟨V,hV,fun J s hs=> gaussianJointMoment_summed V hV J s hs,?_⟩
  intro η C W0 W1 hW0 hW1 F a D X Y hX hY Z hZ q hq
  exact physical_selected_gaussian_reassembly W V hV hsep η C W0 W1 hW0 hW1
    F a D X Y hX hY Z hZ q hq

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical

lemma elementNorm_mul (a b : Eisenstein.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : Eisenstein.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : Eisenstein.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0< B) (hA : 0< A) (hS : 0< S) (hX : 0< X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  have hb : (Real.sqrt B:ℂ)^2=(B:ℂ) := by exact_mod_cast Real.sq_sqrt hB.le
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0< elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma elementNorm_slotProduct {K : ℕ} (p : Fin K→ O) (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=> elementNorm (p i)*x) ih

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→ O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=> hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→ O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0< elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→ O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→ O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→ O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→ Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

/-- Each compensation subset is a finite-weighted sum of Gaussian completed rows. -/
theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→ O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev SelectedSlot {K : ℕ} (J : Finset (Fin K)) := ↥(Finset.univ\J)

def compensationSubsetWeight {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→ O) (J : Finset (Fin K)) : ℂ :=
  compensationSubsetCoefficient η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def selectedSlotFactor {K : ℕ} (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (p : Fin K→ O) (J : Finset (Fin K)) (t : ℝ) : ℂ :=
  ∏i : SelectedSlot J,W i.val (elementNorm (p i.val)/P i.val)*
    kernelLogPhase (-t) (Real.log (elementNorm (p i.val)/P i.val))

def compensationRowTest {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→ O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (physicalRowMonoid η C r) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

lemma gaussian_slot_window_split {K : ℕ} (W : Fin K→ℝ→ℂ) (q : Fin K→ℝ) (J : Finset (Fin K)) :
    (∏i,W i (q i))=(∏i∈J,W i (q i))*(∏i : SelectedSlot J,W i.val (q i.val)) := by
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=> W i (q i))]
  have hh := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i=> W i (q i))
  simpa only [mul_comm] using hh.symm

lemma gaussian_compensation_scale {K : ℕ} (P : Fin K→ℝ) (hP : ∀i,0< P i)
    (p : Fin K→ O) (J : Finset (Fin K)) (Z : ℝ) :
    (Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p i.val)/P i.val)=
      Z*elementNorm (slotProduct p (Finset.univ\J)) := by
  rw [←Finset.prod_coe_sort (Finset.univ\J) P]
  rw [gaussian_selected_scale Z (fun i : SelectedSlot J=> P i.val)
    (fun i : SelectedSlot J=> elementNorm (p i.val)) (fun i=> hP i.val)]
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=> elementNorm (p i)),elementNorm_slotProduct]

theorem compensation_subset_common {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : SelectedSlot J→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→ Fin K→ O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0< P i) (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*compensationSubsetProbe η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,compensationSubsetWeight η W P (p k) J*
        compensationRowTest η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  have hbase : 0< Z*∏i∈Finset.univ\J,P i := mul_pos hZ (Finset.prod_pos (fun i _=> hP i))
  have hh := physical_selected_gaussian_reassembly
    (fun i : SelectedSlot J=> W i.val) V hV hsep η C W0 W1 hW0 hW1 F
    (fun k=> compensationSubsetWeight η W P (p k) J)
    (fun k=> Ideal.span {slotProduct (p k) (Finset.univ\J)})
    (fun k=> X/elementNorm (slotProduct (p k) J)) (fun k=> Y/elementNorm (slotProduct (p k) J))
    (fun k hk=> div_pos hX (slotProduct_norm_pos (p k) (hp k hk) J))
    (fun k hk=> div_pos hY (slotProduct_norm_pos (p k) (hp k hk) J))
    (Z*∏i∈Finset.univ\J,P i) hbase
    (fun k (i : SelectedSlot J)=> elementNorm (p k i.val)/P i.val)
    (fun k hk i=> div_pos (physicalElementNorm_pos _ (hp k hk i.val)) (hP i.val))
  calc
    _ = ∑k∈F,compensationSubsetWeight η W P (p k) J*
      (∏i : SelectedSlot J,W i.val (elementNorm (p k i.val)/P i.val))*
        markedPhysicalProbe η C (Ideal.span {slotProduct (p k) (Finset.univ\J)}) W0 W1
          (X/elementNorm (slotProduct (p k) J)) (Y/elementNorm (slotProduct (p k) J))
          ((Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p k i.val)/P i.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussian_compensation_scale P hP (p k) J Z,gaussian_slot_window_split W (fun i=> elementNorm (p k i)/P i) J]
      unfold compensationSubsetProbe compensationSubsetWeight
      ring
    _ = _ := hh

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace ProbePhysical
local notation "O" => Eisenstein.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤ M i) :
    ∃V : Finset (Fin K)→ SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0< s→∃B : ℝ,0< B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0< Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤ B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→ HasCompactSupport W1→
        ∀slotPrimes : Fin K→ Finset O,(∀i a,a∈slotPrimes i→ a≠0)→
        ∀P : Fin K→ℝ,(∀i,0< P i)→∀X Y Z : ℝ,0< X→0< Y→0< Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=> W i.val)
      (fun i : SelectedSlot A=> M i.val) (fun i=> hM i.val) (fun i=> hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=> gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0< B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=> fun i=>(p i).val)
      (fun p _ i=> hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein JointLogSeparation
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0< N) (hT : 0< T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0< T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            kernelLogPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [if_neg hI,if_neg hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0< T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,kernelLogPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤ rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0< C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0< T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤ C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤ M := tsum_nonneg (fun p=> by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤ _
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=> gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

lemma gaussianWeightedMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) (hR : 0≤ R) : 0≤ gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k A : ℝ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→ gaussianWeightedMoment V hV J k R≤ C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤ _
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→ gaussianWeightedMoment V hV J k R≤ C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤ C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianWeightedMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k s : ℝ) (hs : 0< s) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,0< Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤ C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianWeightedMoment_polynomial_decay V hV J k N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0< s) :
    ∃C : ℝ,0< C ∧ ∀Z A : ℝ,0< Z→1≤ A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤ C*Z^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0< A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0< A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤ gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤ U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0< R := div_pos (by positivity) hZ
    have hM : 0≤ gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤ R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤ R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤ R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤ R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤ _
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z^s+Cp*Z^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss JointLogSeparation
namespace ProbePhysical
open ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gaussianCompletedFamilyIntegral {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→ Id) (Ψ : α→ O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
    (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianCompletedFamilyMass {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*∏i,‖W i (q k i)‖

lemma gaussianCompletedFamilyMass_nonneg {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) :
    0≤ gaussianCompletedFamilyMass F a W q := by
  unfold gaussianCompletedFamilyMass
  positivity

lemma gaussianCompletedFamily_integrable {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→ Id) (Ψ : α→ O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (hT : 0< T) :
    Integrable (fun t : ℝ=>(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t) := by
  have hh := integrable_finsetSum F (fun k _=>(gaussian_selected_completed_integrable W (q k)
    (gaussianJointDensity V hV (T/Z)) S (D k) (Ψ k) T hT).const_mul (a k))
  simpa only [Finset.sum_mul,mul_assoc] using hh

theorem gaussianCompletedFamily_crude :
    ∃C : ℝ,0< C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→ Id,∀Ψ : α→ O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀V : SchwartzMap ℝ ℂ,∀hV : HasCompactSupport (V:ℝ→ℂ),∀T Z : ℝ,0< T→
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV T Z‖≤
        C*T^2*gaussianCompletedFamilyMass F a W q*gaussianJointMoment V hV 0 (T/Z) := by
  obtain ⟨C,hC,hb⟩ := gaussianFixedWindow_completed_crude
  refine ⟨C,hC,?_⟩
  intro α ι _ F a S D Ψ hΨ W q V hV T Z hT
  have hf := gaussianCompletedFamily_integrable F a S D Ψ W q V hV T Z hT
  have hp (t : ℝ) :
      ‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖≤
      (C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∑k∈F,‖a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i)))‖ := norm_sum_le _ _
      _ ≤ ∑k∈F,‖a k‖*(C*T^2)*(∏i,‖W i (q k i)‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,norm_prod,kernelLogPhase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb S (D k) (Ψ k) (hΨ k hk) T t hT) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _=> norm_nonneg _))
      _ = _ := by unfold gaussianCompletedFamilyMass;rw [Finset.mul_sum];congr 1;funext k;ring
  calc
    _ ≤ ∫t : ℝ,‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ :=
      integral_mono hf.norm ((gaussianJointDensity V hV (T/Z)).integrable.norm.const_mul _) hp
    _ = _ := by simp only [integral_const_mul,gaussianJointMoment,pow_zero,one_mul]

/-- Gaussian decay bounds the sum of completed rows outside the central dyadic range. -/
theorem gaussianCompletedFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C : ℝ,0< C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→ Id,∀Ψ : α→ O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0< Z→1≤ A→
      Summable (fun j : ℕ=> if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C*gaussianCompletedFamilyMass F a W q*Z^2/A^N := by
  obtain ⟨Cr,hCr,hr⟩ := gaussianCompletedFamily_crude
  obtain ⟨Cg,hCg,hg⟩ := gaussianRemoteMoment_summed V hV 0 N 2 (by norm_num)
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro α ι _ F a S D Ψ hΨ W q Z A hZ hA
  obtain ⟨hs,ht⟩ := hg Z A hZ hA
  let M := gaussianCompletedFamilyMass F a W q
  have hM : 0≤ M := gaussianCompletedFamilyMass_nonneg F a W q
  have hb (j : ℕ) :
      (if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
      (Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · simpa only [M,Real.rpow_two,mul_assoc,mul_comm,mul_left_comm] using
        hr F a S D Ψ hΨ W q V hV ((2:ℝ)^j) Z (by positivity)
    · simp
  have hnon (j : ℕ) : 0≤(if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) := by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hs.mul_left (Cr*M))
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,(Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := hsum.tsum_le_tsum hb (hs.mul_left (Cr*M))
    _ = (Cr*M)*∑'j : ℕ,gaussianRemoteMoment V hV 0 2 Z A j := tsum_mul_left
    _ ≤ (Cr*M)*(Cg*Z^(2:ℝ)/A^N) := mul_le_mul_of_nonneg_left ht (mul_nonneg hCr.le hM)
    _ = _ := by rw [Real.rpow_two];dsimp only [M];ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss JointLogSeparation
namespace ProbePhysical
open ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gaussianPhysicalFamilyIntegral {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianPhysicalFamilyMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*∑'r : PhysicalRowIndex,‖physicalRowWeight C W0 W1 (X k) (Y k) r‖

lemma gaussianPhysicalFamily_mass_eq {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianCompletedFamilyMass (F×ˢR)
      (fun p=> a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2) W (fun p=> q p.1)=
      gaussianPhysicalFamilyMass C W0 W1 F a X Y W q := by
  unfold gaussianCompletedFamilyMass gaussianPhysicalFamilyMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=> by rw [hR k hk r hr,norm_zero]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_mul]
  ring

lemma gaussianPhysicalFamily_integral_eq {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=> a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=> D p.1) (fun p=> physicalRowMonoid η C p.2) W (fun p=> q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=> by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem gaussianPhysicalFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0< C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→ HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→ Id,∀X Y : α→ℝ,
      (∀k∈F,0< X k)→(∀k∈F,0< Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0< Z→1≤ A→
      Summable (fun j : ℕ=> if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=> a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=> D p.1) (fun p=> physicalRowMonoid η C p.2)
    (fun p _=> physicalRowMonoid_norm η C p.2) W (fun p=> q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [gaussianPhysicalFamily_integral_eq η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

/-- The fixed coefficient of a physical row before its numerator twist. -/
abbrev physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  baseRowCoefficient η Xi s hs

lemma physicalRowBase_norm (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (hXi : ∀a,‖Xi a‖≤1) (s : O) (hs : Supported (Ideal.span {s})) (a : O) :
    ‖physicalRowBase η Xi s hs a‖≤1 := by
  change ‖(targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a‖≤1
  rw [norm_mul,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a))).trans (sexticReciprocityPhase_norm s a)

lemma ray_rowCoefficient_eq_rowTwist (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (χ : RayCharacter) :
    rayMonoid χ*rowCoefficient η Xi s hs n=
      rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z := by
  subst n
  ext a
  change rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a*
      idealRowHom (m^6*f^4*z) (Ideal.span {a}))=
    (rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a))*
      idealRowHom (m^6*f^4*z) (Ideal.span {a})
  ring

def wholeIdealMask (S : Finset Id) (D A : Id) : ℂ :=
  if D∣A ∧ ∀P∈S,¬P∣A then 1 else 0

lemma markedCompletedT_eq_inverse (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0< X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT Ψ W X (wholeIdealMask S D) := by
  rw [InverseMoment.markedCompletedT_eq_tsum Ψ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  change completedMask S D p.1 p.2*CompletedGauss.summand Ψ W X p.1 p.2=
    CompletedGauss.summand Ψ W X p.1 p.2*wholeIdealMask S D (p.1*p.2^3)
  exact mul_comm _ _

theorem correctedPhysicalRow_eq_inverse_rows (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (S : Finset Id) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0< X) :
    correctedCompletedT S D (rowCoefficient η Xi s hs n) W X=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT (rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z)
          W X (wholeIdealMask S D) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_inverse S D _ W hW X hX,ray_rowCoefficient_eq_rowTwist η Xi s hs m f z n hn χ]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion  CanonicalCoefficientClass
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}

def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact primaryIdealGenerator_ne_zero_ideal _ D.numeratorSupported.1

lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=> by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)

lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=> rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  · exact hp x y (Ideal.mul_le_left hxy)

lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : lambda∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : lambda^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ ((supported_iff_native _).mp hn)] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [if_pos hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]

def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*ProbeRow.conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s ((supported_iff_native _).mp hs)

def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_right (Ideal.mul_le_right hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_left (Ideal.mul_le_right hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := by
    apply congrArg χ
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h4)
  rw [hr]

lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)

lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : lambda∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : lambda^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion  CanonicalCoefficientClass Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=> P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    lambda∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr (by simp [cubicTwoIdeal])

lemma supported_of_coprime_bad (B n : O) (hBL : lambda∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_span_iff n |>.mpr
  constructor
  · exact residue_lambda_prime.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : lambda∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : lambda^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [if_pos hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ ((supported_iff_native _).mp hn),lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion  Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma summand_zero_completedIndex (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id)
    (h : completedIndex I J=0) : CompletedGauss.summand Ψ W X I J=0 := by
  have hprod : primaryIdealGenerator I*primaryIdealGenerator J^3=0 := h
  rcases mul_eq_zero.mp hprod with hI|hJ
  · have hg := squarefreeGaussCoefficient_of_primary_zero I hI
    simp only [CompletedGauss.summand, columnWeight, hg, zero_mul, zero_div]
  · have hj : primaryIdealGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (CompletedGauss.angularFactor (primaryIdealGenerator J))^3*
        Ψ (primaryIdealGenerator J)^3/(Ideal.absNorm J:ℂ)=0
      simp only [hj,CompletedGauss.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    simp only [CompletedGauss.summand,hc,mul_zero,zero_mul]

lemma markedSummand_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id) :
    markedSummand S D Ψ W X I J=
      CompletedGauss.summand (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X I J*
        (if D∣I*J^3 then (1:ℂ) else 0) := by
  rw [InverseMoment.summand_mul_fixed_twist]
  change completedMask S D I J*CompletedGauss.summand Ψ W X I J=
    coprimalityMask (calibrationForSet S hS).generator (completedIndex I J)*CompletedGauss.summand Ψ W X I J*
      (if D∣I*J^3 then (1:ℂ) else 0)
  by_cases hA : completedIndex I J=0
  · rw [summand_zero_completedIndex Ψ W X I J hA]
    simp only [mul_zero,zero_mul]
  · have he := calibration_coprime_iff_excluded_span S hS (completedIndex I J)
    rw [completedIndex_eq_primaryIdealGenerator] at he hA
    rw [(primaryIdealGenerator_spec (I*J^3) hA).1] at he
    change _=(if IsCoprime (calibrationForSet S hS).generator (completedIndex I J) then (1:ℂ) else 0)*_ * _
    rw [completedIndex_eq_primaryIdealGenerator,he]
    unfold completedMask
    by_cases hd : D∣I*J^3 <;> by_cases hx : ∀P∈S,¬P∣I*J^3 <;>
      simp only [hd,hx,and_self,and_false,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul] ; simp_all

lemma markedCompletedT_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0< X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X
        (fun A=> if D∣A then (1:ℂ) else 0) := by
  rw [InverseMoment.markedCompletedT_eq_tsum _ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  exact markedSummand_eq_punctured S hS D Ψ W X p.1 p.2

lemma inverseMarkedCompletedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,lambda^2∣n-1→Ψ n=Φ n)
    (W : ℝ→ℂ) (X : ℝ) (d : Id→ℂ) :
    InverseMoment.markedCompletedT Ψ W X d=InverseMoment.markedCompletedT Φ W X d := by
  unfold InverseMoment.markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [CompletedGauss.summand,CompletedGauss.summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

def calibrationLowData (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) :
    GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator :=
  goodMaskRowData _ 1 _ (calibrationForSet S hS).generator_ne_zero one_ne_zero
    (calibrationForSet S hS).generator_ne_zero

theorem correctedPhysicalRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0< X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (rowTwist (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator E s hs χ)
          (calibrationForSet S hS).generator 1 z) W X (fun A=> if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  exact (lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn).symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0< Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=> if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted ProbeRow _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem gaussian_twisted_physical_row_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id) (j : ℕ) (t : ℝ) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)
          (fun A=> if D∣A then (1:ℂ) else 0) := by
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D _
    (gaussianFixedWindow_twist_compact t) _ (by positivity) (calibrationLowData S hS)


end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}

def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s

def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩

lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dif_pos hh]
  exact Classical.choose_spec hh

lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    rw [sexticReciprocityPhase_comm s.val n, sexticReciprocityPhase_comm r.val n]
    exact sexticReciprocityPhase_congr_right n s.val r.val hd
  rw [he]

def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryIdealGenerator s.val)

lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryIdealGenerator r.1.val,(supported_span_primaryIdealGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

lemma physicalRayRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n

def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayPeriodicBase_uniform (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0< T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=> if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
namespace ProbePhysical
local notation "O" => Eisenstein.O

def lowOuterCutoff (a b x : ℝ) : ℂ :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

lemma lowOuterCutoff_small (a b : ℝ) (ha : 0< a) (x : ℝ) (hx : x≤ a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,zero_mul]

lemma lowOuterCutoff_large (a b : ℝ) (hb : 0< b) (x : ℝ) (hx : 2*b≤ x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤ x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,mul_zero]

lemma lowOuterCutoff_one (a b : ℝ) (ha : 0< a) (hb : 0< b) (x : ℝ) (hlo : a≤ x) (hhi : x≤ b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma lowOuterCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma lowOuterCutoff_support (a b : ℝ) (ha : 0< a) (hb : 0< b) :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

lemma lowOuterCutoff_compact (a b : ℝ) (ha : 0< a) (hb : 0< b) :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

lemma physical_ratio_factor (B q X Y m : ℝ) (hq : 0< q) (hY : 0< Y) :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

lemma physical_window_cutoff_one (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (B q X Y m : ℝ) (hq : 0< q) (hY : 0< Y)
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    have hd : (q/Y)*(m/(B*q*X))≤ b0*b1 := by simpa only [mul_comm] using hh
    exact hd.trans (le_max_right _ _)

theorem physicalRowWeight_insert_cutoff (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hY : 0< Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=> hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=> hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)< Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace ProbePhysical

lemma low_mellin_phase_norm (a v : ℝ) (ha : 0< a) :
    ‖(a:ℂ)^((v:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0< a) (hb : 0< b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=> mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=> mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0< a) (hb : 0< b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,positive_quotient_cpow_neg a b ha hb]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0< B) (hq : 0< q) (hX : 0< X) (hY : 0< Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0< B*X*Y := by positivity
  have hb : 0< q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,←CenteredMomentDetectorDictionary.sqrt_inverse_cpow _ hb]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0< B) (hq : 0< q) (hX : 0< X) (hY : 0< Y) (hm : 0< m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0< B*X*Y := by positivity
  have ha : 0< m/(B*X*Y) := div_pos hm hQ
  have hb : 0< q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
