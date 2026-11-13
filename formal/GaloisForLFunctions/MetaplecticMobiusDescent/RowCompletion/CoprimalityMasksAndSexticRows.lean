/-
Coprimality masks and sextic rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalStateRecursion
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.IdealRowCharacters

/-!
# Coprimality masks and sextic rows

Ideal ranges and coprimality masks away from two and three. Denominators supported away from
two and three give finite prime character rows; the sextic Euler criterion before complex
embedding; fixed-ray quadratic phases.
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

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun T => frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow p hg pool v z ^ 3 *
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  apply hi.congr
  filter_upwards [] with ξ
  rw [reopenedCanonicalRow_integrand p hg]
  rfl

theorem separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0  ≤  E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        reopenedCanonicalRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (cubicIdealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K  ≤ 
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        reopenedCanonicalRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (cubicIdealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K  ≤ 
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (cubicIdealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) :=
    separated_canonical_integrable p hg pool Q (β I) n Ψ m (cubicIdealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => reopenedCanonicalRow p hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (cubicIdealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹)

end
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem outsideCanonicalRow_family_binned_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ K : ℝ)
    (hb : 0  ≤  b) (hX : 0 < X) (hK : 0 < K)
    (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hD : b*X  ≤  D) :
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (cubicIdealGenerator I) z W X) K  ≤ 
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m (cubicIdealGenerator I) z W X H₀) K) := by
  apply rowFamilyEnergy_bound_sum labels (cubeLogRange b X) K hK
  intro I hI z hz
  exact outsideCanonicalRow_binned_energy S D hbad hSp Ψ m (cubicIdealGenerator I) z W hWc
    b X H₀ hb hX hW hD

theorem outsideCanonicalBin_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u|  ≤  columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hK : 0 < K) (hE : 0  ≤  E)
    (hn : ∀ v ∈ Q, B  ≤  (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)  ≤  Real.exp 1*B) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (cubicIdealGenerator I)
        (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K  ≤ 
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      outsideCanonicalBin S D hbad Q Ψ m (cubicIdealGenerator I) z W X H₀) K  ≤ 
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => outsideCanonicalBin S D hbad Q Ψ m (cubicIdealGenerator I) z W X H₀) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (cubicIdealGenerator I)
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact outsideCanonicalBin_separated S D hbad Q Ψ m (cubicIdealGenerator I) z W a b ha hs hW V hV
      B ell X H₀ hB hell hX hn hn'
  rw [hrows]
  exact separated_canonical_family_energy (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q labels β n Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
def progressingCubes (S : Finset (Ideal O)) (D : ℕ) (H₀ : ℝ)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀ ≤ (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ))

theorem separatedCubeCoefficient_eq_zero_of_small (S : Finset (Ideal O)) (D : ℕ)
    (H₀ : ℝ) (Ψ : O→*ℂ) (B ξ : ℝ)
    (v : primePool (outsideSquarefreeIdeals S D)→₀ℕ)
    (hsmall : ¬H₀ ≤ (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ)) :
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ Ψ (cubeIdeal (outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) u):ℝ)) B ξ v=0 := by
  have hz : reopenedCubeCoefficient H₀ Ψ (cubeIdeal (outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hn
    exact hsmall (reopenedCubeCoefficient_support H₀ Ψ _ hn).2
  simp only [separatedCubeCoefficient,hz,zero_mul]

theorem outsideCanonicalBin_filter (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=
      outsideCanonicalBin S D hbad (progressingCubes S D H₀ Q) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬H₀ ≤ (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ) :=
    fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  have hz : largeCubeCoefficient H₀ (cubeIdeal (outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (largeCubeCoefficient_support H₀ _ hh).2
  simp only [hz,zero_mul]

theorem progressingCubes_progress (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ))
    (Z F B : ℝ) (hF : 1 ≤ F) (hB : 1 ≤ B)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) Q).Nonempty)
    (hupper : ∀v∈Q,(Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ) ≤ Real.exp 1*B) :
    Z^((1:ℝ)/1000) ≤ (Real.exp 1*B)*F := by
  by_cases hsmall : F<Z^((1:ℝ)/1000)
  · obtain ⟨v,hv⟩ := hQ
    obtain ⟨hvQ,hlo⟩ := Finset.mem_filter.mp hv
    simp only [if_pos hsmall] at hlo
    have he := hlo.trans (hupper v hvQ)
    have hbpos : 0 ≤ Real.exp 1*B := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hB)
    exact he.trans (le_mul_of_one_le_right hbpos hF)
  · have hb : 1 ≤ Real.exp 1*B :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
    exact (le_of_not_gt hsmall).trans (le_mul_of_one_le_left (zero_le_one.trans hF) hb)

theorem progressingActiveBin_progress (S : Finset (Ideal O)) (D : ℕ)
    (b X Z F : ℝ) (j : ℕ) (hF : 1 ≤ F)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)
      (activeCubeLogBin S D b X j)).Nonempty) :
    Z^((1:ℝ)/1000) ≤ (Real.exp 1*normLogScale j)*F :=
  progressingCubes_progress S D (activeCubeLogBin S D b X j) Z F (normLogScale j) hF
    (normLogScale_ge_one j) hQ (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)

theorem outsideCanonicalBin_zero_of_empty_filter (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (hQ : progressingCubes S D H₀ Q=∅) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=0 := by
  rw [outsideCanonicalBin_filter S D hbad Q Ψ m f z W X H₀,hQ]
  simp only [outsideCanonicalBin,Finset.sum_empty]

theorem reopenedCanonicalRow_progressing (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ Ξ : O→*ℂ) (m f z : O) (H₀ B ξ : ℝ)
    (H : Finset (primePool (outsideSquarefreeIdeals S D))→ℂ) :
    let F:=outsideSquarefreeIdeals S D
    let hF:=outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀ Ξ (cubeIdeal F v))
      (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) B ξ
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q β Ψ m f H z=
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
      (progressingCubes S D H₀ Q) β Ψ m f H z := by
  dsimp only
  let F:=outsideSquarefreeIdeals S D
  have hF:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply reopenedCanonicalRow_filter
  intro v hv hsmall
  exact separatedCubeCoefficient_eq_zero_of_small S D H₀ Ξ B ξ v hsmall

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem outside_separated_cube_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal O)) (D : ℕ) (Ψ : O →* ℂ), (∀ z, ‖Ψ z‖  ≤  1) →
      ∀ (m f : O) (H₀ B ξ : ℝ)
      (v : primePool (outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B  ≤  (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)  ≤  Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖  ≤  C*(Real.exp 1*B)^ε := by
  obtain ⟨C,hC,hbound⟩ := reopenedCubeCoefficient_small_power ε hε
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro S D Ψ hΨ m f H₀ B ξ v hB hn hn'
  let F := outsideSquarefreeIdeals S D
  have ht : ∀ z, ‖rowTwist Ψ (m*excludedGenerator S) f 1 z‖  ≤  1 :=
    rowTwist_norm Ψ hΨ (m*excludedGenerator S) f 1
  have hβ : ‖reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)‖  ≤ 
      C*(Real.exp 1*B)^ε := by
    apply (hbound H₀ _ ht _ (cubeIdeal_ne_zero F v)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hε.le) hC.le
  have hh := separatedCubeCoefficient_bound
    (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F u))
    (fun u => (Ideal.absNorm (cubeIdeal F u) : ℝ)) B ξ (C*(Real.exp 1*B)^ε)
    hB (by positivity) v hn hn' hβ
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem outside_pool_coprime_excluded
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (outsideSquarefreeIdeals S D)) :
    IsCoprime (Ideal.span {poolPrimary (outsideSquarefreeIdeals S D) i})
      (∏P∈S,P) := by
  rw [poolPrimary_span _ (outsideSquarefree_admissible S D hbad)]
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply (Ideal.isMaximal_def.mp (inferInstance : i.val.IsMaximal)).not_le_iff_codisjoint.mp
  intro hle
  apply excludedGenerator_not_mem_pool S D hSp i
  apply hle
  have hm : excludedGenerator S ∈ Ideal.span {excludedGenerator S} :=
    Ideal.subset_span (by simp)
  simpa only [excludedGenerator,span_cubicIdealGenerator] using hm

theorem cubeIdeal_eq_primeProduct_span (F : Finset (Ideal O))
    (hF : ∀I∈F,quadraticIdealAdmissible I) (v : primePool F→₀ℕ) :
    Ideal.span {primeProduct (poolPrimary F) v.support v}=cubeIdeal F v := by
  rw [primeProduct,span_finset_prime_product]
  simp only [←Ideal.span_singleton_pow,poolPrimary_span F hF]
  unfold cubeIdeal
  apply Finset.prod_subset (Finset.subset_univ v.support)
  intro i hi hni
  rw [Finsupp.notMem_support_iff.mp hni,pow_zero]

theorem cubeIdeal_primeProduct_norm (F : Finset (Ideal O))
    (hF : ∀I∈F,quadraticIdealAdmissible I) (v : primePool F→₀ℕ) :
    ‖ringComplex (primeProduct (poolPrimary F) v.support v)‖^2=
      (Ideal.absNorm (cubeIdeal F v):ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span,cubeIdeal_eq_primeProduct_span F hF]

theorem progressingActiveBin_cube_bound
    (S : Finset (Ideal O)) (D : ℕ) (b X H₀ : ℝ) (j : ℕ)
    (hQ : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty) :
    (normLogScale j)^3 ≤ b*X := by
  obtain ⟨v,hv⟩:=hQ
  have hbin := (Finset.mem_filter.mp hv).1
  have hactive := (Finset.mem_filter.mp hbin).1
  have hnorm := (activeCubeLogBin_norms S D b X j v hbin).1
  exact (pow_le_pow_left₀ (normLogScale_pos j).le hnorm 3).trans
    (Finset.mem_filter.mp hactive).2

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem progressingCanonicalBin_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0 ≤ M) (hNv : 0 ≤ Nv)
    (hgM : ∀t,g t≠0→|t| ≤ M) (hV : ∀t,V t≠0→|t| ≤ Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η ≤ (1:ℝ)/1000) (hbudget : 3000*η ≤ (1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0 ≤ C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t| ≤ M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t| ≤ M+7) ∧
      ∀(S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : O→*ℂ) (Z : ℝ) (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖ ≤ 1) → 1<Z → Real.exp 9000 ≤ Z → 1 ≤ X → X ≤ Z^3 → F ≤ Z^3 → 1 ≤ E →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K' ≤ E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      ∀j∈cubeLogRange (Real.exp A) X,
      let B:=normLogScale j
      let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
      Q'.Nonempty → ∀ξ : ℝ,
      B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary P) (poolPrimary_good P hP) Finset.univ Q'
          (separatedCubeCoefficient
            (fun v=>reopenedCubeCoefficient H₀
              (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) 1)
              (cubeIdeal P v))
            (fun v=>(Ideal.absNorm (cubeIdeal P v):ℝ)) B ξ)
          Ψ m (cubicIdealGenerator I)
          (fun T=>frequencyTwist g (oldHeight+ξ) (columnLog (poolPrimary P) (X/B^3) T)) z) K ≤ 
        C*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cβ,hCβ,hβbound⟩:=outside_separated_cube_coefficient_bound ε hε
  let Cg:=Cβ*(Real.exp (A+1))^ε
  refine ⟨w₁,w₂,C₀*Cg^2,by positivity,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  have hP:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih j hj hQ ξ
  let B:=normLogScale j
  let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
  let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
  let β:=fun I v=>separatedCubeCoefficient
    (fun u=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal P u))
    (fun u=>(Ideal.absNorm (cubeIdeal P u):ℝ)) B ξ v
  have hB : 1 ≤ B:=normLogScale_ge_one j
  have hBp : 0<B:=normLogScale_pos j
  have hactive : B^3 ≤ Real.exp A*X:=progressingActiveBin_cube_bound S D (Real.exp A) X H₀ j hQ
  have hBscale : Real.exp 1*B ≤ Real.exp (A+1)*Z^3 := by
    calc
      _  ≤  Real.exp 1*(Real.exp A*X) :=
        mul_le_mul_of_nonneg_left ((le_self_pow₀ hB (by decide : (3:ℕ)≠0)).trans hactive) (Real.exp_pos _).le
      _  ≤  Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add];ring
  have hbgrowth : (Real.exp 1*B)^ε ≤ (Real.exp (A+1))^ε*Z^(3*ε) := by
    calc
      _  ≤  (Real.exp (A+1)*Z^3)^ε :=
        Real.rpow_le_rpow (by positivity) hBscale hε.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0 ≤ Z)]
        norm_num
  have hΨ : ∀u,‖normHeightTwist Ψ oldHeight u‖ ≤ 1 :=
    fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hstate.coefficient.norm_le hbase u)
  have hcoeff : ∀I∈labels,∀v∈Q',‖β I v‖ ≤ Cg*Z^(3*ε) := by
    intro I hI v hv
    have hvbin: v∈activeCubeLogBin S D (Real.exp A) X j:=(Finset.mem_filter.mp hv).1
    obtain ⟨hlo,hhi⟩:=activeCubeLogBin_norms S D (Real.exp A) X j v hvbin
    exact (hβbound S D _ hΨ m (cubicIdealGenerator I) H₀ B ξ v hBp hlo hhi).trans
      ((mul_le_mul_of_nonneg_left hbgrowth hCβ.le).trans_eq (by dsimp only [Cg];ring))
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i k he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  have hpr (i : primePool P) : lambda^2∣poolPrimary P i-1 :=
    (primaryIdealPrime_spec i.val (poolPrimary_ne_zero P hP i)).2.2.2
  have hn : ∀v∈Q',‖ringComplex
      (FirstPassCubeLabels.primeProduct (poolPrimary P) v.support v)‖^2 ≤ Real.exp 1*B := by
    intro v hv
    rw [cubeIdeal_primeProduct_norm P hP]
    exact (activeCubeLogBin_norms S D (Real.exp A) X j v (Finset.mem_filter.mp hv).1).2
  have hp := hstep (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj hpr base (∏Q∈S,Q) Z Ψ m labels
    X F K hstate Finset.univ Q' β (Cg*Z^(3*ε)) (oldHeight+ξ) B E hbase
    (outside_pool_coprime_excluded S D hbad hSp) hZ hZbig hX hXZ hFZ
    (by dsimp only [Cg];positivity) hE hB hactive
    (progressingActiveBin_progress S D (Real.exp A) X Z F j hstate.label_ge_one hQ)
    hcoeff (fun v hv=>Finset.subset_univ _) hn ih
  have hpower : (Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε)=Z^(η+17*deltaLoss+38*ε) := by
    rw [←Real.rpow_mul_natCast (by linarith : 0 ≤ Z),←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    norm_num
    ring
  have heq : C₀*(Cg*Z^(3*ε))^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖oldHeight+ξ‖)^(2*J)=
      (C₀*Cg^2)*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
    rw [Real.norm_eq_abs]
    calc
      _ = (C₀*Cg^2)*(X*F)^2*((Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε))*E*(1+|oldHeight+ξ|)^(2*J) := by ring
      _ = _ := by rw [hpower]
  exact (show _ ≤ _ from hp).trans_eq heq

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory CanonicalCoefficientClass
open scoped BigOperators Classical SchwartzMap ContDiff
theorem canonicalLogEnergy_eq_completed_rows
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀ s, V s ≠ 0 → |s|  ≤  A) (X K : ℝ) (hX : 0 < X) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    canonicalLogEnergy (poolPrimary F) (poolPrimary_good F hF) (fun _=>1) Finset.univ Ψ m labels V X K =
    rowFamilyEnergy labels (fun I z =>
      outsideCanonicalRow S D hbad Ψ m (cubicIdealGenerator I) z (radialFromLog V hVs A hV) X) K := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  simp only [canonicalLogEnergy,one_mul]
  change rowFamilyEnergy labels (fun I z =>
    fixedChildRow (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T => V (columnLog (poolPrimary F) X T)) (cubicIdealGenerator I) z) K = _
  congr 1
  funext I z
  unfold outsideCanonicalRow
  dsimp only
  apply congrArg (fun H => fixedChildRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m H (cubicIdealGenerator I) z)
  funext T
  exact (radialFromLog_column (poolPrimary F) (poolPrimary_ne_zero F hF) V hVs A hV X hX T).symm

theorem log_rows_family_binned_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀ s, V s ≠ 0 → |s|  ≤  A) (X H₀ K : ℝ)
    (hX : 0 < X) (hK : 0 < K) (hD : Real.exp A*X  ≤  D) :
    let W := radialFromLog V hVs A hV
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (cubicIdealGenerator I) z W X) K  ≤ 
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K +
        (cubeLogRange (Real.exp A) X).card * ∑ j ∈ cubeLogRange (Real.exp A) X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D (Real.exp A) X j)
              Ψ m (cubicIdealGenerator I) z W X H₀) K) := by
  dsimp only
  exact outsideCanonicalRow_family_binned_energy S D hbad hSp Ψ m labels
    (radialFromLog V hVs A hV) (radialFromLog_hasCompactSupport V hVs A hV)
    (Real.exp A) X H₀ K (Real.exp_pos A).le hX hK
    (fun t ht => (radialFromLog_support V hVs A hV t ht).2) hD

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory CanonicalCoefficientClass
open scoped BigOperators Classical SchwartzMap ContDiff
def outsideLogEnergy (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O)) (V : ℝ→ℂ) (X K : ℝ) : ℝ :=
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  canonicalLogEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) Finset.univ Ψ m labels V X K

theorem outsideLogEnergy_eq_completed
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O))
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) (X K : ℝ) (hX : 0<X) :
    outsideLogEnergy S D hbad Ψ m labels V X K=
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad Ψ m (cubicIdealGenerator I) z
        (radialFromLog V hVs A hV) X) K := by
  exact canonicalLogEnergy_eq_completed_rows S D hbad Ψ m labels V hVs A hV X K hX

theorem outsideLogEnergy_terminal_constant
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) :
    ∃C : ℝ,0 ≤ C ∧ ∀(S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (base : O→*ℂ) (Z η : ℝ) (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖ ≤ 1) → 1<Z → 0 ≤ η → 3000*η ≤ (1:ℝ)/40 →
      (fixedDepthRank Z K=0 ∨ X ≤ 1) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K ≤ C*(X*F)^2 := by
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun s hs=>abs_le.mp (hV s hs))
  let v : 𝓢(ℝ,ℂ):=hVc.toSchwartzMap hVs
  let M:=SchwartzMap.seminorm ℝ 0 0 v
  refine ⟨canonicalTerminalConstant A M,canonicalTerminalConstant_nonneg A M,?_⟩
  intro S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη hbudget hstop
  let P:=outsideSquarefreeIdeals S D
  have hP:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i j he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  have hpr (i : primePool P) : lambda^2∣poolPrimary P i-1 :=
    (primaryIdealPrime_spec i.val (poolPrimary_ne_zero P hP i)).2.2.2
  exact CanonicalStateCondition.terminal_energy (poolPrimary P) (poolPrimary_ne_zero P hP)
    (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj hpr
    Finset.univ base (∏Q∈S,Q) Z η Ψ m labels X F K hstate hbase hZ hη hbudget
    V A M t (apply_nonneg _ _) (fun s=>SchwartzMap.norm_le_seminorm ℝ v s) hV hstop

end CanonicalRowCompletion

namespace CanonicalRowCompletion

open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
private theorem height_sum_bound (a b : ℝ) (J : ℕ) :
    (1+|a+b|)^(2*J) ≤ (1+|a|)^(2*J)*(1+|b|)^(2*J) := by
  have h : 1+|a+b| ≤ (1+|a|)*(1+|b|) := by
    have := abs_add_le a b
    nlinarith [abs_nonneg a,abs_nonneg b]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1+|a+b|) h (2*J)

theorem progressingCanonicalBin_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D)→₀ℕ))
    (labels : Finset (Ideal O)) (Ψ : O→*ℂ) (m : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u| ≤ columnWindowRadius a b→V u=1)
    (B ell X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell) (hK : 0<K) (hE : 0 ≤ E)
    (hn : ∀v∈Q,B ≤ (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀v∈Q,(Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v):ℝ) ≤ Real.exp 1*B) :
    let F:=outsideSquarefreeIdeals S D
    let hF:=outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Q':=progressingCubes S D H₀ Q
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (cubicIdealGenerator I) (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) ell T)) z) K ≤ 
      E*(1+|oldHeight+ξ|)^(2*J)) →
    X*rowFamilyEnergy labels (fun I z=>
      outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (cubicIdealGenerator I) z W X H₀) K ≤ 
      E*(1+|oldHeight|)^(2*J)*
        (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=outsideSquarefreeIdeals S D
  have hF:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Q':=progressingCubes S D H₀ Q
  let β:=fun I v=>reopenedCubeCoefficient H₀
    (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hX0 : 0<X := by rw [hX];positivity
  have hQsub : Q'⊆Q := Finset.filter_subset _ _
  have heq : (fun I z=>outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (cubicIdealGenerator I) z W X H₀)=
      (fun I z=>outsideCanonicalBin S D hbad Q' (normHeightTwist Ψ oldHeight) m (cubicIdealGenerator I) z W X H₀) := by
    funext I z
    exact outsideCanonicalBin_filter S D hbad Q _ m _ z W X H₀
  rw [heq]
  have he := outsideCanonicalBin_energy S D hbad Q' labels (normHeightTwist Ψ oldHeight) m W
    a b ha hs hW V hV B ell X H₀ K ((E/B)*(1+|oldHeight|)^(2*J)) J hB hell hX hK
    (by positivity) (fun v hv=>hn v (hQsub hv)) (fun v hv=>hn' v (hQsub hv))
  have hpnt : ∀ξ : ℝ,rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        (normHeightTwist Ψ oldHeight) m (cubicIdealGenerator I)
        (fun T=>frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤ 
      ((E/B)*(1+|oldHeight|)^(2*J))*(1+|ξ|)^(2*J) := by
    intro ξ
    change (∑I∈labels,nonzeroRowMajorantSum _ K).re ≤ _
    rw [reopenedCanonicalEnergy_two_heights (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_good F hF) Finset.univ Q' labels
      (fun I=>separatedCubeCoefficient (β I) n B ξ) Ψ m V ell K oldHeight ξ hell]
    change rowFamilyEnergy labels _ K ≤ _
    have ht := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hsource ξ)
    calc
      _  ≤  E*(1+|oldHeight+ξ|)^(2*J)/B := by simpa only [Nat.mul_comm J 2] using ht
      _  ≤  E*((1+|oldHeight|)^(2*J)*(1+|ξ|)^(2*J))/B :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (height_sum_bound oldHeight ξ J) hE) hB.le
      _ = _ := by ring
  have hf:=he hpnt
  have hh:=mul_le_mul_of_nonneg_left hf hX0.le
  apply hh.trans_eq
  rw [hX]
  field_simp

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Bounded squarefree ideals coprime to the primes above two and three. -/
def idealRange (X : ℝ) : Finset (Ideal O) :=
  (outsideSquarefreeIdeals fixedBadPrimes ⌈max 1 X⌉₊).filter
    (fun I => (Ideal.absNorm I:ℝ)  ≤  X)

lemma mem_idealRange {X : ℝ} {I : Ideal O} :
    I∈idealRange X ↔ quadraticIdealAdmissible I ∧ (Ideal.absNorm I:ℝ)  ≤  X := by
  constructor
  · intro hi
    obtain ⟨ho,hn⟩:=Finset.mem_filter.mp hi
    exact ⟨outsideSquarefree_admissible _ _ (Finset.Subset.refl _) I ho,hn⟩
  · rintro ⟨hi,hn⟩
    have hs : quadraticSupported I := ⟨hi.1,hi.2.2⟩
    have hav:=(quadraticSupported_iff_bad_not_dvd I).mp hs
    have ho : I∈outsideIdealsUpTo fixedBadPrimes ⌈max 1 X⌉₊ := by
      apply mem_outsideIdealsUpTo.mpr
      refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi.2.1.ne_zero),?_,?_⟩
      · exact Nat.cast_le.mp (hn.trans ((le_max_right 1 X).trans (Nat.le_ceil _)))
      · intro P hP
        rcases Finset.mem_insert.mp hP with rfl|hP
        · exact hav.1
        · rw [Finset.mem_singleton.mp hP]
          exact hav.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ho,hi.2.1⟩,hn⟩

lemma admissible_of_squarefree_coprime_bad (I G : Ideal O)
    (hi : Squarefree I) (hc : IsCoprime I G)
    (hbad : ∀P∈fixedBadPrimes,P∣G) : quadraticIdealAdmissible I := by
  have hn (P : Ideal O) (hP : P∈fixedBadPrimes) : ¬P∣I := by
    intro hd
    exact (fixedBadPrimes_prime P hP).2.1 (hc.isRelPrime hd (hbad P hP))
  have hs : quadraticSupported I := (quadraticSupported_iff_bad_not_dvd I).mpr
    ⟨hn _ (Finset.mem_insert_self _ _),
      hn _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  exact ⟨hs.1,hi,hs.2⟩

theorem canonicalLabels_subset_idealRange
    (base : O→*ℂ) (bad : Ideal O) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
    (labels : Finset (Ideal O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbad : ∀P∈fixedBadPrimes,P∣bad) : labels⊆idealRange F := by
  intro I hI
  have hb:=hstate.label_bounds I hI
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad I bad hb.2.1 hb.2.2.1 hbad,hb.2.2.2⟩

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem canonicalShortState_geometry (S : Finset (Ideal O))
    (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (Z η : ℝ) (Ψ : O→*ℂ) (m : O)
    (labels : Finset (Ideal O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K)
    (hZ : 1 ≤ Z) (hZbig : Real.exp 9000 ≤ Z) (hη : 0 ≤ η)
    (hbudget : 3000*η ≤ (1:ℝ)/80)
    (hfixed : 2*‖ringComplex (excludedGenerator S)‖^2 ≤ Z^((1:ℝ)/80)) :
    let G:=Ideal.span {m*excludedGenerator S}
    G≠0 ∧ (∀P∈fixedBadPrimes,P∣G) ∧ labels⊆idealRange F ∧
      X*F ≤ Z^3 ∧ (2*K)*(Ideal.absNorm G:ℝ) ≤ X*F*Z^(-((1:ℝ)/40)) := by
  have hprod : (∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hSp P hP).ne_zero)
  have he : excludedGenerator S≠0:=cubicIdealGenerator_ne_zero _ hprod
  have hG : (Ideal.span {m*excludedGenerator S}:Ideal O)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hstate.mask_ne_zero he)
  have hpG : ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator S} := by
    intro P hP
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem S (hbad hP)))
  have hlabels : labels⊆idealRange F:=canonicalLabels_subset_idealRange base (∏P∈S,P) Z η Ψ m labels X F K hstate
    (fun P hP=>Finset.dvd_prod_of_mem (fun Q:Ideal O=>Q) (hbad hP))
  have hmass : X*F ≤ Z^3:=hstate.mass_le.trans (canonicalRankMass_global Z hZbig _)
  refine ⟨hG,hpG,hlabels,hmass,?_⟩
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0 ≤ X*F:=mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one)
  have hm : (3:ℝ)/80 ≤ canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K) :=
    (by linarith : (3:ℝ)/80 ≤ (1:ℝ)/20-3000*η).trans (canonicalRankMargin_lower _ η hη _)
  have hi : K*‖ringComplex m‖^2 ≤ (X*F)*Z^(-((3:ℝ)/80)):=
    hstate.invariant.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF)
  rw [←ringComplex_norm_sq_eq_absNorm_span,map_mul,norm_mul,mul_pow]
  calc
    (2*K)*(‖ringComplex m‖^2*‖ringComplex (excludedGenerator S)‖^2)=
        (2*‖ringComplex (excludedGenerator S)‖^2)*(K*‖ringComplex m‖^2):=by ring
    _  ≤  Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))):=
      mul_le_mul hfixed hi (mul_nonneg (zero_le_one.trans hstate.row_ge_one) (sq_nonneg _)) (by positivity)
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))):=by ring
    _ = _:=by rw [←Real.rpow_add hZ0]; norm_num

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma supported_factors_good (I : Ideal O) (hI : quadraticSupported I)
    (P : Ideal O) (hP : P∈normalizedFactors I) :
    P.IsMaximal ∧ lambda∉P ∧ ringChar (O⧸P)≠2 := by
  have h := primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P hI.1 hP)
  exact ⟨h.1,h.2.1,hI.2 P (Multiset.mem_toFinset.mpr hP)⟩

lemma supported_span_iff (n : O) :
    quadraticSupported (Ideal.span {n}) ↔ ¬lambda∣n ∧ ¬(2:O)∣n := by
  rw [quadraticSupported_iff_bad_not_dvd]
  have he (p : O) : (Ideal.span {p}:Ideal O)∣Ideal.span {n} ↔ p∣n := by
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]
  rw [ramifiedIdeal,he,cubicTwoIdeal,he,neg_dvd]

lemma idealRowHom_one_good (I : Ideal O) (hI : primaryIdealGenerator I≠0) :
    idealRowHom 1 I=1 := by
  have hi := primaryIdealGenerator_ne_zero_ideal I hI
  change (if I=0 then 0 else ((normalizedFactors I).map (localRowValue 1)).prod)=1
  rw [if_neg hi]
  calc
    _ = ((normalizedFactors I).map (fun _ => (1:ℂ))).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro P hP
      have hp := primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P hI hP)
      let : P.IsMaximal := hp.1
      rw [localRowValue_good _ _ hp.2.1,map_one,map_one]
    _ = 1 := by simp

lemma idealRowHom_argument_pow (a : O) (k : ℕ) (I : Ideal O)
    (hI : primaryIdealGenerator I≠0) :
    idealRowHom (a^k) I=(idealRowHom a I)^k := by
  induction k with
  | zero => simpa only [pow_zero] using idealRowHom_one_good I hI
  | succ k ih => rw [pow_succ,idealRowHom_argument_mul,ih,pow_succ]

lemma idealRowHom_congr_mod (I : Ideal O) (x y : O) (hxy : x-y∈I) :
    idealRowHom x I=idealRowHom y I := by
  by_cases hi : I=0
  · rw [hi,map_zero,map_zero]
  change (if I=0 then 0 else ((normalizedFactors I).map (localRowValue x)).prod)=
    (if I=0 then 0 else ((normalizedFactors I).map (localRowValue y)).prod)
  simp only [if_neg hi]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hp : x-y∈P :=
    Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP) hxy
  unfold localRowValue
  split_ifs with h
  · rw [Ideal.Quotient.eq.mpr hp]
  · rfl

lemma idealRowHom_eq_prime_count_product (I : Ideal O) (hI : quadraticSupported I) (n : O) :
    idealRowHom n I=∏P : primeSupport I,
      (localRowValue n P.val)^((normalizedFactors I).count P.val) := by
  have hi := primaryIdealGenerator_ne_zero_ideal I hI.1
  have he : I=∏P : primeSupport I,P.val^((normalizedFactors I).count P.val) := by
    exact ((Ideal.prod_normalizedFactors_eq_self hi).symm.trans
      (Finset.prod_multiset_count _)).trans
      (Finset.prod_coe_sort (normalizedFactors I).toFinset
        (fun P => P^((normalizedFactors I).count P))).symm
  calc
    _ = idealRowHom n (∏P : primeSupport I,P.val^((normalizedFactors I).count P.val)) :=
      congrArg (idealRowHom n) he
    _ = ∏P : primeSupport I,(idealRowHom n P.val)^((normalizedFactors I).count P.val) := by
      simp only [map_prod,map_pow]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P _
      rw [idealRowHom,primeValueHom_prime _ P.val (support_prime P.property)]

lemma sextic_power_mod_six (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (k : ℕ) (hk : k≠0) (n : O) :
    (complexSexticChar P hg (Ideal.Quotient.mk P n))^k=
      (complexSexticChar P hg^(k%6)) (Ideal.Quotient.mk P n) := by
  rw [←MulChar.pow_apply' _ hk,pow_eq_pow_mod _ (complexSexticChar_powers P hg).2.2]

/-- A denominator supported away from two and three gives a finite prime character row. -/
lemma idealRowHom_prime_character_product (I : Ideal O) (hI : quadraticSupported I) (n : O) :
    idealRowHom n I=∏P : primeSupport I,
      (letI : P.val.IsMaximal := (supported_factors_good I hI P.val
        (Multiset.mem_toFinset.mp P.property)).1
       (complexSexticChar P.val (supported_factors_good I hI P.val
        (Multiset.mem_toFinset.mp P.property)).2.1^((normalizedFactors I).count P.val%6))
        (Ideal.Quotient.mk P.val n)) := by
  rw [idealRowHom_eq_prime_count_product I hI]
  apply Finset.prod_congr rfl
  intro P _
  have hp := supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)
  let : P.val.IsMaximal := hp.1
  rw [localRowValue_good _ _ hp.2.1]
  exact sextic_power_mod_six P.val hp.2.1 _
    (Nat.ne_of_gt (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property))) n

lemma negative_two_prime : Prime (-2:O) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:O)≠0)).mp
    (show (Ideal.span {(-2:O)}).IsPrime from
      (inferInstance : cubicTwoIdeal.IsMaximal).isPrime)

/-- Removing the two ramified factors leaves a primary numerator supported away from two and three. -/
theorem exists_supported_numerator_factorization (x : O) (hx : x≠0) :
    ∃u : Oˣ,∃a b : ℕ,∃r : O,quadraticSupported (Ideal.span {r}) ∧ lambda^2∣r-1 ∧
      x=(u:O)*lambda^a*(2:O)^b*r := by
  obtain ⟨u,a,I,hI,hxform⟩ := exists_unit_lambda_primary_factor x hx
  let n := primaryIdealGenerator I
  have hn : lambda^2∣n-1 := (primaryIdealGenerator_spec I hI).2
  obtain ⟨r,hr,hrnot⟩ :=
    (FiniteMultiplicity.of_prime_left negative_two_prime hI).exists_eq_pow_mul_and_not_dvd
  let b : ℕ := multiplicity (-2:O) n
  change n=(-2:O)^b*r at hr
  have hneg : lambda^2∣(-2:O)-1 := by
    convert dvd_neg.mpr lambda_sq_dvd_three using 1 <;> ring
  have hp : lambda^2∣(-2:O)^b-1 := hneg.trans (sub_one_dvd_pow_sub_one (-2:O) b)
  have hprimary : lambda^2∣r-1 := by
    have hh := dvd_sub hn (dvd_mul_of_dvd_left hp r)
    have he : n-1-(((-2:O)^b-1)*r)=r-1 := by rw [hr];ring
    rwa [he] at hh
  have hnot2 : ¬(2:O)∣r := by
    intro h2
    exact hrnot (by simpa only [neg_dvd] using h2)
  have hnotlambda : ¬lambda∣r := by
    intro hLam
    have hsub : lambda∣r-1 := (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary
    have hone : lambda∣(1:O) := by
      convert dvd_sub hLam hsub using 1 <;> ring
    exact residue_lambda_prime.2.1 (isUnit_of_dvd_one hone)
  let v : Oˣ := u*(-1:Oˣ)^b
  refine ⟨v,a,b,r,(supported_span_iff r).mpr ⟨hnotlambda,hnot2⟩,hprimary,?_⟩
  have hp2 : (-2:O)^b=(-1:O)^b*(2:O)^b := by
    rw [show (-2:O)=(-1)*2 by ring,mul_pow]
  change x=((u:O)*lambda^a)*n at hxform
  rw [hxform,hr,hp2]
  dsimp only [v]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_neg_one]
  ring

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

def coprimalityMask (m : O) : O→*ℂ where
  toFun n := if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx : IsCoprime m x <;> by_cases hy : IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n : O) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y : O) (hxy : m∣x-y) : IsCoprime m x ↔ IsCoprime m y := by
  obtain ⟨z,hz⟩ := hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m x y : O) (hxy : x-y∈Ideal.span {m}) :
    coprimalityMask m x=coprimalityMask m y := by
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma prime_coprime_span_iff (P : Ideal O) [P.IsMaximal] (m : O) :
    IsCoprime P (Ideal.span {m}) ↔ m∉P := by
  constructor
  · intro h hm
    have hd : P∣Ideal.span {m} :=
      Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm))
    exact (inferInstance : P.IsMaximal).ne_top
      (Ideal.isUnit_iff.mp (h.isUnit_of_dvd' (dvd_refl P) hd))
  · intro hm
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra htop
    have he := Ideal.IsMaximal.eq_of_le (inferInstance : P.IsMaximal)
      htop (show P≤P⊔Ideal.span {m} from le_sup_left)
    apply hm
    rw [he]
    exact (show Ideal.span {m}≤P⊔Ideal.span {m} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton m))

lemma idealRowHom_prime_sixth_mask (m : O) (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg,prime_coprime_span_iff,map_pow,map_pow,
    ←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),(complexSexticChar_powers P hg).2.2]
  by_cases hm : m∈P
  · rw [if_neg (not_not.mpr hm),Ideal.Quotient.eq_zero_iff_mem.mpr hm,MulChar.map_zero]
  · rw [if_pos hm]
    let u : (O⧸P)ˣ := Units.mk0 (Ideal.Quotient.mk P m)
      (fun h => hm (Ideal.Quotient.eq_zero_iff_mem.mp h))
    exact MulChar.one_apply_coe u

theorem idealRowHom_sixth_mask (m : O) (I : Ideal O) (hI : quadraticSupported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s : Multiset (Ideal O))
      (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal O) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp := hs P (Multiset.mem_cons_self _ _)
      let : P.IsMaximal := hp.1
      have ht : ∀R∈s,R.IsMaximal ∧ lambda∉R := fun R hR => hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP : IsCoprime P (Ideal.span {m}) <;>
        by_cases hS : IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h := hprod (normalizedFactors I) (fun P hP =>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self (primaryIdealGenerator_ne_zero_ideal I hI.1)] at h

lemma idealRowHom_sixth_eq_mask (m n : O) (hn : quadraticSupported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ : O→*ℂ) (m f z n : O)
    (hn : quadraticSupported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

lemma rowTwist_zero_of_common_prime (Ψ : O→*ℂ) (m f z n : O)
    (P : Ideal O) (hp : Prime P) (hm : m∈P) (hn : n∈P) :
    rowTwist Ψ m f z n=0 := by
  have hPI : P∣Ideal.span {n} := Ideal.dvd_iff_le.mpr
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hn))
  have hm6 : m^6∈P := by
    rw [show m^6=m^5*m by ring]
    exact P.mul_mem_left _ hm
  have hx : m^6*f^4*z∈P := P.mul_mem_right _ (P.mul_mem_right _ hm6)
  change Ψ n*idealRowHom _ (Ideal.span {n})=0
  rw [idealRowHom_zero_of_dvd _ hp hPI hx,mul_zero]

theorem rowTwist_zero_of_not_supported (Ψ : O→*ℂ) (m f z n : O)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (hn : ¬quadraticSupported (Ideal.span {n})) :
    rowTwist Ψ m f z n=0 := by
  have hbad : lambda∣n ∨ (2:O)∣n := by
    simpa only [supported_span_iff,not_and_or,not_not] using hn
  rcases hbad with hl | h2
  · exact rowTwist_zero_of_common_prime Ψ m f z n ramifiedIdeal ramifiedIdeal_prime
      (Ideal.mem_span_singleton.mpr hmLam) (Ideal.mem_span_singleton.mpr hl)
  · exact rowTwist_zero_of_common_prime Ψ m f z n cubicTwoIdeal quadratic_twoIdeal_prime
      (Ideal.mem_span_singleton.mpr (by simpa only [neg_dvd] using hm2))
      (Ideal.mem_span_singleton.mpr (by simpa only [neg_dvd] using h2))

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CubicRamified
open scoped BigOperators Classical

/-- Integral values allow the sextic Euler criterion to be compared before complex embedding. -/
def integralSexticChar (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) : MulChar (O⧸P) O :=
  cubicChar P hg^2*(quadraticChar (O⧸P)).ringHomComp (Int.castRingHom O)

lemma integralSexticChar_complex (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) (x : O⧸P) :
    ringComplex (integralSexticChar P hg x)=complexSexticChar P hg x := by
  simp only [integralSexticChar,complexSexticChar,complexCubicChar,complexQuadraticChar,
    MulChar.mul_apply,MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),
    MulChar.ringHomComp_apply,map_mul,map_pow]
  congr 1
  change ringComplex (quadraticChar (O⧸P) x : O)=(quadraticChar (O⧸P) x : ℂ)
  exact map_intCast ringComplex _

lemma integralSexticChar_sixth (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (u : (O⧸P)ˣ) : integralSexticChar P hg (u:O⧸P)^6=1 := by
  apply ringComplex_injective
  rw [map_pow,map_one,integralSexticChar_complex,
    ←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),(complexSexticChar_powers P hg).2.2]
  exact MulChar.one_apply_coe u

theorem integralSexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (O⧸P)≠2) (u : (O⧸P)ˣ) :
    Ideal.Quotient.mk P (integralSexticChar P hg (u:O⧸P))=
      (u:O⧸P)^((Nat.card (O⧸P)-1)/6) := by
  let N := Fintype.card (O⧸P)
  let m := (N-1)/6
  have hthree : 3∣N-1 := by
    simpa only [N,Nat.card_eq_fintype_card] using card_sub_one_div_three P hg
  have hodd : N%2=1 := FiniteField.odd_card_of_char_ne_two hc
  have hN : 1<N := Fintype.one_lt_card
  have hsix : 6∣N-1 := by omega
  have hsize : N-1=6*m := by
    dsimp [m]
    exact (Nat.mul_div_cancel_left' hsix).symm
  have hthird : (N-1)/3=2*m := by omega
  have hhalf : N/2=3*m := by omega
  let ρ : O→+*O⧸P := Ideal.Quotient.mk P
  have hquad : ρ ((quadraticChar (O⧸P)).ringHomComp (Int.castRingHom O) (u:O⧸P))=
      (u:O⧸P)^(N/2) := by
    change (quadraticChar (O⧸P) (u:O⧸P):O⧸P)=_
    exact quadraticChar_eq_pow_of_char_ne_two' hc (u:O⧸P)
  have hcub : ρ (cubicChar P hg (u:O⧸P))=(u:O⧸P)^((N-1)/3) := by
    simpa only [N,Nat.card_eq_fintype_card] using cubicChar_reduce P hg (u:O⧸P)
  have hfermat : (u:O⧸P)^(N-1)=1 := FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hg^2*(quadraticChar (O⧸P)).ringHomComp (Int.castRingHom O)) (u:O⧸P))=_
  rw [MulChar.mul_apply,MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),map_mul,map_pow,hcub,hquad,
    hthird,hhalf]
  change ((u:O⧸P)^(2*m))^2*(u:O⧸P)^(3*m)=(u:O⧸P)^((Nat.card (O⧸P)-1)/6)
  rw [Nat.card_eq_fintype_card]
  change ((u:O⧸P)^(2*m))^2*(u:O⧸P)^(3*m)=(u:O⧸P)^m
  calc
    _ = (u:O⧸P)^(7*m) := by rw [←pow_mul,←pow_add];congr 1;omega
    _ = (u:O⧸P)^m*(u:O⧸P)^(N-1) := by rw [hsize,←pow_add];congr 1;omega
    _ = _ := by rw [hfermat,mul_one]

theorem sixth_roots_reduce_injective (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (O⧸P)≠2) {x y : O}
    (hx : x^6=1) (hy : y^6=1)
    (hxy : Ideal.Quotient.mk P x=Ideal.Quotient.mk P y) : x=y := by
  have hs : x^2=y^2 := cubic_roots_reduce_injective P hg
    (by simpa only [←pow_mul] using hx)
    (by simpa only [←pow_mul] using hy)
    (by simpa only [map_pow] using congrArg (fun z : O⧸P => z^2) hxy)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · exact h
  · have hy0 : Ideal.Quotient.mk P y≠0 := by
      intro hz
      have he := congrArg (Ideal.Quotient.mk P) hy
      simp only [map_pow,map_one,hz,zero_pow (by decide : (6:ℕ)≠0)] at he
      exact zero_ne_one he
    have he : -(Ideal.Quotient.mk P y)=Ideal.Quotient.mk P y := by
      simpa only [h,map_neg] using hxy
    have htwo : (2:O⧸P)*Ideal.Quotient.mk P y=0 := by linear_combination -he
    exact False.elim ((Ring.two_ne_zero hc) ((mul_eq_zero.mp htwo).resolve_right hy0))

lemma unit_pow_six (u : Oˣ) : (u:O)^6=1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have he : (η:O)^6=1 := by rw [hη,omega_six]
  have hp : ((η:O)^2)^6=1 := by
    rw [←pow_mul,Nat.mul_comm 2 6,pow_mul,he,one_pow]
  have hu : u∈([1,-1,η,-η,η^2,-η^2]:List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_pow 6
  · change (-1:O)^6=1
    norm_num
  · exact he
  · change (-(η:O))^6=1
    simpa only [neg_pow,show (-1:O)^6=1 by norm_num,one_mul] using he
  · exact hp
  · change (-((η:O)^2))^6=1
    simpa only [neg_pow,show (-1:O)^6=1 by norm_num,one_mul] using hp

theorem complexSextic_unit_euler (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (O⧸P)≠2) (u : Oˣ) :
    complexSexticChar P hg (Ideal.Quotient.mk P (u:O))=
      ringComplex ((u:O)^((Nat.card (O⧸P)-1)/6)) := by
  let v : (O⧸P)ˣ := Units.map (Ideal.Quotient.mk P).toMonoidHom u
  have hx := integralSexticChar_sixth P hg v
  have hy : ((u:O)^((Nat.card (O⧸P)-1)/6))^6=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul,unit_pow_six,one_pow]
  have he : integralSexticChar P hg (v:O⧸P)=(u:O)^((Nat.card (O⧸P)-1)/6) :=
    sixth_roots_reduce_injective P hg hc hx hy
      (by
        rw [map_pow]
        exact integralSexticChar_reduce_unit P hg hc v)
  rw [←integralSexticChar_complex]
  exact congrArg ringComplex he

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma good_prime_norm_mod_six (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (O⧸P)≠2) : Ideal.absNorm P%6=1 := by
  have ht := card_sub_one_div_three P hg
  have ho := FiniteField.odd_card_of_char_ne_two hc
  have hN : 1<Fintype.card (O⧸P) := Fintype.one_lt_card
  have hn : Ideal.absNorm P=Fintype.card (O⧸P) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card] at ht
  rw [hn]
  omega

lemma unit_sixth_exponent_mul (u : Oˣ) (a b : ℕ) (ha : a%6=1) (hb : b%6=1) :
    (u:O)^((a*b-1)/6)=(u:O)^((a-1)/6)*(u:O)^((b-1)/6) := by
  have ha' : a=6*(a/6)+1 := by omega
  have hb' : b=6*(b/6)+1 := by omega
  have hab : a*b=6*(a/6+b/6+6*((a/6)*(b/6)))+1 := by
    calc
      a*b=(6*(a/6)+1)*(6*(b/6)+1) := congrArg₂ (·*·) ha' hb'
      _ = _ := by ring
  have hab' : (a*b-1)/6=a/6+b/6+6*((a/6)*(b/6)) := by omega
  have hda : (a-1)/6=a/6 := by omega
  have hdb : (b-1)/6=b/6 := by omega
  rw [hab',hda,hdb,pow_add,pow_add,pow_mul,unit_pow_six,one_pow,mul_one]

lemma multiset_unit_norm (u : Oˣ) (s : Multiset (Ideal O))
    (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P ∧ ringChar (O⧸P)≠2) :
    (s.map (localRowValue (u:O))).prod=
      ringComplex ((u:O)^(((s.map Ideal.absNorm).prod-1)/6)) ∧
      (s.map Ideal.absNorm).prod%6=1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    have hp := hs P (Multiset.mem_cons_self _ _)
    let : P.IsMaximal := hp.1
    have htail : ∀Q∈s,Q.IsMaximal ∧ lambda∉Q ∧ ringChar (O⧸Q)≠2 :=
      fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hv,hn⟩ := ih htail
    have hP := good_prime_norm_mod_six P hp.2.1 hp.2.2
    simp only [Multiset.map_cons,Multiset.prod_cons]
    refine ⟨?_,by rw [Nat.mul_mod,hP,hn]⟩
    rw [localRowValue_good _ P hp.2.1,complexSextic_unit_euler P hp.2.1 hp.2.2,hv]
    have hcard : Nat.card (O⧸P)=Ideal.absNorm P := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
    rw [hcard,unit_sixth_exponent_mul u _ _ hP hn,map_mul]

lemma multiset_norm_product (s : Multiset (Ideal O)) :
    (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]

theorem idealRowHom_unit_norm (u : Oˣ) (I : Ideal O) (hI : quadraticSupported I) :
    idealRowHom (u:O) I=ringComplex ((u:O)^((Ideal.absNorm I-1)/6)) := by
  have hi := primaryIdealGenerator_ne_zero_ideal I hI.1
  have hh := (multiset_unit_norm u (normalizedFactors I) (supported_factors_good I hI)).1
  rw [multiset_norm_product,Ideal.prod_normalizedFactors_eq_self hi] at hh
  change (if I=0 then 0 else _)=_
  rwa [if_neg hi]

lemma ideal_norm_mod_six_of_good (I : Ideal O) (hI : quadraticSupported I) :
    Ideal.absNorm I%6=1 := by
  have hh := (multiset_unit_norm (1:Oˣ) (normalizedFactors I) (supported_factors_good I hI)).2
  rwa [multiset_norm_product,Ideal.prod_normalizedFactors_eq_self
    (primaryIdealGenerator_ne_zero_ideal I hI.1)] at hh

theorem idealRowHom_unit_eq_of_norm_mod_thirty_six (u : Oˣ) (I J : Ideal O)
    (hI : quadraticSupported I) (hJ : quadraticSupported J)
    (hmod : Ideal.absNorm I%36=Ideal.absNorm J%36) :
    idealRowHom (u:O) I=idealRowHom (u:O) J := by
  rw [idealRowHom_unit_norm u I hI,idealRowHom_unit_norm u J hJ]
  have hmi := ideal_norm_mod_six_of_good I hI
  have hmj := ideal_norm_mod_six_of_good J hJ
  have hm : (Ideal.absNorm I-1)/6 ≡ (Ideal.absNorm J-1)/6 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  exact congrArg ringComplex (pow_eq_pow_of_modEq hm (unit_pow_six u))

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson UniqueFactorizationMonoid
open Eisenstein.Coordinates (eval coords eval_coords)
open scoped BigOperators Classical

lemma norm_eval_residue (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}):ZMod m)=
      (a:ZMod m)^2-(a:ZMod m)*(b:ZMod m)+(b:ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}):ℤ)=a^2-a*b+b^2 := by
    have h := ringComplex_norm_sq_eq_absNorm_span (eval a b)
    rw [Coordinates.complex_norm_eval_sq] at h
    exact_mod_cast h.symm
  have hz := congrArg (fun k : ℤ => (k:ZMod m)) hi
  push_cast at hz
  exact hz

lemma norm_residue_congruent (m : ℕ) (x y : O)
    (hxy : x-y∈(Ideal.span {(m:O)}:Ideal O)) :
    Ideal.absNorm (Ideal.span {x})%m=Ideal.absNorm (Ideal.span {y})%m := by
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f) := by
    calc
      x=y+(m:O)*z := by linear_combination hz
      _ = eval (c+(m:ℤ)*e) (d+(m:ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  apply (ZMod.natCast_eq_natCast_iff' _ _ m).mp
  rw [hx,hy,norm_eval_residue,norm_eval_residue]
  simp

lemma supported_span_congruent_mod_thirty_six (x y : O)
    (hxy : x-y∈(Ideal.span {(36:O)}:Ideal O)) :
    quadraticSupported (Ideal.span {x}) ↔ quadraticSupported (Ideal.span {y}) := by
  have h36 : (36:O)∣x-y := Ideal.mem_span_singleton.mp hxy
  have hl : lambda∣(36:O) :=
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three).trans ⟨12,by norm_num⟩
  have ht : (2:O)∣(36:O) := ⟨18,by norm_num⟩
  have he (a : O) (ha : a∣x-y) : a∣x ↔ a∣y := by
    constructor
    · intro hx
      convert dvd_sub hx ha using 1 <;> ring
    · intro hy
      convert dvd_add ha hy using 1 <;> ring
  rw [supported_span_iff,supported_span_iff,he lambda (hl.trans h36),he 2 (ht.trans h36)]

def supportedIdealRow (a : O) : O→*ℂ where
  toFun n := if quadraticSupported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs : quadraticSupported (1:Ideal O) := by
      refine ⟨by rw [primaryIdealGenerator_one];exact one_ne_zero,?_⟩
      intro P hP
      simp only [primeSupport,normalizedFactors_one,Multiset.toFinset_zero,Finset.notMem_empty] at hP
    rw [show Ideal.span {(1:O)}=(1:Ideal O) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      if_pos hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,quadraticSupported_mul,map_mul]
    by_cases hx : quadraticSupported (Ideal.span {x}) <;>
      by_cases hy : quadraticSupported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n : O) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

def unitSupplement (u : Oˣ) : O→*ℂ := supportedIdealRow (u:O)

lemma unitSupplement_norm (u : Oˣ) (n : O) : ‖unitSupplement u n‖≤1 :=
  supportedIdealRow_norm (u:O) n

theorem unitSupplement_periodic (u : Oˣ) (x y : O)
    (hxy : x-y∈(Ideal.span {(36:O)}:Ideal O)) : unitSupplement u x=unitSupplement u y := by
  have hs := supported_span_congruent_mod_thirty_six x y hxy
  change (if _ then _ else _)=(if _ then _ else _)
  by_cases hx : quadraticSupported (Ideal.span {x})
  · have hy := hs.mp hx
    rw [if_pos hx,if_pos hy]
    exact idealRowHom_unit_eq_of_norm_mod_thirty_six u _ _ hx hy (norm_residue_congruent 36 x y hxy)
  · rw [if_neg hx,if_neg (fun hy => hx (hs.mpr hy))]

theorem rowTwist_unitSupplement (Ψ : O→*ℂ) (m f z : O) (u : Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    rowTwist Ψ m f ((u:O)*z)=unitSupplement u*rowTwist Ψ m f z := by
  ext n
  by_cases hn : quadraticSupported (Ideal.span {n})
  · change Ψ n*idealRowHom (m^6*f^4*((u:O)*z)) (Ideal.span {n})=
      (if quadraticSupported (Ideal.span {n}) then _ else 0)*(Ψ n*idealRowHom _ (Ideal.span {n}))
    rw [if_pos hn,show m^6*f^4*((u:O)*z)=(u:O)*(m^6*f^4*z) by ring,idealRowHom_argument_mul]
    ring
  · change rowTwist Ψ m f ((u:O)*z) n=
      (if quadraticSupported (Ideal.span {n}) then _ else 0)*_
    rw [rowTwist_zero_of_not_supported Ψ m f _ n hmLam hm2 hn,if_neg hn,zero_mul]

theorem rowTwist_unitSupplement_base (Ψ : O→*ℂ) (m f z : O) (u : Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    rowTwist Ψ m f ((u:O)*z)=rowTwist (unitSupplement u*Ψ) m f z := by
  rw [rowTwist_unitSupplement Ψ m f z u hmLam hm2]
  ext n
  change unitSupplement u n*(Ψ n*idealRowHom _ _)=(unitSupplement u n*Ψ n)*idealRowHom _ _
  ring

end CanonicalRowCompletion

namespace CanonicalRowCompletion.FixedRayArithmetic
open Eisenstein Eisenstein.Coordinates QuadraticPhase.Eisenstein
open scoped BigOperators Classical

/-- `i^k` for `k` modulo four, in `ℤ[i]`. -/
def ipow (k : ZMod 4) : GaussianInt := (⟨0, 1⟩ : GaussianInt) ^ k.val

/-- `2Γ` at the coordinates `(a, b)` modulo four. -/
def twoGamma (a b : ZMod 4) : GaussianInt := 1 + ipow (-b) + ipow a + ipow (b - a)

/-- The coordinates of a product, `(a + bω)(c + dω)`. -/
def mulFst (a b c d : ZMod 4) : ZMod 4 := a * c - b * d

def mulSnd (a b c d : ZMod 4) : ZMod 4 := a * d + b * c - b * d

/-- Odd coordinates: not both even. -/
abbrev oddCoord (a b : ZMod 4) : Prop := ¬ (2 ∣ a.val ∧ 2 ∣ b.val)

theorem twoGamma_ne_zero : ∀ a b : ZMod 4, oddCoord a b → twoGamma a b ≠ 0 := by decide

theorem twoGamma_pow_four : ∀ a b : ZMod 4, oddCoord a b → twoGamma a b ^ 4 = 16 := by
  decide

theorem twoGamma_mul_sq : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    twoGamma (mulFst a b (mulFst c d c d) (mulSnd c d c d))
      (mulSnd a b (mulFst c d c d) (mulSnd c d c d)) = twoGamma a b := by
  decide

theorem twoGamma_sq_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    4 * twoGamma (mulFst a b c d) (mulSnd a b c d) ^ 2 = twoGamma a b ^ 2 * twoGamma c d ^ 2 := by
  decide

theorem twoGamma_cocycle : ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ZMod 4, oddCoord a₁ b₁ →
    oddCoord a₂ b₂ → oddCoord a₃ b₃ →
    twoGamma (mulFst (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) a₃ b₃)
        (mulSnd (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) a₃ b₃) *
      twoGamma a₁ b₁ * twoGamma a₂ b₂ * twoGamma a₃ b₃ =
    2 * twoGamma (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) *
      twoGamma (mulFst a₁ b₁ a₃ b₃) (mulSnd a₁ b₁ a₃ b₃) *
        twoGamma (mulFst a₂ b₂ a₃ b₃) (mulSnd a₂ b₂ a₃ b₃) := by
  decide



/-- `i^k = i^{k mod 4}`. -/
theorem I_zpow_eq_ipow (k : ℤ) : Complex.I ^ k = GaussianInt.toComplex (ipow k) := by
  rw [ipow, map_pow, show GaussianInt.toComplex ⟨0, 1⟩ = Complex.I by
    simp [GaussianInt.toComplex_def], ← zpow_natCast, ZMod.val_intCast]
  have hk : k = 4 * (k / 4) + k % ((4 : ℕ) : ℤ) := by omega
  conv_lhs => rw [hk]
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, show Complex.I ^ (4 : ℤ) = 1 by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, Complex.I_pow_four],
    one_zpow, one_mul]

/-- Oddness of `a + bω` in coordinates. -/
theorem oddCoord_of_not_mem (a b : ℤ) (h2 : eval a b ∉ Ideal.span {(2 : O)}) :
    oddCoord (a : ZMod 4) (b : ZMod 4) := by
  rintro ⟨ha, hb⟩
  obtain ⟨a', rfl⟩ : (2 : ℤ) ∣ a := by have := ZMod.val_intCast (n := 4) a; omega
  obtain ⟨b', rfl⟩ : (2 : ℤ) ∣ b := by have := ZMod.val_intCast (n := 4) b; omega
  apply h2
  rw [Ideal.mem_span_singleton]
  refine ⟨eval a' b', ?_⟩
  simp only [eval]
  push_cast
  ring

theorem mulFst_cast (a b c d : ℤ) :
    mulFst (a : ZMod 4) (b : ZMod 4) (c : ZMod 4) (d : ZMod 4) = ((a * c - b * d : ℤ) : ZMod 4) := by
  simp only [mulFst]; push_cast; ring

theorem mulSnd_cast (a b c d : ℤ) :
    mulSnd (a : ZMod 4) (b : ZMod 4) (c : ZMod 4) (d : ZMod 4) =
      ((a * d + b * c - b * d : ℤ) : ZMod 4) := by
  simp only [mulSnd]; push_cast; ring

/-- `Γ(a + bω) = T(a mod 4, b mod 4)/2`, written with the dual average (no proof argument). -/
theorem fixedDualAverage_eval (a b : ℤ) :
    fixedDualAverage (eval a b) = GaussianInt.toComplex (twoGamma (a : ZMod 4) (b : ZMod 4)) / 2 := by
  rw [fixedDualAverage_formula, twoGamma, map_add, map_add, map_add, map_one, I_zpow_eq_ipow,
    I_zpow_eq_ipow, I_zpow_eq_ipow]
  push_cast
  ring

/-- Every element has integer coordinates. -/
theorem exists_eval (c : O) : ∃ a b : ℤ, c = eval a b := ⟨_, _, (eval_coords c).symm⟩

/-- **The cocycle.** For odd `c, d, e`: `Γ(cde) Γ(c) Γ(d) Γ(e) = Γ(cd) Γ(ce) Γ(de)`. -/
theorem gamma_cocycle {c d e : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)})
    (he : e ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d * e) * fixedDualAverage c * fixedDualAverage d * fixedDualAverage e =
      fixedDualAverage (c * d) * fixedDualAverage (c * e) * fixedDualAverage (d * e) := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  obtain ⟨a₃, b₃, rfl⟩ := exists_eval e
  have h := congrArg GaussianInt.toComplex (twoGamma_cocycle (a₁ : ZMod 4) b₁ a₂ b₂ a₃ b₃
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd) (oddCoord_of_not_mem _ _ he))
  simp only [mulFst_cast, mulSnd_cast, map_mul, map_ofNat] at h
  simp only [eval_mul, fixedDualAverage_eval]
  linear_combination h / 16

/-- **The sign.** For odd `c, d`: `Γ(cd)² = Γ(c)² Γ(d)²`. -/
theorem gamma_mul_sq_eq {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d) ^ 2 = fixedDualAverage c ^ 2 * fixedDualAverage d ^ 2 := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  have h := congrArg GaussianInt.toComplex (twoGamma_sq_mul (a₁ : ZMod 4) b₁ a₂ b₂
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd))
  simp only [mulFst_cast, mulSnd_cast, map_mul, map_pow, map_ofNat] at h
  simp only [eval_mul, fixedDualAverage_eval]
  linear_combination h / 16

/-- **Nonvanishing** on the odd classes. -/
theorem gamma_ne_zero {c : O} (hc : c ∉ Ideal.span {(2 : O)}) : fixedDualAverage c ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  rw [fixedDualAverage_eval, div_ne_zero_iff]
  refine ⟨fun h => twoGamma_ne_zero _ _ (oddCoord_of_not_mem _ _ hc) ?_, two_ne_zero⟩
  exact GaussianInt.toComplex_injective (by rw [h, map_zero])

/-- `Γ(c)⁴ = 1` on the odd classes. -/
theorem gamma_pow_four {c : O} (hc : c ∉ Ideal.span {(2 : O)}) : fixedDualAverage c ^ 4 = 1 := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  have h := congrArg GaussianInt.toComplex (twoGamma_pow_four (a : ZMod 4) b
    (oddCoord_of_not_mem _ _ hc))
  simp only [map_pow, map_ofNat] at h
  rw [fixedDualAverage_eval, div_pow, h]
  norm_num

/-- **Square classes.** For odd `c, d`: `Γ(cd²) = Γ(c)`. -/
theorem gamma_mul_sq {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d ^ 2) = fixedDualAverage c := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  have h := congrArg GaussianInt.toComplex (twoGamma_mul_sq (a₁ : ZMod 4) b₁ a₂ b₂
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd))
  simp only [mulFst_cast, mulSnd_cast] at h
  rw [sq, eval_mul, eval_mul, fixedDualAverage_eval, fixedDualAverage_eval, h]



/-- The quadratic reciprocity phase `r(c, d) = Γ(cd)/(Γ(c)Γ(d))`. -/
def quadraticPhase (c d : O) : ℂ :=
  fixedDualAverage (c * d) / (fixedDualAverage c * fixedDualAverage d)

theorem quadraticPhase_comm (c d : O) : quadraticPhase c d = quadraticPhase d c := by
  rw [quadraticPhase, quadraticPhase, mul_comm c d, mul_comm (fixedDualAverage c)]

theorem oddCoord_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    oddCoord (mulFst a b c d) (mulSnd a b c d) := by
  decide

/-- Odd coordinates give an element outside `(2)`. -/
theorem not_mem_of_oddCoord (a b : ℤ) (h : oddCoord (a : ZMod 4) (b : ZMod 4)) :
    eval a b ∉ Ideal.span {(2 : O)} := by
  intro hmem
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨a', b', rfl⟩ := exists_eval z
  have h2 : eval (2 * a') (2 * b') = eval a b := by
    rw [← hz]
    simp only [eval]
    push_cast
    ring
  obtain ⟨ha, hb⟩ := unique_coordinates h2
  apply h
  constructor
  · have := ZMod.val_intCast (n := 4) a
    omega
  · have := ZMod.val_intCast (n := 4) b
    omega

/-- A product of odd elements is odd. -/
theorem odd_mul {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    c * d ∉ Ideal.span {(2 : O)} := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  rw [eval_mul]
  apply not_mem_of_oddCoord
  have h := oddCoord_mul _ _ _ _ (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd)
  rwa [mulFst_cast, mulSnd_cast] at h

/-- `r` is multiplicative in its first argument on the odd classes. -/
theorem quadraticPhase_mul_left {c d e : O} (hc : c ∉ Ideal.span {(2 : O)})
    (hd : d ∉ Ideal.span {(2 : O)}) (he : e ∉ Ideal.span {(2 : O)}) :
    quadraticPhase (c * d) e = quadraticPhase c e * quadraticPhase d e := by
  have h := gamma_cocycle hc hd he
  have h1 := gamma_ne_zero hc
  have h2 := gamma_ne_zero hd
  have h3 := gamma_ne_zero he
  have h12 := gamma_ne_zero (odd_mul hc hd)
  unfold quadraticPhase
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h12 h3)
    (mul_ne_zero (mul_ne_zero h1 h3) (mul_ne_zero h2 h3))]
  linear_combination fixedDualAverage e * h

/-- `r` is a sign on the odd classes. -/
theorem quadraticPhase_sq {c d : O} (hc : c ∉ Ideal.span {(2 : O)})
    (hd : d ∉ Ideal.span {(2 : O)}) : quadraticPhase c d ^ 2 = 1 := by
  have h1 := gamma_ne_zero hc
  have h2 := gamma_ne_zero hd
  rw [quadraticPhase, div_pow, gamma_mul_sq_eq hc hd, mul_pow, div_self
    (mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2))]


end CanonicalRowCompletion.FixedRayArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
