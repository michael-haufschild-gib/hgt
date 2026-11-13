/-
Canonical cube separation adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalRankInduction

/-!
# Canonical cube separation

Column window radii and source log profiles of the separated cube coefficients
(`CanonicalCubeSeparation`). Local reflected brackets with square-root Gauss normalization;
canonical quadratic rows factor over their prime support.
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

namespace CanonicalCubeSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

lemma weighted_schwartz_integrable (b : 𝓢(ℝ,ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1+‖t‖)^J*‖b t‖) := by
  let c := fourierPointBound (J+2) (profileSourceBound (𝓕⁻ b) (J+2))
  have hb (t : ℝ) : ‖b t‖ ≤ c*firstLogDensity J t := by
    simpa [c] using profile_fourier_envelope (𝓕⁻ b) J t
  apply ((firstLogDensity_integrable 0).const_mul c).mono'
  · exact ((continuous_const.add continuous_norm).pow J |>.mul b.continuous.norm).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1+‖t‖)^J*‖b t‖)]
    calc
      _ ≤ (1+‖t‖)^J*(c*firstLogDensity J t) := mul_le_mul_of_nonneg_left (hb t) (by positivity)
      _ = c*firstLogDensity 0 t := by rw [mul_left_comm,mul_comm ((1+‖t‖)^J) (firstLogDensity J t),density_weight_identity]

end CanonicalCubeSeparation

namespace CanonicalCubeSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

lemma columnWindowRadius_nonneg (a b : ℝ) : 0 ≤ columnWindowRadius a b := by
  unfold columnWindowRadius
  positivity

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * kernelLogPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, kernelLogPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma active_column_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (t u : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hWu : W (Real.exp (u+3*t)) ≠ 0) :
    |u| ≤ columnWindowRadius a b := by
  have hab := hs hWu
  have hlo : Real.log a ≤ u+3*t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hab.1
  have hhi : u+3*t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hab.2
  unfold columnWindowRadius
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b), ht.1, ht.2]

lemma reopening_integrable (b V : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * cubeFrequencyFactor t ξ * frequencyTwist V ξ u) := by
  have hi : Integrable (fun ξ : ℝ =>
      b ξ * ((Real.exp (t/2) : ℂ) * kernelLogPhase ξ (3*t) * (kernelLogPhase ξ u * V u))) := by
    apply b.integrable.mul_bdd (c := Real.exp (t/2) * ‖V u‖)
    · exact (((kernelLogPhase_continuous_left (3*t)).const_mul _).mul
        ((kernelLogPhase_continuous_left u).mul_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => by
        simp only [norm_mul, kernelLogPhase_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul, mul_one, le_refl])
  apply hi.congr
  filter_upwards [] with ξ
  rw [frequencyTwist_apply]
  unfold cubeFrequencyFactor
  ring

theorem reopening_separation_with_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (t u : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
        cubeFrequencyFactor t ξ * frequencyTwist V ξ u := by
  have hwindow : V u * W (Real.exp (u+3*t)) = W (Real.exp (u+3*t)) := by
    by_cases hz : W (Real.exp (u+3*t)) = 0
    · simp [hz]
    · rw [hV u (active_column_window W a b ha hs t u ht hz), one_mul]
  have hinv := schwartz_phase_inversion
    (sourceLogProfile W a b ha hs hW) (u+3*t)
  change W (Real.exp (u+3*t)) =
    ∫ ξ : ℝ, kernelLogPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ at hinv
  calc
    _ = ((Real.exp (t/2) : ℂ) * V u) * W (Real.exp (u+3*t)) := by
      rw [mul_assoc, hwindow]
    _ = ∫ ξ : ℝ, ((Real.exp (t/2) : ℂ) * V u) *
        (kernelLogPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ) := by
      rw [hinv, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [kernelLogPhase_add, frequencyTwist_apply]
      unfold cubeFrequencyFactor
      ring

theorem exists_reopening_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ V : 𝓢(ℝ,ℂ), HasCompactSupport V ∧
      (∀ u, |u| ≤ columnWindowRadius a b → V u = 1) ∧
      (∀ u, V u ≠ 0 → |u| ≤ columnWindowRadius a b + 1) ∧
      (∀ t u : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
          ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
            cubeFrequencyFactor t ξ * frequencyTwist V ξ u) ∧
      (∀ t u : ℝ, Integrable (fun ξ : ℝ => reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor t ξ * frequencyTwist V ξ u)) ∧
      (∀ J : ℕ, ∃ C : ℝ, 0 < C ∧
        Integrable (fun ξ : ℝ => (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ∧
        (∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ≤ C ∧
        ∀ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖ ≤ C * firstLogDensity J ξ) := by
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff
    (columnWindowRadius a b) (columnWindowRadius_nonneg a b)
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  have hVone : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1 := hvone
  refine ⟨V,hvc,hVone,?_,?_,reopening_integrable _ V,?_⟩
  · intro u hu
    have hmem := hvsupp (subset_tsupport v hu)
    exact abs_le.mpr hmem
  · exact fun t u ht => reopening_separation_with_window W a b ha hs hW V hVone t u ht
  · intro J
    let g := sourceLogProfile W a b ha hs hW
    let c := fourierPointBound (J+2) (profileSourceBound g (J+2))
    let m := ∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖
    have hc : 0 ≤ c := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
    have hm : 0 ≤ m := integral_nonneg (fun ξ => by positivity)
    refine ⟨1+c+m,by positivity,weighted_schwartz_integrable _ J,by dsimp [m]; linarith,?_⟩
    intro ξ
    exact (profile_fourier_envelope g J ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith : c ≤ 1+c+m) (firstLogDensity_nonneg J ξ))

end CanonicalCubeSeparation

namespace CanonicalCubeSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← JointLogSeparation.sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn

theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]

lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn

theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  apply hi.congr
  filter_upwards [] with ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_filter (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f z : O) (H : Finset ι→ℂ)
    (keep : (ι→₀ℕ)→Prop) [DecidablePred keep]
    (hβ : ∀v∈Q,¬keep v→β v=0) :
    reopenedCanonicalRow p hg pool Q β Ψ m f H z=
      reopenedCanonicalRow p hg pool (Q.filter keep) β Ψ m f H z := by
  unfold reopenedCanonicalRow
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬keep v := fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  simp only [hβ v hv hn,zero_mul,Finset.sum_const_zero]

theorem reopenedCanonicalRow_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f z : O) (H : Finset ι→ℂ)
    (hβ : ∀v∈Q,β v=0) :
    reopenedCanonicalRow p hg pool Q β Ψ m f H z=0 := by
  unfold reopenedCanonicalRow
  apply Finset.sum_eq_zero
  intro v hv
  simp only [hβ v hv,zero_mul,Finset.sum_const_zero]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson Filter
open scoped BigOperators Classical SchwartzMap ContDiff Topology
def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0

theorem positiveRadialProfile_support (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    by_contra hn
    exact hx (by simp [positiveRadialProfile,hn])
  have hlog : |Real.log x| ≤ A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A)  ≤  Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _  ≤  Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2

theorem positiveRadialProfile_compact (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)

theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s| ≤ A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,if_pos hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he

def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)

@[simp] theorem radialFromLog_apply_pos (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) (x : ℝ) (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,if_pos hx]

theorem radialFromLog_hasCompactSupport (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) : HasCompactSupport (radialFromLog V hVs A hV) :=
  positiveRadialProfile_compact V A hV

theorem radialFromLog_support (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) (x : ℝ) (hx : radialFromLog V hVs A hV x≠0) :
    Real.exp (-A) ≤ x ∧ x ≤ Real.exp A := positiveRadialProfile_support V A hV x hx

theorem radialFromLog_column {ι : Type*} (p : ι → O)
    (hp : ∀i,p i≠0) (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s| ≤ A) (X : ℝ) (hX : 0<X) (S : Finset ι) :
    radialFromLog V hVs A hV (primeProductNorm p S/X)=
      V (columnLog p X S) :=
  radialFromLog_apply_pos V hVs A hV _ (div_pos (primeProductNorm_pos p hp S) hX)

end SecondPassArithmetic

namespace SecondPassArithmetic

open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

variable {ι:Type*} [DecidableEq ι] (p:ι→O) (hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
include hp
theorem reopenedCanonicalRow_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f z : O) (g : 𝓢(ℝ,ℂ))
    (X oldHeight newHeight : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hg pool Q β (normHeightTwist Ψ oldHeight) m f
      (fun S=>frequencyTwist g newHeight (columnLog p X S)) z‖=
    ‖reopenedCanonicalRow p hg pool Q β Ψ m f
      (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hg pool Q β
      (normHeightTwist Ψ oldHeight) m f z g X newHeight hX,
    normHeightTwist_twice,
    reopenedCanonicalRow_frequencyTwist_norm p hp hg pool Q β Ψ m f z g X
      (oldHeight+newHeight) hX]

theorem reopenedCanonicalEnergy_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (g : 𝓢(ℝ,ℂ)) (X Ksrc oldHeight newHeight : ℝ) (hX : 0<X) :
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hg pool Q (β I) (normHeightTwist Ψ oldHeight) m
        (cubicIdealGenerator I)
        (fun S=>frequencyTwist g newHeight (columnLog p X S))) Ksrc).re=
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hg pool Q (β I) Ψ m
        (cubicIdealGenerator I)
        (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S))) Ksrc).re := by
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro I hI
  unfold nonzeroRowMajorantSum
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_two_heights p hp hg pool Q (β I) Ψ m _ z g X oldHeight newHeight hX]

end SecondPassArithmetic

namespace CanonicalCubeSeparation

open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
lemma columnWindowRadius_exp (A : ℝ) (hA : 0 ≤ A) :
    columnWindowRadius (Real.exp (-A)) (Real.exp A)=2*A+3 := by
  rw [columnWindowRadius,Real.log_exp,Real.log_exp,abs_neg,abs_of_nonneg hA]
  ring

theorem fixed_reopening_profiles (A : ℝ) (hA : 0 ≤ A) :
    ∃g V : 𝓢(ℝ,ℂ), HasCompactSupport (g:ℝ → ℂ) ∧ HasCompactSupport (V:ℝ → ℂ) ∧
      (∀u,|u| ≤ columnWindowRadius (Real.exp (-A)) (Real.exp A) → g u=1) ∧
      (∀u,g u≠0 → |u| ≤ 2*A+4) ∧
      (∀u,g u≠0 → V u=1) ∧
      (∀u,V u≠0 → |u| ≤ 2*A+5) := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩:=JointLogSeparation.exists_complex_smooth_cutoff (2*A+3) (by linarith)
  obtain ⟨v,hvc,hvs,hvone,hvsupp,hvzero⟩:=JointLogSeparation.exists_complex_smooth_cutoff (2*A+4) (by linarith)
  let gs : 𝓢(ℝ,ℂ):=hgc.toSchwartzMap hgs
  let vs : 𝓢(ℝ,ℂ):=hvc.toSchwartzMap hvs
  have hgbound : ∀u,g u≠0 → |u| ≤ 2*A+4 := by
    intro u hu
    have hh:=abs_le.mpr (hgsupp (subset_tsupport g hu))
    linarith
  refine ⟨gs,vs,hgc,hvc,?_,hgbound,?_,?_⟩
  · intro u hu
    exact hgone u (by simpa only [columnWindowRadius_exp A hA] using hu)
  · intro u hu
    exact hvone u (hgbound u hu)
  · intro u hu
    have hh:=abs_le.mpr (hvsupp (subset_tsupport v hu))
    linarith

lemma fixed_reopening_child_radius (A : ℝ) : (2*A+4)+7=2*A+11 := by ring

end CanonicalCubeSeparation

namespace CanonicalCubeSeparation

open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
def radiusIter (A : ℝ) : ℕ→ℝ
  | 0=>A
  | n+1=>radiusIter (2*A+11) n

@[simp] theorem radiusIter_zero (A : ℝ) : radiusIter A 0=A:=rfl
@[simp] theorem radiusIter_succ (A : ℝ) (n : ℕ) :
    radiusIter A (n+1)=radiusIter (2*A+11) n:=rfl

theorem radiusIter_mono_base (n : ℕ) : Monotone (fun A:ℝ=>radiusIter A n) := by
  induction n with
  | zero=>intro A B h;exact h
  | succ n ih=>intro A B h;exact ih (by linarith : 2*A+11 ≤ 2*B+11)

theorem radiusIter_nonneg (A : ℝ) (hA : 0 ≤ A) (n : ℕ) : 0 ≤ radiusIter A n := by
  induction n generalizing A with
  | zero=>exact hA
  | succ n ih=>exact ih (2*A+11) (by linarith)

theorem radiusIter_mono_depth (A : ℝ) (hA : 0 ≤ A) : Monotone (radiusIter A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact radiusIter_mono_base n (by linarith : A ≤ 2*A+11)

theorem le_radiusIter (A : ℝ) (hA : 0 ≤ A) (n : ℕ) : A ≤ radiusIter A n :=
  radiusIter_mono_depth A hA (Nat.zero_le n)

theorem radiusIter_child_le (A : ℝ) (hA : 0 ≤ A) (s r : ℕ) (hs : s<r) :
    radiusIter (2*A+11) s ≤ radiusIter A r :=
  radiusIter_mono_depth A hA (Nat.succ_le_of_lt hs)

theorem common_pool_parent (A Z X D : ℝ) (r : ℕ) (hA : 0 ≤ A)
    (_hZ : 0 ≤ Z) (hX : 0 ≤ X) (hXZ : X ≤ Z^3)
    (hD : Real.exp (radiusIter A r)*Z^3 ≤ D) : Real.exp A*X ≤ D := by
  exact (mul_le_mul (Real.exp_le_exp.mpr (le_radiusIter A hA r)) hXZ hX
    (Real.exp_pos _).le).trans hD

theorem common_pool_child (A Z D : ℝ) (s r : ℕ) (hA : 0 ≤ A)
    (hZ : 0 ≤ Z) (hs : s<r) (hD : Real.exp (radiusIter A r)*Z^3 ≤ D) :
    Real.exp (radiusIter (2*A+11) s)*Z^3 ≤ D :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (radiusIter_child_le A hA s r hs))
    (pow_nonneg hZ _)).trans hD

end CanonicalCubeSeparation

namespace NormalizedReflection
open Eisenstein
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F]

def rootCard (F : Type*) [Fintype F] : ℝ := Real.sqrt (Fintype.card F)

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

/-- Local reflected bracket with its square-root Gauss normalization. -/
def bracket (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then
    (rootCard F : ℂ)⁻¹ * (-1 + (Fintype.card F : ℂ) * if x = 0 then 1 else 0)
  else if j = 0 then (rootCard F : ℂ)⁻¹ * (χ ^ 2)⁻¹ x
  else (χ ^ (j + 2))⁻¹ x

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem bracket_four_cube_split (χ : MulChar F ℂ) (n b : F) :
    bracket χ 4 (n * b ^ 3) = -(rootCard F : ℂ)⁻¹ +
      (rootCard F : ℂ) * (if n = 0 then 1 else 0) +
      (rootCard F : ℂ) * (if n ≠ 0 ∧ b = 0 then 1 else 0) := by
  rw [bracket_four_split]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

theorem bracket_zero_mask (χ : MulChar F ℂ) (j : ℕ) (hj : j ≠ 4) :
    bracket χ j 0 = 0 := by simp [bracket, hj, MulChar.map_zero]

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, if_neg hj4, if_neg hj0]
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)


lemma norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j≠4) (hj0 : j≠0) (x : F) : ‖bracket χ j x‖≤1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

lemma norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖≤(rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero,mul_one,le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

lemma canonical_bracket_four_cube_split (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (complexSexticChar P hg) 4 (Ideal.Quotient.mk P (n*b^3))=
      -(rootCard (O⧸P):ℂ)⁻¹+(rootCard (O⧸P):ℂ)*(if n∈P then 1 else 0)+
        (rootCard (O⧸P):ℂ)*(if n∉P ∧ b∈P then 1 else 0) := by
  simpa only [map_mul,map_pow,ne_eq,Ideal.Quotient.eq_zero_iff_mem] using
    bracket_four_cube_split (complexSexticChar P hg) (Ideal.Quotient.mk P n) (Ideal.Quotient.mk P b)

/-- The normalized bracket is the native reflected bracket times its local Gauss size. -/
lemma bracket_eq_finiteReflectionBracket (χ : MulChar F ℂ) (hχ : χ^6=1)
    (j : ℕ) (hj : j<6) (x : F) :
    bracket χ j x=(if j=0 ∨ j=4 then (rootCard F:ℂ)⁻¹ else 1)*
      finiteReflectionBracket χ j x := by
  by_cases h4 : j=4
  · subst j
    simp only [bracket,finiteReflectionBracket,if_pos rfl,or_true,ite_true]
    by_cases hx : x=0 <;> simp only [hx,↓reduceIte,mul_one,mul_zero] <;> ring
  · by_cases h0 : j=0
    · subst j
      simp only [bracket,finiteReflectionBracket,if_neg h4,if_pos rfl,true_or,ite_true]
      rw [show (χ^2)⁻¹=χ^reflectedSexticExponent 0 from
        inverse_reflectedSexticExponent χ hχ 0 (by decide)]
    · simp only [bracket,finiteReflectionBracket,if_neg h4,if_neg h0,
        show ¬(j=0 ∨ j=4) from not_or.mpr ⟨h0,h4⟩,ite_false,one_mul]
      rw [inverse_reflectedSexticExponent χ hχ j hj]

end NormalizedReflection

namespace CompletedDyadic
open scoped BigOperators Classical
open Filter MeasureTheory

def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

namespace CompletedDyadic
open scoped BigOperators Classical
open Filter MeasureTheory

theorem weighted_scale_identity (x t a s : ℝ) (hx : 0<x) (ht : 0<t) :
    x^a*(t*x^3)^(-s)=t^(-s)*x^(a-3*s) := by
  rw [Real.mul_rpow ht.le (pow_nonneg hx.le _),←Real.rpow_natCast_mul hx.le]
  calc
    _ = t^(-s)*(x^a*x^((3:ℝ)*(-s))) := by ring_nf
    _ = _ := by rw [←Real.rpow_add hx]; congr 2; ring

theorem double_kernel_sum_bound (s A β : ℝ) (hs : 0<s) (hsA : s<A) (hβ : β<3*s) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      (∀b : ℕ,Summable (kernelTerm (t*((2:ℝ)^b)^3) s A)) ∧
      Summable (fun b : ℕ => ((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u) ∧
      (∑'b : ℕ,((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u)≤C*t^(-s) := by
  obtain ⟨Cu,hCu,hu⟩ := kernel_sum_bound s A hs hsA
  let q : ℝ := (2:ℝ)^(β-3*s)
  have hq : q<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0≤q := by dsimp [q]; positivity
  refine ⟨Cu/(1-q),by positivity,?_⟩
  intro t ht
  have hinner (b : ℕ) := hu (t*((2:ℝ)^b)^3) (by positivity)
  have hf0 (b : ℕ) : 0≤((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (kernelTerm_nonneg _ s A (by positivity))
  have hle (b : ℕ) : ((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u≤
      (Cu*t^(-s))*q^b := by
    calc
      _ ≤ ((2:ℝ)^b)^β*(Cu*(t*((2:ℝ)^b)^3)^(-s)) :=
        mul_le_mul_of_nonneg_left (hinner b).2 (by positivity)
      _ = Cu*(((2:ℝ)^b)^β*(t*((2:ℝ)^b)^3)^(-s)) := by ring
      _ = _ := by rw [weighted_scale_identity _ t β s (by positivity) ht,pow_rpow_comm]; dsimp [q]; ring
  have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (Cu*t^(-s))
  have hf := hgeo.of_nonneg_of_le hf0 hle
  refine ⟨fun b => (hinner b).1,hf,?_⟩
  have hb := hf.tsum_le_tsum hle hgeo
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hb

def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0<ramifiedScale ρ q m := by unfold ramifiedScale; positivity

theorem triple_kernel_sum_bound (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      (∀m b : ℕ,Summable (kernelTerm
        (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A)) ∧
      (∀m : ℕ,Summable (fun b : ℕ => ((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)) ∧
      Summable (fun m : ℕ => (ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u) ∧
      (∑'m : ℕ,(ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)
        ≤C*t^(-s) := by
  obtain ⟨Cb,hCb,hb⟩ := double_kernel_sum_bound s A β hs hsA hβ
  let v : ℝ := q^(-1-3*s)
  have hv : v<1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hq0 : 0<q := by linarith
  have hv0 : 0≤v := by dsimp [v]; positivity
  let B : ℝ := Cb*ρ^(-1-3*s)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B/(1-v),by positivity,?_⟩
  intro t ht
  have hm (m : ℕ) := hb (t*(ramifiedScale ρ q m)^3) (by
    have := ramifiedScale_pos ρ q hρ hq0 m
    positivity)
  have hn (m : ℕ) : 0≤(ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u := by
    apply mul_nonneg (le_of_lt (inv_pos.mpr (ramifiedScale_pos ρ q hρ hq0 m)))
    apply tsum_nonneg
    intro b
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (kernelTerm_nonneg _ s A (by
      have := ramifiedScale_pos ρ q hρ hq0 m
      positivity))
  have hbound (m : ℕ) : (ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u
      ≤(B*t^(-s))*v^m := by
    have hr := ramifiedScale_pos ρ q hρ hq0 m
    calc
      _ ≤ (ramifiedScale ρ q m)⁻¹*(Cb*(t*(ramifiedScale ρ q m)^3)^(-s)) :=
        mul_le_mul_of_nonneg_left (hm m).2.2 (by positivity)
      _ = Cb*((ramifiedScale ρ q m)^(-1:ℝ)*(t*(ramifiedScale ρ q m)^3)^(-s)) := by
        rw [Real.rpow_neg_one]; ring
      _ = Cb*(t^(-s)*(ramifiedScale ρ q m)^(-1-3*s)) := by
        rw [weighted_scale_identity _ t (-1) s hr ht]
      _ = _ := by
        rw [ramifiedScale,Real.mul_rpow hρ.le (pow_nonneg hq0.le _),
          ←Real.rpow_natCast_mul hq0.le,
          mul_comm (m:ℝ) (-1-3*s),Real.rpow_mul_natCast hq0.le]
        dsimp [B,v]
        ring
  have hg := (summable_geometric_of_lt_one hv0 hv).mul_left (B*t^(-s))
  have hf := hg.of_nonneg_of_le hn hbound
  refine ⟨fun m b => (hm m).1 b,fun m => (hm m).2.1,hf,?_⟩
  have hfinal := hf.tsum_le_tsum hbound hg
  rw [tsum_mul_left,tsum_geometric_of_lt_one hv0 hv] at hfinal
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hfinal

def normMajorant (deltaLoss A K t r H U B : ℝ) : ℝ :=
  K^deltaLoss/(r*Real.sqrt H)*
    (Real.sqrt K*B^(deltaLoss-1/2)*U^deltaLoss+B^deltaLoss*U^(deltaLoss+1/2))/(1+t*r^3*B^3*U)^A

theorem normMajorant_nonneg (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    0≤normMajorant deltaLoss A K t r H U B := by unfold normMajorant; positivity

theorem normMajorant_eq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    normMajorant deltaLoss A K t r H U B =
      (K*(U*B))^deltaLoss*(Real.sqrt K+Real.sqrt U*Real.sqrt B)/
        (Real.sqrt B*r*Real.sqrt H*(1+t*r^3*B^3*U)^A) := by
  unfold normMajorant
  rw [Real.mul_rpow hK.le (mul_pos hU hB).le,Real.mul_rpow hU.le hB.le,
    Real.rpow_sub hB,Real.rpow_add hU,←Real.sqrt_eq_rpow B,←Real.sqrt_eq_rpow U]
  have hsB : Real.sqrt B≠0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp

theorem smooth_energy_le_normMajorant_sq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    (K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+t*r^3*B^3*U)^(2*A)
      ≤(normMajorant deltaLoss A K t r H U B)^2 := by
  rw [normMajorant_eq deltaLoss A K t r H U B hK ht hr hH hU hB,div_pow,mul_pow,
    mul_pow,mul_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hH.le]
  have hc : 0≤(K*(U*B))^deltaLoss := by positivity
  have hden : 0<(B*r^2*H)*(1+t*r^3*B^3*U)^(2*A) := by positivity
  have hp (x : ℝ) (hx : 0≤x) (s : ℝ) : (x^s)^2=x^(2*s) := by
    rw [←Real.rpow_mul_natCast hx]
    congr 1
    ring
  rw [hp _ (mul_pos hK (mul_pos hU hB)).le,hp _ (by positivity)]
  rw [div_div]
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcross : 0≤2*Real.sqrt K*(Real.sqrt U*Real.sqrt B) := by positivity
  nlinarith [Real.sq_sqrt hK.le,Real.sq_sqrt hU.le,Real.sq_sqrt hB.le,
    sq_nonneg (Real.sqrt K+Real.sqrt U*Real.sqrt B)]

def tripleTerm (t s A β ρ q : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  (ramifiedScale ρ q i.1)⁻¹*((2:ℝ)^i.2.1)^β*
    kernelTerm (t*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3) s A i.2.2

theorem tripleTerm_nonneg (t s A β ρ q : ℝ) (ht : 0<t) (hρ : 0<ρ) (hq : 0<q)
    (i : ℕ×ℕ×ℕ) : 0≤tripleTerm t s A β ρ q i := by
  unfold tripleTerm
  have hr := ramifiedScale_pos ρ q hρ hq i.1
  exact mul_nonneg (by positivity) (kernelTerm_nonneg _ s A (by positivity) _)

theorem triple_product_kernel_sum_bound (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t → Summable (tripleTerm t s A β ρ q) ∧
      (∑'i : ℕ×ℕ×ℕ,tripleTerm t s A β ρ q i)≤C*t^(-s) := by
  obtain ⟨C,hC,hbound⟩ := triple_kernel_sum_bound s A β ρ q hs hsA hβ hρ hq
  refine ⟨C,hC,?_⟩
  intro t ht
  obtain ⟨hu,hb,hm,hbnd⟩ := hbound t ht
  have hq0 : 0<q := by linarith
  have hpos := tripleTerm_nonneg t s A β ρ q ht hρ hq0
  have hinner (m : ℕ) : Summable (fun j : ℕ×ℕ => tripleTerm t s A β ρ q (m,j)) := by
    apply (summable_prod_of_nonneg (fun j => hpos (m,j))).mpr
    constructor
    · intro b
      simpa only [tripleTerm] using (hu m b).mul_left ((ramifiedScale ρ q m)⁻¹*((2:ℝ)^b)^β)
    · simpa only [tripleTerm,tsum_mul_left,mul_assoc] using
        (hb m).mul_left (ramifiedScale ρ q m)⁻¹
  have hrow (m : ℕ) : (∑'j : ℕ×ℕ,tripleTerm t s A β ρ q (m,j))=
      (ramifiedScale ρ q m)⁻¹*∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u := by
    rw [(hinner m).tsum_prod]
    simp only [tripleTerm,tsum_mul_left,mul_assoc]
  have hall : Summable (tripleTerm t s A β ρ q) := by
    apply (summable_prod_of_nonneg hpos).mpr
    exact ⟨hinner,by simpa only [hrow] using hm⟩
  refine ⟨hall,?_⟩
  simpa only [hall.tsum_prod,hrow] using hbnd

theorem normMajorant_eq_triples (deltaLoss A K t H ρ q : ℝ) (i : ℕ×ℕ×ℕ) :
    normMajorant deltaLoss A K t (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)=
      K^deltaLoss/Real.sqrt H*(Real.sqrt K*tripleTerm t deltaLoss A (deltaLoss-1/2) ρ q i+
        tripleTerm t (deltaLoss+1/2) A deltaLoss ρ q i) := by
  simp only [normMajorant,tripleTerm,kernelTerm]
  ring

theorem normMajorant_sum_bound (deltaLoss A ρ q : ℝ)
    (hδ : 0<deltaLoss) (hA : deltaLoss+1/2<A) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,0<K → 0<Y → 0<H →
      Summable (fun i : ℕ×ℕ×ℕ =>
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) ∧
      (∑'i : ℕ×ℕ×ℕ,
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1))
        ≤C*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H := by
  obtain ⟨C₁,hC₁,h₁⟩ := triple_product_kernel_sum_bound deltaLoss A (deltaLoss-1/2) ρ q hδ
    (by linarith) (by linarith) hρ hq
  obtain ⟨C₂,hC₂,h₂⟩ := triple_product_kernel_sum_bound (deltaLoss+1/2) A deltaLoss ρ q
    (by linarith) hA (by linarith) hρ hq
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro K Y H hK hY hH
  obtain ⟨hs₁,hb₁⟩ := h₁ Y⁻¹ (by positivity)
  obtain ⟨hs₂,hb₂⟩ := h₂ Y⁻¹ (by positivity)
  simp_rw [normMajorant_eq_triples]
  refine ⟨((hs₁.mul_left (Real.sqrt K)).add hs₂).mul_left (K^deltaLoss/Real.sqrt H),?_⟩
  rw [tsum_mul_left,(hs₁.mul_left (Real.sqrt K)).tsum_add hs₂,tsum_mul_left]
  have hp₁ : (Y⁻¹)^(-deltaLoss)=Y^deltaLoss := by rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv]
  have hp₂ : (Y⁻¹)^(-(deltaLoss+1/2))=Y^deltaLoss*Real.sqrt Y := by
    rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv,Real.rpow_add hY,←Real.sqrt_eq_rpow]
  rw [hp₁] at hb₁
  rw [hp₂] at hb₂
  calc
    _ ≤ K^deltaLoss/Real.sqrt H*(Real.sqrt K*(C₁*Y^deltaLoss)+C₂*(Y^deltaLoss*Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hb₁ (Real.sqrt_nonneg _)) hb₂
    _ ≤ K^deltaLoss/Real.sqrt H*((C₁+C₂)*Y^deltaLoss*(Real.sqrt K+Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (le_of_lt hC₁) (show 0≤Y^deltaLoss*Real.sqrt Y by positivity),
        mul_nonneg (le_of_lt hC₂) (show 0≤Y^deltaLoss*Real.sqrt K by positivity)]
    _ = _ := by rw [Real.mul_rpow hK.le hY.le]; ring

end CompletedDyadic

namespace NormalizedReflection
open Eisenstein
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]

def gaussScale (F : ι→Type*) [∀i,Fintype (F i)] (j : ι→ℕ) : ℝ :=
  ∏i,if j i=0 ∨ j i=4 then (rootCard (F i))⁻¹ else 1

lemma gaussScale_pos (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (j : ι→ℕ) :
    0<gaussScale F j := by
  apply Finset.prod_pos
  intro i hi
  split_ifs
  · exact inv_pos.mpr rootCard_pos
  · exact zero_lt_one

lemma gaussScale_sq (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (j : ι→ℕ) :
    gaussScale F j^2=∏i,if j i=0 ∨ j i=4 then (Fintype.card (F i):ℝ)⁻¹ else 1 := by
  rw [pow_two,gaussScale,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs
  · rw [←pow_two,inv_pow,rootCard_sq]
  · exact one_mul 1

lemma gaussScale_mul_prod (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (χ : ∀i,MulChar (F i) ℂ) (hχ : ∀i,χ i^6=1) (j : ι→ℕ) (hj : ∀i,j i<6) (x : ∀i,F i) :
    (gaussScale F j:ℂ)*(∏i,finiteReflectionBracket (χ i) (j i) (x i))=
      ∏i,bracket (χ i) (j i) (x i) := by
  simp only [gaussScale,Complex.ofReal_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [bracket_eq_finiteReflectionBracket (χ i) (hχ i) (j i) (hj i)]
  split_ifs <;> simp only [Complex.ofReal_inv,Complex.ofReal_one]

lemma normalized_phase_bound (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (j : ι→ℕ) (β : ℂ)
    (hβ : ‖β‖^2≤81*∏i,if j i=0 ∨ j i=4 then (Fintype.card (F i):ℝ)⁻¹ else 1) :
    ‖β/(gaussScale F j:ℂ)‖≤9 := by
  have hs := gaussScale_pos F j
  rw [←gaussScale_sq F j] at hβ
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hβ,norm_nonneg β,hs]

lemma bracket_unit_mul {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ^6=1) (j : ℕ) (hj : j<6) (u : Fˣ) (x : F) :
    bracket χ j ((u:F)*x)=finiteReflectionUnitFactor χ j u*bracket χ j x := by
  rw [bracket_eq_finiteReflectionBracket χ hχ j hj,
    finiteReflectionBracket_unit_mul,bracket_eq_finiteReflectionBracket χ hχ j hj]
  ring

end NormalizedReflection

namespace SchwartzPlanePoisson
open Eisenstein
open scoped BigOperators Classical

lemma quadratic_char_transport (P R : Ideal O) [P.IsMaximal] [R.IsMaximal]
    (he : P=R) (z : O) :
    complexQuadraticChar P (Ideal.Quotient.mk P z)=
      complexQuadraticChar R (Ideal.Quotient.mk R z) := by
  subst R
  rfl

local instance quadraticSupportMaximal (I : QuadraticIdeal) (P : primeSupport I.val) :
    P.val.IsMaximal := (quadraticIdealPrimeIndex I P).property.1

/-- The canonical quadratic row is the product over its prime-ideal support. -/
lemma canonicalQuadraticRow_eq_prime_product (I : QuadraticIdeal) (z : O) :
    canonicalQuadraticRow I z=
      ∏P : primeSupport I.val,complexQuadraticChar P.val (Ideal.Quotient.mk P.val z) := by
  unfold canonicalQuadraticRow primeSubsetRow
  rw [quadraticIdealSupport,Finset.prod_map]
  change (∏P : primeSupport I.val,_)=_
  apply Finset.prod_congr rfl
  intro P hP
  exact quadratic_char_transport _ _ (quadraticPrimeGenerator_span (quadraticIdealPrimeIndex I P)) z

lemma canonicalQuadraticRowOfIdeal_eq_prime_product (I : Ideal O) (hI : quadraticIdealAdmissible I)
    (z : O) :
    letI : ∀P : primeSupport I,P.val.IsMaximal := quadraticSupportMaximal ⟨I,hI⟩
    canonicalQuadraticRowOfIdeal I z=
      ∏P : primeSupport I,complexQuadraticChar P.val (Ideal.Quotient.mk P.val z) := by
  rw [canonicalQuadraticRowOfIdeal,dif_pos hI]
  exact canonicalQuadraticRow_eq_prime_product ⟨I,hI⟩ z

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

lemma canonicalQuadraticRowOfIdeal_mul (I : Ideal O) (x y : O) :
    canonicalQuadraticRowOfIdeal I (x*y)=
      canonicalQuadraticRowOfIdeal I x*canonicalQuadraticRowOfIdeal I y := by
  by_cases hI : quadraticIdealAdmissible I
  · simp only [canonicalQuadraticRowOfIdeal,dif_pos hI,canonicalQuadraticRow_mul]
  · simp only [canonicalQuadraticRowOfIdeal,dif_neg hI,mul_zero]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open scoped ContDiff
lemma kernelLogSource_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    kernelLogSource W a b ha hs hW u = W (Real.exp u) := rfl
end SchwartzPlanePoisson

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open scoped BigOperators Classical
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- Uniform canonical height bounds integrate to a bound for the two child energies. -/
theorem densityChildEnergy_from_canonical_heights {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O×O)) (labels : Finset (Ideal O)) (V₁ V₂ : ℝ → ℂ)
    (X F K E : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels) (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K)
    (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hg H₁ pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hg H₂ pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)≤
      (Fintype.card Oˣ:ℝ)*E*(X*F)^2*(∫t : ℝ,firstLogDensity 0 t)^3 := by
  let C:=(Fintype.card Oˣ:ℝ)*E*(X*F)^2
  have hC : 0≤C:=by dsimp only [C]; positivity
  have hl (a : ℝ) : childEnergy p hg H₁ pool Ψ₁ m T V₁ X true false a 0≤
      C*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hg H₁ pool Ψ₁ m
      T labels V₁ X K a 0 hX hK true false hlabels hrows hzero
    simp only [secondSignedHeight,ite_true,zero_sub] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ (-a)) (Nat.cast_nonneg _)).trans_eq
      (by rw [norm_neg]; dsimp only [C]; ring))
  have hr (a : ℝ) : childEnergy p hg H₂ pool Ψ₂ m T V₂ X false true a 0≤
      C*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hg H₂ pool Ψ₂ m
      T labels V₂ X K a 0 hX hK false true hlabels hrows hzero
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ a) (Nat.cast_nonneg _)).trans_eq
      (by dsimp only [C]; ring))
  have hd:=densityChildEnergy_polynomial_bound p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X J
    C C hC hC hl hr
  rwa [Real.mul_self_sqrt hC] at hd

end SecondPassIntegration

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
