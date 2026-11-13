/-
Clipping profiles and initial fibers adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.UniformPolynomialKernels

/-!
# Clipping profiles and initial fibers

Affine logarithmic windows `InverseClippingProfiles.logWindow` keep uniform derivative and
Fourier-moment bounds. Valid tuples of the initial fibers `InverseInitialFibers` have
cardinality and weight bounds at a slot cap.
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

namespace InverseClippingProfiles
open Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

/-- Affine logarithmic windows retain uniform derivative and Fourier-moment bounds. -/
def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_iteratedDeriv (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v)
    (L ρ : ℝ) (n : ℕ) :
    iteratedDeriv n (logWindow v L ρ) =
      fun y => (L⁻¹)^n • iteratedDeriv n v ((y + ρ) / L) := by
  have h : (logWindow v L ρ) =
      fun y => (fun z => v (L⁻¹ * z)) (y + ρ) := by
    funext y
    simp only [logWindow, div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_add_const n (fun z => v (L⁻¹ * z)) ρ,
    iteratedDeriv_comp_const_smul (n := n) (hv.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))]
  simp only [div_eq_mul_inv, mul_comm]

lemma expAffine_iteratedDeriv (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (a * y + b) : ℂ)) =
      fun y => (a : ℂ)^n * (Real.exp (a * y + b) : ℂ) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h := (((hasDerivAt_id y).const_mul a).add_const b).exp
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y h).const_mul ((a : ℂ)^n)
    simp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hc
    rw [hc.deriv]
    simp only [mul_one, Complex.ofReal_mul, pow_succ]
    ring

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

lemma derivative_support (v : 𝓢(ℝ, ℂ)) (M : ℝ)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (n : ℕ) :
    Function.support (iteratedDeriv n v) ⊆ Set.Icc (-M) M :=
  (subset_tsupport _).trans
    ((tsupport_iteratedDeriv_subset v n).trans
      (closure_minimal hv isClosed_Icc))

lemma root_exp_le_one (a H M B L ρ y : ℝ)
    (hL : 0 ≤ L) (hρ : |ρ| ≤ B*L) (hy : |(y+ρ)/L| ≤ M)
    (hL0 : L ≠ 0) (hH : |a| *(M+B) ≤ H) :
    Real.exp (a*y-H*L) ≤ 1 := by
  have hs : |y| ≤ (M+B)*L := by
    have h := (abs_le.mp hy)
    have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have h1 := (le_div_iff₀ hLp).mp h.1
    have h2 := (div_le_iff₀ hLp).mp h.2
    have hr := abs_le.mp hρ
    apply abs_le.mpr
    constructor <;> nlinarith
  have ha := le_abs_self (a*y)
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hH hL
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma expAffine_iteratedFDeriv_norm (a b y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.exp (a*x+b) : ℂ)) y‖ =
      |a|^n * Real.exp (a*y+b) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expAffine_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem rootSchwartz_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
        (rootSchwartz v M B L ρ a H (by linarith) hρ hv) ≤
      ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n * derivativeSeminormSum v 0 n := by
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n *
      derivativeSeminormSum v 0 n := by
    apply mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hC
  intro y
  have hbase (j : ℕ) (hj : j ≤ n) :
      ‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ j (logWindow v L ρ) y‖ ≤
        ((M+B)*L)^k * derivativeSeminormSum v 0 n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logWindow_iteratedDeriv v (v.smooth ⊤)]
    by_cases hz : iteratedDeriv j v ((y+ρ)/L) = 0
    · simp only [hz, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
    have harg := derivative_support v M hv j hz
    have hy : |(y+ρ)/L| ≤ M := abs_le.mpr harg
    have he := root_exp_le_one a H M B L ρ y hLp.le hρ hy (ne_of_gt hLp) hH
    have hx : ‖y‖ ≤ (M+B)*L := by
      have ht := logWindow_support (iteratedDeriv j v) M B L ρ hLp hρ
        (derivative_support v M hv j) hz
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hd : ‖iteratedDeriv j v ((y+ρ)/L)‖ ≤ derivativeSeminormSum v 0 n := by
      have hh := (SchwartzMap.le_seminorm ℝ 0 j v ((y+ρ)/L)).trans
        (seminorm_le_derivativeSeminormSum v 0 n j hj)
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hh
    have hi : ‖L⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      exact inv_le_one_of_one_le₀ hL
    have hs : ‖(L⁻¹)^j • iteratedDeriv j v ((y+ρ)/L)‖ ≤
        derivativeSeminormSum v 0 n := by
      rw [norm_smul, norm_pow]
      calc
        _ ≤ 1 * ‖iteratedDeriv j v ((y+ρ)/L)‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hi
        _ ≤ _ := by simpa using hd
    calc
      _ ≤ ((M+B)*L)^k * 1 * derivativeSeminormSum v 0 n := by gcongr
      _ = _ := by ring
  have he : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  have hh := norm_iteratedFDeriv_mul_le he (logWindow_contDiff v (v.smooth ⊤) L ρ)
    y (n := n) (by exact_mod_cast le_top)
  change ‖y‖^k * ‖iteratedFDeriv ℝ n (rootedWindow v L ρ a H) y‖ ≤ _
  unfold rootedWindow
  calc
    _ ≤ ‖y‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |a|^i *
        (‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) =
        (fun x : ℝ => (Real.exp (a*x+(-H*L)) : ℂ)) by ext x; congr 2; ring]
      rw [expAffine_iteratedFDeriv_norm]
      rw [show a*y+(-H*L) = a*y-H*L by ring]
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1+|a|)^n *
        (((M+B)*L)^k * derivativeSeminormSum v 0 n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : |a|^i ≤ (1+|a|)^n := by
        calc
          _ ≤ (1+|a|)^i := by gcongr; linarith [abs_nonneg a]
          _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg a])
            (Finset.mem_range_succ_iff.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (hbase (n-i) (Nat.sub_le _ _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def twistedDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (1+2*Real.pi)^n * rootDerivativeBound v a n

lemma rootDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ rootDerivativeBound v a n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)

lemma twistedDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ twistedDerivativeBound v a n :=
  mul_nonneg (by positivity) (rootDerivativeBound_nonneg _ _ _)

lemma rootSchwartz_derivativeSum (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n ≤
      ((M+B)*L)^k * rootDerivativeBound v a n := by
  unfold derivativeSeminormSum rootDerivativeBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_assoc] using rootSchwartz_seminorm v M B L ρ a H hM hB hL hρ hv hH k i

theorem rooted_twist_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
      (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      (M+B)^k * twistedDerivativeBound v a n * L^k * (1+‖θ‖)^n := by
  have hb := frequencyTwist_seminorm_polynomial
    (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ k n
  have hd := rootSchwartz_derivativeSum v M B L ρ a H hM hB hL hρ hv hH k n
  calc
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n) *
        (1+‖θ‖)^n := hb
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        (((M+B)*L)^k * rootDerivativeBound v a n)) * (1+‖θ‖)^n := by gcongr
    _ = _ := by unfold twistedDerivativeBound; rw [mul_pow]; ring

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

def windowSourceBound (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (1+(M+B)^(volume : Measure ℝ).integrablePower) *
    ∑ i ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a i

lemma windowSourceBound_nonneg (v : 𝓢(ℝ, ℂ)) (M B a : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (J : ℕ) : 0 ≤ windowSourceBound v M B a J := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)

theorem rooted_twist_moment_sources (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (J i : ℕ) (hi : i ≤ momentOrder J) :
    (SchwartzMap.seminorm ℝ 0 i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  let p := (volume : Measure ℝ).integrablePower
  have h0 := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH 0 i
  have hp := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH p i
  simp only [pow_zero, one_mul, mul_one] at h0
  have hs : twistedDerivativeBound v a i ≤
      ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j := by
    apply Finset.single_le_sum (fun j _ => twistedDerivativeBound_nonneg v a j)
    exact Finset.mem_range_succ_iff.mpr hi
  have hl : 1 ≤ L^p := one_le_pow₀ hL
  have ht : (1+‖θ‖)^i ≤ (1+‖θ‖)^(momentOrder J) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg θ]) hi
  have hc := twistedDerivativeBound_nonneg v a i
  have hsum : 0 ≤ ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j :=
    Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)
  calc
    _ ≤ twistedDerivativeBound v a i * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := add_le_add h0 hp
    _ ≤ twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by gcongr; nlinarith
    _ = (1+(M+B)^p) * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by ring
    _ ≤ _ := by unfold windowSourceBound; gcongr

lemma coefficientMomentBound_mul (J : ℕ) (C D : ℝ) :
    coefficientMomentBound J (C*D) = coefficientMomentBound J C * D := by
  unfold coefficientMomentBound
  ring

theorem rooted_twist_fourier_moment (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H) (J : ℕ) :
    (∫ t : ℝ, (1+‖t‖)^J *
      ‖(𝓕 (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ)) t‖) ≤
      ((2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
        coefficientMomentBound J (windowSourceBound v M B a J))) *
      L^(volume : Measure ℝ).integrablePower * (1+‖θ‖)^(momentOrder J) := by
  have hc := windowSourceBound_nonneg v M B a hM hB J
  have h := uniform_fourier_one_plus_moment
    (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) J 1
    (windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
      (1+‖θ‖)^(momentOrder J)) (by norm_num) (by positivity)
    (by
      intro i hi
      simpa using (rooted_twist_moment_sources v M B L ρ a H θ
        hM hB hL hρ hv hH J i hi))
  simp only [one_mul, coefficientMomentBound_mul] at h
  convert h using 1
  ring

theorem child_log_window_parameters (η Z δ : ℝ) (_hη : 0 ≤ η)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    0 ≤ δ*Real.log Z ∧ |δ*Real.log Z| ≤ 6*(η*Real.log Z) := by
  have hz : 0 ≤ Real.log Z := Real.log_nonneg hZ
  constructor
  · positivity
  · rw [abs_of_nonneg (by positivity : 0 ≤ δ*Real.log Z)]
    nlinarith [mul_le_mul_of_nonneg_right hδu hz]

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

theorem clipped_positive_support (w : ℝ → ℂ) (a b c : ℝ)
    (ha : 0 < a) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) :
    Function.support (fun y => w (c*y)) ⊆ Set.Icc (a/b) b := by
  intro y hy
  have hs := hw hy
  have hcp : 0 < c := by linarith
  have hbp : 0 < b := lt_of_lt_of_le hcp hcb
  have hyp : 0 < y := by nlinarith [hs.1]
  constructor
  · apply (div_le_iff₀ hbp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hyp.le, hs.1]
  · nlinarith [hs.2]

theorem clipped_log_source (w : ℝ → ℂ) (c y : ℝ) (hc : 0 < c) :
    w (c*Real.exp y) = (fun s => w (Real.exp s)) (y+Real.log c) := by
  change w (c*Real.exp y) = w (Real.exp (y+Real.log c))
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => kernelLogPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', kernelLogPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = kernelLogPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, kernelLogPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => kernelLogPhase θ y * f (y+ρ))) t =
      kernelLogPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => kernelLogPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, kernelLogPhase_norm, one_mul]

def childWindowDensity (v : 𝓢(ℝ, ℂ)) (η Z δ θ t : ℝ) : ℂ :=
  (𝓕 (fun y => kernelLogPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)))) t

def windowMomentConstant (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
    coefficientMomentBound J (windowSourceBound v M B a J))

theorem childWindowDensity_moment (v : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (J : ℕ)
    (η Z δ θ : ℝ) (hη : 0 ≤ η) (hZ : 1 ≤ Z)
    (hL : 1 ≤ η*Real.log Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    Integrable (fun t : ℝ => (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ∧
    (∫ t : ℝ, (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ≤
      windowMomentConstant v M 6 0 J * (η*Real.log Z)^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  have hρ := (child_log_window_parameters η Z δ hη hZ hδ hδu).2
  let g := frequencyTwist (rootSchwartz v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0
    (by linarith) hρ hv) θ
  have he (t : ℝ) : childWindowDensity v η Z δ θ t = (𝓕 g) t := by
    rw [congrFun (SchwartzMap.fourier_coe g) t]
    unfold childWindowDensity
    have hg : (g : ℝ → ℂ) = fun y =>
        kernelLogPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)) := by
      funext y
      simp [g, frequencyTwist_apply, rootSchwartz_apply, rootedWindow, logWindow]
    rw [hg]
  simp_rw [he]
  refine ⟨CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g) J, ?_⟩
  exact rooted_twist_fourier_moment v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0 θ
    hM (by norm_num) hL hρ hv (by simp) J

theorem retained_clipped_column (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧
    Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
    ∀ θ t : ℝ,
      (𝓕 (fun y => kernelLogPhase θ y * w (c*Real.exp y))) t =
        kernelLogPhase (t-θ) (Real.log c) * (𝓕 (fun y => w (Real.exp y))) (t-θ) := by
  dsimp only
  have hc := clipping_ratio_of_column_witness w Z N q a b hZ hq hb hw hwitness
  refine ⟨hc.1, hc.2, clipped_positive_support w a b _ ha hc.1 hc.2 hw, ?_⟩
  intro θ t
  have he : (fun y => kernelLogPhase θ y * w (Z^(max 0 N-N)*Real.exp y)) =
      (fun y => kernelLogPhase θ y * (fun s => w (Real.exp s)) (y+Real.log (Z^(max 0 N-N)))) := by
    ext y
    rw [clipped_log_source w _ y (by linarith)]
  rw [he]
  exact fourier_translated_twist (fun s => w (Real.exp s)) (Real.log (Z^(max 0 N-N))) θ t

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => kernelLogPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => kernelLogPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := JointLogSeparation.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => kernelLogPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => kernelLogPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 (frequencyTwist g θ)) J, hb θ⟩


end InverseClippingProfiles

namespace InverseInitialFibers
open Eisenstein
open scoped BigOperators Classical

abbrev PrimeIdeal := {P : Ideal O // Prime P}

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryIdealGenerator x.divisor ≠ 0
  row_eq : primaryIdealGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

theorem Valid.of_reconstruction {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O)
    (hf : primaryIdealGenerator f ≠ 0) (hC : t*x.divisor = x.common)
    (hlabel : x.divisor*x.residual = f)
    (hrow : primaryIdealGenerator x.divisor*x.frequency = k)
    (hslots : ∀ i, (x.assigned i).val ∣ t*f) : Valid x t f k := by
  refine ⟨hC, hlabel, ?_, hrow, hslots⟩
  intro hz
  apply hf
  rw [← hlabel, primaryIdealGenerator_mul, hz, zero_mul]

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryIdealGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma valid_label_squarefree {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hC : Squarefree x.common) (hs : Squarefree x.residual)
    (hmask : IsCoprime x.residual x.common) : Squarefree f := by
  have hdC : x.divisor ∣ x.common := by rw [← hx.common_eq]; exact dvd_mul_left _ _
  have hds : IsCoprime x.divisor x.residual := (hmask.of_isCoprime_of_dvd_right hdC).symm
  rw [← hx.label_eq]
  exact squarefree_mul_iff.mpr ⟨hds.isRelPrime, hC.squarefree_of_dvd hdC, hs⟩

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

theorem valid_tuple_card_le_slot_cap {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) (K : ℕ) (hJ : J ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) := by
  apply (valid_tuple_card_le_separated T t f k ht hf hT).trans
  exact Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos t ht) hJ)

theorem valid_tuple_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (InitialTuple J)) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 → (∀ x ∈ T, Valid x t f k) →
      (T.card : ℝ) ≤ C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  have hJr : 0 < (J+1 : ℝ) := by positivity
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power
    (ε/(J+1)) (div_pos hε hJr)
  refine ⟨C ^ (J+1), by positivity, ?_⟩
  intro T t f k ht hf hT
  have htf : t*f ≠ 0 := mul_ne_zero ht hf
  have hsub : idealDivisors f ⊆ idealDivisors (t*f) := by
    intro D hD
    exact (mem_idealDivisors htf).mpr
      (((mem_idealDivisors hf).mp hD).trans (dvd_mul_left _ _))
  have hcard : T.card ≤ (idealDivisors (t*f)).card^(J+1) := by
    apply (valid_tuple_card_le T t f k ht hf hT).trans
    calc
      _ ≤ (idealDivisors (t*f)).card * (idealDivisors (t*f)).card^J :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = _ := by rw [pow_succ]; ring
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors (t*f)).card : ℝ))
    (hb (t*f) htf) (J+1)
  apply (show (T.card : ℝ) ≤ ((idealDivisors (t*f)).card : ℝ)^(J+1) by
    exact_mod_cast hcard).trans (hh.trans_eq ?_)
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), map_mul, Nat.cast_mul]
  congr 1
  push_cast
  field_simp

def initialFiber {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O) : Finset (InitialTuple J) :=
  source.filter (fun x => Valid x t f k ∧ (∀ i, x.assigned i ∈ lists i) ∧ keep x)

theorem initialFiber_card_le {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(J+1) * (idealDivisors t).card^J :=
  valid_tuple_card_le_separated _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_card_le_slot_cap {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (K : ℕ) (hJ : J ≤ 2*K) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1) K hJ

theorem initialFiber_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (source : Finset (InitialTuple J))
      (lists : Fin J → Finset PrimeIdeal)
      (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 →
      ((initialFiber source lists keep t f k).card : ℝ) ≤
        C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  obtain ⟨C, hC, hbound⟩ := valid_tuple_small_power J ε hε
  refine ⟨C, hC, ?_⟩
  intro source lists keep t f k ht hf
  exact hbound _ t f k ht hf (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_weight_bound {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (w : InitialTuple J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ initialFiber source lists keep t f k, ‖w x‖ ≤ C) :
    (∑ x ∈ initialFiber source lists keep t f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(J+1) * ((idealDivisors t).card : ℝ)^J := by
  calc
    _ ≤ ∑ _x ∈ initialFiber source lists keep t f k, C :=
      Finset.sum_le_sum hw
    _ = ((initialFiber source lists keep t f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(J+1) * (idealDivisors t).card^J : ℕ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast initialFiber_card_le source lists keep t f k ht hf) hC
    _ = _ := by push_cast; ring

end InverseInitialFibers

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
