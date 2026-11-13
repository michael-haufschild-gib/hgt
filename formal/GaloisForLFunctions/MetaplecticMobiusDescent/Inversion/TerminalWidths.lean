/-
Terminal widths adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.SlotTupleProducts
import GaloisForLFunctions.MetaplecticMobiusDescent.Fourier.PositiveLogProfiles

/-!
# Terminal widths

Norm, ramified and terminal dual widths with their width constant (`InverseTerminalWidths`);
uniform kernel sources and the reflected normalization identities for row, cubic and hybrid
shapes.
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
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseKernelSourceUniform

open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory LocalLogFourier
noncomputable section

def smallScalar (R : ℝ) : ℝ := min 1 (R ^ (1/4 : ℝ))

lemma smallScalar_pos {R : ℝ} (hR : 0 < R) : 0 < smallScalar R :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos hR _)

def canonicalDensity (U : ℝ → ℂ) (V : 𝓢(ℝ, ℂ)) (R t : ℝ) : ℂ :=
  ((smallScalar R : ℝ) : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * paperKernel V (R * Real.exp s))) t

theorem paperKernel_window_source_bound (a b : ℝ) (ha : 0 < a) (K : ℕ) (L : ℝ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R → ∀ j ≤ K, ∀ s : ℝ, |s| ≤ L →
      ‖eulerDeriv (paperKernel V) j (R * Real.exp s)‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  choose orders c hc hb using fun j : Fin (K+1) =>
    CompletedHeight.paperKernel_euler_source_power_decay a b ha 0 j.val
  let S := Finset.univ.biUnion orders
  let D := (∑ j : Fin (K+1), c j) + 1
  let E := (Real.exp L) ^ (1/4 : ℝ)
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc j).le)
    dsimp only [D]
    linarith
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcD (j : Fin (K+1)) : c j ≤ D := by
    have hh := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc q).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  refine ⟨S, D*(1+E), by positivity, ?_⟩
  intro V hV R hR j hj s hs
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let q : Fin (K+1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hsource : c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V ≤ D*Q := by
    have hsub : orders q ⊆ S := Finset.subset_biUnion_of_mem orders (Finset.mem_univ q)
    exact mul_le_mul (hcD q) (Seminorm.le_def.mp (Finset.sup_mono hsub) V)
      (by positivity) hD.le
  have hsmall := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).1
  have hlarge := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).2
  have hsmall' : ‖eulerDeriv (paperKernel V) j (R*Real.exp s)‖ ≤
      D*(1+E)*Q * R^(1/4 : ℝ) := by
    have he : (Real.exp s)^(1/4 : ℝ) ≤ E :=
      Real.rpow_le_rpow (by positivity) (Real.exp_le_exp.mpr ((le_abs_self s).trans hs)) (by norm_num)
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le] at hsmall
    calc
      _ ≤ (c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (R^(1/4 : ℝ) * (Real.exp s)^(1/4 : ℝ)) := hsmall
      _ ≤ (D*Q) * (R^(1/4 : ℝ) * E) := mul_le_mul hsource
          (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hQ (Real.rpow_nonneg hR.le (1/4 : ℝ))]
  have hlarge' : ‖eulerDeriv (paperKernel V) j (R*Real.exp s)‖ ≤ D*(1+E)*Q := by
    have hh : ‖eulerDeriv (paperKernel V) j (R*Real.exp s)‖ ≤ D*Q := by
      apply (le_trans ?_ hsource)
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hlarge
    exact hh.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hE.le) hQ])
  change _ ≤ D*(1+E)*Q * min 1 (R^(1/4 : ℝ))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ D*(1+E)*Q), mul_one]
  exact le_min hlarge' hsmall'

private theorem localized_source_seminorm
    (V F : ℝ → ℂ) (R L CW CF : ℝ) (n k : ℕ)
    (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) (hR : 0 < R)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s, ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s, (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) → |s| ≤ L)
    (hEuler : ∀ i ≤ n, ∀ s, |s| ≤ L → ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    (SchwartzMap.seminorm ℝ k n) (positiveLogProfile V F R hVc hVs hF hR) ≤
      L ^ k * derivativeConstant n CW CF := by
  let g := positiveLogProfile V F R hVc hVs hF hR
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hG : ContDiff ℝ ∞ G := by
    apply hF.comp_contDiff (by fun_prop)
    intro z
    exact mul_pos hR (Real.exp_pos _)
  have hgeq : (g : ℝ → ℂ) = fun z => V z * G z := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hF hR
  have hD : 0 ≤ derivativeConstant n CW CF := derivativeConstant_nonneg _ _ _ hCW hCF
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (mul_nonneg (pow_nonneg hL _) hD)
  intro s
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  by_cases hs : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
  · have hwindow' := hwindow s hs
    have hraw : ‖iteratedDeriv n g s‖ ≤ derivativeConstant n CW CF := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      apply hprod.trans
      unfold derivativeConstant
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hGi : ‖iteratedFDeriv ℝ (n - i) G s‖ ≤ CF := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show (G : ℝ → ℂ) = fun z => F (R * Real.exp z) from rfl,
          iteratedDeriv_log_eq_euler]
        exact hEuler (n - i) (Nat.sub_le _ _) s hwindow'
      gcongr
      exact hVderiv i hi' s
    have hsk : ‖s‖ ^ k ≤ L ^ k := by simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg s) hwindow' k
    exact mul_le_mul hsk hraw (norm_nonneg _) (pow_nonneg hL _)
  · have hz (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i V s‖ = 0 := by
      by_contra hne
      exact hs ⟨i, hi, hne⟩
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ‖iteratedFDeriv ℝ (n - i) G s‖) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    have hgzero : ‖iteratedDeriv n g s‖ = 0 := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact le_antisymm (hprod.trans_eq hsum) (norm_nonneg _)
    rw [hgzero, mul_zero]
    positivity

theorem source_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (J : ℕ) :
    ∃ (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * paperKernel V
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * kernelLogPhase t (slope i * y i)) *
            canonicalDensity U V R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) := by
  let T := ∑ i, |slope i| * M i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let K := J + (volume : Measure ℝ).integrablePower
  let L := T+1
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  obtain ⟨U, CW, hUc, hUs, hUone, hCW, hUderiv, hwindow⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  obtain ⟨S, CF, hCF, hkernel⟩ := paperKernel_window_source_bound a b ha K L
  let P0 := momentConstant K L CW CF
  let B0 := (2 : ℝ)^J * (JointLogSeparation.coefficientMomentBound 0 P0 +
    JointLogSeparation.coefficientMomentBound J P0)
  let B1 := JointLogSeparation.fourierPointBound J P0
  have hP0 : 0 ≤ P0 := momentConstant_nonneg K L CW CF hL hCW hCF.le
  have hB0 : 0 ≤ B0 := mul_nonneg (by positivity) (add_nonneg
    (JointLogSeparation.coefficientMomentBound_nonneg 0 P0 hP0)
    (JointLogSeparation.coefficientMomentBound_nonneg J P0 hP0))
  have hB1 : 0 ≤ B1 := JointLogSeparation.fourierPointBound_nonneg J P0 hP0
  refine ⟨U, S, B0+B1, add_nonneg hB0 hB1, hUc, hUs, ?_⟩
  intro V hV R hR
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let m := smallScalar R
  have hm : 0 < m := smallScalar_pos hR
  have hF := paperKernel_compact_source_smooth V a b ha hV (V.smooth ⊤)
  let g := positiveLogProfile U (paperKernel V) R hUc hUs hF hR
  let B : 𝓢(ℝ, ℂ) := ((m : ℂ)⁻¹) • (𝓕 g)
  have hcan (t : ℝ) : B t = canonicalDensity U V R t := by
    rfl
  have hnorm (t : ℝ) : ‖B t‖ = m⁻¹ * ‖(𝓕 g) t‖ := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have hP : 0 ≤ P0*Q := mul_nonneg hP0 hQ
  have hsource (n : ℕ) (hn : n ≤ K) : m⁻¹ *
      ((SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P0*Q := by
    have hsemi (k : ℕ) : (SchwartzMap.seminorm ℝ k n) g ≤
        L^k * derivativeConstant n CW (CF*Q*m) := by
      apply localized_source_seminorm U (paperKernel V)
        R L CW (CF*Q*m) n k hUc hUs hF hR hL hCW (by positivity)
      · intro i hi
        exact hUderiv i (hi.trans hn)
      · intro s hs
        exact (hwindow s (by obtain ⟨i, hi, hz⟩ := hs; exact ⟨i, hi.trans hn, hz⟩)).2.2
      · intro i hi s hs
        exact hkernel V hV R hR i (hi.trans hn) s hs
    have hd : derivativeConstant n CW (CF*Q*m) = derivativeConstant n CW CF * Q * m := by
      simp only [derivativeConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hs : (SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g ≤ (P0*Q)*m := by
      calc
        _ ≤ L^0 * derivativeConstant n CW (CF*Q*m) +
            L^(volume : Measure ℝ).integrablePower * derivativeConstant n CW (CF*Q*m) :=
          add_le_add (hsemi 0) (hsemi _)
        _ = ((1+L^(volume : Measure ℝ).integrablePower)*derivativeConstant n CW CF)*Q*m := by
          rw [hd]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (momentConstant_dominates K n L CW CF hL hCW hCF.le hn) hQ) hm.le
    exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)).trans_eq (by field_simp)
  have hB0Q : (2 : ℝ)^J * (JointLogSeparation.coefficientMomentBound 0 (P0*Q) +
      JointLogSeparation.coefficientMomentBound J (P0*Q)) = B0*Q := by
    dsimp only [B0]
    unfold JointLogSeparation.coefficientMomentBound
    ring
  have hB1Q : JointLogSeparation.fourierPointBound J (P0*Q) = B1*Q := by
    dsimp only [B1]
    unfold JointLogSeparation.fourierPointBound JointLogSeparation.fourierSeminormBound
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ i, windows i (y i)) ≠ 0 → U (∑ i, slope i*y i) = 1 :=
      JointLogSeparation.coupled_cutoff_active windows U slope y M hwindows (by simpa [T] using hUone)
    have hsep := coupled_positive_log_separation windows (paperKernel V)
      U R slope y hUc hUs hF hR hactive
    rw [hsep, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hcan]
    dsimp only [B]
    simp only [smul_apply, smul_eq_mul]
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    change _ = (m : ℂ)*_
    field_simp
    rfl
  · simp_rw [← hcan, hnorm]
    exact JointLogSeparation.schwartz_fourier_one_plus_integrable g J |>.const_mul m⁻¹ |>.congr
      (Filter.Eventually.of_forall (fun t => by dsimp only; ring))
  · simp_rw [← hcan, hnorm]
    have hh := JointLogSeparation.uniform_fourier_one_plus_moment g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP hsource
    rw [hB0Q] at hh
    have he : (∫ t : ℝ, (1+‖t‖)^J * (m⁻¹ * ‖(𝓕 g) t‖)) =
        m⁻¹ * ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 g) t‖ := by
      simp_rw [← mul_assoc, mul_comm ((1+‖_‖)^J) m⁻¹, mul_assoc]
      rw [integral_const_mul]
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB1) hQ)
  · intro t
    rw [← hcan, hnorm]
    have hh := JointLogSeparation.uniform_fourier_pointwise g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP (fun i hi => hsource i (hi.trans (by dsimp only [K]; omega))) t
    rw [hB1Q] at hh
    have he : (1+‖t‖)^J*(m⁻¹*‖(𝓕 g) t‖) = m⁻¹*(1+‖t‖)^J*‖(𝓕 g) t‖ := by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB0) hQ)

def twistedDensity (U W : ℝ → ℂ) (θ R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * paperKernel
      (Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s))) t

theorem normTwistedSource_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (W : ℝ → ℂ) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (n : ℕ) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * paperKernel
          (Vstar (CompletedHeight.normTwistedSource W θ))
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * kernelLogPhase t (slope i * y i)) *
            twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ≤ C * (1 + ‖θ‖)^n ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖ ≤ C * (1 + ‖θ‖)^n) := by
  obtain ⟨U, orders, C, hC, hUc, hUs, hsep⟩ :=
    source_uniform_separation a b ha windows slope M hM hwindows J
  let V := CompletedHeight.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    Vstar_support W a b hsupp
  obtain ⟨G, hG, hbound⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change kernelLogPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(kernelLogPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  obtain ⟨n, D, hD, hpoly⟩ := hbound orders
  refine ⟨U, n, C*D, mul_nonneg hC hD.le, hUc, hUs, ?_⟩
  intro θ R hR
  have hcan : canonicalDensity U (G θ) R = twistedDensity U W θ R := by
    unfold canonicalDensity twistedDensity
    rw [hlink θ]
  obtain ⟨heq, hi, hm, hp⟩ := hsep (G θ) (hGs θ) R hR
  rw [hcan] at heq hi hm hp
  rw [hlink θ] at heq
  have hb : C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G θ) ≤
      C*D * (1+‖θ‖)^n :=
    (mul_le_mul_of_nonneg_left (hpoly θ) hC).trans_eq (by ring)
  exact ⟨heq, hi, hm.trans hb, fun t => (hp t).trans hb⟩

theorem fourier_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (fun p : α × ℝ => (𝓕 (f p.1)) p.2) := by
  simp_rw [Real.fourier_eq']
  apply StronglyMeasurable.integral_prod_right
  have he : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 p.2) : ℂ) * Complex.I)) := by
    fun_prop
  exact (he.stronglyMeasurable.comp_measurable
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).smul
    (hf.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem paperKernel_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (a b : ℝ) (ha : 0 < a) (V : α → 𝓢(ℝ, ℂ))
    (hV : ∀ θ, Function.support (V θ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hf : StronglyMeasurable (fun p : α × ℝ => V p.1 (Real.exp p.2))) :
    StronglyMeasurable (fun p : α × Set.Ioi (0 : ℝ) =>
      paperKernel (V p.1) p.2) := by
  let f : α → ℝ → ℂ := fun θ s => V θ (Real.exp s)
  let g : α → ℝ → ℂ := fun θ u => cubicKernelAxisMultiplier u * (𝓕 (f θ)) u
  have hfF := fourier_joint_stronglyMeasurable f hf
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (cubicKernelAxisMultiplier_continuous.stronglyMeasurable.comp_measurable
      measurable_snd).mul hfF
  have hgF := fourier_joint_stronglyMeasurable g hg
  have harg : Measurable (fun p : α × Set.Ioi (0 : ℝ) =>
      (p.1, Real.log (paperScale * (p.2 : ℝ)))) :=
    measurable_fst.prodMk (Real.measurable_log.comp
      (measurable_const.mul (measurable_subtype_coe.comp measurable_snd)))
  convert hgF.comp_measurable harg using 1
  funext p
  let L := kernelLogSource (V p.1) a b ha (hV p.1) ((V p.1).smooth ⊤)
  exact paperKernel_eq_logFourier (V p.1) L
    (fun _ => rfl) p.2 p.2.property

private theorem twistedDensity_measurable_of_profile
    (U W : ℝ → ℂ) (R : ℝ)
    (hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * paperKernel
        (Vstar (CompletedHeight.normTwistedSource W p.1)) (R * Real.exp p.2))) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  unfold twistedDensity
  exact stronglyMeasurable_const.mul (fourier_joint_stronglyMeasurable
    (fun θ s => U s * paperKernel
      (Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s)) hprofile)

private theorem exists_measurable_twisted_source
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ G : ℝ → 𝓢(ℝ, ℂ),
      (∀ θ, (G θ : ℝ → ℂ) = Vstar (CompletedHeight.normTwistedSource W θ)) ∧
      (∀ θ, Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b) ∧
      StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
  let V := CompletedHeight.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    Vstar_support W a b hsupp
  obtain ⟨G, hG, _⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change kernelLogPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(kernelLogPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
    simp_rw [hG, CompletedHeight.normTwistedSource, Real.log_exp]
    apply Continuous.stronglyMeasurable
    unfold kernelLogPhase
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2*Real.pi*p.1*p.2) : ℂ)*Complex.I))).mul
      (V.continuous.comp (Real.continuous_exp.comp continuous_snd))
  exact ⟨G, hlink, hGs, hf⟩

theorem twistedDensity_joint_stronglyMeasurable
    (U W : ℝ → ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (R : ℝ) (hR : 0 < R) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  obtain ⟨G, hlink, hGs, hf⟩ := exists_measurable_twisted_source W a b ha hsupp hW
  have hkernel := paperKernel_joint_stronglyMeasurable a b ha G hGs hf
  have harg : Measurable (fun p : ℝ × ℝ =>
      (p.1, (⟨R * Real.exp p.2, mul_pos hR (Real.exp_pos _)⟩ : Set.Ioi (0 : ℝ)))) :=
    measurable_fst.prodMk ((measurable_const.mul (Real.measurable_exp.comp measurable_snd)).subtype_mk)
  have hcomposed := hkernel.comp_measurable harg
  change StronglyMeasurable (fun p : ℝ × ℝ =>
    paperKernel (G p.1) (R * Real.exp p.2)) at hcomposed
  have hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * paperKernel
        (Vstar (CompletedHeight.normTwistedSource W p.1)) (R*Real.exp p.2)) := by
    have hprofileG : StronglyMeasurable (fun p : ℝ × ℝ =>
        U p.2 * paperKernel (G p.1) (R * Real.exp p.2)) :=
      (hU.stronglyMeasurable.comp_measurable measurable_snd).mul
        hcomposed
    convert hprofileG using 1
    exact funext (fun p => congrArg
      (fun V : ℝ → ℂ => U p.2 * paperKernel V (R * Real.exp p.2))
      (hlink p.1).symm)
  exact twistedDensity_measurable_of_profile U W R hprofile

end
end InverseKernelSourceUniform

end

noncomputable section
open Eisenstein CompletedGauss NormalizedReflection
open scoped Classical
namespace InverseTerminalWidths
theorem surviving_local_piece (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (j : ℕ) (e : Fin 3) (n b : O)
    (hne : reflectedLocalPiece P hg j e n b ≠ 0) :
    (j ≠ 4 → e = 0) ∧ (j = 4 → e = 1 → n ∈ P) ∧
      (j = 4 → e = 2 → n ∉ P ∧ b ∈ P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    by_contra he
    exact hne (by simp [reflectedLocalPiece, hj, he])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])


end InverseTerminalWidths
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace InverseTerminalWidths
open Eisenstein CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q : Ideal O) (hI : I ≠ 0)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm (rowResidualPart I Q) : ℝ) * CH) *
          ((Ideal.absNorm (rowPowerfulPart I) : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowResidualPart I Q) : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using actual_residual_norm_width I Q hI) (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

def normWidth (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z (rowResidualPart I (B * F * R)) +
      reflectionWidth Z P (fun i => completedLocalExponent I F (P i)) e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z (rowPowerfulPart I) +
        normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hx := actual_ideal_norm_pos (rowResidualPart I (B * F * R))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) (B * F * R))
  have hc := reflectionConductorCost_pos P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B hI hF hR hB P hcop hpool hres e)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P (fun i => NeZero.ne (P i)),
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal O) (hI : I ≠ 0) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal O) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal O) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

theorem logb_widthConstant (Z : ℝ) (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0) -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R hI hF hB hR P hcop hpool hres e Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower (rowPowerfulPart I) Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower (rowResidualPart I (B * F * R)) Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem rpow_reflectionWidth {ι : Type*} [Fintype ι]
    (Z : ℝ) (hZ : 1 < Z) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0)
    (j : ι → ℕ) (e : ι → Fin 3) :
    Z ^ reflectionWidth Z P j e = reflectionConductorCost P j e := by
  rw [← logb_reflectionConductorCost Z P hP j e]
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (reflectionConductorCost_pos P hP j e)

theorem width_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η := by
  have hb := actual_ideal_norm_pos B hB
  obtain ⟨a, ha, h₁⟩ := constant_log_error (CH * Ck * CO) η (by positivity) hη
  obtain ⟨b, hb', h₂⟩ := constant_log_error (widthConstant B Ck CO CH Cf) η
    (by unfold widthConstant; positivity) hη
  exact ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ =>
    ⟨h₁ Z ((le_max_left _ _).trans hZ), h₂ Z ((le_max_right _ _).trans hZ)⟩⟩

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

def ramifiedWidth (Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z 3

theorem rpow_ramifiedWidth (Z : ℝ) (hZ : 1 < Z) (m : ℕ) :
    Z ^ ramifiedWidth Z m = (3 : ℝ) ^ ((m : ℝ) - 4) := by
  unfold ramifiedWidth
  rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ Z),
    Real.rpow_logb (by linarith : 0 < Z) (ne_of_gt hZ) (by norm_num : (0 : ℝ) < 3)]

theorem ramified_width_threshold (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error ((3 : ℝ) ^ (4 : ℕ)) η (by norm_num) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z ((3 : ℝ) ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hz (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem terminal_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨a, ha, h₁⟩ := width_error_threshold B hB Ck CO CH Cf η hk ho hh hf hη
  obtain ⟨b, hb, h₂⟩ := ramified_width_threshold η hη
  refine ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ => ?_⟩
  exact ⟨(h₁ Z ((le_max_left _ _).trans hZ)).1,
    (h₁ Z ((le_max_left _ _).trans hZ)).2, h₂ Z ((le_max_right _ _).trans hZ)⟩

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
      za v ell el (terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) hI Z M O₀ H Ck CO CH hZ hCk hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R hI hF hB hR P hcop hpool hres e
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ


end InverseTerminalWidths

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedNormalization
open InverseTerminalWidths
noncomputable section

def outsideScalar (Z v ell el S₀ B₀ Td : ℝ) : ℝ :=
  Z ^ (-v/2-ell-el/3-(S₀+B₀)/2) *
    InverseKernelSourceUniform.smallScalar (Z ^ (v+3*ell+el-Td))

theorem smallScalar_rpow {Z : ℝ} (hZ : 1 ≤ Z) (d : ℝ) :
    InverseKernelSourceUniform.smallScalar (Z ^ (-d)) = Z ^ (-max 0 d/4) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold InverseKernelSourceUniform.smallScalar
  rw [← Real.rpow_mul hZ0.le]
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd, min_eq_right]
    · congr 1; ring
    · calc
        Z ^ (-d * (1/4:ℝ)) ≤ Z ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
        _ = 1 := Real.rpow_zero _
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_left hd', neg_zero, zero_div, Real.rpow_zero, min_eq_left]
    calc
      1 = Z ^ (0:ℝ) := (Real.rpow_zero _).symm
      _ ≤ Z ^ (-d*(1/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem outsideScalar_square {Z : ℝ} (hZ : 1 ≤ Z) (v ell el S₀ B₀ Td : ℝ) :
    outsideScalar Z v ell el S₀ B₀ Td ^ 2 =
      Z ^ (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold outsideScalar
  rw [show v+3*ell+el-Td = -(Td-v-3*ell-el) by ring, smallScalar_rpow hZ,
    ← Real.rpow_add hZ0, ← Real.rpow_mul_natCast hZ0.le]
  congr 1
  ring

theorem row_shape {Z : ℝ} (hZ : 1 ≤ Z) (H v ell : ℝ) :
    Z^H + Z^v*Z^ell ≤ 2*Z^(max H (v+ell)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [← Real.rpow_add hZ0]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v+ell))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v+ell))
  linarith

theorem cubic_shape {Z : ℝ} (hZ : 1 ≤ Z) (v za : ℝ) :
    Z^v + Z^za + (Z^v*Z^za)^(2/3:ℝ) ≤ 3*Z^(v+za-hybridSaving v za) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hv : hybridSaving v za ≤ v := min_le_left _ _
  have hz : hybridSaving v za ≤ za := (min_le_right _ _).trans (min_le_left _ _)
  have ht : hybridSaving v za ≤ (v+za)/3 := (min_le_right _ _).trans (min_le_right _ _)
  rw [← Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (show v ≤ v+za-hybridSaving v za by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (show za ≤ v+za-hybridSaving v za by linarith)
  have h3 := Real.rpow_le_rpow_of_exponent_le hZ (show (v+za)*(2/3:ℝ) ≤ v+za-hybridSaving v za by linarith)
  linarith

theorem reflected_exponent_identity (H v ell el S₀ B₀ Td za ε : ℝ) :
    (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) +
      (H+v+ell+za)*ε + max H (v+ell) + ell + (v+za-hybridSaving v za) =
    reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za) := by
  unfold reflectedExponent
  ring

theorem normalized_hybrid_shape {Z : ℝ} (hZ : 1 ≤ Z)
    (H v ell el S₀ B₀ Td za ε : ℝ) :
    (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      ((Z^H*Z^v*Z^ell*Z^za)^ε * (Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) ≤
      6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : (Z^H*Z^v*Z^ell*Z^za)^ε = Z^((H+v+ell+za)*ε) := by
    rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
      ← Real.rpow_mul hZ0.le]
  have hb := mul_le_mul (row_shape hZ H v ell) (cubic_shape hZ v za)
    (by positivity : 0 ≤ Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell by positivity)
  calc
    _ ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
        (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell *
        ((2*Z^(max H (v+ell)))*(3*Z^(v+za-hybridSaving v za))) := by
      nlinarith only [hh]
    _ = 6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
      rw [outsideScalar_square hZ,hp]
      calc
        _ = 6*(Z^(-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) *
          Z^((H+v+ell+za)*ε) * Z^(max H (v+ell)) * Z^ell *
          Z^(v+za-hybridSaving v za)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
            ← Real.rpow_add hZ0,reflected_exponent_identity]

end
end InverseReflectedNormalization

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
