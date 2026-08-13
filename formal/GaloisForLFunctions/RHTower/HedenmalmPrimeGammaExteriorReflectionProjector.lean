import GaloisForLFunctions.RHTower.HedenmalmExteriorCayleyAbelGreenLanding
import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryDivisorClosure

/-!
# Prime--Gamma exterior reflection projector

Global exterior determinants ordinarily mix every pair of Xi zeros. This module proves a mixed
covariance law that removes those cross minors before scalarization: determinant rows carry
contragredient fixed-prime clocks and covariant horizontal Cayley clocks. Triple Cesaro averaging
then selects exactly `sigma = 1 - conj rho`. The two ordered surviving minors symmetrize into a
Pluecker square, while critical-line fixed points vanish identically.

The same module identifies the transverse Ward coordinate as the Abel boundary of a regular
source-Cayley resolvent. Together these results replace post-divisor `1 / Im z` insertion by a
source-geometric approximation scheme. All theorems are unconditional.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Bilinear two-feature determinant with independently weighted rows. -/
def finiteOrientedExteriorDeterminant
    {ι : Type*} (s : Finset ι) (f g left right : ι → ℂ) : ℂ :=
  (∑ i ∈ s, left i * f i ^ 2) * (∑ j ∈ s, right j * g j ^ 2) -
    (∑ i ∈ s, left i * f i * g i) *
      (∑ j ∈ s, right j * f j * g j)

/-- Exact ordered Cauchy--Binet expansion of the oriented determinant. -/
theorem finiteOrientedExteriorDeterminant_eq_pairSum
    {ι : Type*} (s : Finset ι) (f g left right : ι → ℂ) :
    finiteOrientedExteriorDeterminant s f g left right =
      ∑ i ∈ s, ∑ j ∈ s,
        left i * right j * (f i * g j) * (f i * g j - f j * g i) := by
  rw [finiteOrientedExteriorDeterminant, Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Three-clock pair projector. Prime clocks are contragredient; horizontal clock is covariant. -/
def finiteExteriorReflectionProjector
    {ι : Type*} (s : Finset ι) (C : ι → ι → ℂ)
    (z w u : ι → ℂ) (N : ℕ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, C i j *
    (((N : ℝ)⁻¹ : ℂ) * ∑ a ∈ Finset.range N, (z i * star (z j)) ^ a) *
    (((N : ℝ)⁻¹ : ℂ) * ∑ b ∈ Finset.range N, (w i * star (w j)) ^ b) *
    (((N : ℝ)⁻¹ : ℂ) * ∑ c ∈ Finset.range N, (u i * u j) ^ c)

/-- The mixed-covariance projector keeps exactly equal prime clocks and reciprocal Cayley clocks. -/
theorem tendsto_finiteExteriorReflectionProjector
    {ι : Type*} (s : Finset ι) (C : ι → ι → ℂ)
    (z w u : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (hu : ∀ i ∈ s, ‖u i‖ = 1) :
    Tendsto (finiteExteriorReflectionProjector s C z w u) atTop
      (nhds (∑ i ∈ s, ∑ j ∈ s,
        if z i = z j ∧ w i = w j ∧ u i * u j = 1 then C i j else 0)) := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Tendsto (fun N : ℕ => C i j *
          (((N : ℝ)⁻¹ : ℂ) * ∑ a ∈ Finset.range N, (z i * star (z j)) ^ a) *
          (((N : ℝ)⁻¹ : ℂ) * ∑ b ∈ Finset.range N, (w i * star (w j)) ^ b) *
          (((N : ℝ)⁻¹ : ℂ) * ∑ c ∈ Finset.range N, (u i * u j) ^ c))
        atTop
        (nhds (if z i = z j ∧ w i = w j ∧ u i * u j = 1 then C i j else 0)) := by
    have hzmode : ‖z i * star (z j)‖ = 1 := by
      rw [norm_mul, norm_star, hz i hi, hz j hj, one_mul]
    have hwmode : ‖w i * star (w j)‖ = 1 := by
      rw [norm_mul, norm_star, hw i hi, hw j hj, one_mul]
    have humode : ‖u i * u j‖ = 1 := by
      rw [norm_mul, hu i hi, hu j hj, one_mul]
    have hzlim := tendsto_complex_geom_cesaro_of_norm_eq_one
      (z i * star (z j)) hzmode
    have hwlim := tendsto_complex_geom_cesaro_of_norm_eq_one
      (w i * star (w j)) hwmode
    have hulim := tendsto_complex_geom_cesaro_of_norm_eq_one
      (u i * u j) humode
    have hconst : Tendsto (fun _ : ℕ => C i j) atTop (nhds (C i j)) :=
      tendsto_const_nhds
    have hlim := ((hconst.mul hzlim).mul hwlim).mul hulim
    convert hlim using 1
    have hziff : z i * star (z j) = 1 ↔ z i = z j := by
      rw [mul_comm, star_mul_eq_one_iff_eq (hz j hj) (hz i hi), eq_comm]
    have hwiff : w i * star (w j) = 1 ↔ w i = w j := by
      rw [mul_comm, star_mul_eq_one_iff_eq (hw j hj) (hw i hi), eq_comm]
    simp only [hziff, hwiff]
    split_ifs <;> simp_all
  have hsumOuter := tendsto_finsetSum s fun i hi =>
    tendsto_finsetSum s (hpoint i hi)
  change Tendsto (fun N : ℕ => ∑ i ∈ s, ∑ j ∈ s, C i j *
      (((N : ℝ)⁻¹ : ℂ) * ∑ a ∈ Finset.range N, (z i * star (z j)) ^ a) *
      (((N : ℝ)⁻¹ : ℂ) * ∑ b ∈ Finset.range N, (w i * star (w j)) ^ b) *
      (((N : ℝ)⁻¹ : ℂ) * ∑ c ∈ Finset.range N, (u i * u j) ^ c)) atTop _
  exact hsumOuter

/-- Oriented three-clock determinant at one depth triple. -/
def finiteExteriorReflectionDeterminant
    {ι : Type*} (s : Finset ι) (r f g z w u : ι → ℂ)
    (a b c : ℕ) : ℂ :=
  finiteOrientedExteriorDeterminant s f g
    (fun i => r i * z i ^ a * w i ^ b * u i ^ c)
    (fun i => r i * star (z i) ^ a * star (w i) ^ b * u i ^ c)

theorem finiteExteriorReflectionDeterminant_eq_pairSum
    {ι : Type*} (s : Finset ι) (r f g z w u : ι → ℂ)
    (a b c : ℕ) :
    finiteExteriorReflectionDeterminant s r f g z w u a b c =
      ∑ i ∈ s, ∑ j ∈ s,
        r i * r j * (f i * g j) * (f i * g j - f j * g i) *
          (z i * star (z j)) ^ a * (w i * star (w j)) ^ b *
          (u i * u j) ^ c := by
  rw [finiteExteriorReflectionDeterminant,
    finiteOrientedExteriorDeterminant_eq_pairSum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow, starRingEnd_apply]
  ring

/-- The pair-projector is exactly the normalized triple Cesaro average of source determinants. -/
theorem finiteExteriorReflectionProjector_eq_detCesaro
    {ι : Type*} (s : Finset ι) (r f g z w u : ι → ℂ) (N : ℕ) :
    finiteExteriorReflectionProjector s
        (fun i j => r i * r j * (f i * g j) * (f i * g j - f j * g i))
        z w u N =
      (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          finiteExteriorReflectionDeterminant s r f g z w u a b c := by
  classical
  let K : ℂ := ((N : ℝ)⁻¹ : ℂ)
  let C : ι → ι → ℂ := fun i j =>
    r i * r j * (f i * g j) * (f i * g j - f j * g i)
  let Z : ι → ι → ℂ := fun i j => z i * star (z j)
  let W : ι → ι → ℂ := fun i j => w i * star (w j)
  let U : ι → ι → ℂ := fun i j => u i * u j
  have hfactor (i j : ι) :
      C i j * (K * ∑ a ∈ Finset.range N, Z i j ^ a) *
          (K * ∑ b ∈ Finset.range N, W i j ^ b) *
          (K * ∑ c ∈ Finset.range N, U i j ^ c) =
        K ^ 3 * ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ∑ c ∈ Finset.range N,
            C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
    rw [show C i j * (K * ∑ a ∈ Finset.range N, Z i j ^ a) *
        (K * ∑ b ∈ Finset.range N, W i j ^ b) *
        (K * ∑ c ∈ Finset.range N, U i j ^ c) =
      K ^ 3 * ((C i j * ∑ a ∈ Finset.range N, Z i j ^ a) *
        (∑ b ∈ Finset.range N, W i j ^ b) *
        (∑ c ∈ Finset.range N, U i j ^ c)) by ring]
    congr 1
    calc
      (C i j * ∑ a ∈ Finset.range N, Z i j ^ a) *
          (∑ b ∈ Finset.range N, W i j ^ b) *
          (∑ c ∈ Finset.range N, U i j ^ c) =
        (∑ a ∈ Finset.range N, C i j * Z i j ^ a) *
          (∑ b ∈ Finset.range N, W i j ^ b) *
          (∑ c ∈ Finset.range N, U i j ^ c) := by
            congr 2
            rw [Finset.mul_sum]
      _ = (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          C i j * Z i j ^ a * W i j ^ b) *
          (∑ c ∈ Finset.range N, U i j ^ c) := by
            rw [Finset.sum_mul]
            apply congrArg (fun x => x * ∑ c ∈ Finset.range N, U i j ^ c)
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
      _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ∑ c ∈ Finset.range N,
            C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum]
  rw [finiteExteriorReflectionProjector]
  change (∑ i ∈ s, ∑ j ∈ s,
      C i j * (K * ∑ a ∈ Finset.range N, Z i j ^ a) *
        (K * ∑ b ∈ Finset.range N, W i j ^ b) *
        (K * ∑ c ∈ Finset.range N, U i j ^ c)) = _
  simp_rw [hfactor]
  calc
    (∑ i ∈ s, ∑ j ∈ s, K ^ 3 * ∑ a ∈ Finset.range N,
        ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          C i j * Z i j ^ a * W i j ^ b * U i j ^ c) =
      K ^ 3 * ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ Finset.range N,
        ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      simp_rw [finiteExteriorReflectionDeterminant_eq_pairSum]
      change (∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
            C i j * Z i j ^ a * W i j ^ b * U i j ^ c) =
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          ∑ i ∈ s, ∑ j ∈ s,
            C i j * Z i j ^ a * W i j ^ b * U i j ^ c
      calc
        _ = ∑ i ∈ s, ∑ a ∈ Finset.range N, ∑ j ∈ s,
            ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
              C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
        _ = ∑ a ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
            ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
              C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
                rw [Finset.sum_comm]
        _ = ∑ a ∈ Finset.range N, ∑ i ∈ s, ∑ b ∈ Finset.range N,
            ∑ j ∈ s, ∑ c ∈ Finset.range N,
              C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
                apply Finset.sum_congr rfl
                intro a ha
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
        _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i ∈ s,
            ∑ j ∈ s, ∑ c ∈ Finset.range N,
              C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.sum_comm]
        _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i ∈ s,
            ∑ c ∈ Finset.range N, ∑ j ∈ s,
              C i j * Z i j ^ a * W i j ^ b * U i j ^ c := by
                apply Finset.sum_congr rfl
                intro a ha
                apply Finset.sum_congr rfl
                intro b hb
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
        _ = _ := by
                apply Finset.sum_congr rfl
                intro a ha
                apply Finset.sum_congr rfl
                intro b hb
                rw [Finset.sum_comm]

/-- Real Cayley reflection is reciprocal on the unit circle. -/
theorem realCayley_neg_mul (x : ℝ) :
    GaloisForLFunctions.HTGeometry.realCayley x *
      GaloisForLFunctions.HTGeometry.realCayley (-x) = 1 := by
  have hp : (x : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero x
  have hm : ((-x : ℝ) : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero (-x)
  unfold GaloisForLFunctions.HTGeometry.realCayley
  field_simp [hp, hm]
  apply Complex.ext <;> norm_num

/-- Two prime clocks plus covariant Cayley reciprocity select exactly line reflection. -/
theorem xiExteriorReflectionPhase_selector_iff
    (rho sigma : XiDivisorSupport) :
    (xiHorizontalPrimePhase 2 (rho : ℂ).im =
        xiHorizontalPrimePhase 2 (sigma : ℂ).im ∧
      xiHorizontalPrimePhase 3 (rho : ℂ).im =
        xiHorizontalPrimePhase 3 (sigma : ℂ).im ∧
      xiHorizontalSourceCayleyPhase (rho : ℂ) *
          xiHorizontalSourceCayleyPhase (sigma : ℂ) = 1) ↔
      sigma = xiZeroLineConjEquiv rho := by
  constructor
  · rintro ⟨h2, h3, hu⟩
    have him : (rho : ℂ).im = (sigma : ℂ).im :=
      xiHorizontalPrimePhase_pair_injective (Prod.ext h2 h3)
    have hrecip : xiHorizontalSourceCayleyPhase (sigma : ℂ) =
        xiHorizontalSourceCayleyPhase (xiZeroLineConjEquiv rho : ℂ) := by
      have hline :
          xiHorizontalSourceCayleyPhase (rho : ℂ) *
              xiHorizontalSourceCayleyPhase (xiZeroLineConjEquiv rho : ℂ) = 1 := by
        rw [xiHorizontalSourceCayleyPhase,
          xiHorizontalSourceCayleyPhase, xiZeroLineConjEquiv_apply]
        rw [show 2 * (1 - (starRingEnd ℂ) (rho : ℂ)).re - 1 =
          -(2 * (rho : ℂ).re - 1) by simp; ring]
        exact realCayley_neg_mul (2 * (rho : ℂ).re - 1)
      have hne : xiHorizontalSourceCayleyPhase (rho : ℂ) ≠ 0 := by
        exact norm_ne_zero_iff.mp (by rw [xiHorizontalSourceCayleyPhase_norm]; norm_num)
      apply mul_left_cancel₀ hne
      exact hu.trans hline.symm
    apply Subtype.ext
    apply eq_of_im_eq_of_horizontalSourceCayleyPhase_eq
    · simpa [xiZeroLineConjEquiv_apply] using him.symm
    · exact hrecip
  · intro hsigma
    subst sigma
    constructor
    · apply congrArg (xiHorizontalPrimePhase 2)
      simp [xiZeroLineConjEquiv_apply]
    constructor
    · apply congrArg (xiHorizontalPrimePhase 3)
      simp [xiZeroLineConjEquiv_apply]
    · rw [xiHorizontalSourceCayleyPhase,
        xiHorizontalSourceCayleyPhase, xiZeroLineConjEquiv_apply]
      rw [show 2 * (1 - (starRingEnd ℂ) (rho : ℂ)).re - 1 =
        -(2 * (rho : ℂ).re - 1) by simp; ring]
      exact realCayley_neg_mul (2 * (rho : ℂ).re - 1)

/-- Three-clock pair projector specialized to Xi divisor support. -/
def xiPrimeCayleyExteriorReflectionProjector
    (S : Finset XiDivisorSupport)
    (C : XiDivisorSupport → XiDivisorSupport → ℂ) (N : ℕ) : ℂ :=
  finiteExteriorReflectionProjector S C
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (fun rho => xiHorizontalSourceCayleyPhase (rho : ℂ)) N

/-- Xi specialization: mixed prime/Cayley covariance projects exactly onto line reflection. -/
theorem tendsto_xiPrimeCayleyExteriorReflectionProjector
    (S : Finset XiDivisorSupport)
    (C : XiDivisorSupport → XiDivisorSupport → ℂ) :
    Tendsto (xiPrimeCayleyExteriorReflectionProjector S C) atTop
      (nhds (∑ rho ∈ S, ∑ sigma ∈ S,
        if sigma = xiZeroLineConjEquiv rho then C rho sigma else 0)) := by
  have hlim := tendsto_finiteExteriorReflectionProjector S C
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (fun rho => xiHorizontalSourceCayleyPhase (rho : ℂ))
    (fun rho _ => xiHorizontalPrimePhase_norm 2 (rho : ℂ).im)
    (fun rho _ => xiHorizontalPrimePhase_norm 3 (rho : ℂ).im)
    (fun rho _ => xiHorizontalSourceCayleyPhase_norm (rho : ℂ))
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    apply Finset.sum_congr rfl
    intro rho hrho
    apply Finset.sum_congr rfl
    intro sigma hsigma
    simp only [xiExteriorReflectionPhase_selector_iff]

/-- A reflection-closed packet collapses the selected double sum to one reflected partner. -/
theorem xiExteriorReflectionSelectedPairSum_eq
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (C : XiDivisorSupport → XiDivisorSupport → ℂ) :
    (∑ rho ∈ S, ∑ sigma ∈ S,
        if sigma = xiZeroLineConjEquiv rho then C rho sigma else 0) =
      ∑ rho ∈ S, C rho (xiZeroLineConjEquiv rho) := by
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [Finset.sum_eq_single (xiZeroLineConjEquiv rho)]
  · simp
  · intro sigma hsigma hne
    rw [if_neg hne]
  · exact fun hnot => (hnot (hclosed rho hrho)).elim

/-- Reindexing a reflection-closed packet by critical-line reflection preserves every sum. -/
theorem sum_comp_xiZeroLineConjEquiv_eq
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (F : XiDivisorSupport → ℂ) :
    (∑ rho ∈ S, F (xiZeroLineConjEquiv rho)) = ∑ rho ∈ S, F rho := by
  refine Finset.sum_bij'
    (fun rho _ => xiZeroLineConjEquiv rho)
    (fun rho _ => xiZeroLineConjEquiv rho)
    hclosed hclosed ?_ ?_ ?_
  · intro rho hrho
    exact xiZeroLineConjEquiv_involutive rho
  · intro rho hrho
    exact xiZeroLineConjEquiv_involutive rho
  · intro rho hrho
    rfl

/-- Reflection symmetrizes ordered minors into one half of the Pluecker square sum. -/
theorem xiReflectionOrientedMinor_sum_eq_half_square
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (r f g : XiDivisorSupport → ℂ) :
    (∑ rho ∈ S,
        r rho * r (xiZeroLineConjEquiv rho) *
          (f rho * g (xiZeroLineConjEquiv rho)) *
          (f rho * g (xiZeroLineConjEquiv rho) -
            f (xiZeroLineConjEquiv rho) * g rho)) =
      (1 / 2 : ℂ) * ∑ rho ∈ S,
        r rho * r (xiZeroLineConjEquiv rho) *
          (f rho * g (xiZeroLineConjEquiv rho) -
            f (xiZeroLineConjEquiv rho) * g rho) ^ 2 := by
  let A : XiDivisorSupport → ℂ := fun rho =>
    r rho * r (xiZeroLineConjEquiv rho) *
      (f rho * g (xiZeroLineConjEquiv rho)) *
      (f rho * g (xiZeroLineConjEquiv rho) -
        f (xiZeroLineConjEquiv rho) * g rho)
  let Q : XiDivisorSupport → ℂ := fun rho =>
    r rho * r (xiZeroLineConjEquiv rho) *
      (f rho * g (xiZeroLineConjEquiv rho) -
        f (xiZeroLineConjEquiv rho) * g rho) ^ 2
  have hreindex : (∑ rho ∈ S, A (xiZeroLineConjEquiv rho)) =
      ∑ rho ∈ S, A rho :=
    sum_comp_xiZeroLineConjEquiv_eq S hclosed A
  have hpair (rho : XiDivisorSupport) :
      A rho + A (xiZeroLineConjEquiv rho) = Q rho := by
    simp only [A, Q]
    rw [xiZeroLineConjEquiv_involutive rho]
    ring
  change (∑ rho ∈ S, A rho) = (1 / 2 : ℂ) * ∑ rho ∈ S, Q rho
  have hdouble : 2 * (∑ rho ∈ S, A rho) = ∑ rho ∈ S, Q rho := by
    calc
      2 * (∑ rho ∈ S, A rho) =
          (∑ rho ∈ S, A rho) + ∑ rho ∈ S, A (xiZeroLineConjEquiv rho) := by
            rw [hreindex]
            ring
      _ = ∑ rho ∈ S, (A rho + A (xiZeroLineConjEquiv rho)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ rho ∈ S, Q rho := by
            apply Finset.sum_congr rfl
            intro rho hrho
            exact hpair rho
  rw [← hdouble]
  ring

/-- Source determinant with contragredient prime rows and covariant horizontal Cayley rows. -/
def xiPrimeCayleyExteriorReflectionDeterminant
    (S : Finset XiDivisorSupport) (r f g : XiDivisorSupport → ℂ)
    (a b c : ℕ) : ℂ :=
  finiteExteriorReflectionDeterminant S r f g
    (fun rho => xiHorizontalPrimePhase 2 (rho : ℂ).im)
    (fun rho => xiHorizontalPrimePhase 3 (rho : ℂ).im)
    (fun rho => xiHorizontalSourceCayleyPhase (rho : ℂ)) a b c

/-- Exact source determinant Cesaro limit: only reflected Pluecker squares survive. -/
theorem tendsto_xiPrimeCayleyExteriorReflectionDeterminant
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (r f g : XiDivisorSupport → ℂ) :
    Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeCayleyExteriorReflectionDeterminant S r f g a b c)
      atTop
      (nhds ((1 / 2 : ℂ) * ∑ rho ∈ S,
        r rho * r (xiZeroLineConjEquiv rho) *
          (f rho * g (xiZeroLineConjEquiv rho) -
            f (xiZeroLineConjEquiv rho) * g rho) ^ 2)) := by
  let C : XiDivisorSupport → XiDivisorSupport → ℂ := fun rho sigma =>
    r rho * r sigma * (f rho * g sigma) *
      (f rho * g sigma - f sigma * g rho)
  have hprojector := tendsto_xiPrimeCayleyExteriorReflectionProjector S C
  have hdet : Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeCayleyExteriorReflectionDeterminant S r f g a b c)
      atTop
      (nhds (∑ rho ∈ S, ∑ sigma ∈ S,
        if sigma = xiZeroLineConjEquiv rho then C rho sigma else 0)) := by
    apply hprojector.congr'
    filter_upwards with N
    rw [xiPrimeCayleyExteriorReflectionProjector,
      finiteExteriorReflectionProjector_eq_detCesaro]
    rfl
  rw [xiExteriorReflectionSelectedPairSum_eq S hclosed C] at hdet
  have hsym := xiReflectionOrientedMinor_sum_eq_half_square S hclosed r f g
  have hlimitEq :
      (∑ rho ∈ S, C rho (xiZeroLineConjEquiv rho)) =
        (1 / 2 : ℂ) * ∑ rho ∈ S,
          r rho * r (xiZeroLineConjEquiv rho) *
            (f rho * g (xiZeroLineConjEquiv rho) -
              f (xiZeroLineConjEquiv rho) * g rho) ^ 2 := by
    simpa only [C] using hsym
  rw [hlimitEq] at hdet
  exact hdet

/-- Abel-regularized source-Cayley realization of the transverse reciprocal coordinate. -/
def cayleyTransverseAbelMultiplier (R x : ℝ) : ℂ :=
  2 * I * (1 - GaloisForLFunctions.HTGeometry.realCayley x) *
    (1 + (R : ℂ) * GaloisForLFunctions.HTGeometry.realCayley x)⁻¹

/-- At the Abel boundary, the Cayley multiplier is exactly `-2/x`. -/
theorem cayleyTransverseAbelMultiplier_one_eq
    {x : ℝ} (hx : x ≠ 0) :
    cayleyTransverseAbelMultiplier 1 x = ((-2 / x : ℝ) : ℂ) := by
  have hp : (x : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero x
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  unfold cayleyTransverseAbelMultiplier
    GaloisForLFunctions.HTGeometry.realCayley
  field_simp [hp, hxC]
  apply Complex.ext <;> norm_num [hx] <;> field_simp [hx] <;> ring

theorem criticalFeatureCauchyKernelTest_conj (t : ℝ) (z : ℂ) :
    criticalFeatureCauchyKernelTest t ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (criticalFeatureCauchyKernelTest t z) := by
  simp [criticalFeatureCauchyKernelTest, criticalHardyLowerCauchyTest,
    criticalHardyUpperCauchyTest, xiWeilCauchyTest]
  ring

/-- Boundary source-Cayley multiplier, including its totalized value at the fixed point. -/
theorem sourceCayleyAbelGreenMultiplier_one_eq_totalized (x : ℝ) :
    sourceCayleyAbelGreenMultiplier 1 x = ((-2 / x : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [sourceCayleyAbelGreenMultiplier,
      GaloisForLFunctions.HTGeometry.realCayley]
  · exact sourceCayleyAbelGreenMultiplier_one_eq hx

/-- Critical feature evaluated at one centered Xi spectral point. -/
def xiCriticalFeatureSpectralValue (t : ℝ) (rho : XiDivisorSupport) : ℂ :=
  criticalFeatureCauchyKernelTest t (xiSpectralPointSupport rho)

theorem xiCriticalFeatureSpectralValue_lineConj
    (t : ℝ) (rho : XiDivisorSupport) :
    xiCriticalFeatureSpectralValue t (xiZeroLineConjEquiv rho) =
      star (xiCriticalFeatureSpectralValue t rho) := by
  rw [xiCriticalFeatureSpectralValue, xiCriticalFeatureSpectralValue,
    xiSpectralPointSupport_lineConj_boundaryClosure,
    criticalFeatureCauchyKernelTest_conj]
  rfl

/-- The Cauchy-test Pluecker coordinate is the established adjacent evaluation determinant. -/
theorem xiCriticalFeatureSpectralValue_wedge_eq_adjacentDet
    (t : ℝ) (rho : XiDivisorSupport) :
    xiCriticalFeatureSpectralValue t rho *
          xiCriticalFeatureSpectralValue (t + 1) (xiZeroLineConjEquiv rho) -
        xiCriticalFeatureSpectralValue t (xiZeroLineConjEquiv rho) *
          xiCriticalFeatureSpectralValue (t + 1) rho =
      adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) := by
  rw [xiCriticalFeatureSpectralValue, xiCriticalFeatureSpectralValue,
    xiCriticalFeatureSpectralValue, xiCriticalFeatureSpectralValue,
    xiSpectralPointSupport_lineConj_boundaryClosure]
  rw [adjacentCriticalFeatureEvaluationDet]
  rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
  rfl

theorem xiSupportMultiplicity_lineConj_projector (rho : XiDivisorSupport) :
    xiSupportMultiplicity (xiZeroLineConjEquiv rho) =
      xiSupportMultiplicity rho := by
  rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xi_orderAt_xiZeroLineConjEquiv]

/-- Abel row coefficient before inserting either critical feature. -/
def xiExteriorAbelRowWeight (R : ℝ) (rho : XiDivisorSupport) : ℂ :=
  ((xiSupportMultiplicity rho : ℕ) : ℂ) *
    xiExteriorCayleyAbelGreenMultiplier R rho

/-- The boundary row weight is odd under critical-line reflection. -/
theorem xiExteriorAbelRowWeight_one_lineConj (rho : XiDivisorSupport) :
    xiExteriorAbelRowWeight 1 (xiZeroLineConjEquiv rho) =
      -xiExteriorAbelRowWeight 1 rho := by
  rw [xiExteriorAbelRowWeight, xiExteriorAbelRowWeight,
    xiSupportMultiplicity_lineConj_projector,
    xiExteriorCayleyAbelGreenMultiplier,
    xiExteriorCayleyAbelGreenMultiplier,
    sourceCayleyAbelGreenMultiplier_one_eq_totalized,
    sourceCayleyAbelGreenMultiplier_one_eq_totalized,
    xiZeroLineConjEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [show 2 * (1 - (rho : ℂ).re) - 1 =
    -(2 * (rho : ℂ).re - 1) by ring]
  push_cast
  rw [div_neg]
  ring

/-- Boundary row weight is real despite its Cayley-resolvent presentation. -/
theorem star_xiExteriorAbelRowWeight_one (rho : XiDivisorSupport) :
    star (xiExteriorAbelRowWeight 1 rho) =
      xiExteriorAbelRowWeight 1 rho := by
  rw [xiExteriorAbelRowWeight, xiExteriorCayleyAbelGreenMultiplier,
    sourceCayleyAbelGreenMultiplier_one_eq_totalized]
  simp

/-- Square of an anti-Hermitian two-feature Pluecker coordinate is negative norm square. -/
theorem sq_conj_wedge_eq_neg_normSq (a b : ℂ) :
    (a * star b - star a * b) ^ 2 =
      -((Complex.normSq (a * star b - star a * b) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply, star_sub, star_mul, star_star]
  ring

/-- Odd real Green weight turns the negative reflected Pluecker square into positive energy. -/
theorem xiExteriorBoundaryReflectedMinor_eq_normSq
    (t : ℝ) (rho : XiDivisorSupport) :
    xiExteriorAbelRowWeight 1 rho *
        xiExteriorAbelRowWeight 1 (xiZeroLineConjEquiv rho) *
        (xiCriticalFeatureSpectralValue t rho *
              xiCriticalFeatureSpectralValue (t + 1) (xiZeroLineConjEquiv rho) -
            xiCriticalFeatureSpectralValue t (xiZeroLineConjEquiv rho) *
              xiCriticalFeatureSpectralValue (t + 1) rho) ^ 2 =
      ((Complex.normSq
        (xiExteriorAbelRowWeight 1 rho *
          (xiCriticalFeatureSpectralValue t rho *
              xiCriticalFeatureSpectralValue (t + 1) (xiZeroLineConjEquiv rho) -
            xiCriticalFeatureSpectralValue t (xiZeroLineConjEquiv rho) *
              xiCriticalFeatureSpectralValue (t + 1) rho)) : ℝ) : ℂ) := by
  rw [xiExteriorAbelRowWeight_one_lineConj,
    xiCriticalFeatureSpectralValue_lineConj,
    xiCriticalFeatureSpectralValue_lineConj,
    Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply, star_sub, star_mul, star_star]
  rw [star_xiExteriorAbelRowWeight_one]
  ring

/-- Fixed-center Abel-normalized adjacent exterior coefficient. -/
def xiExteriorCayleyAbelFixedCoefficient
    (R t : ℝ) (rho : XiDivisorSupport) : ℂ :=
  xiExteriorCayleyAbelGreenMultiplier R rho *
    adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho)

theorem xiExteriorAbelRowWeight_mul_wedge_eq_fixedCoefficient
    (R t : ℝ) (rho : XiDivisorSupport) :
    xiExteriorAbelRowWeight R rho *
        (xiCriticalFeatureSpectralValue t rho *
              xiCriticalFeatureSpectralValue (t + 1) (xiZeroLineConjEquiv rho) -
            xiCriticalFeatureSpectralValue t (xiZeroLineConjEquiv rho) *
              xiCriticalFeatureSpectralValue (t + 1) rho) =
      ((xiSupportMultiplicity rho : ℕ) : ℂ) *
        xiExteriorCayleyAbelFixedCoefficient R t rho := by
  rw [xiExteriorAbelRowWeight,
    xiCriticalFeatureSpectralValue_wedge_eq_adjacentDet,
    xiExteriorCayleyAbelFixedCoefficient]
  ring

/-- Fixed-center, multiplicity-square Abel exterior packet energy. -/
def xiExteriorCayleyAbelFixedPacketEnergy
    (S : Finset XiDivisorSupport) (R t : ℝ) : ℝ :=
  ∑ rho ∈ S, Complex.normSq
    (((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiExteriorCayleyAbelFixedCoefficient R t rho)

/-- The oriented source determinant at fixed reporter center and Abel radius. -/
def xiPrimeGammaExteriorAbelDeterminant
    (S : Finset XiDivisorSupport) (R t : ℝ) (a b c : ℕ) : ℂ :=
  xiPrimeCayleyExteriorReflectionDeterminant S
    (xiExteriorAbelRowWeight R)
    (xiCriticalFeatureSpectralValue t)
    (xiCriticalFeatureSpectralValue (t + 1)) a b c

/-- At the Abel boundary, determinant dephasing is exactly one half of the positive fixed-center
Ward--Green packet energy. -/
theorem tendsto_xiPrimeGammaExteriorAbelDeterminant_one
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeGammaExteriorAbelDeterminant S 1 t a b c)
      atTop
      (nhds (((1 / 2 : ℝ) *
        xiExteriorCayleyAbelFixedPacketEnergy S 1 t : ℝ) : ℂ)) := by
  have hlim := tendsto_xiPrimeCayleyExteriorReflectionDeterminant S hclosed
    (xiExteriorAbelRowWeight 1)
    (xiCriticalFeatureSpectralValue t)
    (xiCriticalFeatureSpectralValue (t + 1))
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    rw [xiExteriorCayleyAbelFixedPacketEnergy]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [xiExteriorBoundaryReflectedMinor_eq_normSq,
      xiExteriorAbelRowWeight_mul_wedge_eq_fixedCoefficient]

theorem xiExteriorReporterCenter_lineConj (rho : XiDivisorSupport) :
    xiExteriorReporterCenter (xiZeroLineConjEquiv rho) =
      xiExteriorReporterCenter rho := by
  rw [xiExteriorReporterCenter, xiExteriorReporterCenter,
    xiSpectralPointSupport_lineConj_boundaryClosure]
  simp

/-- Reporter-center fibre of a finite divisor packet. -/
def xiExteriorReporterBlock
    (S : Finset XiDivisorSupport) (t : ℝ) : Finset XiDivisorSupport :=
  S.filter (fun rho => xiExteriorReporterCenter rho = t)

theorem xiExteriorReporterBlock_lineConj_closed
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S)
    (t : ℝ) (rho : XiDivisorSupport)
    (hrho : rho ∈ xiExteriorReporterBlock S t) :
    xiZeroLineConjEquiv rho ∈ xiExteriorReporterBlock S t := by
  rw [xiExteriorReporterBlock, Finset.mem_filter] at hrho ⊢
  exact ⟨hclosed rho hrho.1, (xiExteriorReporterCenter_lineConj rho).trans hrho.2⟩

theorem xiExteriorCayleyAbelFixedCoefficient_one_eq_plus_of_center
    (t : ℝ) (rho : XiDivisorSupport)
    (hcenter : xiExteriorReporterCenter rho = t) :
    xiExteriorCayleyAbelFixedCoefficient 1 t rho =
      xiWardGreenExteriorPlusCoefficient rho := by
  rw [← xiExteriorCayleyAbelPlusCoefficient_one_eq rho]
  simp only [xiExteriorCayleyAbelFixedCoefficient,
    xiExteriorCayleyAbelPlusCoefficient]
  rw [hcenter]

theorem xiExteriorCayleyAbelFixedCoefficient_one_eq_minus_of_center
    (t : ℝ) (rho : XiDivisorSupport)
    (hcenter : xiExteriorReporterCenter rho = t) :
    xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) rho =
      xiWardGreenExteriorMinusCoefficient rho := by
  rw [← xiExteriorCayleyAbelMinusCoefficient_one_eq rho]
  simp only [xiExteriorCayleyAbelFixedCoefficient,
    xiExteriorCayleyAbelMinusCoefficient]
  rw [hcenter]

/-- Sum of reporter-fibre Abel energies is the existing two-orientation Ward--Green packet. -/
theorem sum_xiExteriorCayleyAbelFixedPacketEnergy_eq_packetEnergy
    (S : Finset XiDivisorSupport) :
    (∑ t ∈ S.image xiExteriorReporterCenter,
        (xiExteriorCayleyAbelFixedPacketEnergy
            (xiExteriorReporterBlock S t) 1 t +
          xiExteriorCayleyAbelFixedPacketEnergy
            (xiExteriorReporterBlock S t) 1 (t - 1))) =
      xiWardGreenExteriorPacketEnergy S := by
  let G := S.image xiExteriorReporterCenter
  have hplus :
      (∑ t ∈ G, xiExteriorCayleyAbelFixedPacketEnergy
          (xiExteriorReporterBlock S t) 1 t) =
        xiWardGreenExteriorOrientationPacketEnergy true S := by
    rw [xiWardGreenExteriorOrientationPacketEnergy]
    change (∑ t ∈ G, ∑ rho ∈ S.filter
        (fun rho => xiExteriorReporterCenter rho = t),
          Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
            xiExteriorCayleyAbelFixedCoefficient 1 t rho)) =
      ∑ rho ∈ S,
        ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorCoefficient true rho‖ ^ 2
    calc
      _ = ∑ t ∈ G, ∑ rho ∈ S.filter
          (fun rho => xiExteriorReporterCenter rho = t),
            Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
              xiWardGreenExteriorPlusCoefficient rho) := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [xiExteriorCayleyAbelFixedCoefficient_one_eq_plus_of_center
              t rho (Finset.mem_filter.mp hrho).2]
      _ = ∑ rho ∈ S,
          Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
            xiWardGreenExteriorPlusCoefficient rho) := by
            exact Finset.sum_fiberwise_of_maps_to
              (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
              (fun rho => Complex.normSq
                (((xiSupportMultiplicity rho : ℕ) : ℂ) *
                  xiWardGreenExteriorPlusCoefficient rho))
      _ = _ := by
            apply Finset.sum_congr rfl
            intro rho hrho
            simp [xiWardGreenExteriorCoefficient,
              Complex.normSq_eq_norm_sq]
  have hminus :
      (∑ t ∈ G, xiExteriorCayleyAbelFixedPacketEnergy
          (xiExteriorReporterBlock S t) 1 (t - 1)) =
        xiWardGreenExteriorOrientationPacketEnergy false S := by
    rw [xiWardGreenExteriorOrientationPacketEnergy]
    change (∑ t ∈ G, ∑ rho ∈ S.filter
        (fun rho => xiExteriorReporterCenter rho = t),
          Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
            xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) rho)) =
      ∑ rho ∈ S,
        ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorCoefficient false rho‖ ^ 2
    calc
      _ = ∑ t ∈ G, ∑ rho ∈ S.filter
          (fun rho => xiExteriorReporterCenter rho = t),
            Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
              xiWardGreenExteriorMinusCoefficient rho) := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [xiExteriorCayleyAbelFixedCoefficient_one_eq_minus_of_center
              t rho (Finset.mem_filter.mp hrho).2]
      _ = ∑ rho ∈ S,
          Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
            xiWardGreenExteriorMinusCoefficient rho) := by
            exact Finset.sum_fiberwise_of_maps_to
              (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
              (fun rho => Complex.normSq
                (((xiSupportMultiplicity rho : ℕ) : ℂ) *
                  xiWardGreenExteriorMinusCoefficient rho))
      _ = _ := by
            apply Finset.sum_congr rfl
            intro rho hrho
            simp [xiWardGreenExteriorCoefficient,
              Complex.normSq_eq_norm_sq]
  rw [Finset.sum_add_distrib, hplus, hminus,
    xiWardGreenExteriorOrientationPacketEnergy_add_eq_packetEnergy]

/-- Complete finite source expression: reporter fibres and both adjacent orientations, with the
factor two restoring ordered reflection-pair counting. -/
def xiPrimeGammaExteriorAbelPacketCesaro
    (S : Finset XiDivisorSupport) (R : ℝ) (N : ℕ) : ℂ :=
  2 * ∑ t ∈ S.image xiExteriorReporterCenter,
    ((((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeGammaExteriorAbelDeterminant
            (xiExteriorReporterBlock S t) R t a b c +
      (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeGammaExteriorAbelDeterminant
            (xiExteriorReporterBlock S t) R (t - 1) a b c)

/-- Mixed-covariance source determinant lands exactly on the full Ward--Green exterior packet. -/
theorem tendsto_xiPrimeGammaExteriorAbelPacketCesaro_one
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S) :
    Tendsto (xiPrimeGammaExteriorAbelPacketCesaro S 1) atTop
      (nhds ((xiWardGreenExteriorPacketEnergy S : ℝ) : ℂ)) := by
  let G := S.image xiExteriorReporterCenter
  have hsum := tendsto_finsetSum G fun t ht =>
    (tendsto_xiPrimeGammaExteriorAbelDeterminant_one
      (xiExteriorReporterBlock S t)
      (xiExteriorReporterBlock_lineConj_closed S hclosed t) t).add
    (tendsto_xiPrimeGammaExteriorAbelDeterminant_one
      (xiExteriorReporterBlock S t)
      (xiExteriorReporterBlock_lineConj_closed S hclosed t) (t - 1))
  have htwo : Tendsto (fun _ : ℕ => (2 : ℂ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hscaled := htwo.mul hsum
  convert hscaled using 1
  · rfl
  · apply congrArg nhds
    rw [← sum_xiExteriorCayleyAbelFixedPacketEnergy_eq_packetEnergy S]
    push_cast
    dsimp [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    push_cast
    ring

end

end RHTower
