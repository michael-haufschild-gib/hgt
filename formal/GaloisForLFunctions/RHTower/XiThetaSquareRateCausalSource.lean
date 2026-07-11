import GaloisForLFunctions.RHTower.CausalFourierBridge
import GaloisForLFunctions.RHTower.XiThetaSquareRateSourceL2
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.SoninPerronSupportTransfer

/-!
# Causal source realization of the theta square-rate reader

Finite square-node Blaschke products are realized by explicit one-sided convolution sources.
Their Fourier profiles converge in `L²` to the canonical infinite reader boundary profile.
Because lower half-line restriction is a continuous operator on `L²`, causal support survives
the limit.  This proves positive support of the canonical inverse-Fourier reader directly, with no
Paley--Wiener existence or membership proposition.
-/

open Complex Real Set Filter Topology MeasureTheory FourierTransform
open scoped Convolution

noncomputable section

namespace RHTower

def thetaSquareFiniteCausalSource (n : ℕ) : ℕ → ℝ → ℂ
  | 0 => fun y => -(thetaSquareBlaschkeNodeSlope n)⁻¹ *
      causalFourierExponential ((n : ℝ) ^ 2) y
  | N + 1 => if N + 1 = n then thetaSquareFiniteCausalSource n N
      else causalBlaschkeStep (((N + 1 : ℕ) : ℝ) ^ 2)
        (thetaSquareFiniteCausalSource n N)

theorem thetaSquareFiniteCausalSource_integrable {n : ℕ} (hn : 1 ≤ n) :
    ∀ N, Integrable (thetaSquareFiniteCausalSource n N) := by
  intro N
  induction N with
  | zero =>
      exact (causalFourierExponential_integrable (sq_pos_of_pos (by positivity : (0 : ℝ) < n)))
        |>.const_mul _
  | succ N ih =>
      rw [thetaSquareFiniteCausalSource]
      split_ifs
      · exact ih
      · exact causalBlaschkeStep_integrable (sq_pos_of_pos (by positivity)) ih

theorem thetaSquareFiniteCausalSource_exists_bound {n : ℕ} :
    ∀ N, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖thetaSquareFiniteCausalSource n N y‖ ≤ C := by
  intro N
  induction N with
  | zero =>
      refine ⟨‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ * Real.pi, by positivity, ?_⟩
      intro y
      rw [thetaSquareFiniteCausalSource, norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left
        (norm_causalFourierExponential_le (sq_nonneg (n : ℝ)) y)
        (norm_nonneg ((thetaSquareBlaschkeNodeSlope n)⁻¹))
  | succ N ih =>
      rw [thetaSquareFiniteCausalSource]
      split_ifs
      · exact ih
      · rcases ih with ⟨C, hC, hbound⟩
        let a : ℝ := ((N + 1 : ℕ) : ℝ) ^ 2
        let D : ℝ := ∫ t : ℝ, ‖causalFourierExponential a t‖
        have ha : 0 < a := by dsimp [a]; positivity
        have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
        refine ⟨C + ‖(2 * a : ℂ)‖ * (D * C), by positivity, ?_⟩
        intro y
        have hconv := norm_convolution_le_of_bound
          (causalFourierExponential_integrable ha) hbound y
        rw [causalBlaschkeStep]
        calc
          ‖-thetaSquareFiniteCausalSource n N y + (2 * a : ℂ) *
              (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ]
                thetaSquareFiniteCausalSource n N) y‖ ≤
              ‖thetaSquareFiniteCausalSource n N y‖ +
                ‖(2 * a : ℂ)‖ * ‖(causalFourierExponential a ⋆[
                  ContinuousLinearMap.mul ℂ ℂ] thetaSquareFiniteCausalSource n N) y‖ := by
            simpa only [norm_neg, norm_mul] using norm_add_le
              (-thetaSquareFiniteCausalSource n N y)
              ((2 * a : ℂ) * (causalFourierExponential a ⋆[
                ContinuousLinearMap.mul ℂ ℂ] thetaSquareFiniteCausalSource n N) y)
          _ ≤ C + ‖(2 * a : ℂ)‖ * (D * C) := by
            exact add_le_add (hbound y)
              (mul_le_mul_of_nonneg_left hconv (norm_nonneg _))

theorem thetaSquareFiniteCausalSource_memLp_two {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    MemLp (thetaSquareFiniteCausalSource n N) 2 volume := by
  rcases thetaSquareFiniteCausalSource_exists_bound (n := n) N with ⟨C, _, hbound⟩
  exact memLp_two_of_integrable_of_norm_le
    (thetaSquareFiniteCausalSource_integrable hn N) hbound

theorem thetaSquareFiniteCausalSource_eq_zero_of_neg {n : ℕ} :
    ∀ N y, y < 0 → thetaSquareFiniteCausalSource n N y = 0 := by
  intro N
  induction N with
  | zero =>
      intro y hy
      change -(thetaSquareBlaschkeNodeSlope n)⁻¹ *
        causalFourierExponential ((n : ℝ) ^ 2) y = 0
      rw [causalFourierExponential_eq_zero_of_neg _ hy, mul_zero]
  | succ N ih =>
      intro y hy
      rw [thetaSquareFiniteCausalSource]
      split_ifs
      · exact ih y hy
      · exact causalBlaschkeStep_eq_zero_of_neg (ih) hy

def thetaSquareFiniteSkippedProduct (n N : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N,
    if j + 1 = n then 1 else
      ((((j + 1 : ℕ) : ℂ) ^ 2 - z) /
        (((j + 1 : ℕ) : ℂ) ^ 2 + z))

def thetaSquareFiniteReaderProfile (n N : ℕ) (ξ : ℝ) : ℂ :=
  -(thetaSquareBlaschkeNodeSlope n)⁻¹ *
    (((n : ℂ) ^ 2 + 2 * I * ξ)⁻¹) *
    thetaSquareFiniteSkippedProduct n N (2 * I * ξ)

theorem fourier_thetaSquareFiniteCausalSource {n : ℕ} (hn : 1 ≤ n) :
    ∀ N ξ, 𝓕 (thetaSquareFiniteCausalSource n N) ξ =
      thetaSquareFiniteReaderProfile n N ξ := by
  intro N
  induction N with
  | zero =>
      intro ξ
      rw [thetaSquareFiniteCausalSource, thetaSquareFiniteReaderProfile]
      simp only [thetaSquareFiniteSkippedProduct, Finset.range_zero, Finset.prod_empty, mul_one]
      rw [show (fun y : ℝ => -(thetaSquareBlaschkeNodeSlope n)⁻¹ *
          causalFourierExponential ((n : ℝ) ^ 2) y) =
          (-(thetaSquareBlaschkeNodeSlope n)⁻¹) •
            causalFourierExponential ((n : ℝ) ^ 2) by rfl]
      have hsmul := congrFun (VectorFourier.fourierIntegral_const_smul
        𝐞 volume (innerₗ ℝ) (causalFourierExponential ((n : ℝ) ^ 2))
          (-(thetaSquareBlaschkeNodeSlope n)⁻¹)) ξ
      change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
          ((-(thetaSquareBlaschkeNodeSlope n)⁻¹) •
            causalFourierExponential ((n : ℝ) ^ 2)) ξ = _
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
          (causalFourierExponential ((n : ℝ) ^ 2)) ξ =
          ((((n : ℝ) ^ 2 : ℝ) : ℂ) + 2 * I * ξ)⁻¹ by
        exact fourier_causalFourierExponential
          (sq_pos_of_pos (by positivity : (0 : ℝ) < n)) ξ]
      push_cast
      rfl
  | succ N ih =>
      intro ξ
      rw [thetaSquareFiniteCausalSource]
      split_ifs with hN
      · rw [ih]
        rw [thetaSquareFiniteReaderProfile, thetaSquareFiniteReaderProfile]
        simp only [thetaSquareFiniteSkippedProduct]
        rw [Finset.prod_range_succ]
        simp [hN]
      · rw [fourier_causalBlaschkeStep (sq_pos_of_pos (by positivity))
          (thetaSquareFiniteCausalSource_integrable hn N), ih]
        rw [thetaSquareFiniteReaderProfile, thetaSquareFiniteReaderProfile]
        simp only [thetaSquareFiniteSkippedProduct]
        rw [Finset.prod_range_succ]
        simp only [hN, ↓reduceIte]
        push_cast
        ring

def thetaSquareFiniteCausalSourceL2 (n N : ℕ) (hn : 1 ≤ n) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (thetaSquareFiniteCausalSource_memLp_two hn N).toLp
    (thetaSquareFiniteCausalSource n N)

theorem thetaSquareFiniteCausalSourceL2_ae
    (n N : ℕ) (hn : 1 ≤ n) :
    (fun y : ℝ => thetaSquareFiniteCausalSourceL2 n N hn y) =ᵐ[volume]
      thetaSquareFiniteCausalSource n N :=
  MemLp.coeFn_toLp (thetaSquareFiniteCausalSource_memLp_two hn N)

theorem fourier_thetaSquareFiniteCausalSourceL2_ae
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    (fun ξ : ℝ => (𝓕 (thetaSquareFiniteCausalSourceL2 n N hn) :
      Lp ℂ 2 (volume : Measure ℝ)) ξ) =ᵐ[volume]
        thetaSquareFiniteReaderProfile n N := by
  let f2 := thetaSquareFiniteCausalSourceL2 n N hn
  have hf2int : Integrable (f2 : ℝ → ℂ) :=
    (thetaSquareFiniteCausalSource_integrable hn N).congr
      (thetaSquareFiniteCausalSourceL2_ae n N hn).symm
  let f1 : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr hf2int).toLp f2
  have hclassical := l2_fourier_coeFn_eq_l1_fourier_of_integrable f2 hf2int
  have hf1ae : (fun y : ℝ => f1 y) =ᵐ[volume] (fun y : ℝ => f2 y) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf2int)
  filter_upwards [hclassical] with ξ hξ
  calc
    (𝓕 f2 : Lp ℂ 2 (volume : Measure ℝ)) ξ =
        Real.Lp.fourierTransform f1 ξ := by simpa [f1, f2] using hξ
    _ = 𝓕 (f1 : ℝ → ℂ) ξ := rfl
    _ = 𝓕 (f2 : ℝ → ℂ) ξ := Real.fourier_congr_ae hf1ae ξ
    _ = 𝓕 (thetaSquareFiniteCausalSource n N) ξ :=
      Real.fourier_congr_ae (thetaSquareFiniteCausalSourceL2_ae n N hn) ξ
    _ = thetaSquareFiniteReaderProfile n N ξ :=
      fourier_thetaSquareFiniteCausalSource hn N ξ

theorem thetaSquareFiniteReaderProfile_memLp_two
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    MemLp (thetaSquareFiniteReaderProfile n N) 2 volume := by
  exact (Lp.memLp (𝓕 (thetaSquareFiniteCausalSourceL2 n N hn))).ae_eq
    (fourier_thetaSquareFiniteCausalSourceL2_ae hn N)

def thetaSquareFiniteReaderProfileL2 (n N : ℕ) (hn : 1 ≤ n) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (thetaSquareFiniteReaderProfile_memLp_two hn N).toLp
    (thetaSquareFiniteReaderProfile n N)

theorem thetaSquareFiniteReaderProfileL2_ae
    (n N : ℕ) (hn : 1 ≤ n) :
    (fun ξ : ℝ => thetaSquareFiniteReaderProfileL2 n N hn ξ) =ᵐ[volume]
      thetaSquareFiniteReaderProfile n N :=
  MemLp.coeFn_toLp (thetaSquareFiniteReaderProfile_memLp_two hn N)

theorem fourier_thetaSquareFiniteCausalSourceL2
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    𝓕 (thetaSquareFiniteCausalSourceL2 n N hn) =
      thetaSquareFiniteReaderProfileL2 n N hn := by
  apply Lp.ext
  exact (fourier_thetaSquareFiniteCausalSourceL2_ae hn N).trans
    (thetaSquareFiniteReaderProfileL2_ae n N hn).symm

theorem thetaSquareFiniteCausalSourceL2_hasAELowerSupport
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    HasAELowerSupport (fun y : ℝ => thetaSquareFiniteCausalSourceL2 n N hn y) 0 := by
  filter_upwards [thetaSquareFiniteCausalSourceL2_ae n N hn] with y hy
  intro hyneg
  rw [hy]
  exact thetaSquareFiniteCausalSource_eq_zero_of_neg N y hyneg

theorem tendsto_thetaSquareBlaschkeFinite_mul_I {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun N => thetaSquareBlaschkeFinite N ((t : ℂ) * I)) atTop
      (𝓝 (thetaSquareBlaschkeSymbol ((t : ℂ) * I))) := by
  let z : ℂ := (t : ℂ) * I
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hsqrt0 : Complex.sqrt z ≠ 0 := by
    intro h
    have hsquare := complex_sqrt_sq z
    rw [h] at hsquare
    norm_num at hsquare
    exact hz0 hsquare.symm
  have hnum := Complex.tendsto_euler_sin_prod (Complex.sqrt z)
  have hden := tendsto_euler_sinh_prod (Complex.sqrt z)
  have hsinh : Complex.sinh ((Real.pi : ℂ) * Complex.sqrt z) ≠ 0 := by
    exact sinh_pi_sqrt_pureImag_ne_zero ht
  have hdiv := hnum.div hden hsinh
  convert hdiv using 1
  ext N
  rw [thetaSquareBlaschkeFinite]
  have hroot : (Complex.sqrt z) ^ 2 = z := complex_sqrt_sq z
  rw [hroot, Finset.prod_div_distrib]
  have hc : (Real.pi : ℂ) * Complex.sqrt z ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hsqrt0
  change
    (∏ j ∈ Finset.range N, ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2)) /
        (∏ j ∈ Finset.range N, ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2)) =
      (((Real.pi : ℂ) * Complex.sqrt z) *
          ∏ j ∈ Finset.range N, ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2)) /
        (((Real.pi : ℂ) * Complex.sqrt z) *
          ∏ j ∈ Finset.range N, ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2))
  exact (mul_div_mul_left _ _ hc).symm

lemma thetaSquareBlaschkeFinite_eq_linearProduct (N : ℕ) (z : ℂ) :
    thetaSquareBlaschkeFinite N z =
      ∏ j ∈ Finset.range N,
        ((((j + 1 : ℕ) : ℂ) ^ 2 - z) / (((j + 1 : ℕ) : ℂ) ^ 2 + z)) := by
  unfold thetaSquareBlaschkeFinite
  apply Finset.prod_congr rfl
  intro j hj
  have hj0 : (((j + 1 : ℕ) : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
  field_simp
  push_cast
  rfl

lemma prod_skip_nat_add_one
    {M : Type*} [CommMonoid M] {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (f : ℕ → M) :
    (∏ j ∈ Finset.range N, if j + 1 = n then 1 else f j) =
      ∏ j ∈ (Finset.range N).erase (n - 1), f j := by
  let k : ℕ := n - 1
  let h : ℕ → M := fun j => if j + 1 = n then 1 else f j
  have hk : k ∈ Finset.range N := by
    rw [Finset.mem_range]
    dsimp [k]
    omega
  have hkone : h k = 1 := by
    dsimp [h, k]
    rw [if_pos]
    omega
  change (∏ j ∈ Finset.range N, h j) = _
  rw [← Finset.prod_erase (s := Finset.range N) hkone]
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [h, k]
  rw [if_neg]
  intro hjn
  have hjk : j = n - 1 := by omega
  subst j
  exact (Finset.notMem_erase (n - 1) (Finset.range N) hj).elim

theorem thetaSquareBlaschkeFinite_split_selected
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (z : ℂ) :
    thetaSquareBlaschkeFinite N z =
      (((n : ℂ) ^ 2 - z) / ((n : ℂ) ^ 2 + z)) *
        thetaSquareFiniteSkippedProduct n N z := by
  let k : ℕ := n - 1
  let f : ℕ → ℂ := fun j =>
    ((((j + 1 : ℕ) : ℂ) ^ 2 - z) / (((j + 1 : ℕ) : ℂ) ^ 2 + z))
  have hk : k ∈ Finset.range N := by
    rw [Finset.mem_range]
    dsimp [k]
    omega
  rw [thetaSquareBlaschkeFinite_eq_linearProduct]
  change (∏ j ∈ Finset.range N, f j) = _
  rw [← Finset.mul_prod_erase (Finset.range N) f hk]
  have hfk : f k = (((n : ℂ) ^ 2 - z) / ((n : ℂ) ^ 2 + z)) := by
    dsimp [f]
    rw [show k + 1 = n by dsimp [k]; omega]
  rw [hfk]
  congr 1
  simpa only [thetaSquareFiniteSkippedProduct] using
    (prod_skip_nat_add_one hn hnN f).symm

lemma cancel_selected_blaschke_factor
    {a z S P : ℂ} (hminus : z - a ≠ 0) (hplus : a + z ≠ 0) :
    (-S * (a + z)⁻¹) * P = S * (((a - z) / (a + z)) * P) / (z - a) := by
  have hscalar : -S * (a + z)⁻¹ = S * ((a - z) / (a + z)) / (z - a) := by
    field_simp [hminus, hplus]
    ring
  calc
    (-S * (a + z)⁻¹) * P =
        (S * ((a - z) / (a + z)) / (z - a)) * P := congrArg (· * P) hscalar
    _ = S * (((a - z) / (a + z)) * P) / (z - a) := by ring

theorem thetaSquareFiniteReaderProfile_eq_blaschkeFinite
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (ξ : ℝ) :
    thetaSquareFiniteReaderProfile n N ξ =
      (thetaSquareBlaschkeNodeSlope n)⁻¹ *
        thetaSquareBlaschkeFinite N (((2 * ξ : ℝ) : ℂ) * I) /
          ((((2 * ξ : ℝ) : ℂ) * I) - thetaSquare n) := by
  let z : ℂ := 2 * I * ξ
  have hz : (((2 * ξ : ℝ) : ℂ) * I) = z := by
    dsimp [z]
    push_cast
    ring
  rw [hz]
  have htheta : thetaSquare n = (n : ℂ) ^ 2 := by simp [thetaSquare]
  have hminus : z - (n : ℂ) ^ 2 ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    dsimp [z] at hre
    norm_num [pow_two, Complex.mul_re] at hre
    omega
  have hplus : (n : ℂ) ^ 2 + z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    dsimp [z] at hre
    norm_num [pow_two, Complex.mul_re] at hre
    omega
  let S : ℂ := (thetaSquareBlaschkeNodeSlope n)⁻¹
  let P : ℂ := thetaSquareFiniteSkippedProduct n N z
  have hsplit := thetaSquareBlaschkeFinite_split_selected hn hnN z
  calc
    thetaSquareFiniteReaderProfile n N ξ =
        (-S * ((n : ℂ) ^ 2 + z)⁻¹) * P := by rfl
    _ = S * ((((n : ℂ) ^ 2 - z) / ((n : ℂ) ^ 2 + z)) * P) /
        (z - (n : ℂ) ^ 2) := cancel_selected_blaschke_factor hminus hplus
    _ = S * thetaSquareBlaschkeFinite N z / (z - (n : ℂ) ^ 2) := by
      rw [hsplit]
    _ = (thetaSquareBlaschkeNodeSlope n)⁻¹ *
        thetaSquareBlaschkeFinite N z / (z - thetaSquare n) := by
      rw [htheta]

theorem tendsto_thetaSquareFiniteReaderProfile
    {n : ℕ} (hn : 1 ≤ n) {ξ : ℝ} (hξ : ξ ≠ 0) :
    Tendsto (fun N => thetaSquareFiniteReaderProfile n N ξ) atTop
      (𝓝 (thetaHeatRateReaderFourierProfile n ξ)) := by
  let z : ℂ := (((2 * ξ : ℝ) : ℂ) * I)
  have ht : 2 * ξ ≠ 0 := mul_ne_zero two_ne_zero hξ
  have hznode : z - thetaSquare n ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    norm_num [thetaSquare, pow_two, Complex.mul_re] at hre
    omega
  have hB : Tendsto (fun N => thetaSquareBlaschkeFinite N z) atTop
      (𝓝 (thetaSquareBlaschkeSymbol z)) :=
    tendsto_thetaSquareBlaschkeFinite_mul_I ht
  have hlim : Tendsto (fun N =>
      (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N z /
        (z - thetaSquare n)) atTop
      (𝓝 ((thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeSymbol z /
        (z - thetaSquare n))) :=
    (hB.const_mul (thetaSquareBlaschkeNodeSlope n)⁻¹).div_const _
  have hevent : ∀ᶠ N : ℕ in atTop,
      thetaSquareFiniteReaderProfile n N ξ =
        (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N z /
          (z - thetaSquare n) := by
    exact eventually_atTop.2 ⟨n, fun N hN =>
      thetaSquareFiniteReaderProfile_eq_blaschkeFinite hn hN ξ⟩
  have hevent' :
      (fun N => (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N z /
        (z - thetaSquare n)) =ᶠ[atTop]
      (fun N => thetaSquareFiniteReaderProfile n N ξ) := by
    filter_upwards [hevent] with N hN
    exact hN.symm
  have hprofile := hlim.congr' hevent'
  convert hprofile using 1
  unfold thetaHeatRateReaderFourierProfile thetaHeatRateReaderSymbol
  have hscale :
      ((((2 * Real.pi * ξ : ℝ) : ℂ) * I) / (Real.pi : ℂ)) = z := by
    dsimp [z]
    push_cast
    field_simp
  rw [hscale, thetaSquareBlaschkeReaderSymbol,
    dslope_of_ne _ (sub_ne_zero.mp hznode), slope_def_field,
    thetaSquareBlaschkeSymbol_zero, sub_zero]
  ring

lemma norm_linearBlaschkeFactor_mul_I (a t : ℝ) (ha : 0 < a) :
    ‖((a : ℂ) - (t : ℂ) * I) / ((a : ℂ) + (t : ℂ) * I)‖ = 1 := by
  have hden : (a : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re] at hre
    exact ha.ne' hre
  have hsq :
      ‖(a : ℂ) - (t : ℂ) * I‖ ^ 2 = ‖(a : ℂ) + (t : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  have hnorm : ‖(a : ℂ) - (t : ℂ) * I‖ = ‖(a : ℂ) + (t : ℂ) * I‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [norm_div, hnorm, div_self]
  exact norm_ne_zero_iff.mpr hden

theorem norm_thetaSquareFiniteSkippedProduct_mul_I (n N : ℕ) (t : ℝ) :
    ‖thetaSquareFiniteSkippedProduct n N ((t : ℂ) * I)‖ = 1 := by
  rw [thetaSquareFiniteSkippedProduct, norm_prod]
  apply Finset.prod_eq_one
  intro j hj
  by_cases hjn : j + 1 = n
  · simp [hjn]
  · simp only [hjn, ↓reduceIte]
    have hcast : ((((j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) = ((j + 1 : ℕ) : ℂ) ^ 2 := by
      push_cast
      rfl
    have hfac :=
      norm_linearBlaschkeFactor_mul_I (((j + 1 : ℕ) : ℝ) ^ 2) t (by positivity)
    rw [hcast] at hfac
    exact hfac

theorem norm_thetaSquareFiniteReaderProfile (n N : ℕ) (ξ : ℝ) :
    ‖thetaSquareFiniteReaderProfile n N ξ‖ =
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ /
        ‖(n : ℂ) ^ 2 + 2 * I * ξ‖ := by
  have hz : 2 * I * (ξ : ℂ) = (((2 * ξ : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [thetaSquareFiniteReaderProfile, norm_mul, norm_mul, norm_neg, hz,
    norm_thetaSquareFiniteSkippedProduct_mul_I n N (2 * ξ)]
  simp only [norm_inv, mul_one, div_eq_mul_inv]

theorem norm_thetaHeatRateReaderFourierProfile_eq_finite
    {n : ℕ} (hn : 1 ≤ n) {ξ : ℝ} (hξ : ξ ≠ 0) (N : ℕ) :
    ‖thetaHeatRateReaderFourierProfile n ξ‖ =
      ‖thetaSquareFiniteReaderProfile n N ξ‖ := by
  have hlim := (tendsto_thetaSquareFiniteReaderProfile hn hξ).norm
  have hconst : Tendsto (fun _ : ℕ =>
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ /
        ‖(n : ℂ) ^ 2 + 2 * I * ξ‖) atTop
      (𝓝 (‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ /
        ‖(n : ℂ) ^ 2 + 2 * I * ξ‖)) := tendsto_const_nhds
  have heq : (fun N => ‖thetaSquareFiniteReaderProfile n N ξ‖) =
      fun _ : ℕ => ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ /
        ‖(n : ℂ) ^ 2 + 2 * I * ξ‖ := by
    funext M
    exact norm_thetaSquareFiniteReaderProfile n M ξ
  rw [heq] at hlim
  have hunique := tendsto_nhds_unique hlim hconst
  rw [norm_thetaSquareFiniteReaderProfile]
  exact hunique

lemma sq_norm_thetaSquareFiniteReaderProfile
    (n N : ℕ) (ξ : ℝ) :
    ‖thetaSquareFiniteReaderProfile n N ξ‖ ^ 2 =
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        ((((n : ℝ) ^ 2) ^ 2 + (2 * ξ) ^ 2)⁻¹) := by
  rw [norm_thetaSquareFiniteReaderProfile, div_pow]
  have hden : ‖(n : ℂ) ^ 2 + 2 * I * ξ‖ ^ 2 =
      ((n : ℝ) ^ 2) ^ 2 + (2 * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hden, div_eq_mul_inv]

private lemma integrable_inv_square_add_two_mul_sq
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : ℝ => (a ^ 2 + (2 * ξ) ^ 2)⁻¹) := by
  have hbase := integrable_inv_one_add_sq.comp_div ha.ne'
  have hscaled := hbase.const_mul (a⁻¹ ^ 2)
  have hunit : Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) := by
    apply hscaled.congr
    filter_upwards [] with t
    field_simp
  have hcomp := hunit.comp_mul_left' two_ne_zero
  simpa using hcomp

private lemma integrable_thetaSquareFiniteReaderDifferenceBound
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun ξ : ℝ =>
      4 * ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        ((((n : ℝ) ^ 2) ^ 2 + (2 * ξ) ^ 2)⁻¹)) := by
  have hnR : (0 : ℝ) < n := by positivity
  exact (integrable_inv_square_add_two_mul_sq (sq_pos_of_pos hnR)).const_mul _

theorem tendsto_integral_sq_norm_thetaSquareFiniteReaderProfile_sub
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => ∫ ξ : ℝ,
      ‖thetaSquareFiniteReaderProfile n N ξ -
        thetaHeatRateReaderFourierProfile n ξ‖ ^ 2) atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ := fun N ξ =>
    ‖thetaSquareFiniteReaderProfile n N ξ -
      thetaHeatRateReaderFourierProfile n ξ‖ ^ 2
  let bound : ℝ → ℝ := fun ξ =>
    4 * ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
      ((((n : ℝ) ^ 2) ^ 2 + (2 * ξ) ^ 2)⁻¹)
  have hFmeas : ∀ N, AEStronglyMeasurable (F N) := by
    intro N
    exact ((thetaSquareFiniteReaderProfile_memLp_two hn N).aestronglyMeasurable.sub
      (thetaHeatRateReaderFourierProfile_aestronglyMeasurable hn)).norm.pow 2
  have hboundInt : Integrable bound :=
    integrable_thetaSquareFiniteReaderDifferenceBound hn
  have hξ0 : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff, measure_singleton]
  have hbound : ∀ N, ∀ᵐ ξ : ℝ, ‖F N ξ‖ ≤ bound ξ := by
    intro N
    filter_upwards [hξ0] with ξ hξ
    have htri := norm_sub_le (thetaSquareFiniteReaderProfile n N ξ)
      (thetaHeatRateReaderFourierProfile n ξ)
    have heq := norm_thetaHeatRateReaderFourierProfile_eq_finite hn hξ N
    have hpow := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [Real.norm_eq_abs, abs_of_nonneg] <;> try positivity
    calc
      ‖thetaSquareFiniteReaderProfile n N ξ -
          thetaHeatRateReaderFourierProfile n ξ‖ ^ 2 ≤
          (‖thetaSquareFiniteReaderProfile n N ξ‖ +
            ‖thetaHeatRateReaderFourierProfile n ξ‖) ^ 2 := hpow
      _ = 4 * ‖thetaSquareFiniteReaderProfile n N ξ‖ ^ 2 := by rw [heq]; ring
      _ = bound ξ := by
        rw [sq_norm_thetaSquareFiniteReaderProfile]
        dsimp [bound]
        ring
  have hlim : ∀ᵐ ξ : ℝ, Tendsto (fun N => F N ξ) atTop (𝓝 0) := by
    filter_upwards [hξ0] with ξ hξ
    have hconst : Tendsto (fun _ : ℕ => thetaHeatRateReaderFourierProfile n ξ) atTop
        (𝓝 (thetaHeatRateReaderFourierProfile n ξ)) := tendsto_const_nhds
    have hpoint := (tendsto_thetaSquareFiniteReaderProfile hn hξ).sub hconst
    simpa [F] using hpoint.norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence bound hFmeas hboundInt hbound hlim
  simpa [F] using hDCT

theorem tendsto_thetaSquareFiniteReaderProfileL2
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun N => thetaSquareFiniteReaderProfileL2 n N hn) atTop
      (𝓝 (thetaHeatRateReaderFourierProfileL2 n hn)) := by
  have hsqNorm (N : ℕ) :
      ‖thetaSquareFiniteReaderProfileL2 n N hn -
        thetaHeatRateReaderFourierProfileL2 n hn‖ ^ 2 =
        ∫ ξ : ℝ, ‖thetaSquareFiniteReaderProfile n N ξ -
          thetaHeatRateReaderFourierProfile n ξ‖ ^ 2 := by
    rw [norm_l2_sq_complex]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (thetaSquareFiniteReaderProfileL2 n N hn)
        (thetaHeatRateReaderFourierProfileL2 n hn),
      thetaSquareFiniteReaderProfileL2_ae n N hn,
      thetaHeatRateReaderFourierProfileL2_ae n hn] with ξ hsub hfin htarget
    rw [hsub, Pi.sub_apply, hfin, htarget]
  have hsq : Tendsto (fun N =>
      ‖thetaSquareFiniteReaderProfileL2 n N hn -
        thetaHeatRateReaderFourierProfileL2 n hn‖ ^ 2) atTop (𝓝 0) := by
    apply (tendsto_integral_sq_norm_thetaSquareFiniteReaderProfile_sub hn).congr'
    filter_upwards [] with N
    exact (hsqNorm N).symm
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun N =>
      ‖thetaSquareFiniteReaderProfileL2 n N hn -
        thetaHeatRateReaderFourierProfileL2 n hn‖) atTop (𝓝 0) := by
    have heq : (fun N => Real.sqrt
        (‖thetaSquareFiniteReaderProfileL2 n N hn -
          thetaHeatRateReaderFourierProfileL2 n hn‖ ^ 2)) =
        fun N => ‖thetaSquareFiniteReaderProfileL2 n N hn -
          thetaHeatRateReaderFourierProfileL2 n hn‖ := by
      funext N
      rw [Real.sqrt_sq (norm_nonneg _)]
    change Tendsto (fun N => Real.sqrt
      (‖thetaSquareFiniteReaderProfileL2 n N hn -
        thetaHeatRateReaderFourierProfileL2 n hn‖ ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) at hsqrt
    rw [heq] at hsqrt
    simpa only [Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

theorem tendsto_thetaSquareFiniteCausalSourceL2
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun N => thetaSquareFiniteCausalSourceL2 n N hn) atTop
      (𝓝 (thetaHeatRateSourceReaderL2 n hn)) := by
  have hprofile := tendsto_thetaSquareFiniteReaderProfileL2 hn
  have hmap := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous.continuousAt.tendsto.comp hprofile
  have hevent : (fun N => (Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (thetaSquareFiniteReaderProfileL2 n N hn)) =ᶠ[atTop]
      (fun N => thetaSquareFiniteCausalSourceL2 n N hn) := by
    filter_upwards [] with N
    rw [← fourier_thetaSquareFiniteCausalSourceL2 hn N,
      show (Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (𝓕 (thetaSquareFiniteCausalSourceL2 n N hn)) =
          thetaSquareFiniteCausalSourceL2 n N hn by
        change (Lp.fourierTransformₗᵢ ℝ ℂ).symm
          ((Lp.fourierTransformₗᵢ ℝ ℂ) (thetaSquareFiniteCausalSourceL2 n N hn)) = _
        exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _]
  simpa only [Function.comp_apply, thetaHeatRateSourceReaderL2] using hmap.congr' hevent

def negativeHalfLineRestrictionL2 :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Iio 0)) :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Iio 0)

theorem hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    HasAELowerSupport (fun y : ℝ => f y) 0 ↔
      negativeHalfLineRestrictionL2 f = 0 := by
  constructor
  · intro hsupp
    change (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Iio (0 : ℝ))) f = 0
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (Set.Iio (0 : ℝ)) f,
      ae_restrict_of_ae hsupp,
      ae_restrict_mem (measurableSet_Iio : MeasurableSet (Set.Iio (0 : ℝ))),
      Lp.coeFn_zero ℂ 2 ((volume : Measure ℝ).restrict (Set.Iio (0 : ℝ)))] with
        y hcoe hs hy hzero
    rw [hcoe, hs hy, hzero]
    rfl
  · intro hzero
    change (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Iio (0 : ℝ))) f = 0 at hzero
    have hcoe := LpToLpRestrictCLM_coeFn ℂ (Set.Iio (0 : ℝ)) f
    have hresZero :
        (fun y : ℝ => negativeHalfLineRestrictionL2 f y) =ᵐ[
          (volume : Measure ℝ).restrict (Set.Iio (0 : ℝ))] (fun _ => 0) := by
      unfold negativeHalfLineRestrictionL2
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 ((volume : Measure ℝ).restrict (Set.Iio (0 : ℝ)))
    have hfZero : (fun y : ℝ => f y) =ᵐ[
        (volume : Measure ℝ).restrict (Set.Iio (0 : ℝ))] (fun _ => 0) :=
      hcoe.symm.trans hresZero
    have hfZero' := (ae_restrict_iff'
      (measurableSet_Iio : MeasurableSet (Set.Iio (0 : ℝ)))).mp hfZero
    filter_upwards [hfZero'] with y hy
    intro hyneg
    exact hy hyneg

theorem thetaHeatRateSourceReaderL2_hasAELowerSupport
    {n : ℕ} (hn : 1 ≤ n) :
    HasAELowerSupport (fun y : ℝ => thetaHeatRateSourceReaderL2 n hn y) 0 := by
  have hsource := tendsto_thetaSquareFiniteCausalSourceL2 hn
  have hrestrict := negativeHalfLineRestrictionL2.continuous.continuousAt.tendsto.comp hsource
  change Tendsto (fun N => negativeHalfLineRestrictionL2
    (thetaSquareFiniteCausalSourceL2 n N hn)) atTop
    (𝓝 (negativeHalfLineRestrictionL2 (thetaHeatRateSourceReaderL2 n hn))) at hrestrict
  have hzeroSeq : (fun N => negativeHalfLineRestrictionL2
      (thetaSquareFiniteCausalSourceL2 n N hn)) =
      fun _ : ℕ => 0 := by
    funext N
    exact (hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero _).mp
      (thetaSquareFiniteCausalSourceL2_hasAELowerSupport hn N)
  rw [hzeroSeq] at hrestrict
  have htargetZero : negativeHalfLineRestrictionL2
      (thetaHeatRateSourceReaderL2 n hn) = 0 :=
    tendsto_nhds_unique hrestrict tendsto_const_nhds
  exact (hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero _).mpr htargetZero



end RHTower

