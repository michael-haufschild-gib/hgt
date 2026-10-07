import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction
import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCoherentGap

/-!
# Finite coherent completion of the far-polar Fejer source

A positive finite geometric filter expresses `farPolarTest (N*s)` as a weighted sum of
translates of `farPolarTest s`. Weighted variance gives actual polar completion tests at the
same aperture. For `1/201 ≤ s ≤ 1/200`, their complete integer trace cancels the far source,
while their total archimedean energy has a bound independent of `N`.

The public theorem `bounded_coherent_completion` is unconditional. It bounds the energy of
one constructed repair family. The exact zero-frequency identity also gives a strictly positive
total-energy floor, even under arbitrary refinements `s -> 0` with `N*s >= 4`. This is a
family-specific bound, not prime-blind positivity. The earlier independent-atom box-budget
obstruction does not apply to these coherent repairs.
-/

open Real Finset Filter Topology Set Complex MeasureTheory Zeta23
noncomputable section
namespace RHTower.ExposingRayCompletion

private theorem variance_identity {ι : Type*} [Fintype ι] (w : ι → ℝ) (v : ι → ℂ)
    (M V : ℝ) (z : ℂ) (hM : 0 < M) (hw : ∑ i, w i = M)
    (hv : ∀ i, ‖v i‖ ^ 2 = V) (hz : ∑ i, (w i : ℂ) * v i = z) :
    ‖z‖ ^ 2 + ∑ i, (w i / M) * ‖(M : ℂ) * v i - z‖ ^ 2 = M ^ 2 * V := by
  have hre : ∑ i, w i * (v i).re = z.re := by
    have := congrArg Complex.re hz
    simpa using this
  have him : ∑ i, w i * (v i).im = z.im := by
    have := congrArg Complex.im hz
    simpa using this
  have he : ∀ i, (w i / M) * ‖(M : ℂ) * v i - z‖ ^ 2 =
      M * V * w i - 2 * z.re * (w i * (v i).re) -
        2 * z.im * (w i * (v i).im) + (‖z‖ ^ 2 / M) * w i := by
    intro i
    have hi := hv i
    simp only [Complex.sq_norm, Complex.normSq_apply] at hi ⊢
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_im, Complex.mul_im]
    field_simp [hM.ne']
    linear_combination (M ^ 2 * w i) * hi
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hw, hre, him]
  rw [div_mul_cancel₀ _ hM.ne']
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private def q (s : ℝ) : ℝ := Real.exp (-(s / 2))
private def gain (N : ℕ) (s : ℝ) : ℝ := (1 + q s ^ 2) / (1 + (q s ^ N) ^ 2)
/-- Positive weight of an actual finite geometric-filter translate. -/
def weight (N : ℕ) (s : ℝ) (i : Fin N × Fin N) : ℝ :=
  gain N s * q s ^ i.1.val * q s ^ i.2.val
/-- Total mass of the finite geometric filter. -/
def mass (N : ℕ) (s : ℝ) : ℝ := ∑ i, weight N s i
private def shift (s : ℝ) {N : ℕ} (i : Fin N × Fin N) : ℝ := (i.1.val - (i.2.val : ℝ)) * s
private def source (N : ℕ) (s : ℝ) (i : Fin N × Fin N) (u : ℝ) : ℂ :=
  farPolarTest s (u - shift s i)
/-- Actual variance repair paired with one geometric-filter translate. -/
def repair (N : ℕ) (s : ℝ) (i : Fin N × Fin N) (u : ℝ) : ℂ :=
  (mass N s : ℂ) * source N s i u - farPolarTest (N * s) u

private theorem q_pos (s : ℝ) : 0 < q s := Real.exp_pos _
private theorem gain_pos (N : ℕ) (s : ℝ) : 0 < gain N s := by unfold gain; positivity
private theorem weight_pos (N : ℕ) (s : ℝ) (i : Fin N × Fin N) : 0 < weight N s i := by
  unfold weight; exact mul_pos (mul_pos (gain_pos _ _) (pow_pos (q_pos _) _)) (pow_pos (q_pos _) _)

private theorem q_nat (N : ℕ) (s : ℝ) : q s ^ N = q (N * s) := by
  unfold q
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem coeff_q (s : ℝ) : farPolarCoeff s * (1 + q s ^ 2) = 2 * q s := by
  have hc := Real.cosh_pos (s / 2)
  have he : Real.exp (s / 2) * q s = 1 := by
    unfold q; rw [← Real.exp_add]; simp
  have hcosh : Real.cosh (s / 2) * (2 * q s) = 1 + q s ^ 2 := by
    rw [Real.cosh_eq]
    change (Real.exp (s / 2) + q s) / 2 * (2 * q s) = _
    nlinarith
  rw [farPolarCoeff, hcosh.symm]
  field_simp

private def phase (x τ : ℝ) : ℂ := Complex.exp ((τ * x : ℝ) * I)

private theorem phase_mul_neg (x τ : ℝ) : phase x τ * phase (-x) τ = 1 := by
  unfold phase
  rw [← Complex.exp_add]
  have he : ((τ * x : ℝ) : ℂ) * I + ((τ * -x : ℝ) : ℂ) * I = 0 := by
    push_cast; ring
  rw [he, Complex.exp_zero]

private theorem phase_pow (x τ : ℝ) (N : ℕ) : phase x τ ^ N = phase (N * x) τ := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem phase_cos (x τ : ℝ) :
    phase x τ + phase (-x) τ = 2 * Complex.cos ((x : ℂ) * τ) := by
  unfold phase
  rw [Complex.cos]
  have hp : ((τ * x : ℝ) : ℂ) * I = (x : ℂ) * τ * I := by push_cast; ring
  have hm : ((τ * -x : ℝ) : ℂ) * I = -((x : ℂ) * τ) * I := by push_cast; ring
  rw [hp, hm]
  ring

private theorem multiplier_factor (x τ : ℝ) :
    (1 + (q x : ℂ) ^ 2) * (1 - (farPolarCoeff x : ℂ) * Complex.cos ((x : ℂ) * τ)) =
      (1 - (q x : ℂ) * phase x τ) * (1 - (q x : ℂ) * phase (-x) τ) := by
  have hp := phase_mul_neg x τ
  have hc : (farPolarCoeff x : ℂ) * (1 + (q x : ℂ) ^ 2) = 2 * q x := by
    exact_mod_cast coeff_q x
  calc _ = 1 + (q x : ℂ) ^ 2 - (q x : ℂ) * (phase x τ + phase (-x) τ) := by
        rw [phase_cos]
        linear_combination -(Complex.cos ((x : ℂ) * τ)) * hc
    _ = _ := by linear_combination -(q x : ℂ) ^ 2 * hp

private theorem geom_factor (a b : ℂ) (N : ℕ) :
    ((1 - a) * (1 - b)) * ((∑ j : Fin N, a ^ j.val) * (∑ k : Fin N, b ^ k.val)) =
      (1 - a ^ N) * (1 - b ^ N) := by
  have ha : (∑ j : Fin N, a ^ j.val) * (1 - a) = 1 - a ^ N := by
    rw [Fin.sum_univ_eq_sum_range (fun j => a ^ j) N]
    exact geom_sum_mul_neg a N
  have hb : (∑ k : Fin N, b ^ k.val) * (1 - b) = 1 - b ^ N := by
    rw [Fin.sum_univ_eq_sum_range (fun k => b ^ k) N]
    exact geom_sum_mul_neg b N
  calc _ = ((∑ j : Fin N, a ^ j.val) * (1 - a)) *
      ((∑ k : Fin N, b ^ k.val) * (1 - b)) := by ring
    _ = _ := by rw [ha, hb]

private theorem geometric_multiplier (N : ℕ) (s τ : ℝ) :
    (gain N s : ℂ) * (1 - (farPolarCoeff s : ℂ) * Complex.cos ((s : ℂ) * τ)) *
      (∑ j : Fin N, ((q s : ℂ) * phase s τ) ^ j.val) *
      (∑ k : Fin N, ((q s : ℂ) * phase (-s) τ) ^ k.val) =
      1 - (farPolarCoeff (N * s) : ℂ) * Complex.cos (((N * s : ℝ) : ℂ) * τ) := by
  have hD : (1 + ((q s : ℂ) ^ N) ^ 2) ≠ 0 := by
    have hr : (1 + (q s ^ N) ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast hr
  have hA : (1 + ((q s : ℂ) ^ N) ^ 2) * (gain N s : ℂ) = 1 + (q s : ℂ) ^ 2 := by
    have hr : (1 + (q s ^ N) ^ 2) * gain N s = 1 + q s ^ 2 := by
      unfold gain
      field_simp
    exact_mod_cast hr
  have hp : ((q s : ℂ) * phase s τ) ^ N = (q (N * s) : ℂ) * phase (N * s) τ := by
    rw [mul_pow, phase_pow, ← Complex.ofReal_pow, q_nat]
  have hm : ((q s : ℂ) * phase (-s) τ) ^ N = (q (N * s) : ℂ) * phase (-(N * s)) τ := by
    rw [mul_pow, phase_pow, ← Complex.ofReal_pow, q_nat]
    congr 2
    ring
  apply mul_left_cancel₀ hD
  calc (1 + ((q s : ℂ) ^ N) ^ 2) * _ =
        ((1 + ((q s : ℂ) ^ N) ^ 2) * (gain N s : ℂ)) *
          (1 - (farPolarCoeff s : ℂ) * Complex.cos ((s : ℂ) * τ)) *
          ((∑ j : Fin N, ((q s : ℂ) * phase s τ) ^ j.val) *
          (∑ k : Fin N, ((q s : ℂ) * phase (-s) τ) ^ k.val)) := by ring
    _ = ((1 - (q s : ℂ) * phase s τ) * (1 - (q s : ℂ) * phase (-s) τ)) *
          ((∑ j : Fin N, ((q s : ℂ) * phase s τ) ^ j.val) *
          (∑ k : Fin N, ((q s : ℂ) * phase (-s) τ) ^ k.val)) := by
      rw [hA, multiplier_factor]
    _ = (1 - ((q s : ℂ) * phase s τ) ^ N) *
          (1 - ((q s : ℂ) * phase (-s) τ) ^ N) := geom_factor _ _ N
    _ = (1 + ((q s : ℂ) ^ N) ^ 2) *
          (1 - (farPolarCoeff (N * s) : ℂ) * Complex.cos (((N * s : ℝ) : ℂ) * τ)) := by
      rw [hp, hm, ← multiplier_factor, ← q_nat, Complex.ofReal_pow]

private theorem paperFT_source (N : ℕ) (s τ : ℝ) (i : Fin N × Fin N) :
    paperFT (source N s i) τ = phase (shift s i) τ * paperFT (farPolarTest s) τ := by
  unfold source
  rw [paperFT_translate']
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

private theorem phase_shift {N : ℕ} (s τ : ℝ) (i : Fin N × Fin N) :
    phase (shift s i) τ = phase s τ ^ i.1.val * phase (-s) τ ^ i.2.val := by
  rw [phase_pow, phase_pow]
  unfold phase shift
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact finite positive-filter identity on the whole real Fourier line. -/
private theorem fourier_mean (N : ℕ) (s τ : ℝ) :
    ∑ i : Fin N × Fin N, (weight N s i : ℂ) * paperFT (source N s i) τ =
      paperFT (farPolarTest (N * s)) τ := by
  simp_rw [paperFT_source, phase_shift]
  rw [Fintype.sum_prod_type]
  have hs : (∑ j : Fin N, ∑ k : Fin N,
      (weight N s (j, k) : ℂ) *
        (phase s τ ^ j.val * phase (-s) τ ^ k.val * paperFT (farPolarTest s) τ)) =
      (gain N s : ℂ) * (∑ j : Fin N, ((q s : ℂ) * phase s τ) ^ j.val) *
        (∑ k : Fin N, ((q s : ℂ) * phase (-s) τ) ^ k.val) *
          paperFT (farPolarTest s) τ := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [weight, Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
    ring
  rw [hs, paperFT_farPolarTest]
  calc _ = paperFT fejerTest τ *
      ((gain N s : ℂ) * (1 - (farPolarCoeff s : ℂ) * Complex.cos ((s : ℂ) * τ)) *
        (∑ j : Fin N, ((q s : ℂ) * phase s τ) ^ j.val) *
        (∑ k : Fin N, ((q s : ℂ) * phase (-s) τ) ^ k.val)) := by ring
    _ = paperFT (farPolarTest (N * s)) τ := by
      rw [geometric_multiplier, paperFT_farPolarTest]

private theorem source_norm (N : ℕ) (s τ : ℝ) (i : Fin N × Fin N) :
    ‖paperFT (source N s i) τ‖ = ‖paperFT (farPolarTest s) τ‖ := by
  rw [paperFT_source, norm_mul]
  have hp : ‖phase (shift s i) τ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [hp, one_mul]

private theorem mass_eq (N : ℕ) (s : ℝ) :
    mass N s = gain N s * (∑ j : Fin N, q s ^ j.val) ^ 2 := by
  unfold mass weight
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem mass_pos {N : ℕ} (hN : 0 < N) (s : ℝ) : 0 < mass N s := by
  unfold mass
  apply Finset.sum_pos'
  · intro i _; exact (weight_pos N s i).le
  · exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _, weight_pos _ _ _⟩

private theorem source_polar {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin N × Fin N) : IsPolarTest (N * s + 17 / 50) (source N s i) := by
  have hshift : -((N : ℝ) - 1) * s ≤ shift s i ∧ shift s i ≤ ((N : ℝ) - 1) * s := by
    have hj : (i.1.val : ℝ) ≤ (N : ℝ) - 1 := by
      have h : (i.1.val : ℝ) + 1 ≤ N := by exact_mod_cast i.1.isLt
      linarith
    have hk : (i.2.val : ℝ) ≤ (N : ℝ) - 1 := by
      have h : (i.2.val : ℝ) + 1 ≤ N := by exact_mod_cast i.2.isLt
      linarith
    have hj0 : (0 : ℝ) ≤ i.1.val := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ i.2.val := Nat.cast_nonneg _
    unfold shift
    constructor
    · exact mul_le_mul_of_nonneg_right (by linarith) hs
    · exact mul_le_mul_of_nonneg_right (by linarith) hs
  refine ⟨by positivity, (contDiff_farPolarTest s).comp (contDiff_id.sub contDiff_const), ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    have hm : u - shift s i ∈ tsupport (farPolarTest s) := subset_tsupport _ hu
    have hb := tsupport_farPolarTest hs hm
    exact ⟨by nlinarith [hb.1, hshift.1], by nlinarith [hb.2, hshift.2]⟩
  · unfold source
    rw [paperFT_translate', paperFT_farPolarTest_half_I, mul_zero]
  · unfold source
    rw [paperFT_translate', paperFT_farPolarTest_neg_half_I, mul_zero]

private theorem compact_of_polar {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) :
    HasCompactSupport f := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hf.2.2.1

private theorem paperFT_linear {a : ℝ} {f g : ℝ → ℂ} (hf : IsPolarTest a f)
    (hg : IsPolarTest a g) (M : ℝ) (z : ℂ) :
    paperFT (fun u => (M : ℂ) * f u - g u) z = (M : ℂ) * paperFT f z - paperFT g z := by
  have hfi : Integrable fun u => f u * Complex.exp (I * z * u) :=
    (hf.2.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport (compact_of_polar hf).mul_right
  have hgi : Integrable fun u => g u * Complex.exp (I * z * u) :=
    (hg.2.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport (compact_of_polar hg).mul_right
  unfold paperFT
  have he : (fun u => ((M : ℂ) * f u - g u) * Complex.exp (I * z * u)) =
      fun u => (M : ℂ) * (f u * Complex.exp (I * z * u)) - g u * Complex.exp (I * z * u) := by
    funext u; ring
  rw [he, integral_sub (hfi.const_mul _) hgi, integral_const_mul]

private theorem polar_linear {a : ℝ} {f g : ℝ → ℂ} (hf : IsPolarTest a f)
    (hg : IsPolarTest a g) (M : ℝ) : IsPolarTest a (fun u => (M : ℂ) * f u - g u) := by
  refine ⟨hf.1, (contDiff_const.mul hf.2.1).sub hg.2.1, ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    by_contra h
    have hf0 : f u = 0 := image_eq_zero_of_notMem_tsupport (fun hm => h (hf.2.2.1 hm))
    have hg0 : g u = 0 := image_eq_zero_of_notMem_tsupport (fun hm => h (hg.2.2.1 hm))
    exact hu (by simp [hf0, hg0])
  · rw [paperFT_linear hf hg, hf.2.2.2.1, hg.2.2.2.1, mul_zero, sub_zero]
  · rw [paperFT_linear hf hg, hf.2.2.2.2, hg.2.2.2.2, mul_zero, sub_zero]

private theorem far_polar {x : ℝ} (hx : 0 ≤ x) : IsPolarTest (x + 17 / 50) (farPolarTest x) :=
  ⟨by linarith, contDiff_farPolarTest x, tsupport_farPolarTest hx,
    paperFT_farPolarTest_half_I x, paperFT_farPolarTest_neg_half_I x⟩

private theorem repair_polar {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin N × Fin N) : IsPolarTest (N * s + 17 / 50) (repair N s i) :=
  polar_linear (source_polar hN hs i) (far_polar (by positivity)) (mass N s)

private theorem density_identity {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (τ : ℝ) :
    ‖paperFT (farPolarTest (N * s)) τ‖ ^ 2 +
      ∑ i : Fin N × Fin N, (weight N s i / mass N s) * ‖paperFT (repair N s i) τ‖ ^ 2 =
        mass N s ^ 2 * ‖paperFT (farPolarTest s) τ‖ ^ 2 := by
  have hi (i : Fin N × Fin N) : paperFT (repair N s i) τ =
      (mass N s : ℂ) * paperFT (source N s i) τ - paperFT (farPolarTest (N * s)) τ :=
    paperFT_linear (source_polar hN hs i) (far_polar (by positivity)) _ _
  simp_rw [hi]
  exact variance_identity (weight N s) (fun i => paperFT (source N s i) τ) _ _ _
    (mass_pos hN s) rfl (fun i => by rw [source_norm]) (fourier_mean N s τ)

private def massBound : ℝ := 2 * (1 / (1 - Real.exp (-1 / 402))) ^ 2

private theorem mass_le {N : ℕ} {s : ℝ} (hs : 1 / 201 ≤ s) : mass N s ≤ massBound := by
  have hr : Real.exp (-1 / 402) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hq : q s ≤ Real.exp (-1 / 402) := by
    unfold q
    exact Real.exp_le_exp.mpr (by linarith)
  have hq1 : q s ≤ 1 := hq.trans hr.le
  have hA : gain N s ≤ 2 := by
    unfold gain
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q s ^ N), q_pos s]
  let S : ℝ := ∑ j : Fin N, q s ^ j.val
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => (pow_pos (q_pos s) _).le)
  have hgeom : S * (1 - q s) = 1 - q s ^ N := by
    unfold S
    rw [Fin.sum_univ_eq_sum_range (fun j => q s ^ j) N]
    exact geom_sum_mul_neg _ _
  have hSb : S ≤ 1 / (1 - Real.exp (-1 / 402)) := by
    apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    nlinarith [pow_nonneg (q_pos s).le N, mul_nonneg hS (sub_nonneg.mpr hq)]
  rw [mass_eq]
  change gain N s * S ^ 2 ≤ _
  unfold massBound
  nlinarith [sq_nonneg (S - 1 / (1 - Real.exp (-1 / 402))),
    mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg S)]

private theorem integrate_identity {ι : Type*} [Fintype ι] (F G : ℝ → ℝ)
    (H : ι → ℝ → ℝ) (w : ι → ℝ) (c : ℝ)
    (hF : Integrable F) (hH : ∀ i, Integrable (H i))
    (h : ∀ t, F t + ∑ i, w i * H i t = c * G t) :
    (∫ t, F t) + ∑ i, w i * ∫ t, H i t = c * ∫ t, G t := by
  have hsum : Integrable (fun t => ∑ i, w i * H i t) :=
    integrable_finsetSum _ (fun i _ => (hH i).const_mul _)
  calc _ = (∫ t, F t) + ∫ t, ∑ i, w i * H i t := by
         rw [integral_finsetSum _ (fun i _ => (hH i).const_mul _)]
         simp only [integral_const_mul]
    _ = ∫ t, F t + ∑ i, w i * H i t := (integral_add hF hsum).symm
    _ = _ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul]

private theorem energy_identity {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) :
    archEnergy (farPolarTest (N * s)) +
      ∑ i : Fin N × Fin N, (weight N s i / mass N s) * archEnergy (repair N s i) =
        mass N s ^ 2 * archEnergy (farPolarTest s) := by
  apply integrate_identity
  · exact integrable_normSq_paperFT_mul_arch (contDiff_farPolarTest _) (tsupport_farPolarTest (by positivity))
  · intro i
    exact integrable_normSq_paperFT_mul_arch (repair_polar hN hs i).2.1 (repair_polar hN hs i).2.2.1
  · intro t
    have hd := congrArg (fun x : ℝ => x * archimedeanWeilSymbol (t / (2 * π))) (density_identity hN hs t)
    simpa only [add_mul, Finset.sum_mul, mul_assoc] using hd

private theorem atom_identity {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    atomCoeff (farPolarTest (N * s)) n +
      ∑ i : Fin N × Fin N, (weight N s i / mass N s) * atomCoeff (repair N s i) n =
        mass N s ^ 2 * atomCoeff (farPolarTest s) n := by
  have he := integrate_identity
    (fun t => ‖paperFT (farPolarTest (N * s)) t‖ ^ 2 * Real.cos (t * Real.log n))
    (fun t => ‖paperFT (farPolarTest s) t‖ ^ 2 * Real.cos (t * Real.log n))
    (fun i : Fin N × Fin N => fun t => ‖paperFT (repair N s i) t‖ ^ 2 * Real.cos (t * Real.log n))
    (fun i => weight N s i / mass N s) (mass N s ^ 2)
    (integrable_normSq_paperFT_mul_cos (contDiff_farPolarTest _) (tsupport_farPolarTest (by positivity)) _)
    (fun i => integrable_normSq_paperFT_mul_cos (repair_polar hN hs i).2.1 (repair_polar hN hs i).2.2.1 _)
    (fun t => by
      have hd := congrArg (fun x : ℝ => x * Real.cos (t * Real.log n)) (density_identity hN hs t)
      simpa only [add_mul, Finset.sum_mul, mul_assoc] using hd)
  simp_rw [integral_normSq_paperFT_mul_cos_eq (contDiff_farPolarTest _) (tsupport_farPolarTest (by positivity : 0 ≤ (N : ℝ) * s)),
    integral_normSq_paperFT_mul_cos_eq (contDiff_farPolarTest _) (tsupport_farPolarTest hs)] at he
  simp_rw [integral_normSq_paperFT_mul_cos_eq (repair_polar hN hs _).2.1 (repair_polar hN hs _).2.2.1] at he
  change π * atomCoeff (farPolarTest (N * s)) n +
    ∑ i, (weight N s i / mass N s) * (π * atomCoeff (repair N s i) n) =
      mass N s ^ 2 * (π * atomCoeff (farPolarTest s) n) at he
  have hsum : (∑ i, (weight N s i / mass N s) * (π * atomCoeff (repair N s i) n)) =
      π * ∑ i, (weight N s i / mass N s) * atomCoeff (repair N s i) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsum] at he
  nlinarith [Real.pi_pos]

private theorem short_atoms_zero {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 200)
    {n : ℕ} (hn : 2 ≤ n) : atomCoeff (farPolarTest s) n = 0 := by
  apply atomCoeff_eq_zero_of_floor_lt (tsupport_farPolarTest hs0)
  have hlog : 2 * (s + 17 / 50) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have he : Real.exp (2 * (s + 17 / 50)) < 2 := (Real.lt_log_iff_exp_lt (by norm_num)).mp hlog
  exact (Nat.floor_lt (Real.exp_pos _).le).mpr (he.trans_le (by exact_mod_cast hn))

private theorem abs_energy_far_le {x : ℝ} (hx : 0 ≤ x) :
    |archEnergy (farPolarTest x)| ≤ 4 * fejerArchAbsEnergy := by
  have hc0 := farPolarCoeff_nonneg x
  have hc1 : farPolarCoeff x ≤ 1 := by
    unfold farPolarCoeff
    apply (div_le_iff₀ (Real.cosh_pos _)).mpr
    simpa only [one_mul] using Real.one_le_cosh (x / 2)
  have hF := integrable_normSq_paperFT_mul_arch (contDiff_farPolarTest x) (tsupport_farPolarTest hx)
  have hψ := integrable_normSq_paperFT_mul_arch contDiff_fejerTest tsupport_fejerTest
  unfold archEnergy fejerArchAbsEnergy
  calc _ ≤ ∫ t : ℝ, |‖paperFT (farPolarTest x) t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * π))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, 4 * |‖paperFT fejerTest t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * π))| := by
      apply integral_mono hF.abs (hψ.abs.const_mul 4)
      intro t
      simp only
      rw [normSq_paperFT_farPolarTest]
      have hm : (1 - farPolarCoeff x * Real.cos (t * x)) ^ 2 ≤ 4 := by
        have hb := (abs_le.mp (abs_sq_sub_one_le hc0 (Real.abs_cos_le_one (t * x)))).2
        nlinarith
      have he : ‖paperFT fejerTest t‖ ^ 2 * (1 - farPolarCoeff x * Real.cos (t * x)) ^ 2 *
          archimedeanWeilSymbol (t / (2 * π)) =
          (1 - farPolarCoeff x * Real.cos (t * x)) ^ 2 *
            (‖paperFT fejerTest t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * π))) := by ring
      rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right hm (abs_nonneg _)
    _ = _ := integral_const_mul _ _

private theorem choose_step {X : ℝ} (hX : 4 ≤ X) :
    ∃ N : ℕ, 0 < N ∧ ∃ s : ℝ, 1 / 201 ≤ s ∧ s ≤ 1 / 200 ∧ N * s = X := by
  let N := ⌈200 * X⌉₊
  have hlo : 200 * X ≤ (N : ℝ) := Nat.le_ceil _
  have hup : (N : ℝ) < 200 * X + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨N, hN, X / N, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hNr).mpr
    linarith
  · apply (div_le_iff₀ hNr).mpr
    linarith
  · field_simp

/-- Every far negative-energy polar packet has a positive, finite, same-aperture completion
whose complete integer trace cancels exactly and whose archimedean cost is uniformly bounded.
No prime-blind positivity or Riemann-hypothesis premise is used. -/
theorem bounded_coherent_completion :
    ∃ C : ℝ, ∀ X : ℝ, 4 ≤ X →
      ∃ (N : ℕ) (h : Fin N × Fin N → ℝ → ℂ) (α : Fin N × Fin N → ℝ),
        (∀ i, IsPolarTest (X + 17 / 50) (h i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → atomCoeff (farPolarTest X) n + ∑ i, α i * atomCoeff (h i) n = 0) ∧
        (∑ i, α i * archEnergy (h i)) ≤ C := by
  have hE0 : 0 ≤ fejerArchAbsEnergy := integral_nonneg (fun _ => abs_nonneg _)
  refine ⟨4 * (massBound ^ 2 + 1) * fejerArchAbsEnergy, ?_⟩
  intro X hX
  obtain ⟨N, hN, s, hslo, hshi, he⟩ := choose_step hX
  have hs : 0 ≤ s := by linarith
  refine ⟨N, repair N s, (fun i => weight N s i / mass N s), ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [he] using repair_polar hN hs i
  · intro i
    exact (div_pos (weight_pos N s i) (mass_pos hN s)).le
  · intro n hn
    have hi := atom_identity hN hs n
    rw [he, short_atoms_zero hs hshi hn, mul_zero] at hi
    exact hi
  · have hi := energy_identity hN hs
    rw [he] at hi
    have hshort := (abs_le.mp (abs_energy_far_le hs)).2
    have hfar := (abs_le.mp (abs_energy_far_le (show 0 ≤ X by linarith))).1
    have hM := mass_le (N := N) hslo
    have hM0 := (mass_pos hN s).le
    have hB0 : 0 ≤ massBound := by unfold massBound; positivity
    have hMsq : mass N s ^ 2 ≤ massBound ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hshort (sq_nonneg (mass N s))
    have hb := mul_le_mul_of_nonneg_right hMsq (show 0 ≤ 4 * fejerArchAbsEnergy by positivity)
    nlinarith

/-- The finite filter preserves its exact zero-frequency defect, even as the step tends to zero. -/
theorem mass_defect_identity (N : ℕ) (s : ℝ) :
    mass N s * (1-farPolarCoeff s) = 1-farPolarCoeff (N*s) := by
  have h := geometric_multiplier N s 0
  simp only [mul_zero,zero_mul,Complex.ofReal_zero,Complex.cos_zero,mul_one,phase,Complex.exp_zero] at h
  have hr : gain N s * (1-farPolarCoeff s) *
      (∑ j : Fin N, q s ^ j.val) * (∑ j : Fin N, q s ^ j.val) =
        1-farPolarCoeff (N*s) := by exact_mod_cast h
  rw [mass_eq]
  nlinarith only [hr]

/-- Exact family-specific total energy floor, uniform under arbitrary short-step refinement. -/
theorem geometric_completion_energy_floor {N : ℕ} (hN : 0 < N)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/200) :
    (3*π/25)*(1-farPolarCoeff (N*s))^2 ≤
      archEnergy (farPolarTest (N*s)) +
        ∑ i : Fin N × Fin N, (weight N s i / mass N s) * archEnergy (repair N s i) := by
  rw [energy_identity hN hs0]
  have h := mul_le_mul_of_nonneg_left
    (ExposingRayCoherentGap.short_source_energy_floor hs0 hs) (sq_nonneg (mass N s))
  calc (3*π/25)*(1-farPolarCoeff (N*s))^2 =
      mass N s^2*((3*π/25)*(1-farPolarCoeff s)^2) := by
        rw [← mass_defect_identity N s]
        ring
    _ ≤ _ := h

/-- A fixed positive separation gives a uniform total-energy floor under every short-step refinement. -/
theorem geometric_completion_uniform_positive_floor :
    ∀ X₀ : ℝ, 0 < X₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1/200 → X₀ ≤ N*s →
        δ ≤ archEnergy (farPolarTest (N*s)) +
          ∑ i : Fin N × Fin N, (weight N s i / mass N s) * archEnergy (repair N s i) := by
  intro X₀ hX₀
  have hc : farPolarCoeff X₀ < 1 := by
    unfold farPolarCoeff
    rw [div_lt_one (Real.cosh_pos _)]
    exact Real.one_lt_cosh.mpr (ne_of_gt (by positivity))
  refine ⟨(3*π/25)*(1-farPolarCoeff X₀)^2,
    mul_pos (by positivity) (sq_pos_of_pos (sub_pos.mpr hc)),?_⟩
  intro N s hs0 hs hX
  have hN : 0 < N := by
    by_contra h
    have : N=0 := Nat.eq_zero_of_not_pos h
    simp only [this,Nat.cast_zero,zero_mul] at hX
    linarith
  have hm : farPolarCoeff (N*s) ≤ farPolarCoeff X₀ := by
    unfold farPolarCoeff
    apply one_div_le_one_div_of_le (Real.cosh_pos _)
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ X₀/2),abs_of_nonneg (by positivity)]
    linarith
  have hsq : (1-farPolarCoeff X₀)^2 ≤ (1-farPolarCoeff (N*s))^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans
    (geometric_completion_energy_floor hN hs0 hs)

/-- The original compact-step conjecture, with no unproved source premise. -/
theorem geometric_completion_fixed_step_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → ∀ s : ℝ, 1/201 ≤ s → s ≤ 1/200 →
      δ ≤ mass N s ^ 2 * archEnergy (farPolarTest s) := by
  obtain ⟨δ,hδ,hfloor⟩ := geometric_completion_uniform_positive_floor (1/201) (by norm_num)
  refine ⟨δ,hδ,fun N hN s hslo hshi => ?_⟩
  have hs0 : 0 ≤ s := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXs : 1/201 ≤ (N : ℝ)*s := hslo.trans (by nlinarith)
  have h := hfloor N s hs0 hshi hXs
  rwa [energy_identity hN hs0] at h

end RHTower.ExposingRayCompletion
