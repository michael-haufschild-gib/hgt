import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentDyadicSaving
import GaloisForLFunctions.ExceptionalLayerTheory.PolynomialDampingReadsTheDivisor
import GaloisForLFunctions.RHTower.Sieve.DirichletDyadicTailAssembly

/-!
# Gaussian moment cancellation at every product scale

The first derivative controls active rectangles below a logarithmic
multiple of the stationary scale. Beyond it, real Gaussian damping
supplies the same inverse-height saving. Height-sized Vaughan cutoffs
therefore give a uniform estimate with half the Gaussian decay retained.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_gaussian_phase_on_rectangle_le {α : ℝ} (hα : 0 ≤ α)
    (ξ t : ℝ) {D M d m : ℕ} (hd : D ≤ d) (hm : M ≤ m) :
    ‖gaussianPrimePhase α ξ t (d * m)‖ ≤
      Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have hnorm : ‖gaussianPrimePhase α ξ t (d * m)‖ =
      Real.exp (-α * (d : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
    rw [gaussianPrimePhase, Complex.norm_exp]
    congr 1
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.natCast_im, pow_two, Complex.mul_im]
    push_cast
    ring
  rw [hnorm]
  apply Real.exp_le_exp.mpr
  have hprod : (D : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
    have hD2 : (D : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hd 2
    have hM2 : (M : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hm 2
    exact mul_le_mul hD2 hM2 (sq_nonneg _) (sq_nonneg _)
  have hh := mul_le_mul_of_nonpos_left hprod (neg_nonpos.mpr hα)
  nlinarith only [hh]

/-- The elementary energy bound retains Gaussian damping even at resonant frequencies. -/
theorem norm_maskedGaussian_dyadic_trivial_sq_le {α : ℝ} (hα : 0 ≤ α)
    (ξ t : ℝ) (A B D M : ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Ico D (2 * D), a d *
      ∑ m ∈ Ico M (2 * M), b m * maskedGaussianPhase α ξ t A B d m‖ ^ 2 ≤
      (∑ d ∈ Ico D (2 * D), ‖a d‖ ^ 2) *
        (∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) *
          ((D : ℝ) * M) * Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have hmasks (d m : ℕ) (hd : d ∈ Ico D (2 * D)) (hm : m ∈ Ico M (2 * M)) :
      ‖maskedGaussianPhase α ξ t A B d m‖ ^ 2 ≤
        Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
    by_cases hcut : d ∈ fibreIco A B m
    · rw [maskedGaussianPhase, if_pos hcut]
      calc
        _ ≤ (Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) ^ 2 := by
          gcongr
          exact norm_gaussian_phase_on_rectangle_le hα ξ t (mem_Ico.mp hd).1 (mem_Ico.mp hm).1
        _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    · rw [maskedGaussianPhase, if_neg hcut, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      positivity
  have hinner (d : ℕ) (hd : d ∈ Ico D (2 * D)) :
      ‖∑ m ∈ Ico M (2 * M), b m * maskedGaussianPhase α ξ t A B d m‖ ^ 2 ≤
        (∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) *
          ((M : ℝ) * Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) := by
    refine (norm_bilinear_sq_le (Ico M (2 * M)) b _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun _ _ => sq_nonneg _)
    calc
      _ ≤ ∑ m ∈ Ico M (2 * M), Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) :=
        sum_le_sum fun m hm => hmasks d m hd hm
      _ = _ := by simp [show 2 * M - M = M by omega]
  refine (norm_bilinear_sq_le (Ico D (2 * D)) a _).trans ?_
  have hh := sum_le_sum hinner
  have he : (∑ d ∈ Ico D (2 * D), (∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) *
      ((M : ℝ) * Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))) =
      (D : ℝ) * ((∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) *
        ((M : ℝ) * Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))) := by
    simp [show 2 * D - D = D by omega]
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)

private theorem norm_gaussianVaughan_dyadic_trivial_sq_le {α : ℝ} (hα : 0 ≤ α)
    (σ ξ t : ℝ) {A B D M : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hM : 1 ≤ M) (U V : ℕ) :
    ‖gaussianVaughanDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      (∑ d ∈ Ico D (2 * D), ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
        (∑ m ∈ Ico M (2 * M), ‖((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
          ((D : ℝ) * M) * Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have he : gaussianVaughanDyadicSum σ α ξ t A B D M U V =
      ∑ d ∈ Ico D (2 * D),
        (((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          ∑ m ∈ Ico M (2 * M),
            (((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)) *
              maskedGaussianPhase α ξ t A B d m := by
    unfold gaussianVaughanDyadicSum
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    have hf : d * m ∈ Ico A B ↔ d ∈ fibreIco A B m :=
      mem_fibre_iff (hM.trans (mem_Ico.mp hm).1) hA hB d
    by_cases hc : d * m ∈ Ico A B
    · rw [if_pos hc, maskedGaussianPhase, if_pos (hf.mp hc)]
      simp only [gaussianPrimeWeight, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m), Complex.ofReal_mul]
      ring
    · rw [if_neg hc, maskedGaussianPhase, if_neg (fun hh => hc (hf.mpr hh)), mul_zero, mul_zero]
  rw [he]
  exact norm_maskedGaussian_dyadic_trivial_sq_le hα ξ t A B D M _ _

/-- A Gaussian moment has a uniform absolute envelope at every frequency. -/
theorem exists_gaussianVaughan_moment_trivial_envelope_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → α ≤ ξ → 0 < ξ → 0 < t →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
              (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t) ^ 2) := by
  obtain ⟨C, hC, henergy⟩ := exists_gaussianVaughan_shifted_dyadic_coefficient_energy
  refine ⟨4 * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM
  have hE := henergy σ D M U V hσ hD hM
  have hε : ‖(α : ℂ) - ξ * I‖ ≤ 2 * ξ := by
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
      _ = α + ξ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hα, abs_of_pos hξ, Complex.norm_I, mul_one]
      _ ≤ _ := by linarith only [hαξ]
  have hεt : ‖((α : ℂ) - ξ * I) / t‖ ^ 2 ≤ (2 * ξ / t) ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    gcongr
  have hbase := (norm_gaussianVaughan_dyadic_trivial_sq_le hα (σ - 2) ξ t hA hB hM U V).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hE (by positivity)) (Real.exp_pos _).le)
  unfold gaussianVaughanMomentDyadicSum
  rw [norm_mul, mul_pow]
  exact (mul_le_mul hεt hbase (sq_nonneg _) (by positivity)).trans_eq (by ring)

private theorem moment_gaussian_absorption {r y : ℝ} (hr : 0 ≤ r) (hy : r / 2 ≤ y) :
    r * Real.exp (-y) ≤ 2 ∧ r ^ 2 * Real.exp (-y) ≤ 8 ∧
      r ^ 2 * Real.exp (-y) ≤ 32 * Real.exp (-(r / 4)) := by
  have he : Real.exp (-y) ≤ Real.exp (-(r / 2)) := Real.exp_le_exp.mpr (neg_le_neg hy)
  have hlin : r ≤ 2 * Real.exp (r / 2) := by
    have hh := Real.add_one_le_exp (r / 2)
    linarith only [hh]
  have hsq : r ^ 2 ≤ 8 * Real.exp (r / 2) := by
    have hh := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ r / 2)
    nlinarith only [hh, hr]
  have hquarter : r ^ 2 ≤ 32 * Real.exp (r / 4) := by
    have hh := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ r / 4)
    nlinarith only [hh, hr]
  have hcancel : Real.exp (r / 2) * Real.exp (-(r / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hhalve : Real.exp (r / 4) * Real.exp (-(r / 2)) = Real.exp (-(r / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · calc
      _ ≤ (2 * Real.exp (r / 2)) * Real.exp (-(r / 2)) :=
        mul_le_mul hlin he (Real.exp_pos _).le (by positivity)
      _ = 2 := by rw [mul_assoc, hcancel, mul_one]
  constructor
  · calc
      _ ≤ (8 * Real.exp (r / 2)) * Real.exp (-(r / 2)) :=
        mul_le_mul hsq he (Real.exp_pos _).le (by positivity)
      _ = 8 := by rw [mul_assoc, hcancel, mul_one]
  · calc
      _ ≤ (32 * Real.exp (r / 4)) * Real.exp (-(r / 2)) :=
        mul_le_mul hquarter he (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [mul_assoc, hhalve]

private theorem moment_nonstationary_cost_le {r y t M K : ℝ}
    (hr : 0 ≤ r) (hy : r / 2 ≤ y) (ht : 0 < t) (htM : t ≤ M) (hK : 0 ≤ K) :
    Real.exp (-2 * y) * (r ^ 2 / M + K * r / t) ≤
      (8 + 2 * K) * Real.exp (-y) / t := by
  obtain ⟨hlin, hsq, _⟩ := moment_gaussian_absorption hr hy
  have hM : 0 < M := ht.trans_le htM
  have hfirst : (r ^ 2 * Real.exp (-y)) / M ≤ 8 / t := by
    calc
      _ ≤ 8 / M := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) ht htM
  have hsecond : K * ((r * Real.exp (-y)) / t) ≤ K * (2 / t) := by gcongr
  have hh := _root_.add_le_add hfirst hsecond
  have he : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = Real.exp (-y) * ((r ^ 2 * Real.exp (-y)) / M + K * ((r * Real.exp (-y)) / t)) := by
      rw [he]; ring
    _ ≤ Real.exp (-y) * (8 / t + K * (2 / t)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by ring

private theorem moment_tail_cost_le {r y t : ℝ} (hr : 0 ≤ r)
    (hy : r / 2 ≤ y) (ht : 0 < t) (hfar : 4 * Real.log t ≤ r) :
    Real.exp (-2 * y) * r ^ 2 ≤ 32 * Real.exp (-y) / t := by
  have hquarter : Real.exp (-(r / 4)) ≤ 1 / t := by
    calc
      _ ≤ Real.exp (-Real.log t) := Real.exp_le_exp.mpr (by linarith only [hfar])
      _ = _ := by rw [Real.exp_neg, Real.exp_log ht, one_div]
  have hh := (moment_gaussian_absorption hr hy).2.2.trans
    (mul_le_mul_of_nonneg_left hquarter (by norm_num))
  have he : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = Real.exp (-y) * (r ^ 2 * Real.exp (-y)) := by rw [he]; ring
    _ ≤ Real.exp (-y) * (32 * (1 / t)) := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by ring

/-- Logarithmic-height cutoffs give a uniform inverse-height saving on
all rectangles, retaining half the Gaussian damping in squared norm. -/
theorem exists_gaussianVaughan_moment_all_scale_harmonic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
            (1 + Real.log (2 * (M : ℝ))) *
              Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) / t) := by
  obtain ⟨C₁, hC₁, hnear⟩ := exists_gaussianVaughan_moment_dyadic_envelope_bound
  obtain ⟨C₂, hC₂, hfar⟩ := exists_gaussianVaughan_moment_trivial_envelope_bound
  refine ⟨(C₁ + C₂) * (32 + 4 * Real.pi), by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hξ ht1 hlower hupper hA hB hD hM hU hV
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hα : 0 ≤ α := (by positivity : 0 < ξ / (2 * t)).le.trans hlower
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * M by omega))
  let r := ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t
  let y := α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2
  let L := 1 + Real.log (2 * (M : ℝ))
  let W := ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
    Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hlogM]
  have hH0 := invSum_nonneg (2 * M)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hy : r / 2 ≤ y := by
    have hh := mul_le_mul_of_nonneg_right hlower (by positivity : 0 ≤ (D : ℝ) ^ 2 * (M : ℝ) ^ 2)
    dsimp only [r, y]
    calc
      ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t / 2 =
          (ξ / (2 * t)) * ((D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by ring
      _ ≤ α * ((D : ℝ) ^ 2 * (M : ℝ) ^ 2) := hh
      _ = _ := by ring
  have he : Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) = Real.exp (-2 * y) := by
    congr 1
    dsimp only [y]
    ring
  suffices hresult : ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      (C₁ + C₂) * W * ((32 + 4 * Real.pi) * L * Real.exp (-y) / t) by
    rw [show Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) = Real.exp (-y) by
      congr 1
      dsimp only [y]
      ring]
    change ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      ((C₁ + C₂) * (32 + 4 * Real.pi)) * (W * L * Real.exp (-y) / t)
    exact hresult.trans_eq (by ring)
  by_cases hcut : 2 * D ≤ U ∨ 2 * M ≤ V
  · rw [gaussianVaughanMomentDyadicSum_eq_zero_of_cutoff σ α ξ t A B D M U V hM hcut,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  have hUD : (U : ℝ) < 2 * D := by exact_mod_cast (show U < 2 * D by omega)
  have hVM : (V : ℝ) < 2 * M := by exact_mod_cast (show V < 2 * M by omega)
  have htM : t ≤ M := by linarith only [hV, hVM]
  by_cases hsmall : r ≤ 4 * Real.log t
  · have hscale : ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (4 * Real.log t) * t :=
      (div_le_iff₀ ht).mp hsmall
    have hθD : 16 * (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) ≤ Real.pi * D := by
      have hh := mul_lt_mul_of_pos_left hUD Real.pi_pos
      nlinarith only [hscale, hU, hh]
    have hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi := by
      have hh : 16 * ξ * D * (M : ℝ) ^ 2 =
          (16 * (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) / D := by field_simp [hD0.ne']
      rw [hh]
      exact (div_le_iff₀ hD0).mpr hθD
    have hb := hnear σ α ξ t A B D M U V hσ hα hupper hξ ht hA hB hD hM hband
    rw [he] at hb
    change ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      C₁ * (W * Real.exp (-2 * y) * (r ^ 2 *
        (1 / (M : ℝ) + 2 * Real.pi * L / (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)))) at hb
    have hrow : r ^ 2 * (1 / (M : ℝ) + 2 * Real.pi * L /
        (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) = r ^ 2 / M + (2 * Real.pi * L) * r / t := by
      dsimp only [r]
      field_simp [hξ.ne', hD0.ne', hM0.ne', ht.ne']
    rw [hrow] at hb
    have hc := moment_nonstationary_cost_le hr.le hy ht htM (by positivity : 0 ≤ 2 * Real.pi * L)
    have hnum : 8 + 2 * (2 * Real.pi * L) ≤ (32 + 4 * Real.pi) * L := by
      nlinarith only [hL]
    have hc' : Real.exp (-2 * y) * (r ^ 2 / M + (2 * Real.pi * L) * r / t) ≤
        (32 + 4 * Real.pi) * L * Real.exp (-y) / t := hc.trans (by gcongr)
    calc
      _ ≤ C₁ * W * (Real.exp (-2 * y) * (r ^ 2 / M + (2 * Real.pi * L) * r / t)) :=
        hb.trans_eq (by ring)
      _ ≤ C₁ * W * ((32 + 4 * Real.pi) * L * Real.exp (-y) / t) :=
        mul_le_mul_of_nonneg_left hc' (mul_nonneg hC₁.le hW)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hC₂] : C₁ ≤ C₁ + C₂) hW) (by positivity)
  · have hb := hfar σ α ξ t A B D M U V hσ hα hupper hξ ht hA hB hD hM
    rw [he] at hb
    change ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      C₂ * (W * Real.exp (-2 * y) * r ^ 2) at hb
    have hc := moment_tail_cost_le hr.le hy ht (lt_of_not_ge hsmall).le
    have hnum : (32 : ℝ) ≤ (32 + 4 * Real.pi) * L := by
      have hh := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 32 + 4 * Real.pi)
      nlinarith only [hh, Real.pi_pos]
    have hc' : Real.exp (-2 * y) * r ^ 2 ≤
        (32 + 4 * Real.pi) * L * Real.exp (-y) / t := hc.trans (by gcongr)
    calc
      _ ≤ C₂ * W * (Real.exp (-2 * y) * r ^ 2) := hb.trans_eq (by ring)
      _ ≤ C₂ * W * ((32 + 4 * Real.pi) * L * Real.exp (-y) / t) :=
        mul_le_mul_of_nonneg_left hc' (mul_nonneg hC₂.le hW)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hC₁] : C₂ ≤ C₁ + C₂) hW) (by positivity)

/-- Every moment rectangle has a square-root-of-height saving with only
logarithmic arithmetic losses and a retained Gaussian envelope. -/
theorem exists_gaussianVaughan_moment_all_scale_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          (1 + Real.log (2 * (D : ℝ))) * (1 + Real.log (2 * (M : ℝ))) ^ 4 *
            Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) / t) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_all_scale_harmonic_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hξ ht hlower hupper hA hB hD hM hU hV
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hLM : 1 ≤ 1 + Real.log (2 * (M : ℝ)) := by linarith only [hlogM]
  have hH0 := invSum_nonneg (2 * M)
  have hHle : invSum (2 * M) ≤ 1 + Real.log (2 * (M : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using invSum_le_one_add_log (N := 2 * M) (by omega)
  have hHpow := pow_le_pow_left₀ hH0 hHle 3
  have hLpow : 1 ≤ (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hLM 3
  have hH : 1 + invSum (2 * M) ^ 3 ≤ 2 * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
    linarith only [hHpow, hLpow]
  have hp : Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) ≤
      (1 + Real.log (2 * (D : ℝ))) * (2 * (1 + Real.log (2 * (M : ℝ))) ^ 3) := by
    apply mul_le_mul (by linarith only) hH <;> positivity
  have hw := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 + Real.log (2 * (M : ℝ)))
  have hh := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ C * ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
      Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) / t)
  refine (hb σ α ξ t A B D M U V hσ hξ ht hlower hupper hA hB hD hM hU hV).trans ?_
  convert hh using 1 <;> ring

/-- The boundary-angle damping supplies the Gaussian lower bound uniformly
in every positive radius, including every geometric filter sample. -/
theorem eventually_boundaryDamping_lower_sector :
    ∀ᶠ t : ℝ in atTop, ∀ y : ℝ, 0 < y →
      -(complexGaussianDamping y (boundaryDampingAngle t)).im / (2 * t) ≤
        (complexGaussianDamping y (boundaryDampingAngle t)).re := by
  have hs : Tendsto (fun t : ℝ => Real.sinc (1 / t)) atTop (𝓝 1) := by
    simpa [Function.comp_def, one_div] using
      (Real.continuous_sinc.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  filter_upwards [hs.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with t ht_sinc ht
  intro y hy
  have hi : 0 < 1 / t := by positivity
  have hsin : (1 / 2 : ℝ) * (1 / t) ≤ Real.sin (1 / t) := by
    rw [Real.sinc_of_ne_zero hi.ne'] at ht_sinc
    exact (le_div_iff₀ hi).mp ht_sinc.le
  have him : -(complexGaussianDamping y (boundaryDampingAngle t)).im =
      y * Real.cos (1 / t) := by
    calc
      _ = -(y * Real.sin (boundaryDampingAngle t)) := by
        simp [complexGaussianDamping_eq hy, Complex.exp_im]
      _ = _ := by
        rw [show boundaryDampingAngle t = -(Real.pi / 2 - 1 / t) by
          dsimp only [boundaryDampingAngle]; ring,
          Real.sin_neg, Real.sin_pi_div_two_sub]
        ring
  rw [him, complexGaussianDamping_boundary_re hy]
  have hcos := Real.cos_le_one (1 / t)
  calc
    _ ≤ y / (2 * t) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcos hy.le
    _ = y * ((1 / 2 : ℝ) * (1 / t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsin hy.le

/-- The actual convolution moment is the sum of its masked dyadic rectangles. -/
theorem gaussianVaughanMomentBlock_eq_sum_dyadic
    (σ α ξ t : ℝ) {A B K : ℕ} (hA : 1 ≤ A) (hB : B ≤ 2 ^ K) (U V : ℕ) :
    (((α : ℂ) - ξ * I) / t) *
      (∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
        gaussianPrimeWeight (σ - 2) α ξ t n) =
      ∑ j ∈ range K, ∑ k ∈ range K,
        gaussianVaughanMomentDyadicSum σ α ξ t A B (2 ^ j) (2 ^ k) U V := by
  classical
  have hI : ∀ n ∈ Ico A B, 1 ≤ n ∧ n ≤ 2 ^ K - 1 := by
    intro n hn
    have hn' := mem_Ico.mp hn
    constructor <;> omega
  have hinterval : Icc 1 (2 ^ K - 1) = Ico 1 (2 ^ K) := by
    ext n
    have hpow := Nat.one_le_two_pow (n := K)
    simp only [mem_Icc, mem_Ico]
    omega
  have he : (∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      gaussianPrimeWeight (σ - 2) α ξ t n) =
      ∑ d ∈ Ico 1 (2 ^ K), ∑ m ∈ Ico 1 (2 ^ K),
        if d * m ∈ Ico A B then
          ((typeIILong U d : ℝ) : ℂ) * ((typeIIShort V m : ℝ) : ℂ) *
            gaussianPrimeWeight (σ - 2) α ξ t (d * m) else 0 := by
    simp_rw [coe_mul_apply]
    rw [sum_conv_mul_eq hI (fun d => ((typeIILong U d : ℝ) : ℂ))
      (fun m => ((typeIIShort V m : ℝ) : ℂ))
      (gaussianPrimeWeight (σ - 2) α ξ t), sum_filter, sum_product, hinterval]
  rw [he]
  have hd := sum_Ico_dyadic 1 (fun d => ∑ m ∈ Ico 1 (2 ^ K),
    if d * m ∈ Ico A B then
      ((typeIILong U d : ℝ) : ℂ) * ((typeIIShort V m : ℝ) : ℂ) *
        gaussianPrimeWeight (σ - 2) α ξ t (d * m) else 0) K
  simp only [one_mul, pow_succ, Nat.mul_comm _ 2] at hd
  rw [hd, mul_sum]
  apply sum_congr rfl
  intro j _
  have hm (d : ℕ) := sum_Ico_dyadic 1 (fun m =>
    if d * m ∈ Ico A B then
      ((typeIILong U d : ℝ) : ℂ) * ((typeIIShort V m : ℝ) : ℂ) *
        gaussianPrimeWeight (σ - 2) α ξ t (d * m) else 0) K
  simp only [one_mul, pow_succ, Nat.mul_comm _ 2] at hm
  simp_rw [hm]
  rw [sum_comm, mul_sum]
  rfl

/-- The arithmetic and Gaussian energy retained after extracting the height saving. -/
def gaussianMomentRectangleEnergy (σ α : ℝ) (D M : ℕ) : ℝ :=
  ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
    (1 + Real.log (2 * (D : ℝ))) * (1 + Real.log (2 * (M : ℝ))) ^ 4 *
      Real.exp (-α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)

/-- The complete finite type-II convolution inherits the all-scale saving;
its dyadic majorant retains Gaussian decay at every product scale. -/
theorem exists_gaussianVaughan_moment_typeII_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B K U V : ℕ),
      0 ≤ σ → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      1 ≤ A → 1 ≤ B → B ≤ 2 ^ K →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖(((α : ℂ) - ξ * I) / t) *
        (∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
          gaussianPrimeWeight (σ - 2) α ξ t n)‖ ≤
        Real.sqrt (C / t) * ∑ j ∈ range K, ∑ k ∈ range K,
          Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k)) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_all_scale_bound
  refine ⟨C, hC, ?_⟩
  intro σ α ξ t A B K U V hσ hξ ht hlower hupper hA hB hBK hU hV
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hblock (j k : ℕ) :
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B (2 ^ j) (2 ^ k) U V‖ ≤
        Real.sqrt (C / t) * Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k)) := by
    have hh := hb σ α ξ t A B (2 ^ j) (2 ^ k) U V hσ hξ ht hlower hupper hA hB
      Nat.one_le_two_pow Nat.one_le_two_pow hU hV
    change ‖gaussianVaughanMomentDyadicSum σ α ξ t A B (2 ^ j) (2 ^ k) U V‖ ^ 2 ≤
      C * (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k) / t) at hh
    have hh' : ‖gaussianVaughanMomentDyadicSum σ α ξ t A B (2 ^ j) (2 ^ k) U V‖ ^ 2 ≤
        (C / t) * gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k) :=
      hh.trans_eq (by ring)
    have hn := (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hh')).mpr hh'
    rwa [Real.sqrt_mul (div_nonneg hC.le ht0.le)] at hn
  rw [gaussianVaughanMomentBlock_eq_sum_dyadic σ α ξ t hA hBK U V]
  calc
    _ ≤ ∑ j ∈ range K, ‖∑ k ∈ range K,
        gaussianVaughanMomentDyadicSum σ α ξ t A B (2 ^ j) (2 ^ k) U V‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range K, ∑ k ∈ range K,
        Real.sqrt (C / t) * Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k)) := by
      apply sum_le_sum
      intro j _
      exact (norm_sum_le _ _).trans (sum_le_sum fun k _ => hblock j k)
    _ = _ := by simp_rw [← mul_sum]

#print axioms gaussianVaughanMomentBlock_eq_sum_dyadic
#print axioms exists_gaussianVaughan_moment_typeII_block_bound
#print axioms exists_gaussianVaughan_moment_all_scale_bound
#print axioms eventually_boundaryDamping_lower_sector

#print axioms exists_gaussianVaughan_moment_all_scale_harmonic_bound

#print axioms norm_maskedGaussian_dyadic_trivial_sq_le
#print axioms exists_gaussianVaughan_moment_trivial_envelope_bound

end GaloisForLFunctions.ExceptionalLayerTheory
