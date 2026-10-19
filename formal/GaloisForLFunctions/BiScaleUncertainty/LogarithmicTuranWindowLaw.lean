import GaloisForLFunctions.BiScaleUncertainty.DisjointCollarCliqueDivergenceAndTuransProblem
import GaloisForLFunctions.RHTower.WeilWorkPBAPSpectralMeasure
import GaloisForLFunctions.RHTower.WeilLagFejerBlockExcursionRigidity
import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity

/-!
# Logarithmic, not square-root, cancellation in the Beurling–Turán window

If the correlation `h = autocorr f` vanishes on the arithmetic progression `mδ`, `1 ≤ m ≤ M`,
the clique sphere argument of `DisjointCollarCliqueDivergenceAndTuransProblem` gives
`∫_0^{(M+1)δ} h ≤ δ √(M+1) h(0)`. The true growth is logarithmic:

`|∫_0^{(M+1)δ} h| ≤ 12 δ (4 + log(M+1)) h(0)`.

**Mechanism.** Write `h(y) = ∫ ρ(ξ) cos(2πξy) dξ` with the spectral density `ρ = |f̂|²`.
The zeros make every Dirichlet energy `D_K(s) = |Σ_{k<K} e^{iks}|²`, `K = M + 1`, have
`∫ ρ(ξ) D_K(θ - 2πδξ) dξ = K h(0)` for every phase `θ`: only the diagonal of the double sum
survives. Since `D_K ≥ K²/4` within `1/K` of `2πℤ`, this caps the spectral mass of every
arc of length `≍ 1/(Kδ)` by `O(h(0)/K)`. The window kernel `∫_0^{Kδ} cos(2πξx) dx` is at most
`min(Kδ, 1/(2π|ξ|))`; covering the frequency circle by `O(K)` arcs with weights `K/max(1,n)`
sums these caps to a harmonic sum, hence a logarithm.
-/

open MeasureTheory Set Filter Topology Complex
open Zeta23
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {f : ℝ → ℝ}

/-! ### 1. The spectral density of a real source -/

/-- A real compact `C²` source, viewed as a corpus Weil test. -/
def realWeilTest (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    RHTower.WeilOneSided.WeilTestFn :=
  ⟨fun u => (f u : ℂ), Complex.ofRealCLM.contDiff.comp hf, hfc.comp_left Complex.ofReal_zero⟩

/-- The spectral density `|f̂|²` of a real compact `C²` source. -/
def sourceSpectralDensity (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ξ : ℝ) : ℝ :=
  RHTower.WeilWorkPBAP.testSpectralDensity (realWeilTest f hf hfc) ξ

theorem sourceSpectralDensity_nonneg (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ξ : ℝ) :
    0 ≤ sourceSpectralDensity f hf hfc ξ :=
  RHTower.WeilWorkPBAP.testSpectralDensity_nonneg _ ξ

theorem integrable_sourceSpectralDensity (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (sourceSpectralDensity f hf hfc) :=
  RHTower.WeilWorkPBAP.integrable_testSpectralDensity _

/-- The spectral density integrates against every continuous bounded weight. -/
theorem integrable_spectral_mul (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {b : ℝ → ℝ} (hb : Continuous b) {C : ℝ} (hC : ∀ ξ, |b ξ| ≤ C) :
    Integrable (fun ξ => sourceSpectralDensity f hf hfc ξ * b ξ) := by
  have h := (integrable_sourceSpectralDensity hf hfc).bdd_mul (c := C) hb.aestronglyMeasurable
    (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs]; exact hC ξ)
  exact h.congr (ae_of_all _ fun ξ => mul_comm _ _)

private theorem integrable_spectral_phase (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (y : ℝ) :
    Integrable (fun ξ : ℝ =>
      (sourceSpectralDensity f hf hfc ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y)) := by
  refine (integrable_sourceSpectralDensity hf hfc).ofReal.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp
      (RHTower.WeilWorkPBAP.continuous_testSpectralDensity _)).mul
        (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      simp [Complex.norm_exp, abs_of_nonneg (sourceSpectralDensity_nonneg hf hfc ξ)]

private theorem spectral_phase_eq (ρ ξ y : ℝ) :
    (ρ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y) =
      (ρ : ℂ) * Complex.exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * I) := by
  congr 2
  push_cast
  ring

/-- **Spectral form of the correlation.** `h(y) = ∫ ρ(ξ) cos(2πξy) dξ`. -/
theorem autocorr_eq_integral_spectral_cos (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (y : ℝ) :
    autocorr f y = ∫ ξ, sourceSpectralDensity f hf hfc ξ * Real.cos (2 * Real.pi * ξ * y) := by
  have h1 := RHTower.WeilWorkPBAP.weilTest_eq_integral_testSpectralDensity
    (realWeilTest f hf hfc) y
  have h2 := RHTower.AutocorrelationKrein.weilTest_eq f y
  change EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y = _ at h1
  rw [h2] at h1
  have hre := congrArg Complex.re h1
  rw [Complex.ofReal_re] at hre
  have hi : (∫ ξ, ((sourceSpectralDensity f hf hfc ξ : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * I * ξ * y)).re = ∫ ξ, (((sourceSpectralDensity f hf hfc ξ : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * I * ξ * y)).re :=
    (integral_re (integrable_spectral_phase hf hfc y)).symm
  rw [hre]
  refine hi.trans (integral_congr_ae (ae_of_all _ fun ξ => ?_))
  change (((RHTower.WeilWorkPBAP.testSpectralDensity (realWeilTest f hf hfc) ξ : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * I * ξ * y)).re = _
  rw [spectral_phase_eq, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rfl

/-- The odd spectral moments vanish: `∫ ρ(ξ) sin(2πξy) dξ = 0`. -/
theorem integral_spectral_sin_eq_zero (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (y : ℝ) :
    ∫ ξ, sourceSpectralDensity f hf hfc ξ * Real.sin (2 * Real.pi * ξ * y) = 0 := by
  have h1 := RHTower.WeilWorkPBAP.weilTest_eq_integral_testSpectralDensity
    (realWeilTest f hf hfc) y
  have h2 := RHTower.AutocorrelationKrein.weilTest_eq f y
  change EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y = _ at h1
  rw [h2] at h1
  have him := congrArg Complex.im h1
  rw [Complex.ofReal_im] at him
  have hi : (∫ ξ, ((sourceSpectralDensity f hf hfc ξ : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * I * ξ * y)).im = ∫ ξ, (((sourceSpectralDensity f hf hfc ξ : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * I * ξ * y)).im :=
    (integral_im (integrable_spectral_phase hf hfc y)).symm
  refine Eq.trans ?_ (hi.symm.trans him.symm)
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  change _ = (((RHTower.WeilWorkPBAP.testSpectralDensity (realWeilTest f hf hfc) ξ : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * I * ξ * y)).im
  rw [spectral_phase_eq, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  rfl

/-! ### 2. Dirichlet energies -/

/-- The Dirichlet energy `|Σ_{k<K} e^{iks}|²` in real form. -/
def dirichletEnergy (K : ℕ) (s : ℝ) : ℝ :=
  (∑ k ∈ Finset.range K, Real.cos (k * s)) ^ 2 + (∑ k ∈ Finset.range K, Real.sin (k * s)) ^ 2

theorem dirichletEnergy_eq_sum (K : ℕ) (s : ℝ) :
    dirichletEnergy K s = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
      Real.cos (((j : ℝ) - k) * s) := by
  unfold dirichletEnergy
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((j : ℝ) - k) * s = j * s - k * s by ring, Real.cos_sub]

theorem dirichletEnergy_nonneg (K : ℕ) (s : ℝ) : 0 ≤ dirichletEnergy K s := by
  unfold dirichletEnergy; positivity

theorem continuous_dirichletEnergy (K : ℕ) : Continuous (dirichletEnergy K) := by
  unfold dirichletEnergy
  fun_prop

theorem dirichletEnergy_le (K : ℕ) (s : ℝ) : dirichletEnergy K s ≤ 2 * (K : ℝ) ^ 2 := by
  have hc : |∑ k ∈ Finset.range K, Real.cos (k * s)| ≤ K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_cos_le_one _
      _ = K := by simp
  have hs : |∑ k ∈ Finset.range K, Real.sin (k * s)| ≤ K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_sin_le_one _
      _ = K := by simp
  unfold dirichletEnergy
  nlinarith [sq_abs (∑ k ∈ Finset.range K, Real.cos (k * s)),
    sq_abs (∑ k ∈ Finset.range K, Real.sin (k * s)), abs_nonneg (∑ k ∈ Finset.range K,
      Real.cos (k * s)), abs_nonneg (∑ k ∈ Finset.range K, Real.sin (k * s))]

/-- Within `1/K` of `2πℤ` the Dirichlet energy is at least `K²/4`. -/
theorem dirichletEnergy_ge {K : ℕ} {s : ℝ} {n : ℤ} (hs : |s - 2 * Real.pi * n| ≤ 1 / K) :
    ((K : ℝ) / 2) ^ 2 ≤ dirichletEnergy K s := by
  have hre := RHTower.SubexpExcursion.re_dirSum_ge (K := K) hs
  have hsum : (RHTower.AlmostEverySpacing.dirSum K s).re =
      ∑ k ∈ Finset.range K, Real.cos (k * s) := by
    unfold RHTower.AlmostEverySpacing.dirSum
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  rw [hsum] at hre
  have hK : (0 : ℝ) ≤ (K : ℝ) / 2 := by positivity
  unfold dirichletEnergy
  nlinarith [sq_nonneg (∑ k ∈ Finset.range K, Real.sin (k * s))]

/-! ### 3. Arithmetic zeros flatten the spectral Dirichlet energies -/

private theorem autocorr_progression_offdiag_eq_zero {δ : ℝ} {M : ℕ}
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) {j k : ℕ}
    (hj : j < M + 1) (hk : k < M + 1) (hjk : j ≠ k) :
    autocorr f (((j : ℝ) - k) * δ) = 0 := by
  rcases lt_or_gt_of_ne hjk with h | h
  · have hcast : ((j : ℝ) - k) * δ = -(((k - j : ℕ) : ℝ) * δ) := by
      rw [Nat.cast_sub h.le]; ring
    rw [hcast, autocorr_neg]
    exact hzeros _ (by omega) (by omega)
  · have hcast : ((j : ℝ) - k) * δ = ((j - k : ℕ) : ℝ) * δ := by
      rw [Nat.cast_sub h.le]
    rw [hcast]
    exact hzeros _ (by omega) (by omega)

/-- **Flat spectral Dirichlet energy.** If `h` vanishes at `mδ` for `1 ≤ m ≤ M`, then for every
phase `θ`, `∫ ρ(ξ) D_{M+1}(θ - 2πδξ) dξ = (M + 1) h(0)`. -/
theorem integral_spectral_dirichletEnergy (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {δ : ℝ} {M : ℕ} (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0)
    (θ : ℝ) :
    ∫ ξ, sourceSpectralDensity f hf hfc ξ * dirichletEnergy (M + 1) (θ - 2 * Real.pi * δ * ξ) =
      ((M + 1 : ℕ) : ℝ) * autocorr f 0 := by
  set ρ := sourceSpectralDensity f hf hfc with hρ
  have hint : ∀ j k : ℕ, Integrable (fun ξ => ρ ξ *
      Real.cos (((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ))) := fun j k =>
    integrable_spectral_mul hf hfc (by fun_prop) (fun ξ => Real.abs_cos_le_one _)
  have hterm : ∀ j k : ℕ, (∫ ξ, ρ ξ * Real.cos (((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ))) =
      Real.cos (((j : ℝ) - k) * θ) * autocorr f (((j : ℝ) - k) * δ) := by
    intro j k
    have hsplit : (fun ξ => ρ ξ * Real.cos (((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ))) =
        fun ξ => Real.cos (((j : ℝ) - k) * θ) *
            (ρ ξ * Real.cos (2 * Real.pi * ξ * (((j : ℝ) - k) * δ))) +
          Real.sin (((j : ℝ) - k) * θ) *
            (ρ ξ * Real.sin (2 * Real.pi * ξ * (((j : ℝ) - k) * δ))) := by
      funext ξ
      rw [show ((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ) =
        ((j : ℝ) - k) * θ - 2 * Real.pi * ξ * (((j : ℝ) - k) * δ) by ring, Real.cos_sub]
      ring
    rw [hsplit, integral_add, integral_const_mul, integral_const_mul,
      ← autocorr_eq_integral_spectral_cos hf hfc, integral_spectral_sin_eq_zero hf hfc,
      mul_zero, add_zero]
    · exact (integrable_spectral_mul hf hfc (by fun_prop)
        (fun ξ => Real.abs_cos_le_one _)).const_mul _
    · exact (integrable_spectral_mul hf hfc (by fun_prop)
        (fun ξ => Real.abs_sin_le_one _)).const_mul _
  have hexpand : (fun ξ => ρ ξ * dirichletEnergy (M + 1) (θ - 2 * Real.pi * δ * ξ)) =
      fun ξ => ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        ρ ξ * Real.cos (((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ)) := by
    funext ξ
    rw [dirichletEnergy_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  rw [hexpand, integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hint j k)]
  have hrow : ∀ j ∈ Finset.range (M + 1), (∫ ξ, ∑ k ∈ Finset.range (M + 1),
      ρ ξ * Real.cos (((j : ℝ) - k) * (θ - 2 * Real.pi * δ * ξ))) = autocorr f 0 := by
    intro j hj
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    simp only [hterm]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      rw [autocorr_progression_offdiag_eq_zero hzeros (Finset.mem_range.mp hj)
        (Finset.mem_range.mp hk) (Ne.symm hkj), mul_zero]
    · intro hj'; exact absurd hj hj'
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### 4. The window as a spectral integral -/

/-- The cosine window `∫_0^T cos(2πξx) dx` is at most `T / max 1 (2πT|ξ|)`. -/
theorem abs_cosWindow_le {T : ℝ} (hT : 0 ≤ T) (ξ : ℝ) :
    |∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x)| ≤
      T / max 1 (2 * Real.pi * T * |ξ|) := by
  have htriv : |∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x)| ≤ T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
      (f := fun x => Real.cos (2 * Real.pi * ξ * x)) (fun x _ => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT, one_mul] at this
    exact this
  rcases le_or_gt (2 * Real.pi * T * |ξ|) 1 with h | h
  · rw [max_eq_left h, div_one]; exact htriv
  · rw [max_eq_right h.le]
    have hξ : ξ ≠ 0 := by
      intro h0; rw [h0, abs_zero, mul_zero] at h; linarith
    have hc : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
    have heval : (∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x)) =
        Real.sin (2 * Real.pi * ξ * T) / (2 * Real.pi * ξ) := by
      rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos,
        mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
      field_simp
    have hT0 : 0 < T := by
      by_contra hT0
      have : T = 0 := le_antisymm (not_lt.mp hT0) hT
      rw [this] at h; simp at h; linarith
    rw [heval, abs_div, div_le_div_iff₀ (abs_pos.mpr hc) (by positivity)]
    have habs : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [habs]
    have hs := Real.abs_sin_le_one (2 * Real.pi * ξ * T)
    have : 0 ≤ 2 * Real.pi * T * |ξ| := by positivity
    nlinarith [abs_nonneg ξ, Real.pi_pos]

/-- **Window as a spectral integral.** `∫_0^T h = ∫ ρ(ξ) (∫_0^T cos(2πξx) dx) dξ`. -/
theorem integral_window_eq_spectral (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ) :
    ∫ x in (0 : ℝ)..T, autocorr f x =
      ∫ ξ, sourceSpectralDensity f hf hfc ξ * ∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x) := by
  set ρ := sourceSpectralDensity f hf hfc with hρ
  set F : ℝ → ℝ → ℝ := fun x ξ => ρ ξ * Real.cos (2 * Real.pi * ξ * x) with hF
  have hρc : Continuous ρ := RHTower.WeilWorkPBAP.continuous_testSpectralDensity _
  have hprod : Integrable (Function.uncurry F) ((volume.restrict (Set.uIoc 0 T)).prod volume) := by
    refine (Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := ρ)
      continuous_const.integrableOn_uIoc (integrable_sourceSpectralDensity hf hfc)).mono' ?_ ?_
    · exact ((hρc.comp continuous_snd).mul (by fun_prop)).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rcases p with ⟨x, ξ⟩
      simp only [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_mul, one_mul]
      rw [abs_of_nonneg (sourceSpectralDensity_nonneg hf hfc ξ)]
      exact mul_le_of_le_one_right (sourceSpectralDensity_nonneg hf hfc ξ)
        (Real.abs_cos_le_one _)
  have hleft : (∫ x in (0 : ℝ)..T, autocorr f x) = ∫ x in (0 : ℝ)..T, ∫ ξ, F x ξ := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF]
    rw [autocorr_eq_integral_spectral_cos hf hfc x]
  rw [hleft, MeasureTheory.intervalIntegral_integral_swap hprod]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [hF]
  rw [intervalIntegral.integral_const_mul]

/-! ### 5. Covering the frequency circle by Dirichlet energies -/

/-- The window weight `K / max 1 (K|s|)`. -/
def turanWeight (K : ℕ) (s : ℝ) : ℝ := K / max 1 (K * |s|)

/-- `|x - round x| ≤ |x|`. -/
private theorem abs_sub_round_le_abs (x : ℝ) : |x - round x| ≤ |x| := by
  rcases lt_or_ge |x| (1 / 2) with h | h
  · have hr : round x = 0 := by
      rw [round_eq, Int.floor_eq_zero_iff]
      constructor <;> linarith [abs_lt.mp h]
    rw [hr, Int.cast_zero, sub_zero]
  · exact (abs_sub_round x).trans h

/-- **Covering inequality.** With `L = ⌈Kπ⌉ + 1`, every frequency has
`turanWeight K s ≤ (6/K²) Σ_{n ≤ L} (K/max 1 n) (D_K(n/K - s) + D_K(-n/K - s))`. -/
theorem turanWeight_le_sum {K : ℕ} (hK : 0 < K) (s : ℝ) :
    turanWeight K s ≤ 6 / (K : ℝ) ^ 2 * ∑ n ∈ Finset.range (⌈(K : ℝ) * Real.pi⌉₊ + 1 + 1),
      (K : ℝ) / max 1 (n : ℝ) *
        (dirichletEnergy K ((n : ℝ) / K - s) + dirichletEnergy K (-((n : ℝ) / K) - s)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set n₀ : ℤ := round (s / (2 * Real.pi)) with hn₀
  set s' : ℝ := s - 2 * Real.pi * n₀ with hs'
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hs'eq : s' = 2 * Real.pi * (s / (2 * Real.pi) - n₀) := by
    rw [hs']; field_simp
  have hs'abs : |s'| ≤ Real.pi := by
    rw [hs'eq, abs_mul, abs_of_pos h2pi]
    have := abs_sub_round (s / (2 * Real.pi))
    rw [← hn₀] at this
    nlinarith
  have hs'le : |s'| ≤ |s| := by
    rw [hs'eq, abs_mul, abs_of_pos h2pi]
    have h1 := abs_sub_round_le_abs (s / (2 * Real.pi))
    rw [← hn₀, abs_div, abs_of_pos h2pi] at h1
    calc
      _ ≤ 2 * Real.pi * (|s| / (2 * Real.pi)) := mul_le_mul_of_nonneg_left h1 h2pi.le
      _ = |s| := by field_simp
  set l : ℤ := round ((K : ℝ) * s') with hl
  have hlr : |(K : ℝ) * s' - l| ≤ 1 / 2 := abs_sub_round _
  have hlabs : |(l : ℝ)| ≤ (K : ℝ) * Real.pi + 1 / 2 := by
    have : |(K : ℝ) * s'| ≤ (K : ℝ) * Real.pi := by
      rw [abs_mul, abs_of_pos hKpos]; exact mul_le_mul_of_nonneg_left hs'abs hKpos.le
    have h1 := abs_sub_abs_le_abs_sub (l : ℝ) ((K : ℝ) * s')
    have h2 : |(l : ℝ) - (K : ℝ) * s'| = |(K : ℝ) * s' - l| := abs_sub_comm _ _
    linarith
  -- the selected Dirichlet energy is large
  have hθ : |((l : ℝ) / K - s) - 2 * Real.pi * ((-n₀ : ℤ) : ℝ)| ≤ 1 / K := by
    have he : ((l : ℝ) / K - s) - 2 * Real.pi * ((-n₀ : ℤ) : ℝ) = -(((K : ℝ) * s' - l) / K) := by
      rw [hs']; push_cast; field_simp; ring
    rw [he, abs_neg, abs_div, abs_of_pos hKpos, div_le_div_iff₀ hKpos hKpos]
    nlinarith
  have hD := dirichletEnergy_ge hθ
  -- weight comparison
  set n : ℕ := l.natAbs with hndef
  have hn_abs : (n : ℝ) = |(l : ℝ)| := by rw [hndef, Nat.cast_natAbs, Int.cast_abs]
  have hw1 : turanWeight K s ≤ turanWeight K s' := by
    unfold turanWeight
    apply div_le_div_of_nonneg_left hKpos.le (lt_of_lt_of_le one_pos (le_max_left _ _))
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left hs'le hKpos.le)
  have hw2 : turanWeight K s' ≤ 3 / 2 * ((K : ℝ) / max 1 (n : ℝ)) := by
    unfold turanWeight
    have hb : (n : ℝ) ≤ (K : ℝ) * |s'| + 1 / 2 := by
      rw [hn_abs]
      have : |(K : ℝ) * s'| = (K : ℝ) * |s'| := by rw [abs_mul, abs_of_pos hKpos]
      linarith [abs_sub_abs_le_abs_sub (l : ℝ) ((K : ℝ) * s'), abs_sub_comm (l : ℝ) ((K : ℝ) * s')]
    have hmax : max 1 (n : ℝ) ≤ 3 / 2 * max 1 ((K : ℝ) * |s'|) := by
      rcases le_or_gt 1 ((K : ℝ) * |s'|) with ha | ha
      · rw [max_eq_right ha]
        apply max_le (by linarith) (by linarith)
      · rw [max_eq_left ha.le]
        apply max_le (by linarith) (by linarith)
    rw [div_le_iff₀ (lt_of_lt_of_le one_pos (le_max_left _ _))]
    calc
      (K : ℝ) ≤ (K : ℝ) / max 1 (n : ℝ) * max 1 (n : ℝ) := by
        rw [div_mul_cancel₀ _ (lt_of_lt_of_le one_pos (le_max_left _ _)).ne']
      _ ≤ (K : ℝ) / max 1 (n : ℝ) * (3 / 2 * max 1 ((K : ℝ) * |s'|)) :=
        mul_le_mul_of_nonneg_left hmax (div_nonneg hKpos.le (by positivity))
      _ = _ := by ring
  -- the selected term of the covering sum
  have hnmem : n ∈ Finset.range (⌈(K : ℝ) * Real.pi⌉₊ + 1 + 1) := by
    rw [Finset.mem_range]
    have h1 : (n : ℝ) < (⌈(K : ℝ) * Real.pi⌉₊ : ℝ) + 2 := by
      have := Nat.le_ceil ((K : ℝ) * Real.pi)
      linarith [hn_abs ▸ hlabs]
    exact_mod_cast h1
  have hsel : dirichletEnergy K ((l : ℝ) / K - s) ≤
      dirichletEnergy K ((n : ℝ) / K - s) + dirichletEnergy K (-((n : ℝ) / K) - s) := by
    rcases le_or_gt 0 l with hl0 | hl0
    · have : (n : ℝ) = l := by rw [hn_abs, abs_of_nonneg (by exact_mod_cast hl0)]
      rw [this]; linarith [dirichletEnergy_nonneg K (-((l : ℝ) / K) - s)]
    · have : (n : ℝ) = -l := by rw [hn_abs, abs_of_neg (by exact_mod_cast hl0)]
      rw [this, neg_div, neg_neg]; linarith [dirichletEnergy_nonneg K (-((l : ℝ) / K) - s)]
  have hwpos : 0 ≤ (K : ℝ) / max 1 (n : ℝ) := div_nonneg hKpos.le (by positivity)
  have hterm_nonneg : ∀ m ∈ Finset.range (⌈(K : ℝ) * Real.pi⌉₊ + 1 + 1), 0 ≤
      (K : ℝ) / max 1 (m : ℝ) *
        (dirichletEnergy K ((m : ℝ) / K - s) + dirichletEnergy K (-((m : ℝ) / K) - s)) :=
    fun m _ => mul_nonneg (div_nonneg hKpos.le (by positivity))
      (add_nonneg (dirichletEnergy_nonneg _ _) (dirichletEnergy_nonneg _ _))
  have hsingle := Finset.single_le_sum hterm_nonneg hnmem
  have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  calc
    turanWeight K s ≤ 3 / 2 * ((K : ℝ) / max 1 (n : ℝ)) := hw1.trans hw2
    _ ≤ 3 / 2 * ((K : ℝ) / max 1 (n : ℝ)) * (dirichletEnergy K ((l : ℝ) / K - s) /
        ((K : ℝ) / 2) ^ 2) := by
      have : 1 ≤ dirichletEnergy K ((l : ℝ) / K - s) / ((K : ℝ) / 2) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hwpos]
    _ = 6 / (K : ℝ) ^ 2 * ((K : ℝ) / max 1 (n : ℝ) * dirichletEnergy K ((l : ℝ) / K - s)) := by
      field_simp; ring
    _ ≤ 6 / (K : ℝ) ^ 2 * ((K : ℝ) / max 1 (n : ℝ) *
        (dirichletEnergy K ((n : ℝ) / K - s) + dirichletEnergy K (-((n : ℝ) / K) - s))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsel hwpos
    _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (by positivity)

/-! ### 6. The logarithmic window law -/

/-- `Σ_{n<N+1} 1/max 1 n ≤ 2 + log N`. -/
private theorem sum_inv_max_one_le (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / max 1 (n : ℝ) ≤ 2 + Real.log N := by
  rw [Finset.sum_range_succ']
  have hh := harmonic_le_one_add_log N
  have hharm : (harmonic N : ℝ) = ∑ i ∈ Finset.range N, 1 / max 1 ((i + 1 : ℕ) : ℝ) := by
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [max_eq_right (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]), one_div]
  rw [← hharm]
  simp only [Nat.cast_zero, max_eq_left (zero_le_one' ℝ), div_one]
  linarith

/-- **Logarithmic Beurling–Turán window law.** If `h(mδ) = 0` for `1 ≤ m ≤ M`, then
`|∫_0^{(M+1)δ} h| ≤ 12 δ (4 + log(M+1)) h(0)`; the clique bound `δ√(M+1) h(0)` is not sharp. -/
theorem abs_integral_autocorr_le_log_of_arithmetic_zeros (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) (M : ℕ)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) :
    |∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr f x| ≤
      12 * δ * (4 + Real.log ((M + 1 : ℕ) : ℝ)) * autocorr f 0 := by
  set K : ℕ := M + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos M
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set T : ℝ := (K : ℝ) * δ with hT
  have hT0 : 0 ≤ T := by positivity
  set ρ := sourceSpectralDensity f hf hfc with hρ
  set L : ℕ := ⌈(K : ℝ) * Real.pi⌉₊ + 1 with hL
  set S : ℝ → ℝ := fun ξ => ∑ n ∈ Finset.range (L + 1), (K : ℝ) / max 1 (n : ℝ) *
      (dirichletEnergy K ((n : ℝ) / K - 2 * Real.pi * δ * ξ) +
        dirichletEnergy K (-((n : ℝ) / K) - 2 * Real.pi * δ * ξ)) with hS
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  -- pointwise kernel bound
  have hker : ∀ ξ, |∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x)| ≤
      δ * (6 / (K : ℝ) ^ 2) * S ξ := by
    intro ξ
    refine (abs_cosWindow_le hT0 ξ).trans ?_
    have hcov := turanWeight_le_sum hK (2 * Real.pi * δ * ξ)
    have heq : T / max 1 (2 * Real.pi * T * |ξ|) = δ * turanWeight K (2 * Real.pi * δ * ξ) := by
      unfold turanWeight
      rw [hT]
      have : (K : ℝ) * |2 * Real.pi * δ * ξ| = 2 * Real.pi * ((K : ℝ) * δ) * |ξ| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * δ)]; ring
      rw [this]; ring
    rw [heq]
    calc
      _ ≤ δ * (6 / (K : ℝ) ^ 2 * ∑ n ∈ Finset.range (⌈(K : ℝ) * Real.pi⌉₊ + 1 + 1),
          (K : ℝ) / max 1 (n : ℝ) *
            (dirichletEnergy K ((n : ℝ) / K - 2 * Real.pi * δ * ξ) +
              dirichletEnergy K (-((n : ℝ) / K) - 2 * Real.pi * δ * ξ))) :=
        mul_le_mul_of_nonneg_left hcov hδ.le
      _ = δ * (6 / (K : ℝ) ^ 2) * S ξ := (mul_assoc δ (6 / (K : ℝ) ^ 2) _).symm
  -- each Dirichlet energy integrates to K h(0)
  have hDcont : ∀ θ : ℝ, Continuous fun ξ : ℝ => dirichletEnergy K (θ - 2 * Real.pi * δ * ξ) :=
    fun θ => (continuous_dirichletEnergy K).comp (by fun_prop)
  have hDint : ∀ θ : ℝ, Integrable fun ξ => ρ ξ * dirichletEnergy K (θ - 2 * Real.pi * δ * ξ) :=
    fun θ => integrable_spectral_mul hf hfc (hDcont θ) (fun ξ => by
      rw [abs_of_nonneg (dirichletEnergy_nonneg _ _)]; exact dirichletEnergy_le _ _)
  have hDval : ∀ θ : ℝ, ∫ ξ, ρ ξ * dirichletEnergy K (θ - 2 * Real.pi * δ * ξ) =
      (K : ℝ) * autocorr f 0 := fun θ => integral_spectral_dirichletEnergy hf hfc hzeros θ
  have hSint : Integrable fun ξ => ρ ξ * S ξ := by
    have : (fun ξ => ρ ξ * S ξ) = fun ξ => ∑ n ∈ Finset.range (L + 1),
        (K : ℝ) / max 1 (n : ℝ) * (ρ ξ * dirichletEnergy K ((n : ℝ) / K - 2 * Real.pi * δ * ξ) +
          ρ ξ * dirichletEnergy K (-((n : ℝ) / K) - 2 * Real.pi * δ * ξ)) := by
      funext ξ; simp only [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun n _ => ((hDint _).add (hDint _)).const_mul _
  have hSval : ∫ ξ, ρ ξ * S ξ = 2 * (K : ℝ) * autocorr f 0 *
      ∑ n ∈ Finset.range (L + 1), (K : ℝ) / max 1 (n : ℝ) := by
    have : (fun ξ => ρ ξ * S ξ) = fun ξ => ∑ n ∈ Finset.range (L + 1),
        (K : ℝ) / max 1 (n : ℝ) * (ρ ξ * dirichletEnergy K ((n : ℝ) / K - 2 * Real.pi * δ * ξ) +
          ρ ξ * dirichletEnergy K (-((n : ℝ) / K) - 2 * Real.pi * δ * ξ)) := by
      funext ξ; simp only [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    have hpair : ∀ a b : ℝ, Integrable (fun ξ => ρ ξ * dirichletEnergy K (a - 2 * Real.pi * δ * ξ) +
        ρ ξ * dirichletEnergy K (b - 2 * Real.pi * δ * ξ)) := fun a b => (hDint a).add (hDint b)
    rw [this, integral_finsetSum _ fun n _ => (hpair _ _).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_add (hDint _) (hDint _), hDval, hDval]
    ring
  -- assemble
  have hwin := integral_window_eq_spectral hf hfc T
  have hWint : Integrable fun ξ => ρ ξ * ∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x) := by
    refine (integrable_sourceSpectralDensity hf hfc).bdd_mul (c := T) ?_ ?_ |>.congr
      (ae_of_all _ fun ξ => mul_comm _ _)
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T).aestronglyMeasurable
    · exact ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs]
        refine (abs_cosWindow_le hT0 ξ).trans ?_
        exact div_le_self hT0 (le_max_left _ _)
  have hmain : |∫ x in (0 : ℝ)..T, autocorr f x| ≤ δ * (6 / (K : ℝ) ^ 2) * ∫ ξ, ρ ξ * S ξ := by
    rw [hwin]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono hWint.abs (hSint.const_mul _) fun ξ => ?_
    simp only
    rw [abs_mul, abs_of_nonneg (sourceSpectralDensity_nonneg hf hfc ξ)]
    calc
      ρ ξ * |∫ x in (0 : ℝ)..T, Real.cos (2 * Real.pi * ξ * x)| ≤
          ρ ξ * (δ * (6 / (K : ℝ) ^ 2) * S ξ) :=
        mul_le_mul_of_nonneg_left (hker ξ) (sourceSpectralDensity_nonneg hf hfc ξ)
      _ = _ := by ring
  rw [hSval] at hmain
  have hsum : ∑ n ∈ Finset.range (L + 1), (K : ℝ) / max 1 (n : ℝ) ≤ (K : ℝ) * (2 + Real.log L) := by
    have h := sum_inv_max_one_le L
    calc
      _ = (K : ℝ) * ∑ n ∈ Finset.range (L + 1), 1 / max 1 (n : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hKpos.le
  have hlogL : Real.log L ≤ 2 + Real.log K := by
    have hLle : (L : ℝ) ≤ 6 * K := by
      have hc := Nat.ceil_lt_add_one (show 0 ≤ (K : ℝ) * Real.pi by positivity)
      have hpi := Real.pi_lt_four
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      rw [hL]; push_cast; nlinarith
    have hLpos : (0 : ℝ) < L := by positivity
    have h1 := Real.log_le_log hLpos hLle
    rw [Real.log_mul (by norm_num) hKpos.ne'] at h1
    have h6 : Real.log 6 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  calc
    _ ≤ δ * (6 / (K : ℝ) ^ 2) * (2 * (K : ℝ) * autocorr f 0 *
        ∑ n ∈ Finset.range (L + 1), (K : ℝ) / max 1 (n : ℝ)) := hmain
    _ ≤ δ * (6 / (K : ℝ) ^ 2) * (2 * (K : ℝ) * autocorr f 0 * ((K : ℝ) * (2 + Real.log L))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 12 * δ * (2 + Real.log L) * autocorr f 0 := by field_simp; ring
    _ ≤ 12 * δ * (4 + Real.log K) * autocorr f 0 := by
      apply mul_le_mul_of_nonneg_right _ h0
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

end

end GaloisForLFunctions.BiScaleUncertainty
