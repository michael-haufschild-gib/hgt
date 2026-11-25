import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.RoughSemigroupDivisorRigidityMollifierSquareAndHuxleyDispersion
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62CriticalMultipliers
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalAnalytic
import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs
import GaloisForLFunctions.FamilyContinuationTheory.TheTrueVertexBelowSevenEighths
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Pole-Free `χ`-Twisted Cross-Height Gaussian Duality, Smooth-Rough Vaughan Annihilation, Multi-Power Trigonometric Positivity, and the `u₀`-Roughened Vertex LP Beyond `3001 / 24000`

For `riemannZeta`, the cross-height Gaussian two-series expansion carries a `w = 1 - s` shifted-pole
residue (`smoothAFEZetaShiftedPoleResidue`), requiring `(d x, 2 d x)` parity subtraction and forcing
an exponentially growing continuum piece (`Piece 2`) inside `SmoothReflectedMobiusVaughanTypeIAnnihilation`
that is suppressed only above height `|Im s| > 184`. Meanwhile, in `SubSevenEighthsHighTransport` and
`TheTrueVertexBelowSevenEighths`, unroughened plain zero-witness cofactors at scales `0 < m < u₀`
force the crossing `rowCount δ x` and lock the cubic-probe LP behind the unconstrained `ℝ³` Farkas
barrier `40535 / 46328` (`20999 / 24000` certified, i.e. `3001 / 24000` on `0 < Re s < 1 / 2`).

This module couples the `χ`-twisted cross-height Gaussian identity for nonprincipal Dirichlet twists
`L(s, ψ)` (`ψ` primitive, e.g. inducing `χ^k` for `k ≥ 1`) with smooth Vaughan Type-I/II
annihilation, multi-power `χ^j` trigonometric positivity, and the `u₀`-roughened cubic-probe LP:

1. **Pole-free single-scale `ψ`-twisted cross-height Gaussian identity, critical-line `L`-free
   residue extraction, and shifted-pole-free Vaughan bilinearization across all `Im s ∈ ℝ`
   (`dirichletL_crossHeight_gaussian_singleScale_eq`,
   `tsum_dirichlet_smoothAFECutoff_eq_LFunction_add_mellinAt_neg`,
   `dirichletDualGaussianCoeff_eq_neg_factor_mul_add_criticalLine`,
   `twisted_vaughan_dual_band_eq_offLine_add_criticalLine`):**
   For every primitive nonprincipal Dirichlet character `P : CGLLemma62PrimitiveCharacter`, entireness
   of `L(·, P.character)` eliminates the `w = 1 - s` shifted-pole residue identically across **all**
   `0 < Re s < 1 / 2` and **all** `Im s ∈ ℝ` (both in the outer cross-height identity and in the
   inner Type-I smooth AFE). Complete multiplicativity `P.character⁻¹ d * P.character⁻¹ (k / d) =
   P.character⁻¹ k` collapses the `1 ≤ k ≤ K_hi` Vaughan Type-II dual sieve to the exact unsmoothed
   `twistedBalancedBilinearDirichletPoly P.character⁻¹ U V K_hi` at `1 - s` and `conj (linePt (Im s + v))`,
   where `‖cglLemma62PrimitiveFunctionalFactor P (linePt t)‖ = 1` identically.

2. **Complete smooth-rough Vaughan annihilation, sub-horizon prime-modulus `χ^j` trigonometric
   positivity, cyclic subgroup projection, and rough mollifier-square `LSeries` identity
   (`typeIIShort_smooth_mul_rough_eq_zero`, `vaughanDualBilinear_smooth_mul_rough_eq_zero`,
   `trigPoly_twistedBalancedBilinearDirichletPoly_re_nonneg`,
   `deLaValleePoussin_both_signs_twistedBalancedBilinear_nonneg`,
   `cyclic_orthogonality_twistedBalancedBilinear_eq_ker_rough_divisors`,
   `LSeries_rough_divisors_sub_two_eq_sq`):**
   `vaughanDualBilinear U V` annihilates every `s * r` with `2 ≤ s ≤ min U V` and `max U V`-rough `r`
   (regardless of `Ω(r)`). Whenever every prime `p ≤ max U V` divides the modulus `q`, every coprime
   `k ≥ 2` is `max U V`-rough with `vaughanDualBilinear U V k = d(k) - 2 ≥ 0` while non-coprime `k`
   satisfy `((χ⁻¹)^j) k = 0` for all `j ≥ 0` (including `j = 0`), making
   `∑_{j=0}^m c_j Re D_{(χ⁻¹)^j, U, V, K_hi}(σ₁ + i j T) ≥ 0` unconditionally for **every**
   nonnegative cosine polynomial `∑ c_j cos(j θ) ≥ 0`, with rough generating series `(ζ_W(w) - 1)^2`.

3. **Exact `u₀`-roughened cubic-probe LP breaking the `40535 / 46328` (`3001 / 24000`) barrier
   (`roughenedRowCount`, `plainMarked_slot_capacity_feasible`, `roughened_witness_branch_domination`,
   `roughened_farkas_bin_crossing_thresholds`,
   `roughened_LP_breaks_farkas_barrier_of_gt_threshold`,
   `roughened_three_sevenths_certificate`, `roughened_half_certificate_and_floor_attainment`):**
   Removing plain witness cofactors on `(0, u₀)` (`11 / 148 ≤ u₀ ≤ 1 / 2`) satisfies the exact slot
   capacity `0 ≤ z ≤ 7 / 37` of `DetectorRawFibers` at `t_* = 1` and collapses `rowCount δ x` to the
   bilinear-affine count `roughenedRowCount δ x u₀ = 1 - (4/9) δ x - δ (2 - 8x/9) u₀`, whose worst
   case over `[0, 5/6] × [0, 1/2]` reduces to three corners `(0, 0), (5/6, 0), (5/6, 1/2)`. Across
   every `u₀ ∈ (16556 / 40519, 1 / 2]`, this LP strictly crosses `40535 / 46328`: explicitly,
   `u₀ = 3 / 7` certifies `σ₀ = 131 / 150` (`1 - σ₀ = 19 / 150 > 3001 / 24000`) with margin `-1 / 900`,
   and `u₀ = 1 / 2` collapses `roughenedRowCount` to `1 - δ`, attaining `σ₀ = 13 / 15` (`1 - σ₀ = 2 / 15`)
   at `(2/5, 2/5, 1/5)` and certifying `σ₀ = 867 / 1000` (`1 - σ₀ = 133 / 1000`) with margin `-1 / 1000`.

4. **Pointwise `HasStrictPrimeGasWitness` transfer across all `|Im s| > 184` and exact linear-mollifier
   / Euler-deletion obstructions
   (`hasStrictPrimeGasWitness_below_sub_one_eighth_all_heights`,
   `hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane`,
   `linear_mollifier_prime_persistence_above_cutoff`,
   `euler_deletion_multiplier_violates_half_ball_of_harmonic_sum`):**
   Any right zero-free half-plane `Re z > σ₀` transfers via `ζ(s) = 0 → ζ(1 - s) = 0` to pointwise
   `HasStrictPrimeGasWitness` across all `0 < Re s < 1 - σ₀` and all `|Im s| > 184`, while no linear
   detector `1 - Q(s) L(s)` of length `W` can remove primes `p > W` (`(1 - ζ * q) p = -1`) and direct
   Euler-factor deletion `∏_{n ∈ S} (1 - χ(n) n^{-σ})` violates `‖H - 1‖ ≤ 1 / 2` whenever
   `∑_{n ∈ S} n^{-σ} > 1 / 2`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.FamilyContinuationTheory
open _root_.RHTower

/-! ### Part 1: Pole-Free `ψ`-Twisted Cross-Height Gaussian Identity and Critical-Line Vaughan Reduction -/

section Part1PoleFreeTwistedDirichletCrossHeightVaughanDuality

/-- Functional-equation Gamma ratio for odd characters expressed via `zetaChi (z + 1)`:
for every `z ≠ 0`, `Gammaℝ (2 - z) / Gammaℝ (z + 1) = (-z / (2 * π)) * zetaChi (z + 1)`. -/
lemma gammaℝ_two_sub_div_add_one {z : ℂ} (hz : z ≠ 0) :
    Complex.Gammaℝ (2 - z) / Complex.Gammaℝ (z + 1) =
      (-z / (2 * (Real.pi : ℂ))) * zetaChi (z + 1) := by
  set w : ℂ := -z
  have hw : w ≠ 0 := neg_ne_zero.mpr hz
  have hw2 : w / 2 ≠ 0 := div_ne_zero hw two_ne_zero
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2z : (2 : ℂ) - z = w + 2 := by dsimp only [w]; ring
  have h1z : (1 : ℂ) - (z + 1) = w := by dsimp only [w]; ring
  have hG_step : Complex.Gammaℝ (w + 2) = (w / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ w := by
    rw [Complex.Gammaℝ_def (w + 2), Complex.Gammaℝ_def w,
      show (w + 2) / 2 = w / 2 + 1 by ring, Complex.Gamma_add_one (w / 2) hw2,
      show -(w + 2) / 2 = -w / 2 + (-1 : ℂ) by ring,
      Complex.cpow_add _ _ hpi_ne, Complex.cpow_neg_one]
    field_simp [hpi_ne]
  rw [h2z, hG_step]
  unfold zetaChi
  rw [h1z]
  dsimp only [w]
  ring

/-- `cglLemma62PrimitiveFunctionalFactor P` is complex differentiable on `{z : ℂ | z.re < 1}`. -/
lemma differentiableOn_cglPrimitiveFunctionalFactor_re_lt_one
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) :
    DifferentiableOn ℂ (_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P)
      {z : ℂ | z.re < 1} := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  intro z hz
  have hz_lt1 : z.re < 1 := hz
  have hqpos : 0 < (P.modulus.value : ℝ) := by exact_mod_cast P.modulus.positive
  have hexp : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) - w) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hqpow : DifferentiableAt ℂ
      (fun w : ℂ => (P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - w)) z :=
    DifferentiableAt.cpow (differentiableAt_const _) hexp
      (Complex.ofReal_mem_slitPlane.mpr hqpos)
  have hGammaR_pos : ∀ {u : ℂ}, 0 < u.re → DifferentiableAt ℂ Complex.Gammaℝ u := fun {u} hu => by
    have hinv : AnalyticAt ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) u :=
      (Complex.differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) u (Set.mem_univ u)
    have h := hinv.differentiableAt.inv (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hu))
    have heq : (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)⁻¹ = Complex.Gammaℝ := by ext w; simp
    rwa [heq] at h
  have hgamma_num : DifferentiableAt ℂ (fun w : ℂ => P.character⁻¹.gammaFactor (1 - w)) z := by
    rcases P.character⁻¹.even_or_odd with heven | hodd
    · have hfun : DirichletCharacter.gammaFactor P.character⁻¹ = Complex.Gammaℝ :=
        funext fun w => heven.gammaFactor_def w
      rw [hfun]
      exact (hGammaR_pos (by simp; linarith)).comp z ((differentiableAt_const _).sub differentiableAt_id)
    · have hfun : DirichletCharacter.gammaFactor P.character⁻¹ = fun w => Complex.Gammaℝ (w + 1) :=
        funext fun w => hodd.gammaFactor_def w
      rw [hfun]
      exact (hGammaR_pos (by simp; linarith)).comp z
        (((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _))
  have hgamma_inv : DifferentiableAt ℂ (fun w : ℂ => (P.character.gammaFactor w)⁻¹) z := by
    rcases P.character.even_or_odd with heven | hodd
    · have hfun : (fun w : ℂ => (P.character.gammaFactor w)⁻¹) = fun w => (Complex.Gammaℝ w)⁻¹ :=
        funext fun w => by rw [heven.gammaFactor_def]
      rw [hfun]
      exact Complex.differentiable_Gammaℝ_inv z
    · have hfun : (fun w : ℂ => (P.character.gammaFactor w)⁻¹) = fun w => (Complex.Gammaℝ (w + 1))⁻¹ :=
        funext fun w => by rw [hodd.gammaFactor_def]
      rw [hfun]
      exact (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add (differentiable_const _))) z
  unfold _root_.RHTower.cglLemma62PrimitiveFunctionalFactor
  rw [div_eq_mul_inv]
  exact (((hqpow.mul (differentiableAt_const _)).mul hgamma_num).mul hgamma_inv).differentiableWithinAt

/-- Polynomial vertical growth of `cglLemma62PrimitiveFunctionalFactor P` off the real axis across
any strip `α ≤ Re z ≤ 1 / 2`. -/
lemma exists_strip_poly_growth_cglPrimitiveFunctionalFactor
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) (α : ℝ) (_hα : α ≤ 1 / 2) :
    ∃ (T₀ : ℝ) (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ z : ℂ, α ≤ z.re → z.re ≤ 1 / 2 → T₀ ≤ |z.im| →
        ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P z‖ ≤ C * (1 + |z.im|) ^ N := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  obtain ⟨T₀, N, C_z, hCz_pos, hchi⟩ := hasStripPolyGrowthOffReal_zetaChi α (3 / 2)
  set T₁ : ℝ := max 1 (|T₀| + 1)
  set Q_bd : ℝ := (P.modulus.value : ℝ) ^ (1 / 2 - α)
  set M_re : ℝ := |α| + 1
  set C_tot : ℝ := Q_bd * ((1 + M_re / (2 * Real.pi)) * C_z)
  refine ⟨T₁, N + 1, C_tot, by dsimp only [C_tot, Q_bd, M_re]; positivity, fun z hz_lo hz_hi hz_im => ?_⟩
  have hz_im1 : 1 ≤ |z.im| := (le_max_left 1 (|T₀| + 1)).trans hz_im
  have hz_im_T₀ : T₀ ≤ |z.im| := by
    have h1 : |T₀| + 1 ≤ |z.im| := (le_max_right 1 (|T₀| + 1)).trans hz_im
    linarith [le_abs_self T₀]
  have hz_ne0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im, abs_zero] at hz_im1; linarith
  have hq_pow : ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z)‖ ≤ Q_bd := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    have hbase : (1 : ℝ) ≤ (P.modulus.value : ℝ) := by exact_mod_cast P.modulus.positive
    have hexp : ((1 / 2 : ℂ) - z).re ≤ 1 / 2 - α := by simp; linarith
    exact Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hroot : ‖P.character.rootNumber‖ = 1 :=
    _root_.RHTower.cglLemma62_primitive_rootNumber_norm_one P
  have h1_le_im : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  have hpow_step : (1 + |z.im|) ^ N ≤ (1 + |z.im|) ^ (N + 1) :=
    pow_le_pow_right₀ h1_le_im (Nat.le_succ N)
  have hgrat : ‖P.character⁻¹.gammaFactor (1 - z) / P.character.gammaFactor z‖ ≤
      ((1 + M_re / (2 * Real.pi)) * C_z) * (1 + |z.im|) ^ (N + 1) := by
    rw [_root_.RHTower.gammaFactor_inv]
    rcases P.character.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def (1 - z), heven.gammaFactor_def z]
      change ‖zetaChi z‖ ≤ _
      have hb := hchi z hz_lo (hz_hi.trans (by norm_num)) hz_im_T₀
      have h1_le_fac : (1 : ℝ) ≤ 1 + M_re / (2 * Real.pi) := by
        dsimp only [M_re]
        linarith [div_nonneg (by positivity : (0 : ℝ) ≤ |α| + 1) Real.two_pi_pos.le]
      have hcoef : C_z ≤ (1 + M_re / (2 * Real.pi)) * C_z :=
        le_mul_of_one_le_left hCz_pos h1_le_fac
      exact hb.trans (mul_le_mul hcoef hpow_step (by positivity) (by linarith))
    · rw [hodd.gammaFactor_def (1 - z), hodd.gammaFactor_def z,
        show (1 : ℂ) - z + 1 = 2 - z by ring, gammaℝ_two_sub_div_add_one hz_ne0, norm_mul, norm_div,
        norm_neg, show ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]]
      have hz_norm : ‖z‖ ≤ M_re * (1 + |z.im|) := by
        have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        have hre_abs : |z.re| ≤ M_re := by
          dsimp only [M_re]
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le α], by linarith [abs_nonneg α]⟩
        have hM1 : 1 ≤ M_re := by dsimp only [M_re]; linarith [abs_nonneg α]
        nlinarith [abs_nonneg z.im]
      have hz1_chi : ‖zetaChi (z + 1)‖ ≤ C_z * (1 + |z.im|) ^ N := by
        have hb := hchi (z + 1) (by simp; linarith) (by simp; linarith) (by simpa using hz_im_T₀)
        simpa using hb
      calc (‖z‖ / (2 * Real.pi)) * ‖zetaChi (z + 1)‖
          ≤ (M_re * (1 + |z.im|) / (2 * Real.pi)) * (C_z * (1 + |z.im|) ^ N) :=
            mul_le_mul (div_le_div_of_nonneg_right hz_norm (by positivity)) hz1_chi
              (norm_nonneg _) (by dsimp only [M_re]; positivity)
        _ = ((M_re / (2 * Real.pi)) * C_z) * (1 + |z.im|) ^ (N + 1) := by
            rw [pow_succ]; ring
        _ ≤ ((1 + M_re / (2 * Real.pi)) * C_z) * (1 + |z.im|) ^ (N + 1) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hCz_pos]) (by positivity)
  unfold _root_.RHTower.cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul, hroot, mul_one, mul_div_assoc, ← norm_div]
  calc ‖(P.modulus.value : ℂ) ^ (1 / 2 - z)‖ *
          ‖P.character⁻¹.gammaFactor (1 - z) / P.character.gammaFactor z‖
      ≤ Q_bd * (((1 + M_re / (2 * Real.pi)) * C_z) * (1 + |z.im|) ^ (N + 1)) :=
        mul_le_mul hq_pow hgrat (norm_nonneg _) (by dsimp only [Q_bd]; positivity)
    _ = C_tot * (1 + |z.im|) ^ (N + 1) := by dsimp only [C_tot]; ring

/-- Global polynomial bound on `cglLemma62PrimitiveFunctionalFactor P (s + (-2 + i v))` across all
`v : ℝ` when `0 < Re s < 1 / 2`. -/
lemma exists_leftLine_poly_growth_cglPrimitiveFunctionalFactor
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) {s : ℂ}
    (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ v : ℝ,
        ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + ((-2 : ℂ) + (v : ℂ) * I))‖ ≤
          C * (1 + |v|) ^ N := by
  obtain ⟨T₀, N, C₁, hC₁, hstrip⟩ :=
    exists_strip_poly_growth_cglPrimitiveFunctionalFactor P (-2) (by norm_num)
  set V₀ : ℝ := |T₀| + |s.im| + 1
  have hcont_line : Continuous (fun v : ℝ =>
      _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + ((-2 : ℂ) + (v : ℂ) * I))) := by
    refine (differentiableOn_cglPrimitiveFunctionalFactor_re_lt_one P).continuousOn.comp_continuous
      (by fun_prop) fun v => ?_
    show (s + ((-2 : ℂ) + (v : ℂ) * I)).re < 1
    simp; linarith
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont_line.continuousOn (s := Set.Icc (-V₀) V₀))
  set C_all : ℝ := max (max M₀ 0) (C₁ * (1 + |s.im|) ^ N)
  refine ⟨C_all, N, by dsimp only [C_all]; positivity, fun v => ?_⟩
  rcases le_or_gt (|v|) V₀ with hv_le | hv_gt
  · have hmem : v ∈ Set.Icc (-V₀) V₀ := abs_le.mp hv_le
    have hb : ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P
        (s + ((-2 : ℂ) + (v : ℂ) * I))‖ ≤ C_all :=
      (hM₀ v hmem).trans ((le_max_left M₀ 0).trans (le_max_left (max M₀ 0) (C₁ * (1 + |s.im|) ^ N)))
    have h1pow : (1 : ℝ) ≤ (1 + |v|) ^ N := one_le_pow₀ (by linarith [abs_nonneg v])
    calc ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + ((-2 : ℂ) + (v : ℂ) * I))‖
        ≤ C_all * 1 := by linarith
      _ ≤ C_all * (1 + |v|) ^ N :=
          mul_le_mul_of_nonneg_left h1pow (by dsimp only [C_all]; positivity)
  · set z : ℂ := s + ((-2 : ℂ) + (v : ℂ) * I)
    have hz_lo : (-2 : ℝ) ≤ z.re := by simp [z]; linarith
    have hz_hi : z.re ≤ 1 / 2 := by simp [z]; linarith
    have hz_im : T₀ ≤ |z.im| := by
      have him : z.im = s.im + v := by simp [z]
      have htri : |v| - |s.im| ≤ |s.im + v| := by
        have h := abs_sub_abs_le_abs_sub v (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      rw [him]
      dsimp only [V₀] at hv_gt
      linarith [le_abs_self T₀]
    have h1_im : 1 + |z.im| ≤ (1 + |s.im|) * (1 + |v|) := by
      have him : z.im = s.im + v := by simp [z]
      rw [him]
      have htri := abs_add_le s.im v
      nlinarith [abs_nonneg s.im, abs_nonneg v]
    have hb := hstrip z hz_lo hz_hi hz_im
    calc ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P z‖
        ≤ C₁ * (1 + |z.im|) ^ N := hb
      _ ≤ C₁ * ((1 + |s.im|) * (1 + |v|)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1_im N) hC₁
      _ = (C₁ * (1 + |s.im|) ^ N) * (1 + |v|) ^ N := by rw [mul_pow]; ring
      _ ≤ C_all * (1 + |v|) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Uncompleted functional equation and dual Dirichlet series expansion for a primitive nonprincipal
Dirichlet `L`-function throughout `Re z < 0`. -/
theorem cglPrimitiveLFunction_eq_factor_mul_tsum_of_re_neg
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) {z : ℂ} (hz : z.re < 0) :
    letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
    DirichletCharacter.LFunction P.character z =
      _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P z *
        ∑' m : ℕ, P.character⁻¹ (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - z)) := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  have hz_ne0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h1z_re : 1 < (1 - z).re := by simp; linarith
  have h1z_ne0 : (1 : ℂ) - z ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hgam_ne0 : P.character⁻¹.gammaFactor (1 - z) ≠ 0 := by
    rcases P.character⁻¹.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [hodd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcomp := _root_.RHTower.cglLemma62_primitiveCompletedL_one_sub P (1 - z)
  rw [show (1 : ℂ) - (1 - z) = z by ring] at hcomp
  have hleft := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character z (Or.inl hz_ne0)
  have hright := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character⁻¹ (1 - z) (Or.inl h1z_ne0)
  have hcomp_right : DirichletCharacter.completedLFunction P.character⁻¹ (1 - z) =
      DirichletCharacter.LFunction P.character⁻¹ (1 - z) * P.character⁻¹.gammaFactor (1 - z) := by
    rw [hright, div_mul_cancel₀ _ hgam_ne0]
  have hfe : DirichletCharacter.LFunction P.character z =
      _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P z *
        DirichletCharacter.LFunction P.character⁻¹ (1 - z) := by
    rw [hleft, hcomp, hcomp_right]
    unfold _root_.RHTower.cglLemma62PrimitiveFunctionalFactor
    rw [show (1 : ℂ) - z - 1 / 2 = 1 / 2 - z by ring]
    ring
  rw [hfe, DirichletCharacter.LFunction_eq_LSeries P.character⁻¹ h1z_re]
  congr 1
  have hsum : LSeriesSummable (fun n : ℕ => P.character⁻¹ n) (1 - z) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re P.character⁻¹ h1z_re
  rw [LSeries, ← hsum.sum_add_tsum_nat_add 1, Finset.sum_range_one, LSeries.term_zero, zero_add]
  refine tsum_congr fun m => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m), div_eq_mul_inv, ← Complex.cpow_neg,
    Nat.succ_eq_add_one,
    show ((m + 1 : ℕ) : ZMod P.modulus.value) = (m : ZMod P.modulus.value) + 1 by push_cast; rfl]

/-- Reflected Mellin integrand for the `m`-th dual mode of a primitive nonprincipal Dirichlet
`L`-function. -/
def dirichletReflectedTerm
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) (s : ℂ) (y : ℝ) (m : ℕ) (w : ℂ) : ℂ :=
  _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
    ((m + 1 : ℕ) : ℂ) ^ (s + w - 1) * (y : ℂ) ^ w * smoothAFEGaussianKernel w

/-- Normalized reflected Gaussian dual coefficient for `P.character` on the line `Re w = -2`. -/
def dirichletDualGaussianCoeff
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) (s : ℂ) (y : ℝ) (m : ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ v : ℝ, dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)

private lemma integrable_tsum_of_summable_integral_norm_dir {G : ℕ → ℝ → ℂ}
    (hG : ∀ n, Integrable (G n)) (hs : Summable fun n => ∫ v, ‖G n v‖) :
    Integrable (fun v => ∑' n, G n v) := by
  have hlint : ∀ n, ∫⁻ v, ‖G n v‖ₑ = ENNReal.ofReal (∫ v, ‖G n v‖) := fun n => by
    rw [ofReal_integral_eq_lintegral_ofReal (hG n).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    congr 1; funext v; rw [ofReal_norm]
  have hfin : ∑' n, ∫⁻ v, ‖G n v‖ₑ ≠ ⊤ := by
    simp_rw [hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hlt : ∫⁻ v, ∑' n, ‖G n v‖ₑ < ⊤ := by
    rw [lintegral_tsum fun n => (hG n).1.enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hae : ∀ᵐ v, ∑' n, ‖G n v‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun n => (hG n).1.enorm) hlt.ne
  have hsum : ∀ᵐ v, Summable fun n => G n v := by
    filter_upwards [hae] with v hv
    refine Summable.of_norm ?_
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm] using hv.ne))
  refine ⟨aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset ℕ)))
      (f := fun s v => ∑ n ∈ s, G n v)
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun n _ => (hG n).1)
      (by filter_upwards [hsum] with v hv; exact hv.hasSum), ?_⟩
  unfold HasFiniteIntegral
  exact (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_lt hlt

private lemma dirichletReflectedTerm_left_two_integrable_and_summable
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) {s : ℂ}
    (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {y : ℝ} (hy : 0 < y) :
    (∀ m : ℕ, Integrable (fun v : ℝ => dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I))) ∧
    Summable (fun m : ℕ =>
      ∫ v : ℝ, ‖dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)‖) := by
  obtain ⟨C_f, N_f, hCf_nn, hCf⟩ := exists_leftLine_poly_growth_cglPrimitiveFunctionalFactor P hs0 hhi
  have hker_int : Integrable (fun v : ℝ => (1 + |v|) ^ N_f * Real.exp (-(v ^ (2 : ℕ)))) := by
    simpa using integrable_shifted_pow_mul_exp_neg_sq 1 N_f
  set K_y : ℝ := C_f * y ^ (-2 : ℝ) * (Real.exp 4 / 2)
  have hKy_nn : 0 ≤ K_y := by dsimp only [K_y]; positivity
  have hpt_bd : ∀ (m : ℕ) (v : ℝ),
      ‖dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)‖ ≤
        (K_y * ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) *
          ((1 + |v|) ^ N_f * Real.exp (-(v ^ (2 : ℕ)))) := by
    intro m v
    set w : ℂ := (-2 : ℂ) + (v : ℂ) * I
    have hm_pos : 0 < m + 1 := Nat.succ_pos m
    have hm_ge1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm_pos
    have hm_pow : ‖((m + 1 : ℕ) : ℂ) ^ (s + w - 1)‖ ≤ ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [Complex.norm_natCast_cpow_of_pos hm_pos]
      have hexp : (s + w - 1).re ≤ -(5 / 2 : ℝ) := by simp [w]; linarith
      exact Real.rpow_le_rpow_of_exponent_le hm_ge1 hexp
    have hy_pow : ‖(y : ℂ) ^ w‖ = y ^ (-2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp [w]
    have hker : ‖smoothAFEGaussianKernel w‖ ≤ (Real.exp 4 / 2) * Real.exp (-(v ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = 4 - v ^ (2 : ℕ) := by
        dsimp only [w]
        norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      have hwnorm : (2 : ℝ) ≤ ‖w‖ := by
        have h := Complex.abs_re_le_norm w
        have hre : |w.re| = 2 := by simp [w]
        rwa [hre] at h
      rw [hw_re_sq, sub_eq_add_neg, Real.exp_add]
      calc Real.exp 4 * Real.exp (-(v ^ (2 : ℕ))) / ‖w‖
          ≤ Real.exp 4 * Real.exp (-(v ^ (2 : ℕ))) / 2 :=
            div_le_div_of_nonneg_left (by positivity) two_pos hwnorm
        _ = (Real.exp 4 / 2) * Real.exp (-(v ^ (2 : ℕ))) := by ring
    unfold dirichletReflectedTerm
    rw [norm_mul, norm_mul, norm_mul, hy_pow]
    calc ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w)‖ *
            ‖((m + 1 : ℕ) : ℂ) ^ (s + w - 1)‖ * y ^ (-2 : ℝ) * ‖smoothAFEGaussianKernel w‖
        ≤ (C_f * (1 + |v|) ^ N_f) * ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * y ^ (-2 : ℝ) *
            ((Real.exp 4 / 2) * Real.exp (-(v ^ (2 : ℕ)))) := by
          refine mul_le_mul
            (mul_le_mul (mul_le_mul (hCf v) hm_pow (norm_nonneg _) (by positivity))
              le_rfl (by positivity) (by positivity))
            hker (norm_nonneg _) (by positivity)
      _ = (K_y * ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) *
            ((1 + |v|) ^ N_f * Real.exp (-(v ^ (2 : ℕ)))) := by dsimp only [K_y]; ring
  have hint_m : ∀ m : ℕ, Integrable (fun v : ℝ =>
      dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)) := by
    intro m
    refine Integrable.mono' (hker_int.const_mul (K_y * ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))) ?_
      (Filter.Eventually.of_forall (hpt_bd m))
    have hcont : Continuous (fun v : ℝ =>
        dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)) := by
      unfold dirichletReflectedTerm smoothAFEGaussianKernel
      have hpath : Continuous (fun v : ℝ => (-2 : ℂ) + (v : ℂ) * I) := by fun_prop
      have hfac_c : Continuous (fun v : ℝ =>
          _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + ((-2 : ℂ) + (v : ℂ) * I))) := by
        refine (differentiableOn_cglPrimitiveFunctionalFactor_re_lt_one P).continuousOn.comp_continuous
          (continuous_const.add hpath) fun v => ?_
        show (s + ((-2 : ℂ) + (v : ℂ) * I)).re < 1
        simp; linarith
      have hm_c : Continuous (fun v : ℝ =>
          ((m + 1 : ℕ) : ℂ) ^ (s + ((-2 : ℂ) + (v : ℂ) * I) - 1)) :=
        Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
      have hy_c : Continuous (fun v : ℝ => (y : ℂ) ^ ((-2 : ℂ) + (v : ℂ) * I)) :=
        Continuous.const_cpow hpath (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
      have hker_c : Continuous (fun v : ℝ =>
          Complex.exp (((-2 : ℂ) + (v : ℂ) * I) ^ (2 : ℕ)) / ((-2 : ℂ) + (v : ℂ) * I)) :=
        (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v h0 => by
          have := congrArg Complex.re h0; simp at this
      exact ((hfac_c.mul hm_c).mul hy_c).mul hker_c
    exact hcont.aestronglyMeasurable
  refine ⟨hint_m, ?_⟩
  set I_ker : ℝ := ∫ v : ℝ, (1 + |v|) ^ N_f * Real.exp (-(v ^ (2 : ℕ)))
  have hsum_rpow : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact ((summable_nat_add_iff 1).mpr hbase).congr fun m => by push_cast; rfl
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
    (hsum_rpow.mul_left (K_y * I_ker))
  have hm_int := integral_mono_ae (hint_m m).norm
    (hker_int.const_mul (K_y * ((m + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))))
    (Filter.Eventually.of_forall (hpt_bd m))
  rw [MeasureTheory.integral_const_mul] at hm_int
  exact hm_int.trans_eq (by dsimp only [I_ker]; ring)

/-- **Pole-free single-scale `ψ`-twisted cross-height Gaussian identity across all heights `Im s ∈ ℝ`:**
for every primitive nonprincipal character `P : CGLLemma62PrimitiveCharacter`, every `s ∈ ℂ` in the
open left critical strip `0 < Re s < 1 / 2` (at **every** ordinate `Im s ∈ ℝ`), and every `y > 0`,
`L(s, P.character)` equals the direct smoothed series minus the reflected `P.character⁻¹`-series
with **zero shifted-pole residue** and **no `(y, 2 y)` parity subtraction**. -/
theorem dirichletL_crossHeight_gaussian_singleScale_eq
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {y : ℝ} (hy : 0 < y) :
    letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
    DirichletCharacter.LFunction P.character s =
      (∑' n : ℕ, P.character (n + 1) *
          (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y))) -
        ∑' m : ℕ, P.character⁻¹ (m + 1) * dirichletDualGaussianCoeff P s y m := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  set g : ℂ → ℂ := fun w =>
    DirichletCharacter.LFunction P.character (s + w) * (y : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ))
  set MF : ℂ → ℂ := fun w =>
    DirichletCharacter.LFunction P.character (s + w) * (y : ℂ) ^ w * smoothAFEGaussianKernel w
  have hg_diff : Differentiable ℂ g := by
    haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
    exact (((DirichletCharacter.differentiable_LFunction P.nonprincipal).comp
      (differentiable_const s |>.add differentiable_id)).mul
      (differentiable_const_cpow_of_neZero (y : ℂ))).mul
      (differentiable_exp.comp (differentiable_pow 2))
  have hg_an : AnalyticOnNhd ℂ g Set.univ := hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hg_zero : g 0 = DirichletCharacter.LFunction P.character s := by dsimp only [g]; simp
  have hMF_eq : MF = fun w => g w * (w - 0)⁻¹ := by
    funext w; dsimp only [MF, g, smoothAFEGaussianKernel]; simp [div_eq_mul_inv]; ring
  have hrect : ∀ T : ℝ, 0 < T →
      ((∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, MF ((1 : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, MF ((-2 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * DirichletCharacter.LFunction P.character s := by
    intro T hT
    set z₁ : ℂ := (-2 : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (1 : ℂ) + (T : ℂ) * I
    have hbox := rectIntegral_cauchyFormula_analyticOnNhd (Set.subset_univ _) hg_an
      (z₁ := z₁) (z₂ := z₂) (p := 0)
      (by simp [z₁]) (by simp [z₂]) (by simp [z₁]; linarith) (by simp [z₂]; linarith)
    rw [← hMF_eq, hg_zero] at hbox
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  obtain ⟨C_L, hCL_pos, hL_strip⟩ := _root_.RHTower.bound_LFunction_strip P.nonprincipal P.primitive
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ => ∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set Y_bd : ℝ := max (y ^ (-2 : ℝ)) (y ^ (1 : ℝ))
    set K_h : ℝ := C_L * Y_bd * Real.exp 4
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_h * (((7 + |s.im|) + T) ^ (3 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (7 + |s.im|) 3).const_mul K_h)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT u hu
    rw [Set.uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 1)] at hu
    have hT_pos : 0 < T := zero_lt_one.trans_le hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos hT_pos]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hsw_lo : (-2 : ℝ) ≤ (s + w).re := by simp [w]; linarith [hu.1.le]
    have hsw_hi : (s + w).re ≤ 3 := by simp [w]; linarith [hu.2]
    have hnorm_sub4 : ‖s + w - 4‖ ≤ (7 + |s.im|) + T := by
      have h1 : ‖s + w - 4‖ ≤ |(s + w - 4).re| + |(s + w - 4).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have hre : |(s + w - 4).re| ≤ 7 := by
        rw [abs_le]
        exact ⟨by simp [w]; linarith [hu.1.le], by simp [w]; linarith [hu.2]⟩
      have him : |(s + w - 4).im| ≤ |s.im| + T := by
        have him_eq : (s + w - 4).im = s.im + ε * T := by simp [w]
        rw [him_eq]
        exact (abs_add_le s.im (ε * T)).trans_eq (by rw [habsv])
      linarith
    have hL_bd : ‖DirichletCharacter.LFunction P.character (s + w)‖ ≤
        C_L * ((7 + |s.im|) + T) ^ (3 : ℕ) :=
      (hL_strip (s + w) hsw_lo hsw_hi).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm_sub4 3) hCL_pos.le)
    have hy_bd : ‖(y : ℂ) ^ w‖ ≤ Y_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, show w.re = u by simp [w]]
      rcases le_total 1 y with h1y | h1y
      · exact (Real.rpow_le_rpow_of_exponent_le h1y hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h1y hu.1.le).trans (le_max_left _ _)
    have hker_bd : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 4 * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = u ^ (2 : ℕ) - T ^ (2 : ℕ) := by
        dsimp only [w]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ (2 : ℕ) ≤ 4 := by
        have h1 : -2 ≤ u := hu.1.le
        have h2 : u ≤ 1 := hu.2
        nlinarith
      have hwnorm1 : 1 ≤ ‖w‖ := by
        calc (1 : ℝ) ≤ T := hT
          _ = |w.im| := by simp [w, habsv]
          _ ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [hw_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hwnorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    dsimp only [MF]
    rw [norm_mul, norm_mul]
    calc ‖DirichletCharacter.LFunction P.character (s + w)‖ * ‖(y : ℂ) ^ w‖ *
            ‖smoothAFEGaussianKernel w‖
        ≤ (C_L * ((7 + |s.im|) + T) ^ (3 : ℕ)) * Y_bd *
            (Real.exp 4 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hL_bd hy_bd (norm_nonneg _) (by positivity))
            hker_bd (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) ((Real.rpow_nonneg hy.le (-2)).trans (le_max_left _ _))
      _ = K_h * (((7 + |s.im|) + T) ^ (3 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))) := by
          dsimp only [K_h]; ring
  have hsc1 : 1 < s.re + 1 := by linarith
  have hMF_right_eq : ∀ v : ℝ,
      MF ((1 : ℂ) + (v : ℂ) * I) =
        ∑' n : ℕ, P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I) := by
    intro v
    have hre : 1 < (s + ((1 : ℂ) + (v : ℂ) * I)).re := by simp; linarith
    have hsumL : LSeriesSummable (fun k : ℕ => P.character k) (s + ((1 : ℂ) + (v : ℂ) * I)) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re P.character hre
    dsimp only [MF]
    rw [DirichletCharacter.LFunction_eq_LSeries P.character hre, LSeries,
      ← hsumL.sum_add_tsum_nat_add 1, Finset.sum_range_one, LSeries.term_zero, zero_add,
      ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), smoothAFEZetaMellinTerm, div_eq_mul_inv,
      one_div]
    push_cast; ring
  have hterm_dir_int : ∀ n : ℕ,
      Integrable (fun v : ℝ =>
        P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I)) :=
    fun n => (smoothAFEZetaMellinTerm_verticalIntegrable hy zero_lt_one n).const_mul _
  have hsum_dir_norm : Summable (fun n : ℕ =>
      ∫ v : ℝ, ‖P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_)
      (summable_integral_norm_smoothAFEZetaMellinTerm hy zero_lt_one hsc1)
    refine integral_mono_ae (hterm_dir_int n).norm
      (smoothAFEZetaMellinTerm_verticalIntegrable hy zero_lt_one n).norm
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [norm_mul, show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num]
    exact mul_le_of_le_one_left (norm_nonneg _) (P.character.norm_le_one (n + 1))
  have hMF_right_int : Integrable (fun v : ℝ => MF ((1 : ℂ) + (v : ℂ) * I)) :=
    (integrable_tsum_of_summable_integral_norm_dir hterm_dir_int hsum_dir_norm).congr
      (Filter.Eventually.of_forall fun v => (hMF_right_eq v).symm)
  have hint_right : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, P.character (n + 1) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)) := by
    have h1eq : (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) =
        ∑' n : ℕ, ∫ v : ℝ,
          P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I) := by
      calc (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I))
          = ∫ v : ℝ, ∑' n : ℕ,
              P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I) :=
            integral_congr_ae (Filter.Eventually.of_forall hMF_right_eq)
        _ = ∑' n : ℕ, ∫ v : ℝ,
              P.character (n + 1) * smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I) :=
            (MeasureTheory.integral_tsum_of_summable_integral_norm hterm_dir_int hsum_dir_norm).symm
    rw [h1eq, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [MeasureTheory.integral_const_mul,
      show (∫ v : ℝ, smoothAFEZetaMellinTerm s y n ((1 : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ, smoothAFEZetaMellinTerm s y n (((1 : ℝ) : ℂ) + (v : ℂ) * I) by norm_num,
      integral_smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegral hy,
      ← smoothAFECutoffAt_eq_smoothAFECutoff (div_pos (by exact_mod_cast Nat.succ_pos n) hy) zero_lt_one,
      smoothAFECutoffAt_eq_integral, Complex.real_smul]
    push_cast; ring
  obtain ⟨hint_base, hsum_base⟩ := dirichletReflectedTerm_left_two_integrable_and_summable P hs0 hhi hy
  have hMF_left_eq : ∀ v : ℝ,
      MF ((-2 : ℂ) + (v : ℂ) * I) =
        ∑' m : ℕ, P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I) := by
    intro v
    set w : ℂ := (-2 : ℂ) + (v : ℂ) * I
    have hsw_neg : (s + w).re < 0 := by simp [w]; linarith
    dsimp only [MF]
    rw [cglPrimitiveLFunction_eq_factor_mul_tsum_of_re_neg P hsw_neg]
    calc (_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
            ∑' m : ℕ, P.character⁻¹ (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) *
          (y : ℂ) ^ w * smoothAFEGaussianKernel w
        = (∑' m : ℕ, P.character⁻¹ (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) *
            (_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
              (y : ℂ) ^ w * smoothAFEGaussianKernel w) := by ring
      _ = ∑' m : ℕ, P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m w := by
          rw [← tsum_mul_right]
          refine tsum_congr fun m => ?_
          unfold dirichletReflectedTerm
          rw [show -(1 - (s + w)) = s + w - 1 by ring]
          ring
  have hterm_dual_int : ∀ m : ℕ,
      Integrable (fun v : ℝ =>
        P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)) :=
    fun m => (hint_base m).const_mul _
  have hsum_dual_norm : Summable (fun m : ℕ =>
      ∫ v : ℝ, ‖P.character⁻¹ (m + 1) *
        dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_) hsum_base
    refine integral_mono_ae (hterm_dual_int m).norm (hint_base m).norm
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (P.character⁻¹.norm_le_one (m + 1))
  have hMF_left_int : Integrable (fun v : ℝ => MF ((-2 : ℂ) + (v : ℂ) * I)) :=
    (integrable_tsum_of_summable_integral_norm_dir hterm_dual_int hsum_dual_norm).congr
      (Filter.Eventually.of_forall fun v => (hMF_left_eq v).symm)
  have hint_left : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ, MF ((-2 : ℂ) + (v : ℂ) * I)) =
      ∑' m : ℕ, P.character⁻¹ (m + 1) * dirichletDualGaussianCoeff P s y m := by
    have h2eq : (∫ v : ℝ, MF ((-2 : ℂ) + (v : ℂ) * I)) =
        ∑' m : ℕ, ∫ v : ℝ,
          P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I) := by
      calc (∫ v : ℝ, MF ((-2 : ℂ) + (v : ℂ) * I))
          = ∫ v : ℝ, ∑' m : ℕ,
              P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I) :=
            integral_congr_ae (Filter.Eventually.of_forall hMF_left_eq)
        _ = ∑' m : ℕ, ∫ v : ℝ,
              P.character⁻¹ (m + 1) * dirichletReflectedTerm P s y m ((-2 : ℂ) + (v : ℂ) * I) :=
            (MeasureTheory.integral_tsum_of_summable_integral_norm hterm_dual_int hsum_dual_norm).symm
    rw [h2eq, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [MeasureTheory.integral_const_mul]
    unfold dirichletDualGaussianCoeff
    ring
  have hlim_r := intervalIntegral_tendsto_integral hMF_right_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_l := intervalIntegral_tendsto_integral hMF_left_int tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ => ∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_r.const_smul I)).sub (hlim_l.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-2 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, MF ((1 : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, MF ((-2 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * DirichletCharacter.LFunction P.character s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) - (∫ v : ℝ, MF ((-2 : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * DirichletCharacter.LFunction P.character s := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hpi_ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hinv_pi : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
    push_cast; exact one_div_mul_cancel hpi_ne
  rw [← hint_right, ← hint_left]
  have hmul := congrArg (fun z : ℂ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) * z) hcancel
  rw [mul_sub, ← mul_assoc, hinv_pi, one_mul] at hmul
  exact hmul.symm

/-- **Pole-free two-line smooth AFE for nonprincipal primitive Dirichlet `L(w, ψ)`
(`Piece 2 = ShiftedPoleResidue ≡ 0` in smooth Vaughan Type-I annihilation):**
shifting `∑_{m ≥ 1} ψ(m) m^{-w} W(m / X)` from `Re z = b > 0` (`1 < w.re + b`) across `z = 0` to
`Re z = a < 0` across **any** `-1 ≤ w.re ≤ 1` and **any** `Im w ∈ ℝ` produces **zero shifted-pole
residue**. -/
theorem tsum_dirichlet_smoothAFECutoff_eq_LFunction_add_mellinAt_neg
    {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive)
    {w : ℂ} (hw_lo : -1 ≤ w.re) (hw_hi : w.re ≤ 1)
    {X a b : ℝ} (hX : 0 < X) (ha_lo : -1 ≤ a) (ha0 : a < 0) (h0b : 0 < b) (hb_hi : b ≤ 2)
    (hwb : 1 < w.re + b) :
    (∑' m : ℕ, ψ (m + 1) * (((m + 1 : ℕ) : ℂ) ^ (-w) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X))) =
      DirichletCharacter.LFunction ψ w +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            DirichletCharacter.LFunction ψ (w + ((a : ℂ) + (v : ℂ) * I)) *
              (X : ℂ) ^ ((a : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel ((a : ℂ) + (v : ℂ) * I) := by
  set g : ℂ → ℂ := fun z =>
    DirichletCharacter.LFunction ψ (w + z) * (X : ℂ) ^ z * Complex.exp (z ^ (2 : ℕ))
  set F : ℂ → ℂ := fun z =>
    DirichletCharacter.LFunction ψ (w + z) * (X : ℂ) ^ z * smoothAFEGaussianKernel z
  have hg_diff : Differentiable ℂ g := by
    haveI : NeZero (X : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
    exact (((DirichletCharacter.differentiable_LFunction hψ).comp
      (differentiable_const w |>.add differentiable_id)).mul
      (differentiable_const_cpow_of_neZero (X : ℂ))).mul
      (differentiable_exp.comp (differentiable_pow 2))
  have hg_an : AnalyticOnNhd ℂ g Set.univ := hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hF_eq : F = fun z => g z * (z - 0)⁻¹ := by
    funext z; dsimp only [F, g, smoothAFEGaussianKernel]; simp [div_eq_mul_inv]; ring
  obtain ⟨C_L, hCL_pos, hL_strip⟩ := _root_.RHTower.bound_LFunction_strip hψ hprim
  have hrect : ∀ T : ℝ, 0 < T →
      ((∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F ((b : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F ((a : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * DirichletCharacter.LFunction ψ w := by
    intro T hT
    set z₁ : ℂ := (a : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (b : ℂ) + (T : ℂ) * I
    have hbox := rectIntegral_cauchyFormula_analyticOnNhd (Set.subset_univ _) hg_an
      (z₁ := z₁) (z₂ := z₂) (p := 0)
      (by simp [z₁]; exact ha0) (by simp [z₂]; exact h0b)
      (by simp [z₁]; linarith) (by simp [z₂]; linarith)
    have hg0 : g 0 = DirichletCharacter.LFunction ψ w := by dsimp only [g]; simp
    rw [← hF_eq, hg0] at hbox
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set X_bd : ℝ := max (X ^ a) (X ^ b)
    set K_h : ℝ := C_L * X_bd * Real.exp 4
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_h * (((7 + |w.im|) + T) ^ (3 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (7 + |w.im|) 3).const_mul K_h)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT u hu
    rw [Set.uIoc_of_le (ha0.trans h0b).le] at hu
    have hT_pos : 0 < T := zero_lt_one.trans_le hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos hT_pos]
    set z : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hwz_lo : (-2 : ℝ) ≤ (w + z).re := by simp [z]; linarith [hu.1.le]
    have hwz_hi : (w + z).re ≤ 3 := by simp [z]; linarith [hu.2]
    have hnorm_sub4 : ‖w + z - 4‖ ≤ (7 + |w.im|) + T := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (w + z - 4)
      have hre : |(w + z - 4).re| ≤ 7 := by
        rw [abs_le]; exact ⟨by simp [z]; linarith [hu.1.le], by simp [z]; linarith [hu.2]⟩
      have him : |(w + z - 4).im| ≤ |w.im| + T := by
        have him_eq : (w + z - 4).im = w.im + ε * T := by simp [z]
        rw [him_eq]
        exact (abs_add_le w.im (ε * T)).trans_eq (by rw [habsv])
      linarith
    have hL_bd : ‖DirichletCharacter.LFunction ψ (w + z)‖ ≤
        C_L * ((7 + |w.im|) + T) ^ (3 : ℕ) :=
      (hL_strip (w + z) hwz_lo hwz_hi).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm_sub4 3) hCL_pos.le)
    have hX_bd : ‖(X : ℂ) ^ z‖ ≤ X_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, show z.re = u by simp [z]]
      rcases le_total 1 X with h1X | h1X
      · exact (Real.rpow_le_rpow_of_exponent_le h1X hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hX h1X hu.1.le).trans (le_max_left _ _)
    have hker_bd : ‖smoothAFEGaussianKernel z‖ ≤ Real.exp 4 * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hz_re_sq : (z ^ 2).re = u ^ (2 : ℕ) - T ^ (2 : ℕ) := by
        dsimp only [z]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ (2 : ℕ) ≤ 4 := by
        have h1 : -1 ≤ u := ha_lo.trans hu.1.le
        have h2 : u ≤ 2 := hu.2.trans hb_hi
        nlinarith
      have hznorm1 : 1 ≤ ‖z‖ := by
        calc (1 : ℝ) ≤ T := hT
          _ = |z.im| := by simp [z, habsv]
          _ ≤ ‖z‖ := Complex.abs_im_le_norm z
      rw [hz_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hznorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    dsimp only [F]
    rw [norm_mul, norm_mul]
    calc ‖DirichletCharacter.LFunction ψ (w + z)‖ * ‖(X : ℂ) ^ z‖ * ‖smoothAFEGaussianKernel z‖
        ≤ (C_L * ((7 + |w.im|) + T) ^ (3 : ℕ)) * X_bd *
            (Real.exp 4 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hL_bd hX_bd (norm_nonneg _) (by positivity))
            hker_bd (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) ((Real.rpow_nonneg hX.le a).trans (le_max_left _ _))
      _ = K_h * (((7 + |w.im|) + T) ^ (3 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))) := by
          dsimp only [K_h]; ring
  have hvert_int : ∀ c : ℝ, c ≠ 0 → -1 ≤ c → c ≤ 2 →
      Integrable (fun v : ℝ => F ((c : ℂ) + (v : ℂ) * I)) := by
    intro c hc hc_lo hc_hi
    have hdom : Integrable (fun v : ℝ =>
        ((7 + |w.im|) + |v|) ^ (3 : ℕ) * Real.exp (-(v ^ (2 : ℕ)))) :=
      integrable_shifted_pow_mul_exp_neg_sq (7 + |w.im|) 3
    set K_c : ℝ := C_L * X ^ c * (Real.exp (c ^ (2 : ℕ)) / |c|)
    refine Integrable.mono' (hdom.const_mul K_c) ?_ (Filter.Eventually.of_forall fun v => ?_)
    · have hpath : Continuous (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) := by fun_prop
      have hcont : Continuous (fun v : ℝ => F ((c : ℂ) + (v : ℂ) * I)) := by
        rw [hF_eq]
        exact (hg_diff.continuous.comp hpath).mul
          ((hpath.sub continuous_const).inv₀ fun v h0 => hc (by simpa using congrArg Complex.re h0))
      exact hcont.aestronglyMeasurable
    · set z : ℂ := (c : ℂ) + (v : ℂ) * I
      have hwz_lo : (-2 : ℝ) ≤ (w + z).re := by simp [z]; linarith
      have hwz_hi : (w + z).re ≤ 3 := by simp [z]; linarith
      have hnorm_sub4 : ‖w + z - 4‖ ≤ (7 + |w.im|) + |v| := by
        have h1 := Complex.norm_le_abs_re_add_abs_im (w + z - 4)
        have hre : |(w + z - 4).re| ≤ 7 := by
          rw [abs_le]; exact ⟨by simp [z]; linarith, by simp [z]; linarith⟩
        have him : |(w + z - 4).im| ≤ |w.im| + |v| := by
          have him_eq : (w + z - 4).im = w.im + v := by simp [z]
          rw [him_eq]; exact abs_add_le w.im v
        linarith
      have hL_bd : ‖DirichletCharacter.LFunction ψ (w + z)‖ ≤
          C_L * ((7 + |w.im|) + |v|) ^ (3 : ℕ) :=
        (hL_strip (w + z) hwz_lo hwz_hi).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm_sub4 3) hCL_pos.le)
      have hX_eq : ‖(X : ℂ) ^ z‖ = X ^ c := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]; simp [z]
      have hker : ‖smoothAFEGaussianKernel z‖ ≤
          (Real.exp (c ^ (2 : ℕ)) / |c|) * Real.exp (-(v ^ (2 : ℕ))) := by
        rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
        have hz_re_sq : (z ^ 2).re = c ^ (2 : ℕ) - v ^ (2 : ℕ) := by
          dsimp only [z]
          simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        have hznorm : |c| ≤ ‖z‖ := by
          have h := Complex.abs_re_le_norm z; simpa [z] using h
        rw [hz_re_sq, sub_eq_add_neg, Real.exp_add]
        calc Real.exp (c ^ (2 : ℕ)) * Real.exp (-(v ^ (2 : ℕ))) / ‖z‖
            ≤ Real.exp (c ^ (2 : ℕ)) * Real.exp (-(v ^ (2 : ℕ))) / |c| :=
              div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hc) hznorm
          _ = (Real.exp (c ^ (2 : ℕ)) / |c|) * Real.exp (-(v ^ (2 : ℕ))) := by ring
      dsimp only [F]
      rw [norm_mul, norm_mul, hX_eq]
      calc ‖DirichletCharacter.LFunction ψ (w + z)‖ * X ^ c * ‖smoothAFEGaussianKernel z‖
          ≤ (C_L * ((7 + |w.im|) + |v|) ^ (3 : ℕ)) * X ^ c *
              ((Real.exp (c ^ (2 : ℕ)) / |c|) * Real.exp (-(v ^ (2 : ℕ)))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hL_bd (by positivity)) hker
              (norm_nonneg _) (by positivity)
        _ = K_c * (((7 + |w.im|) + |v|) ^ (3 : ℕ) * Real.exp (-(v ^ (2 : ℕ)))) := by
            dsimp only [K_c]; ring
  have hF_right_eq : ∀ v : ℝ,
      F ((b : ℂ) + (v : ℂ) * I) =
        ∑' m : ℕ, ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I) := by
    intro v
    have hre : 1 < (w + ((b : ℂ) + (v : ℂ) * I)).re := by simp; linarith
    have hsumL : LSeriesSummable (fun k : ℕ => ψ k) (w + ((b : ℂ) + (v : ℂ) * I)) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hre
    dsimp only [F]
    rw [DirichletCharacter.LFunction_eq_LSeries ψ hre, LSeries,
      ← hsumL.sum_add_tsum_nat_add 1, Finset.sum_range_one, LSeries.term_zero, zero_add,
      ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m), smoothAFEZetaMellinTerm, div_eq_mul_inv, one_div]
    push_cast; ring
  have hterm_b_int : ∀ m : ℕ,
      Integrable (fun v : ℝ => ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I)) :=
    fun m => (smoothAFEZetaMellinTerm_verticalIntegrable hX h0b m).const_mul _
  have hsum_b_norm : Summable (fun m : ℕ =>
      ∫ v : ℝ, ‖ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
      (summable_integral_norm_smoothAFEZetaMellinTerm hX h0b hwb)
    refine integral_mono_ae (hterm_b_int m).norm
      (smoothAFEZetaMellinTerm_verticalIntegrable hX h0b m).norm
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only; rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one (m + 1))
  have hint_b : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ, F ((b : ℂ) + (v : ℂ) * I)) =
      ∑' m : ℕ, ψ (m + 1) * (((m + 1 : ℕ) : ℂ) ^ (-w) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X)) := by
    have h1eq : (∫ v : ℝ, F ((b : ℂ) + (v : ℂ) * I)) =
        ∑' m : ℕ, ∫ v : ℝ, ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I) := by
      calc (∫ v : ℝ, F ((b : ℂ) + (v : ℂ) * I))
          = ∫ v : ℝ, ∑' m : ℕ, ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I) :=
            integral_congr_ae (Filter.Eventually.of_forall hF_right_eq)
        _ = ∑' m : ℕ, ∫ v : ℝ, ψ (m + 1) * smoothAFEZetaMellinTerm w X m ((b : ℂ) + (v : ℂ) * I) :=
            (MeasureTheory.integral_tsum_of_summable_integral_norm hterm_b_int hsum_b_norm).symm
    rw [h1eq, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [MeasureTheory.integral_const_mul,
      integral_smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegral hX,
      ← smoothAFECutoffAt_eq_smoothAFECutoff (div_pos (by exact_mod_cast Nat.succ_pos m) hX) h0b,
      smoothAFECutoffAt_eq_integral, Complex.real_smul]
    push_cast; ring
  have hlim_r := intervalIntegral_tendsto_integral
    (hvert_int b h0b.ne' (by linarith) hb_hi) tendsto_neg_atTop_atBot tendsto_id
  have hlim_l := intervalIntegral_tendsto_integral
    (hvert_int a ha0.ne ha_lo (by linarith)) tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_r.const_smul I)).sub (hlim_l.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F ((b : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F ((a : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * DirichletCharacter.LFunction ψ w := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, F ((b : ℂ) + (v : ℂ) * I)) - (∫ v : ℝ, F ((a : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * DirichletCharacter.LFunction ψ w := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hpi_ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hinv_pi : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
    push_cast; exact one_div_mul_cancel hpi_ne
  rw [← hint_b]
  have hmul := congrArg (fun z : ℂ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) * z) hcancel
  rw [mul_sub, ← mul_assoc, hinv_pi, one_mul] at hmul
  dsimp only [F] at hmul
  linear_combination hmul

/-- Multiplicative scale covariance of `dirichletDualGaussianCoeff`:
`d^{-(1 - s)} * dirichletDualGaussianCoeff P s (d * x) m = dirichletDualGaussianCoeff P s x (d * (m + 1) - 1)`. -/
theorem dirichletDualGaussianCoeff_mul_scale
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) {d : ℕ} (hd : 1 ≤ d)
    {x : ℝ} (hx : 0 < x) (s : ℂ) (m : ℕ) :
    (d : ℂ) ^ (-(1 - s)) * dirichletDualGaussianCoeff P s ((d : ℝ) * x) m =
      dirichletDualGaussianCoeff P s x (d * (m + 1) - 1) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_ne0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  unfold dirichletDualGaussianCoeff
  rw [← mul_assoc, mul_comm ((d : ℂ) ^ (-(1 - s))), mul_assoc, ← MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only [dirichletReflectedTerm]
  set w : ℂ := (-2 : ℂ) + (v : ℂ) * I
  have hdx : (((d : ℝ) * x : ℝ) : ℂ) ^ w = (d : ℂ) ^ w * (x : ℂ) ^ w := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hd_pos.le hx.le w, Complex.ofReal_natCast]
  have hd_exp : (d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ w = (d : ℂ) ^ (s + w - 1) := by
    rw [← Complex.cpow_add _ _ hd_ne0]; congr 1; ring
  have hdm : (d : ℂ) ^ (s + w - 1) * ((m + 1 : ℕ) : ℂ) ^ (s + w - 1) =
      ((d * (m + 1) - 1 + 1 : ℕ) : ℂ) ^ (s + w - 1) := by
    have hsub : d * (m + 1) - 1 + 1 = d * (m + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos hd (Nat.succ_pos m))
    rw [hsub, Nat.cast_mul, ← Complex.ofReal_natCast d, ← Complex.ofReal_natCast (m + 1),
      ← Complex.mul_cpow_ofReal_nonneg hd_pos.le hm_pos.le (s + w - 1)]
  rw [hdx]
  calc (d : ℂ) ^ (-(1 - s)) *
          (_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
            ((m + 1 : ℕ) : ℂ) ^ (s + w - 1) * ((d : ℂ) ^ w * (x : ℂ) ^ w) *
            smoothAFEGaussianKernel w)
      = _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
          (((d : ℂ) ^ (-(1 - s)) * (d : ℂ) ^ w) * ((m + 1 : ℕ) : ℂ) ^ (s + w - 1)) *
          (x : ℂ) ^ w * smoothAFEGaussianKernel w := by ring
    _ = _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
          ((d * (m + 1) - 1 + 1 : ℕ) : ℂ) ^ (s + w - 1) *
          (x : ℂ) ^ w * smoothAFEGaussianKernel w := by rw [hd_exp, hdm]

/-- **Exact critical-line residue extraction for `dirichletDualGaussianCoeff P s y 0`:**
for every `0 < Re s < 1 / 2` and `y > 0`, shifting `Re w = -2` rightward across `w = 0` onto
`Re w = 1 / 2 - Re s > 0` (`s + w = linePt (Im s + v)`) extracts
`-cglLemma62PrimitiveFunctionalFactor P s` plus the critical-line Gaussian integral where
`‖cglLemma62PrimitiveFunctionalFactor P (linePt (Im s + v))‖ = 1` identically. -/
theorem dirichletDualGaussianCoeff_zero_eq_neg_factor_add_criticalLine
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {y : ℝ} (hy : 0 < y) :
    dirichletDualGaussianCoeff P s y 0 =
      -_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
              (y : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by
  set a : ℝ := 1 / 2 - s.re
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ)))) := by
    simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
  have hisOpen_one : IsOpen {z : ℂ | z.re < 1} :=
    isOpen_lt Complex.continuous_re continuous_const
  set U_dom : Set ℂ := {w : ℂ | (s + w).re < 1}
  have hU_open : IsOpen U_dom :=
    isOpen_lt (Complex.continuous_re.comp (continuous_const.add continuous_id)) continuous_const
  set g : ℂ → ℂ := fun w =>
    _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w) *
      (y : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ))
  have hg_diff : DifferentiableOn ℂ g U_dom := by
    intro w hw
    haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
    have hd1 : DifferentiableAt ℂ
        (fun u => _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + u)) w :=
      ((differentiableOn_cglPrimitiveFunctionalFactor_re_lt_one P).analyticOnNhd hisOpen_one
        (s + w) hw).differentiableAt.comp w (differentiableAt_const s |>.add differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun u => (y : ℂ) ^ u) w :=
      (differentiable_const_cpow_of_neZero (y : ℂ)).differentiableAt
    have hd3 : DifferentiableAt ℂ (fun u => Complex.exp (u ^ (2 : ℕ))) w :=
      (differentiable_exp.comp (differentiable_pow 2)).differentiableAt
    exact ((hd1.mul hd2).mul hd3).differentiableWithinAt
  have hg_an : AnalyticOnNhd ℂ g U_dom := hg_diff.analyticOnNhd hU_open
  have hg_zero : g 0 = _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s := by
    dsimp only [g]; simp
  have hH_eq : dirichletReflectedTerm P s y 0 = fun w => g w * (w - 0)⁻¹ := by
    funext w
    unfold dirichletReflectedTerm smoothAFEGaussianKernel
    dsimp only [g]
    simp only [zero_add, Nat.cast_one, Complex.one_cpow, mul_one, sub_zero, div_eq_mul_inv]
    ring
  have hrect : ∀ T : ℝ, 0 < T →
      ((∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, dirichletReflectedTerm P s y 0 ((-2 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s := by
    intro T hT
    set z₁ : ℂ := (-2 : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (a : ℂ) + (T : ℂ) * I
    have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U_dom := by
      intro w hw
      rw [Complex.mem_reProdIm, show z₁.re = -2 by simp [z₁], show z₂.re = a by simp [z₂],
        uIcc_of_le (by linarith)] at hw
      show (s + w).re < 1
      rw [Complex.add_re]
      have hw_hi : w.re ≤ 1 / 2 - s.re := hw.1.2
      linarith
    have hbox := rectIntegral_cauchyFormula_analyticOnNhd hsub hg_an
      (p := 0) (by simp [z₁]) (by simp [z₂]; exact ha_pos)
      (by simp [z₁]; linarith) (by simp [z₂]; linarith)
    rw [← hH_eq, hg_zero] at hbox
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  obtain ⟨T₀_s, N_s, C_s, hCs_pos, hfac_strip⟩ :=
    exists_strip_poly_growth_cglPrimitiveFunctionalFactor P (s.re - 2) (by linarith)
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ =>
        ∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set Y_bd : ℝ := max (y ^ (-2 : ℝ)) (y ^ a)
    set K_sh : ℝ := C_s * Y_bd * Real.exp 4
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (1 + |s.im|) N_s).const_mul K_sh)
    filter_upwards [eventually_ge_atTop (max 1 (|T₀_s| + |s.im| + 2))] with T hT u hu
    rw [Set.uIoc_of_le (by linarith : (-2 : ℝ) ≤ a)] at hu
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hT_big : |T₀_s| + |s.im| + 2 ≤ T := (le_max_right _ _).trans hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos (zero_lt_one.trans_le hT1)]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hsw_re1 : s.re - 2 ≤ (s + w).re := by simp [w]; linarith [hu.1.le]
    have hsw_re2 : (s + w).re ≤ 1 / 2 := by
      simp [w]; have : u ≤ 1 / 2 - s.re := hu.2; linarith
    have hsw_im_ge : T₀_s ≤ |(s + w).im| := by
      rw [Complex.add_im, show w.im = ε * T by simp [w]]
      have htri : |ε * T| - |s.im| ≤ |s.im + ε * T| := by
        have h := abs_sub_abs_le_abs_sub (ε * T) (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      linarith [le_abs_self T₀_s]
    have hsw_im_le : 1 + |(s + w).im| ≤ (1 + |s.im|) + T := by
      calc 1 + |(s + w).im|
          = 1 + |s.im + ε * T| := by rw [Complex.add_im, show w.im = ε * T by simp [w]]
        _ ≤ 1 + (|s.im| + |ε * T|) := by linarith [abs_add_le s.im (ε * T)]
        _ = (1 + |s.im|) + T := by rw [habsv]; ring
    have hfac_bd : ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w)‖ ≤
        C_s * ((1 + |s.im|) + T) ^ N_s :=
      (hfac_strip (s + w) hsw_re1 hsw_re2 hsw_im_ge).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsw_im_le N_s) hCs_pos)
    have hy_le : ‖(y : ℂ) ^ w‖ ≤ Y_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, show w.re = u by simp [w]]
      rcases le_total 1 y with h1y | h1y
      · exact (Real.rpow_le_rpow_of_exponent_le h1y hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h1y hu.1.le).trans (le_max_left _ _)
    have hker_le : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 4 * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = u ^ (2 : ℕ) - T ^ (2 : ℕ) := by
        dsimp only [w]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ (2 : ℕ) ≤ 4 := by
        have h1 : -2 ≤ u := hu.1.le
        have h2 : u ≤ 1 := hu.2.trans (by dsimp only [a]; linarith)
        nlinarith
      have hwnorm1 : 1 ≤ ‖w‖ := by
        calc (1 : ℝ) ≤ T := hT1
          _ = |w.im| := by simp [w, habsv]
          _ ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [hw_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hwnorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    unfold dirichletReflectedTerm
    simp only [zero_add, Nat.cast_one, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul]
    calc ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (s + w)‖ *
            ‖(y : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
        ≤ (C_s * ((1 + |s.im|) + T) ^ N_s) * Y_bd *
            (Real.exp 4 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hfac_bd hy_le (norm_nonneg _) (by positivity))
            hker_le (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) ((Real.rpow_nonneg hy.le (-2)).trans (le_max_left _ _))
      _ = K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))) := by
          dsimp only [K_sh]; ring
  have hsw_lp : ∀ v : ℝ, s + ((a : ℂ) + (v : ℂ) * I) = linePt (s.im + v) := fun v => by
    unfold linePt; dsimp only [a]; apply Complex.ext <;> simp
  have hnorm_crit : ∀ u : ℝ,
      ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt u)‖ = 1 := fun u => by
    have heq : linePt u = (_root_.RHTower.cglLemma62CriticalPoint u).value := by
      unfold linePt _root_.RHTower.cglLemma62CriticalPoint
      apply Complex.ext <;> simp
    rw [heq]
    exact _root_.RHTower.cglLemma62_primitiveFunctionalFactor_critical_norm_one P
      (_root_.RHTower.cglLemma62CriticalPoint u)
  have hpt_right : ∀ v : ℝ,
      ‖dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I)‖ ≤
        (y ^ a * (Real.exp (a ^ (2 : ℕ)) / a)) * Real.exp (-(v ^ (2 : ℕ))) := by
    intro v
    have hfac_v : ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P
        (s + ((a : ℂ) + (v : ℂ) * I))‖ = 1 := by
      rw [hsw_lp v]; exact hnorm_crit (s.im + v)
    have hker_v := norm_smoothAFEGaussianKernel_vertical_le ha_pos v
    unfold dirichletReflectedTerm
    simp only [zero_add, Nat.cast_one, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul, hfac_v, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      show (((a : ℂ) + (v : ℂ) * I).re) = a by simp]
    exact (mul_le_mul_of_nonneg_left hker_v (by positivity)).trans_eq (by ring)
  have hright_int : Integrable (fun v : ℝ =>
      dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I)) := by
    refine Integrable.mono' (hgauss_int.const_mul (y ^ a * (Real.exp (a ^ (2 : ℕ)) / a))) ?_
      (Filter.Eventually.of_forall hpt_right)
    have hcont : Continuous (fun v : ℝ =>
        dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I)) := by
      rw [hH_eq]
      have hpath : Continuous (fun v : ℝ => (a : ℂ) + (v : ℂ) * I) := by fun_prop
      have hg_v : Continuous (fun v : ℝ => g ((a : ℂ) + (v : ℂ) * I)) := by
        refine hg_an.continuousOn.comp_continuous hpath fun v => ?_
        show (s + ((a : ℂ) + (v : ℂ) * I)).re < 1
        simp [a]; norm_num
      have hinv_v : Continuous (fun v : ℝ => (((a : ℂ) + (v : ℂ) * I) - 0)⁻¹) :=
        (hpath.sub continuous_const).inv₀ fun v h0 =>
          ha_ne (by simpa using congrArg Complex.re h0)
      exact hg_v.mul hinv_v
    exact hcont.aestronglyMeasurable
  have hleft_int := (dirichletReflectedTerm_left_two_integrable_and_summable P hs0 hhi hy).1 0
  have hlim_r := intervalIntegral_tendsto_integral hright_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_l := intervalIntegral_tendsto_integral hleft_int tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T =>
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_r.const_smul I)).sub (hlim_l.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-2 : ℝ)..a, dirichletReflectedTerm P s y 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, dirichletReflectedTerm P s y 0 ((-2 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I)) -
        (∫ v : ℝ, dirichletReflectedTerm P s y 0 ((-2 : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hint_a_eq :
      (∫ v : ℝ, dirichletReflectedTerm P s y 0 ((a : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ,
          _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
            (y : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only [dirichletReflectedTerm]
    simp only [zero_add, Nat.cast_one, Complex.one_cpow, mul_one]
    have hlp := hsw_lp v
    dsimp only [a] at hlp ⊢
    rw [hlp]
  have hpi_ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hinv_pi : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
    push_cast; exact one_div_mul_cancel hpi_ne
  unfold dirichletDualGaussianCoeff
  rw [← hint_a_eq]
  linear_combination
    -((((1 / (2 * Real.pi) : ℝ) : ℂ)) * hcancel) -
      _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s * hinv_pi

/-- **Exact critical-line residue extraction for `dirichletDualGaussianCoeff P s x (k - 1)` (`k ≥ 1`):**
cancelling `Re s` inside `k^{-(1 - s)} * (k x)^{(1/2 - Re s) + i v}` isolates `-factor(s) * k^{-(1 - s)}`
plus the `L`-free critical-line integral of `k^{-conj (linePt (Im s + v))}`. -/
theorem dirichletDualGaussianCoeff_eq_neg_factor_mul_add_criticalLine
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {x : ℝ} (hx : 0 < x)
    {k : ℕ} (hk1 : 1 ≤ k) :
    dirichletDualGaussianCoeff P s x (k - 1) =
      -_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s * (k : ℂ) ^ (-(1 - s)) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
              (k : ℂ) ^ (-conj (linePt (s.im + v))) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_ne0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hscale := dirichletDualGaussianCoeff_mul_scale P hk1 hx s 0
  rw [zero_add, mul_one] at hscale
  rw [← hscale,
    dirichletDualGaussianCoeff_zero_eq_neg_factor_add_criticalLine P hs0 hhi (mul_pos hk_pos hx)]
  have hpull :
      (k : ℂ) ^ (-(1 - s)) *
        (-_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ,
              _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
                (((k : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) =
        -_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s * (k : ℂ) ^ (-(1 - s)) +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ((k : ℂ) ^ (-(1 - s)) *
              ∫ v : ℝ,
                _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
                  (((k : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                  smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) := by ring
  rw [hpull, ← MeasureTheory.integral_const_mul]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  set z : ℂ := ((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I
  have hkx : (((k : ℝ) * x : ℝ) : ℂ) ^ z = (k : ℂ) ^ z * (x : ℂ) ^ z := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk_pos.le hx.le z, Complex.ofReal_natCast]
  have hk_exp : (k : ℂ) ^ (-(1 - s)) * (k : ℂ) ^ z = (k : ℂ) ^ (-conj (linePt (s.im + v))) := by
    rw [← Complex.cpow_add _ _ hk_ne0]
    congr 1
    rw [conj_linePt]
    unfold linePt
    dsimp only [z]
    apply Complex.ext <;> simp
  rw [hkx]
  calc (k : ℂ) ^ (-(1 - s)) *
          (_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
            ((k : ℂ) ^ z * (x : ℂ) ^ z) * smoothAFEGaussianKernel z)
      = (x : ℂ) ^ z * smoothAFEGaussianKernel z *
          _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
          ((k : ℂ) ^ (-(1 - s)) * (k : ℂ) ^ z) := by ring
    _ = (x : ℂ) ^ z * smoothAFEGaussianKernel z *
          _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
          (k : ℂ) ^ (-conj (linePt (s.im + v))) := by rw [hk_exp]

/-- Pure unweighted `χ`-twisted balanced Vaughan bilinear Dirichlet polynomial
`∑_{(U + 1)(V + 1) ≤ k ≤ K_hi} χ(k) (vaughanDualBilinear U V k) k^{-z}`. -/
def twistedBalancedBilinearDirichletPoly
    {q : ℕ} (χ : DirichletCharacter ℂ q) (U V K_hi : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
    χ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) * (k : ℂ) ^ (-z)

/-- Complete multiplicativity collapses the `χ`-twisted Vaughan Type-II divisor sum at any `k : ℕ`
to `χ k * vaughanDualBilinear U V k`. -/
theorem twisted_vaughanTypeII_divisor_sum_eq
    {q : ℕ} (χ : DirichletCharacter ℂ q) (U V k : ℕ) :
    (∑ d ∈ k.divisors,
        χ d * ((((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) d : ℝ)) : ℂ) * χ (k / d)) =
      χ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) := by
  set F : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
      _root_.RHTower.Sieve.typeIIShort V
  have hpt : ∀ d ∈ k.divisors,
      χ d * ((F d : ℝ) : ℂ) * χ (k / d) = χ k * ((F d : ℝ) : ℂ) := by
    intro d hd
    have hdk : d * (k / d) = k := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hmul_χ : χ d * χ (k / d) = χ k := by
      rw [← map_mul, ← Nat.cast_mul, hdk]
    linear_combination ((F d : ℝ) : ℂ) * hmul_χ
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, ← Complex.ofReal_sum]
  congr 2
  dsimp only [F]
  rw [← zeta_mul_vaughanTypeIICoeff_eq_vaughanDualBilinear U V,
    ArithmeticFunction.coe_zeta_mul_apply]

/-- **Exact `L`-free decomposition of the finite `ψ⁻¹`-twisted balanced Vaughan dual band:**
for every primitive nonprincipal `P`, `0 < Re s < 1 / 2`, `x > 0`, and `U, V, K_hi : ℕ`, the finite
dual Vaughan band equals `-factor(s) * D_{ψ⁻¹, U, V, K_hi}(1 - s)` plus the Gaussian-weighted
critical-line integral of `D_{ψ⁻¹, U, V, K_hi}(conj (linePt (Im s + v)))`. -/
theorem twisted_vaughan_dual_band_eq_offLine_add_criticalLine
    (P : _root_.RHTower.CGLLemma62PrimitiveCharacter) (U V K_hi : ℕ)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
    (∑ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
        P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) *
          dirichletDualGaussianCoeff P s x (k - 1)) =
      -_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s *
          twistedBalancedBilinearDirichletPoly P.character⁻¹ U V K_hi (1 - s) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v)) *
              twistedBalancedBilinearDirichletPoly P.character⁻¹ U V K_hi
                (conj (linePt (s.im + v))) := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  set S : Finset ℕ := Finset.Icc ((U + 1) * (V + 1)) K_hi
  have hk_ge1 : ∀ k ∈ S, 1 ≤ k := fun k hk => by
    have hlo : (U + 1) * (V + 1) ≤ k := (Finset.mem_Icc.mp hk).1
    have h1 : 1 ≤ (U + 1) * (V + 1) := Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)
    exact h1.trans hlo
  set a : ℝ := 1 / 2 - s.re
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  set pref : ℝ → ℂ := fun v =>
    (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
      smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
      _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v))
  have hnorm_crit : ∀ u : ℝ,
      ‖_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt u)‖ = 1 := fun u => by
    have heq : linePt u = (_root_.RHTower.cglLemma62CriticalPoint u).value := by
      unfold linePt _root_.RHTower.cglLemma62CriticalPoint
      apply Complex.ext <;> simp
    rw [heq]
    exact _root_.RHTower.cglLemma62_primitiveFunctionalFactor_critical_norm_one P
      (_root_.RHTower.cglLemma62CriticalPoint u)
  have hpref_int : Integrable pref := by
    have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ)))) := by
      simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
    refine Integrable.mono' (hgauss_int.const_mul (x ^ a * (Real.exp (a ^ (2 : ℕ)) / a))) ?_
      (Filter.Eventually.of_forall fun v => ?_)
    · have hpath : Continuous (fun v : ℝ => ((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by fun_prop
      have hx_c : Continuous (fun v : ℝ => (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) :=
        Continuous.const_cpow hpath (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      have hker_c : Continuous (fun v : ℝ =>
          smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) := by
        unfold smoothAFEGaussianKernel
        exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v h0 =>
          ha_ne (by simpa [a] using congrArg Complex.re h0)
      have hfac_c : Continuous (fun v : ℝ =>
          _root_.RHTower.cglLemma62PrimitiveFunctionalFactor P (linePt (s.im + v))) := by
        refine (differentiableOn_cglPrimitiveFunctionalFactor_re_lt_one P).continuousOn.comp_continuous
          (by unfold linePt; fun_prop) fun v => ?_
        show (linePt (s.im + v)).re < 1
        unfold linePt; simp; norm_num
      exact ((hx_c.mul hker_c).mul hfac_c).aestronglyMeasurable
    · dsimp only [pref]
      rw [norm_mul, norm_mul, hnorm_crit (s.im + v), mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hx,
        show ((((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I).re) = a by simp [a]]
      exact (mul_le_mul_of_nonneg_left (norm_smoothAFEGaussianKernel_vertical_le ha_pos v)
        (by positivity)).trans_eq (by ring)
  have hterm_int : ∀ k ∈ S, Integrable (fun v : ℝ =>
      pref v * (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) *
        (k : ℂ) ^ (-conj (linePt (s.im + v))))) := by
    intro k hk
    have hk1 := hk_ge1 k hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    set B_k : ℝ := ‖P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ)‖ *
      (k : ℝ) ^ (-(1 / 2 : ℝ))
    refine Integrable.mono' (hpref_int.norm.const_mul B_k) ?_ (Filter.Eventually.of_forall fun v => ?_)
    · have hk_c : Continuous (fun v : ℝ => (k : ℂ) ^ (-conj (linePt (s.im + v)))) :=
        Continuous.const_cpow (by unfold linePt; fun_prop) (Or.inl (by exact_mod_cast (by omega : k ≠ 0)))
      exact (hpref_int.1.mul (continuous_const.mul hk_c).aestronglyMeasurable)
    · rw [norm_mul (pref v), norm_mul (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ)),
        ← Complex.ofReal_natCast k, Complex.norm_cpow_eq_rpow_re_of_pos hk_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; unfold linePt; simp; norm_num]
      dsimp only [B_k]
      exact (by ring : ‖pref v‖ * (‖P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ)‖ *
        (k : ℝ) ^ (-(1 / 2 : ℝ))) = B_k * ‖pref v‖).le
  have hsum_step :
      (∑ k ∈ S, P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) *
          dirichletDualGaussianCoeff P s x (k - 1)) =
        (∑ k ∈ S, -_root_.RHTower.cglLemma62PrimitiveFunctionalFactor P s *
            (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) * (k : ℂ) ^ (-(1 - s)))) +
          ∑ k ∈ S, (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, pref v * (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) *
              (k : ℂ) ^ (-conj (linePt (s.im + v)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [dirichletDualGaussianCoeff_eq_neg_factor_mul_add_criticalLine P hs0 hhi hx (hk_ge1 k hk)]
    have hpull :
        (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ)) *
          ∫ v : ℝ, pref v * (k : ℂ) ^ (-conj (linePt (s.im + v))) =
        ∫ v : ℝ, pref v * (P.character⁻¹ k * ((vaughanDualBilinear U V k : ℝ) : ℂ) *
          (k : ℂ) ^ (-conj (linePt (s.im + v)))) := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)
    dsimp only [pref] at hpull ⊢
    linear_combination (((1 / (2 * Real.pi) : ℝ) : ℂ)) * hpull
  rw [hsum_step]
  congr 1
  · rw [← Finset.mul_sum]; rfl
  · rw [← Finset.mul_sum, ← integral_finsetSum S hterm_int]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only [pref]
    rw [← Finset.mul_sum]
    rfl

end Part1PoleFreeTwistedDirichletCrossHeightVaughanDuality


/-! ### Part 2: Complete Smooth-Rough Vaughan Annihilation and Sub-Horizon `χ^j` Trig-Polynomial Positivity -/

section Part2SmoothRoughAnnihilationAndTrigPolynomialPositivity

/-- **Exact smooth-times-rough annihilation law for `typeIIShort`:**
for every `W ≥ 1`, every integer `s` with `2 ≤ s ≤ W`, and every `W`-rough integer `r ≥ 1`
(`IsRoughAbove W r`, regardless of `Ω(r)`), `typeIIShort W (s * r) = 0` identically. -/
theorem typeIIShort_smooth_mul_rough_eq_zero
    {W s r : ℕ} (_hW : 1 ≤ W) (hs2 : 2 ≤ s) (hsW : s ≤ W) (hr1 : 1 ≤ r)
    (hrough : IsRoughAbove W r) :
    _root_.RHTower.Sieve.typeIIShort W (s * r) = 0 := by
  have hsr2 : 2 ≤ s * r := by nlinarith
  have hsub :
      ((1 : ArithmeticFunction ℝ) -
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) (s * r) =
      (1 : ArithmeticFunction ℝ) (s * r) -
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) (s * r) := rfl
  change ((1 : ArithmeticFunction ℝ) -
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W) (s * r) = 0
  rw [hsub, ArithmeticFunction.one_apply, if_neg (by omega : ¬ s * r = 1),
    ArithmeticFunction.coe_zeta_mul_apply]
  have hdiv_s : s.divisors ⊆ (s * r).divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) r, by omega⟩
  have hsum_eq :
      (∑ d ∈ (s * r).divisors,
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) W d) =
      ∑ d ∈ s.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    rw [← Finset.sum_subset hdiv_s]
    · refine Finset.sum_congr rfl fun d hd => ?_
      have hds : d ≤ s := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
      rw [_root_.RHTower.Sieve.truncAF_apply, if_pos (hds.trans hsW)]
      rfl
    · intro d hd hnot_s
      by_cases hdW : d ≤ W
      · exfalso
        have hdsr : d ∣ s * r := Nat.dvd_of_mem_divisors hd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdsr (by omega)
        have hcop : Nat.Coprime d r := by
          by_contra hnc
          set g : ℕ := Nat.gcd d r
          have hp : Nat.Prime g.minFac := Nat.minFac_prime hnc
          have hpg : g.minFac ∣ g := Nat.minFac_dvd g
          have hpd : g.minFac ∣ d := dvd_trans hpg (Nat.gcd_dvd_left d r)
          have hpr : g.minFac ∣ r := dvd_trans hpg (Nat.gcd_dvd_right d r)
          have hp_le_d : g.minFac ≤ d := Nat.le_of_dvd hd_pos hpd
          have hW_lt_p : W < g.minFac := hrough g.minFac hp hpr
          omega
        exact hnot_s (Nat.mem_divisors.mpr ⟨hcop.dvd_of_dvd_mul_right hdsr, by omega⟩)
      · rw [_root_.RHTower.Sieve.truncAF_apply, if_neg hdW]
  have hmoeb_zero : (∑ d ∈ s.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    have hzm : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) s =
        (1 : ArithmeticFunction ℝ) s := by
      rw [mul_comm]
      exact congrArg (fun f : ArithmeticFunction ℝ => f s)
        ArithmeticFunction.coe_moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
      if_neg (by omega : ¬ s = 1)] at hzm
    exact hzm
  rw [hsum_eq, hmoeb_zero, sub_zero]

/-- **Exact smooth-times-rough annihilation law for `vaughanDualBilinear U V`:**
for all `U, V ≥ 1`, every `2 ≤ s ≤ min U V`, and every `max U V`-rough `r ≥ 1` (even when `r` has
arbitrarily many prime factors `> max U V`), `vaughanDualBilinear U V (s * r) = 0` identically. -/
theorem vaughanDualBilinear_smooth_mul_rough_eq_zero
    {U V s r : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hs2 : 2 ≤ s) (hs_min : s ≤ min U V)
    (hr1 : 1 ≤ r) (hrough : IsRoughAbove (max U V) r) :
    vaughanDualBilinear U V (s * r) = 0 := by
  unfold vaughanDualBilinear
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hprod : p.1 * p.2 = s * r := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hp1_pos : 0 < p.1 := by
    by_contra h0; have hz : p.1 = 0 := by omega
    rw [hz, zero_mul] at hprod; nlinarith
  set s₁ : ℕ := Nat.gcd p.1 s
  have hs₁_pos : 0 < s₁ := Nat.gcd_pos_of_pos_left s hp1_pos
  obtain ⟨r₁, hr₁_eq⟩ : s₁ ∣ p.1 := Nat.gcd_dvd_left p.1 s
  obtain ⟨s₂, hs₂_eq⟩ : s₁ ∣ s := Nat.gcd_dvd_right p.1 s
  have hr₁_pos : 1 ≤ r₁ := by
    by_contra h0; have hz : r₁ = 0 := by omega
    rw [hz, mul_zero] at hr₁_eq; nlinarith
  have hs₂_pos : 1 ≤ s₂ := by
    by_contra h0; have hz : s₂ = 0 := by omega
    rw [hz, mul_zero] at hs₂_eq; nlinarith
  have hcancel1 : r₁ * p.2 = s₂ * r := by
    apply Nat.eq_of_mul_eq_mul_left hs₁_pos
    calc s₁ * (r₁ * p.2) = (s₁ * r₁) * p.2 := (mul_assoc s₁ r₁ p.2).symm
      _ = p.1 * p.2 := by rw [← hr₁_eq]
      _ = s * r := hprod
      _ = (s₁ * s₂) * r := by rw [← hs₂_eq]
      _ = s₁ * (s₂ * r) := mul_assoc s₁ s₂ r
  have hr₁_rough : IsRoughAbove (max U V) r₁ := by
    intro q hq hq_r₁
    have hnot_s₂ : ¬ (q ∣ s₂) := by
      intro hq_s₂
      obtain ⟨c₁, hc₁⟩ := hq_r₁
      obtain ⟨c₂, hc₂⟩ := hq_s₂
      have hdvd1 : s₁ * q ∣ p.1 := ⟨c₁, by rw [hr₁_eq, hc₁]; ring⟩
      have hdvd2 : s₁ * q ∣ s := ⟨c₂, by rw [hs₂_eq, hc₂]; ring⟩
      have hdvd_g : s₁ * q ∣ s₁ := Nat.dvd_gcd hdvd1 hdvd2
      have hle_g : s₁ * q ≤ s₁ := Nat.le_of_dvd hs₁_pos hdvd_g
      have hq2 : 2 ≤ q := hq.two_le
      nlinarith
    have hq_mul : q ∣ s₂ * r := by
      rw [← hcancel1]
      exact dvd_mul_of_dvd_left hq_r₁ p.2
    have hq_r : q ∣ r := (hq.dvd_mul.mp hq_mul).resolve_left hnot_s₂
    exact hrough q hq hq_r
  have hcop_r₁_s₂ : Nat.Coprime r₁ s₂ := by
    by_contra hnc
    set g : ℕ := Nat.gcd r₁ s₂
    have hq : Nat.Prime g.minFac := Nat.minFac_prime hnc
    have hq_r₁ : g.minFac ∣ r₁ := dvd_trans (Nat.minFac_dvd g) (Nat.gcd_dvd_left r₁ s₂)
    have hq_s₂ : g.minFac ∣ s₂ := dvd_trans (Nat.minFac_dvd g) (Nat.gcd_dvd_right r₁ s₂)
    have hq_gt : max U V < g.minFac := hr₁_rough g.minFac hq hq_r₁
    have hq_le_s₂ : g.minFac ≤ s₂ := Nat.le_of_dvd hs₂_pos hq_s₂
    have hs₂_le_s : s₂ ≤ s := Nat.le_of_dvd (by omega) ⟨s₁, by rw [mul_comm]; exact hs₂_eq⟩
    have hs_le_max : s ≤ max U V := hs_min.trans (min_le_left U V |>.trans (le_max_left U V))
    omega
  have hs₂_dvd_p2 : s₂ ∣ p.2 :=
    hcop_r₁_s₂.symm.dvd_of_dvd_mul_left ⟨r, hcancel1⟩
  obtain ⟨r₂, hr₂_eq⟩ := hs₂_dvd_p2
  have hr₁r₂_eq : r₁ * r₂ = r := by
    apply Nat.eq_of_mul_eq_mul_left hs₂_pos
    calc s₂ * (r₁ * r₂) = r₁ * (s₂ * r₂) := by ring
      _ = r₁ * p.2 := by rw [← hr₂_eq]
      _ = s₂ * r := hcancel1
  have hr₂_pos : 1 ≤ r₂ := by
    by_contra h0; have hz : r₂ = 0 := by omega
    rw [hz, mul_zero] at hr₁r₂_eq; nlinarith
  have hr₂_rough : IsRoughAbove (max U V) r₂ :=
    hrough.of_dvd ⟨r₁, by rw [mul_comm]; exact hr₁r₂_eq.symm⟩
  have hs₁_or_s₂ : 2 ≤ s₁ ∨ 2 ≤ s₂ := by
    by_contra hboth
    push Not at hboth
    have hs₁_eq1 : s₁ = 1 := by omega
    have hs₂_eq1 : s₂ = 1 := by omega
    rw [hs₁_eq1, hs₂_eq1, one_mul] at hs₂_eq
    omega
  rcases hs₁_or_s₂ with hs₁_ge2 | hs₂_ge2
  · have hs₁_le_U : s₁ ≤ U :=
      (Nat.le_of_dvd (by omega) ⟨s₂, hs₂_eq⟩).trans (hs_min.trans (min_le_left U V))
    rw [hr₁_eq, typeIIShort_smooth_mul_rough_eq_zero hU hs₁_ge2 hs₁_le_U hr₁_pos
      (hr₁_rough.mono (le_max_left U V)), zero_mul]
  · have hs₂_le_V : s₂ ≤ V :=
      (Nat.le_of_dvd (by omega) ⟨s₁, by rw [mul_comm]; exact hs₂_eq⟩).trans
        (hs_min.trans (min_le_right U V))
    rw [hr₂_eq, typeIIShort_smooth_mul_rough_eq_zero hV hs₂_ge2 hs₂_le_V hr₂_pos
      (hr₂_rough.mono (le_max_right U V)), mul_zero]

/-- A modulus `q : ℕ` contains all sub-horizon primes up to `W` if every prime `p ≤ W` divides `q`. -/
def HasSubHorizonPrimeModulus (W q : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≤ W → p ∣ q

/-- Every integer `k` coprime to a modulus `q` with `HasSubHorizonPrimeModulus W q` is
automatically `W`-rough. -/
lemma isRoughAbove_of_coprime_of_hasSubHorizonPrimeModulus
    {W q k : ℕ} (hmod : HasSubHorizonPrimeModulus W q) (hcop : Nat.Coprime k q) :
    IsRoughAbove W k := by
  intro p hp hpk
  by_contra hle
  push Not at hle
  have hpq : p ∣ q := hmod p hp hle
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpk hpq
  exact hp.not_dvd_one hp1

/-- **Universal multi-power `χ^j` trigonometric-polynomial positivity under sub-horizon prime removal:**
whenever `HasSubHorizonPrimeModulus (max U V) q` (`U, V ≥ 1`), every integer `k ≥ 2` coprime to `q`
is `max U V`-rough (`vaughanDualBilinear U V k = d(k) - 2 ≥ 0`) while every non-coprime `k` has
`((χ⁻¹) ^ j) k = 0` for **all** `j ≥ 0` (including `j = 0`). Hence for **every** nonnegative cosine
polynomial `∑_{j=0}^m c_j cos(j θ) ≥ 0` and **all** `σ₁, T ∈ ℝ` and `K_hi : ℕ`,
`∑_{j=0}^m c_j Re D_{(χ⁻¹)^j, U, V, K_hi}(σ₁ + i j T) ≥ 0`. -/
theorem trigPoly_twistedBalancedBilinearDirichletPoly_re_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (K_hi : ℕ)
    (hmod : HasSubHorizonPrimeModulus (max U V) q)
    {m : ℕ} {c : ℕ → ℝ}
    (hpos : ∀ θ : ℝ, 0 ≤ ∑ j ∈ Finset.range (m + 1), c j * Real.cos ((j : ℝ) * θ))
    (σ₁ T : ℝ) :
    0 ≤ ∑ j ∈ Finset.range (m + 1),
      c j * (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ j) U V K_hi
        ((σ₁ : ℂ) + (((j : ℝ) * T : ℝ) : ℂ) * I)).re := by
  unfold twistedBalancedBilinearDirichletPoly
  simp_rw [Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun k hk => ?_
  have hk_ge4 : 4 ≤ k := by
    have hlo : (U + 1) * (V + 1) ≤ k := (Finset.mem_Icc.mp hk).1
    nlinarith
  have hk_ge2 : 2 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  by_cases hcop : Nat.Coprime k q
  · have hu : IsUnit (k : ZMod q) := (ZMod.isUnit_iff_coprime k q).mpr hcop
    have hrough : IsRoughAbove (max U V) k :=
      isRoughAbove_of_coprime_of_hasSubHorizonPrimeModulus hmod hcop
    have hv_eq : vaughanDualBilinear U V k = (k.divisors.card : ℝ) - 2 :=
      vaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hk_ge2 hrough
    have hv_nn : 0 ≤ vaughanDualBilinear U V k := by
      by_cases hp : Nat.Prime k
      · rw [hv_eq, hp.divisors, Finset.card_pair hp.ne_one.symm]; norm_num
      · linarith [one_le_vaughanDualBilinear_of_composite_rough hU hV hk_ge2 hp hrough]
    have hnorm1 : ‖χ⁻¹ (k : ZMod q)‖ = 1 :=
      _root_.RHTower.norm_dirichletCharacter_apply χ⁻¹ hu
    set θ_k : ℝ := Complex.arg (χ⁻¹ (k : ZMod q)) - T * Real.log (k : ℝ)
    have hχ_exp : χ⁻¹ (k : ZMod q) = Complex.exp ((Complex.arg (χ⁻¹ (k : ZMod q)) : ℂ) * I) := by
      have h := Complex.norm_mul_exp_arg_mul_I (χ⁻¹ (k : ZMod q))
      rw [hnorm1, Complex.ofReal_one, one_mul] at h
      exact h.symm
    have hterm_re : ∀ j : ℕ,
        (((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) *
            ((vaughanDualBilinear U V k : ℝ) : ℂ) *
            (k : ℂ) ^ (-((σ₁ : ℂ) + (((j : ℝ) * T : ℝ) : ℂ) * I))).re =
          (vaughanDualBilinear U V k * (k : ℝ) ^ (-σ₁)) * Real.cos ((j : ℝ) * θ_k) := by
      intro j
      obtain ⟨u_k, hu_eq⟩ := hu
      have hpow_j : ((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) =
          (χ⁻¹ (k : ZMod q)) ^ j := by
        rw [← hu_eq, MulChar.pow_apply_coe]
      have hk_cpow : (k : ℂ) ^ (-((σ₁ : ℂ) + (((j : ℝ) * T : ℝ) : ℂ) * I)) =
          (((k : ℝ) ^ (-σ₁) : ℝ) : ℂ) *
            Complex.exp (((-(j : ℝ) * T * Real.log (k : ℝ) : ℝ) : ℂ) * I) := by
        rw [← Complex.ofReal_natCast k,
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk_pos.ne'),
          ← Complex.ofReal_log hk_pos.le, Real.rpow_def_of_pos hk_pos, Complex.ofReal_exp,
          ← Complex.exp_add]
        congr 1; push_cast; ring
      have hchi_j_exp : (χ⁻¹ (k : ZMod q)) ^ j =
          Complex.exp ((((j : ℝ) * Complex.arg (χ⁻¹ (k : ZMod q)) : ℝ) : ℂ) * I) := by
        conv_lhs => rw [hχ_exp]
        rw [← Complex.exp_nat_mul]
        congr 1; push_cast; ring
      rw [hpow_j, hchi_j_exp, hk_cpow]
      have hcomb_exp :
          Complex.exp ((((j : ℝ) * Complex.arg (χ⁻¹ (k : ZMod q)) : ℝ) : ℂ) * I) *
            ((vaughanDualBilinear U V k : ℝ) : ℂ) *
            ((((k : ℝ) ^ (-σ₁) : ℝ) : ℂ) *
              Complex.exp (((-(j : ℝ) * T * Real.log (k : ℝ) : ℝ) : ℂ) * I)) =
          (((vaughanDualBilinear U V k * (k : ℝ) ^ (-σ₁) : ℝ) : ℂ)) *
            Complex.exp ((((j : ℝ) * θ_k : ℝ) : ℂ) * I) := by
        have hexp_add :
            Complex.exp ((((j : ℝ) * Complex.arg (χ⁻¹ (k : ZMod q)) : ℝ) : ℂ) * I) *
              Complex.exp (((-(j : ℝ) * T * Real.log (k : ℝ) : ℝ) : ℂ) * I) =
            Complex.exp ((((j : ℝ) * θ_k : ℝ) : ℂ) * I) := by
          rw [← Complex.exp_add]; congr 1; dsimp only [θ_k]; push_cast; ring
        calc Complex.exp ((((j : ℝ) * Complex.arg (χ⁻¹ (k : ZMod q)) : ℝ) : ℂ) * I) *
                ((vaughanDualBilinear U V k : ℝ) : ℂ) *
                ((((k : ℝ) ^ (-σ₁) : ℝ) : ℂ) *
                   Complex.exp (((-(j : ℝ) * T * Real.log (k : ℝ) : ℝ) : ℂ) * I))
            = (((vaughanDualBilinear U V k : ℝ) : ℂ) * (((k : ℝ) ^ (-σ₁) : ℝ) : ℂ)) *
                (Complex.exp ((((j : ℝ) * Complex.arg (χ⁻¹ (k : ZMod q)) : ℝ) : ℂ) * I) *
                  Complex.exp (((-(j : ℝ) * T * Real.log (k : ℝ) : ℝ) : ℂ) * I)) := by ring
          _ = (((vaughanDualBilinear U V k * (k : ℝ) ^ (-σ₁) : ℝ) : ℂ)) *
                Complex.exp ((((j : ℝ) * θ_k : ℝ) : ℂ) * I) := by
              rw [hexp_add, Complex.ofReal_mul]
              push_cast; ring
      rw [hcomb_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero]
      ring
    have hsum_k :
        (∑ j ∈ Finset.range (m + 1),
            c j * (((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) *
              ((vaughanDualBilinear U V k : ℝ) : ℂ) *
              (k : ℂ) ^ (-((σ₁ : ℂ) + (((j : ℝ) * T : ℝ) : ℂ) * I))).re) =
          (vaughanDualBilinear U V k * (k : ℝ) ^ (-σ₁)) *
            ∑ j ∈ Finset.range (m + 1), c j * Real.cos ((j : ℝ) * θ_k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hterm_re j]; ring
    rw [hsum_k]
    exact mul_nonneg (mul_nonneg hv_nn (Real.rpow_nonneg hk_pos.le _)) (hpos θ_k)
  · have hnu : ¬ IsUnit (k : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime k q).mp hu)
    refine Finset.sum_nonneg fun j _ => ?_
    have hz : ((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) = 0 :=
      MulChar.map_nonunit (χ⁻¹ ^ j) hnu
    rw [hz, zero_mul, zero_mul, Complex.zero_re, mul_zero]

/-- **De la Vallée Poussin `3 ± 4 cos + cos 2` positivity on `twistedBalancedBilinearDirichletPoly`:**
both `3 + 4 Re D_{χ⁻¹}(σ₁ + i T) + Re D_{χ⁻²}(σ₁ + 2 i T)` and its antiphase partner
`3 - 4 Re D_{χ⁻¹}(σ₁ + i T) + Re D_{χ⁻²}(σ₁ + 2 i T)` are unconditionally `≥ 0` across all
`σ₁, T ∈ ℝ` whenever `HasSubHorizonPrimeModulus (max U V) q`. -/
theorem deLaValleePoussin_both_signs_twistedBalancedBilinear_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (K_hi : ℕ)
    (hmod : HasSubHorizonPrimeModulus (max U V) q) (σ₁ T : ℝ) :
    0 ≤ 3 * (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (0 : ℕ)) U V K_hi (σ₁ : ℂ)).re +
          4 * (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (1 : ℕ)) U V K_hi
            ((σ₁ : ℂ) + (T : ℂ) * I)).re +
          (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (2 : ℕ)) U V K_hi
            ((σ₁ : ℂ) + ((2 * T : ℝ) : ℂ) * I)).re ∧
    0 ≤ 3 * (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (0 : ℕ)) U V K_hi (σ₁ : ℂ)).re -
          4 * (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (1 : ℕ)) U V K_hi
            ((σ₁ : ℂ) + (T : ℂ) * I)).re +
          (twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ (2 : ℕ)) U V K_hi
            ((σ₁ : ℂ) + ((2 * T : ℝ) : ℂ) * I)).re := by
  set c_plus : ℕ → ℝ := fun j => if j = 0 then 3 else if j = 1 then 4 else 1
  set c_minus : ℕ → ℝ := fun j => if j = 0 then 3 else if j = 1 then -4 else 1
  have hcp0 : c_plus 0 = 3 := rfl
  have hcp1 : c_plus 1 = 4 := rfl
  have hcp2 : c_plus 2 = 1 := rfl
  have hcm0 : c_minus 0 = 3 := rfl
  have hcm1 : c_minus 1 = -4 := rfl
  have hcm2 : c_minus 2 = 1 := rfl
  have hpos_plus : ∀ θ : ℝ, 0 ≤ ∑ j ∈ Finset.range 3, c_plus j * Real.cos ((j : ℝ) * θ) := by
    intro θ
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hcp0, hcp1, hcp2]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, Nat.cast_one, one_mul,
      Nat.cast_ofNat, Real.cos_two_mul]
    nlinarith [sq_nonneg (1 + Real.cos θ)]
  have hpos_minus : ∀ θ : ℝ, 0 ≤ ∑ j ∈ Finset.range 3, c_minus j * Real.cos ((j : ℝ) * θ) := by
    intro θ
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hcm0, hcm1, hcm2]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, Nat.cast_one, one_mul,
      Nat.cast_ofNat, Real.cos_two_mul]
    nlinarith [sq_nonneg (1 - Real.cos θ)]
  have h1 := trigPoly_twistedBalancedBilinearDirichletPoly_re_nonneg χ hU hV K_hi hmod hpos_plus σ₁ T
  have h2 := trigPoly_twistedBalancedBilinearDirichletPoly_re_nonneg χ hU hV K_hi hmod hpos_minus σ₁ T
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hcp0, hcp1, hcp2] at h1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hcm0, hcm1, hcm2] at h2
  simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, add_zero, Nat.cast_one, one_mul,
    Nat.cast_ofNat] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Exact cyclic order-`n` character orthogonality identity and kernel divisor positivity:**
for any character `χ` of order dividing `n ≥ 1` (`χ ^ n = 1`) on a modulus `q` with
`HasSubHorizonPrimeModulus (max U V) q`, averaging `twistedBalancedBilinearDirichletPoly ((χ⁻¹)^j)`
over `0 ≤ j < n` isolates the `χ(k) = 1` rough kernel with strictly nonnegative divisor weights
`d(k) - 2 ≥ 0`. -/
theorem cyclic_orthogonality_twistedBalancedBilinear_eq_ker_rough_divisors
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn1 : 1 ≤ n) (hord : χ ^ n = 1)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (K_hi : ℕ)
    (hmod : HasSubHorizonPrimeModulus (max U V) q) (σ₁ : ℝ) :
    (((1 / (n : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Finset.range n,
          twistedBalancedBilinearDirichletPoly ((χ⁻¹) ^ j) U V K_hi (σ₁ : ℂ)) =
      (((∑ k ∈ (Finset.Icc ((U + 1) * (V + 1)) K_hi).filter
            (fun k => Nat.Coprime k q ∧ χ k = 1),
          ((k.divisors.card : ℝ) - 2) * (k : ℝ) ^ (-σ₁) : ℝ) : ℂ)) ∧
    0 ≤ ∑ k ∈ (Finset.Icc ((U + 1) * (V + 1)) K_hi).filter
          (fun k => Nat.Coprime k q ∧ χ k = 1),
        ((k.divisors.card : ℝ) - 2) * (k : ℝ) ^ (-σ₁) := by
  have hn_ne0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine ⟨?_, ?_⟩
  · unfold twistedBalancedBilinearDirichletPoly
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_ge2 : 2 ≤ k := by
      have hlo := (Finset.mem_Icc.mp hk).1
      nlinarith
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk_cpow : (k : ℂ) ^ (-(σ₁ : ℂ)) = (((k : ℝ) ^ (-σ₁) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast k, ← Complex.ofReal_neg,
        Complex.ofReal_cpow hk_pos.le]
    by_cases hcop : Nat.Coprime k q
    · obtain ⟨u_k, hu_eq⟩ := (ZMod.isUnit_iff_coprime k q).mpr hcop
      have hrough := isRoughAbove_of_coprime_of_hasSubHorizonPrimeModulus hmod hcop
      have hv_eq := vaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hk_ge2 hrough
      have hsum_j :
          (∑ j ∈ Finset.range n,
              ((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) *
                ((vaughanDualBilinear U V k : ℝ) : ℂ) * (k : ℂ) ^ (-(σ₁ : ℂ))) =
            (∑ j ∈ Finset.range n, (χ⁻¹ (k : ZMod q)) ^ j) *
              ((((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) * (((k : ℝ) ^ (-σ₁) : ℝ) : ℂ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hu_eq, MulChar.pow_apply_coe, hv_eq, hk_cpow]
        ring
      rw [hsum_j]
      by_cases hχ1 : χ (k : ZMod q) = 1
      · rw [if_pos ⟨hcop, hχ1⟩]
        have hinv1 : χ⁻¹ (k : ZMod q) = 1 := by
          rw [MulChar.inv_apply_eq_inv', hχ1, inv_one]
        rw [hinv1]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast
        field_simp [hn_ne0]
      · rw [if_neg (fun h => hχ1 h.2), Complex.ofReal_zero]
        have hinv_ne1 : χ⁻¹ (k : ZMod q) ≠ 1 := fun h1 => hχ1 (by
          rw [MulChar.inv_apply_eq_inv', inv_eq_one] at h1; exact h1)
        have hχn1 : (χ (k : ZMod q)) ^ n = 1 := by
          have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ (u_k : ZMod q)) hord
          rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hu_eq] at h
          exact h
        have hzn1 : (χ⁻¹ (k : ZMod q)) ^ n = 1 := by
          rw [MulChar.inv_apply_eq_inv', inv_pow, hχn1, inv_one]
        have hgeom : (∑ j ∈ Finset.range n, (χ⁻¹ (k : ZMod q)) ^ j) = 0 := by
          have hm := geom_sum_mul (χ⁻¹ (k : ZMod q)) n
          rw [hzn1, sub_self] at hm
          exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hinv_ne1)
        rw [hgeom, zero_mul, mul_zero]
    · have hnu : ¬ IsUnit (k : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime k q).mp hu)
      rw [if_neg (fun h => hcop h.1), Complex.ofReal_zero]
      have hz_sum : (∑ j ∈ Finset.range n,
          ((χ⁻¹ ^ j : DirichletCharacter ℂ q) (k : ZMod q)) *
            ((vaughanDualBilinear U V k : ℝ) : ℂ) * (k : ℂ) ^ (-(σ₁ : ℂ))) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [MulChar.map_nonunit (χ⁻¹ ^ j) hnu, zero_mul, zero_mul]
      rw [hz_sum, mul_zero]
  · refine Finset.sum_nonneg fun k hk => ?_
    obtain ⟨hk_Icc, hcop, _⟩ := Finset.mem_filter.mp hk
    have hk_ge2 : 2 ≤ k := by have hlo := (Finset.mem_Icc.mp hk_Icc).1; nlinarith
    have hrough := isRoughAbove_of_coprime_of_hasSubHorizonPrimeModulus hmod hcop
    have hv_eq := vaughanDualBilinear_eq_divisors_sub_two_of_rough hU hV hk_ge2 hrough
    have hv_nn : 0 ≤ (k.divisors.card : ℝ) - 2 := by
      rw [← hv_eq]
      by_cases hp : Nat.Prime k
      · rw [hv_eq, hp.divisors, Finset.card_pair hp.ne_one.symm]; norm_num
      · linarith [one_le_vaughanDualBilinear_of_composite_rough hU hV hk_ge2 hp hrough]
    exact mul_nonneg hv_nn (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- Generating `LSeries` of the `W`-rough multiplicative subsemigroup on `Re w > 1`. -/
def roughZetaSeries (W : ℕ) (w : ℂ) : ℂ :=
  LSeries (fun n : ℕ =>
    by classical exact if 1 ≤ n ∧ IsRoughAbove W n then (1 : ℂ) else 0) w

/-- **Exact rough-semigroup mollifier-square `LSeries` identity (`(ζ_W(w) - 1)^2`):**
on `{w : ℂ | 1 < Re w}`, the Dirichlet series of `1_{k ≥ 2 ∧ IsRoughAbove W k} · (d(k) - 2)`
converges unconditionally and equals `(roughZetaSeries W w - 1) ^ 2`. -/
theorem LSeries_rough_divisors_sub_two_eq_sq
    (W : ℕ) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun k : ℕ =>
      by classical exact if 2 ≤ k ∧ IsRoughAbove W k
        then (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) else 0) w ∧
    LSeries (fun k : ℕ =>
      by classical exact if 2 ≤ k ∧ IsRoughAbove W k
        then (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) else 0) w =
      (roughZetaSeries W w - 1) ^ (2 : ℕ) := by
  classical
  set f₁ : ℕ → ℂ := fun n => if 1 ≤ n ∧ IsRoughAbove W n then 1 else 0
  set f₂ : ℕ → ℂ := fun n => if 2 ≤ n ∧ IsRoughAbove W n then 1 else 0
  have hf₁_sum : LSeriesSummable f₁ w := by
    refine Summable.of_norm_bounded (LSeriesSummable_one_iff.mpr hw).norm fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0, norm_div, norm_div]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      dsimp only [f₁]
      split_ifs <;> simp
  have hdelta_sum : LSeriesSummable LSeries.delta w :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      rw [LSeries.term_delta, if_neg (Finset.notMem_singleton.mp hn)]
  have hf₂_eq : f₂ = f₁ - LSeries.delta := by
    ext n
    dsimp only [f₂, f₁, Pi.sub_apply, LSeries.delta]
    rcases n with _ | _ | m
    · simp
    · have hr1 : IsRoughAbove W 1 := fun p hp hp1 => False.elim (hp.not_dvd_one hp1)
      simp [hr1]
    · have hge2 : 2 ≤ m + 2 := by omega
      have hge1 : 1 ≤ m + 2 := by omega
      simp [hge2, hge1]
  have hf₂_sum : LSeriesSummable f₂ w := hf₂_eq ▸ hf₁_sum.sub hdelta_sum
  have hl_f₂ : LSeries f₂ w = roughZetaSeries W w - 1 := by
    rw [hf₂_eq, LSeries_sub hf₁_sum hdelta_sum,
      show LSeries LSeries.delta w = 1 by simpa using congrFun LSeries_delta w]
    unfold roughZetaSeries
    congr 2
  have hconv_eq :
      (fun k : ℕ => if 2 ≤ k ∧ IsRoughAbove W k then (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) else 0) =
        LSeries.convolution f₂ f₂ := by
    ext k
    rw [LSeries.convolution_def]
    dsimp only
    rcases k with _ | _ | m
    · simp [f₂]
    · simp [f₂]
    · set k₀ : ℕ := m + 2
      have hk2 : 2 ≤ k₀ := by omega
      by_cases hrough : IsRoughAbove W k₀
      · rw [if_pos ⟨hk2, hrough⟩]
        set E : Finset (ℕ × ℕ) := {(1, k₀), (k₀, 1)}
        have hpair_ne : ((1 : ℕ), k₀) ≠ (k₀, 1) := fun h => by
          have h1 := congrArg Prod.fst h; dsimp only at h1; omega
        have hE_sub : E ⊆ k₀.divisorsAntidiagonal := fun x hx => by
          simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul k₀, by omega⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one k₀, by omega⟩
        have hsum_E : (∑ p ∈ E, f₂ p.1 * f₂ p.2) = 0 := by
          dsimp only [E, f₂]
          rw [Finset.sum_pair hpair_ne]
          simp
        have hpt_sdiff : ∀ p ∈ k₀.divisorsAntidiagonal \ E, f₂ p.1 * f₂ p.2 = 1 := by
          intro p hp
          obtain ⟨hp_mem, hp_notE⟩ := Finset.mem_sdiff.mp hp
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hp_mem).1
          have hp1_ne0 : p.1 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; omega
          have hp2_ne0 : p.2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hprod; omega
          have hp1_ne1 : p.1 ≠ 1 := fun h1 => hp_notE (by
            simp only [E, Finset.mem_insert, Finset.mem_singleton]
            exact Or.inl (Prod.ext h1 (by rw [h1, one_mul] at hprod; exact hprod)))
          have hp2_ne1 : p.2 ≠ 1 := fun h1 => hp_notE (by
            simp only [E, Finset.mem_insert, Finset.mem_singleton]
            exact Or.inr (Prod.ext (by rw [h1, mul_one] at hprod; exact hprod) h1))
          have hr1 : IsRoughAbove W p.1 := hrough.of_dvd ⟨p.2, hprod.symm⟩
          have hr2 : IsRoughAbove W p.2 := hrough.of_dvd ⟨p.1, by rw [mul_comm]; exact hprod.symm⟩
          dsimp only [f₂]
          rw [if_pos ⟨by omega, hr1⟩, if_pos ⟨by omega, hr2⟩, mul_one]
        rw [← Finset.sum_sdiff hE_sub, hsum_E, add_zero, Finset.sum_congr rfl hpt_sdiff]
        have hcard_sdiff :
            (∑ _p ∈ k₀.divisorsAntidiagonal \ E, (1 : ℂ)) = (k₀.divisors.card : ℂ) - 2 := by
          have h1 :
              (∑ _p ∈ k₀.divisorsAntidiagonal \ E, (1 : ℂ)) + (∑ _p ∈ E, (1 : ℂ)) =
                ∑ _p ∈ k₀.divisorsAntidiagonal, (1 : ℂ) := Finset.sum_sdiff hE_sub
          have h2 : (∑ _p ∈ E, (1 : ℂ)) = 2 := by
            dsimp only [E]; rw [Finset.sum_pair hpair_ne]; norm_num
          have h3 : (∑ _p ∈ k₀.divisorsAntidiagonal, (1 : ℂ)) = (k₀.divisors.card : ℂ) := by
            rw [Finset.sum_const, _root_.RHTower.Sieve.card_divisorsAntidiagonal, nsmul_eq_mul,
              mul_one]
          rw [h2, h3] at h1
          linear_combination h1
        rw [hcard_sdiff]
        push_cast
        ring
      · rw [if_neg (fun h => hrough h.2)]
        symm
        refine Finset.sum_eq_zero fun p hp => ?_
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
        dsimp only [f₂]
        by_cases h1 : 2 ≤ p.1 ∧ IsRoughAbove W p.1
        · by_cases h2 : 2 ≤ p.2 ∧ IsRoughAbove W p.2
          · exfalso
            refine hrough fun q hq hqk => ?_
            rw [← hprod] at hqk
            rcases hq.dvd_mul.mp hqk with hq1 | hq2
            · exact h1.2 q hq hq1
            · exact h2.2 q hq hq2
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
  have hgoal_eq :
      (fun k : ℕ =>
        by classical exact if 2 ≤ k ∧ IsRoughAbove W k
          then (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) else 0) =
      (fun k : ℕ => if 2 ≤ k ∧ IsRoughAbove W k then (((k.divisors.card : ℝ) - 2 : ℝ) : ℂ) else 0) := by
    ext k; split_ifs <;> rfl
  rw [hgoal_eq, hconv_eq]
  exact ⟨hf₂_sum.convolution hf₂_sum,
    by rw [LSeries_convolution' hf₂_sum hf₂_sum, hl_f₂, sq]⟩

end Part2SmoothRoughAnnihilationAndTrigPolynomialPositivity


/-! ### Part 3: The `u₀`-Roughened Cubic-Probe LP Breaking `40535 / 46328` (`3001 / 24000`) -/

section Part3RoughenedVertexLPBreakthroughBelowSubSevenEighths

open Budget

/-- Bilinear-affine row count exponent obtained when plain witness cofactors on `(0, u₀)` are
removed at `t_* = 1`. -/
def roughenedRowCount (δ x u₀ : ℝ) : ℝ :=
  1 - (4 / 9) * δ * x - δ * (2 - 8 * x / 9) * u₀

/-- Exact plain-marked fiber count exponent `1 - 2 δ m - 2 (δ x) z(m)` (`Δ = 0`, `z(m) = (2/9)(1 - 2m)`)
from `DetectorRawFibers.Fiber.plain_marked_count`. -/
def plainMarkedFiberExp (δ x m : ℝ) : ℝ :=
  1 - 2 * δ * m - 2 * (δ * x) * ((2 / 9) * (1 - 2 * m))

theorem plainMarkedFiberExp_eq_roughenedRowCount (δ x m : ℝ) :
    plainMarkedFiberExp δ x m = roughenedRowCount δ x m := by
  unfold plainMarkedFiberExp roughenedRowCount
  ring

/-- **Exact slot-supply feasibility (`0 ≤ z ≤ 7 / 37`) on `[11 / 148, 1 / 2]`:**
for every `m ∈ [11 / 148, 1 / 2]`, the optimal plain-slot capacity `z = (2 / 9) * (1 - 2 * m)`
satisfies `0 ≤ z ≤ 7 / 37` and `2 * m + 6 * (3 / 4) * z = 1`. -/
theorem plainMarked_slot_capacity_feasible {m : ℝ} (hm_lo : 11 / 148 ≤ m) (hm_hi : m ≤ 1 / 2) :
    let z : ℝ := (2 / 9) * (1 - 2 * m)
    0 ≤ z ∧ z ≤ 7 / 37 ∧ 2 * m + 6 * (3 / 4) * z = 1 := by
  dsimp only
  exact ⟨by linarith, by linarith, by ring⟩

/-- **Exact `u₀`-roughened witness branch domination at `t_* = 1`:**
for all `0 ≤ δ`, `x ≤ 1 / 2`, and `0 ≤ u₀ ≤ 1 / 2`, every zero witness pair `(r, m)` at `t_* = 1`
(`1 ≤ r + m`, `r ≤ 1`) with sub-horizon plain scales `(0, u₀)` removed (`m = 0 ∨ u₀ ≤ m ≤ 1 / 2`)
has count exponent at most `roughenedRowCount δ x u₀`. -/
theorem roughened_witness_branch_domination
    {δ x u₀ r m : ℝ} (hδ0 : 0 ≤ δ) (hx : x ≤ 1 / 2) (_hu₀_nn : 0 ≤ u₀) (hu₀_hi : u₀ ≤ 1 / 2)
    (hrm : 1 ≤ r + m) (hr1 : r ≤ 1)
    (_hsupp : m = 0 ∨ (u₀ ≤ m ∧ m ≤ 1 / 2)) :
    (m = 0 → r = 1 ∧ rowLong δ 1 ≤ roughenedRowCount δ x u₀) ∧
    (u₀ ≤ m ∧ m ≤ 1 / 2 → plainMarkedFiberExp δ x m ≤ roughenedRowCount δ x u₀) := by
  have hslope_pos : 0 ≤ 2 - 8 * x / 9 := by linarith
  refine ⟨fun hm0 => ?_, fun ⟨hmu, _hm_half⟩ => ?_⟩
  · have hr_eq : r = 1 := by linarith
    refine ⟨hr_eq, ?_⟩
    unfold rowLong roughenedRowCount
    have h1 : δ * (2 - 8 * x / 9) * u₀ ≤ δ * (2 - 8 * x / 9) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hu₀_hi (mul_nonneg hδ0 hslope_pos)
    linarith
  · rw [plainMarkedFiberExp_eq_roughenedRowCount]
    unfold roughenedRowCount
    have h1 : δ * (2 - 8 * x / 9) * u₀ ≤ δ * (2 - 8 * x / 9) * m :=
      mul_le_mul_of_nonneg_left hmu (mul_nonneg hδ0 hslope_pos)
    linarith

/-- **Exact crossing thresholds at the three Farkas barrier bins (`5/13`, `79/204`, `16/41`):**
at full prime amplitude `x = 1 / 2`, `roughenedRowCount δ (1 / 2) u₀ < rowCount δ (1 / 2)` holds if
and only if `20 / 49 < u₀`, `29 / 71 < u₀`, and `2198 / 5377 < u₀` respectively. -/
theorem roughened_farkas_bin_crossing_thresholds (u₀ : ℝ) :
    (roughenedRowCount (5 / 13) (1 / 2) u₀ < rowCount (5 / 13) (1 / 2) ↔ 20 / 49 < u₀) ∧
    (roughenedRowCount (79 / 204) (1 / 2) u₀ < rowCount (79 / 204) (1 / 2) ↔ 29 / 71 < u₀) ∧
    (roughenedRowCount (16 / 41) (1 / 2) u₀ < rowCount (16 / 41) (1 / 2) ↔ 2198 / 5377 < u₀) := by
  rw [rowCount_five_thirteenths, rowCount_binding, rowCount_sixteen_fortyfirsts]
  unfold roughenedRowCount
  exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- **Exact three-corner convex decomposition of `endpointExponent` under `roughenedRowCount`:**
across `(δ, x) ∈ [0, 5 / 6] × [0, 1 / 2]`, `endpointExponent lx ly ℓ σ₀ δ (x * δ) (roughenedRowCount δ x u₀)`
is an exact convex combination with weights `(1 - 6δ/5, (6δ/5)(1 - 2x), 12δx/5)` of the three
corners `(0, 0)`, `(5 / 6, 0)`, and `(5 / 6, 1 / 2)`. -/
theorem endpointExponent_roughened_three_corner_identity (lx ly ℓ σ₀ δ x u₀ : ℝ) :
    endpointExponent lx ly ℓ σ₀ δ (x * δ) (roughenedRowCount δ x u₀) =
      (1 - (6 / 5) * δ) *
          endpointExponent lx ly ℓ σ₀ 0 0 (roughenedRowCount 0 0 u₀) +
        ((6 / 5) * δ * (1 - 2 * x)) *
          endpointExponent lx ly ℓ σ₀ (5 / 6) 0 (roughenedRowCount (5 / 6) 0 u₀) +
        ((12 / 5) * δ * x) *
          endpointExponent lx ly ℓ σ₀ (5 / 6) (5 / 12) (roughenedRowCount (5 / 6) (1 / 2) u₀) := by
  unfold endpointExponent roughenedRowCount
  ring

theorem endpointExponent_roughened_le_max_three_corners
    {lx ly ℓ σ₀ δ x u₀ B : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2)
    (hc0 : endpointExponent lx ly ℓ σ₀ 0 0 (roughenedRowCount 0 0 u₀) ≤ B)
    (hc1 : endpointExponent lx ly ℓ σ₀ (5 / 6) 0 (roughenedRowCount (5 / 6) 0 u₀) ≤ B)
    (hc2 : endpointExponent lx ly ℓ σ₀ (5 / 6) (5 / 12)
      (roughenedRowCount (5 / 6) (1 / 2) u₀) ≤ B) :
    endpointExponent lx ly ℓ σ₀ δ (x * δ) (roughenedRowCount δ x u₀) ≤ B := by
  have hw0 : 0 ≤ 1 - (6 / 5) * δ := by linarith
  have hw1 : 0 ≤ (6 / 5) * δ * (1 - 2 * x) := mul_nonneg (by linarith) (by linarith)
  have hw2 : 0 ≤ (12 / 5) * δ * x := mul_nonneg (by linarith) hx0
  rw [endpointExponent_roughened_three_corner_identity]
  calc (1 - (6 / 5) * δ) * endpointExponent lx ly ℓ σ₀ 0 0 (roughenedRowCount 0 0 u₀) +
          ((6 / 5) * δ * (1 - 2 * x)) *
            endpointExponent lx ly ℓ σ₀ (5 / 6) 0 (roughenedRowCount (5 / 6) 0 u₀) +
          ((12 / 5) * δ * x) *
            endpointExponent lx ly ℓ σ₀ (5 / 6) (5 / 12) (roughenedRowCount (5 / 6) (1 / 2) u₀)
      ≤ (1 - (6 / 5) * δ) * B + ((6 / 5) * δ * (1 - 2 * x)) * B + ((12 / 5) * δ * x) * B :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hc0 hw0) (mul_le_mul_of_nonneg_left hc1 hw1))
          (mul_le_mul_of_nonneg_left hc2 hw2)
    _ = B := by ring

/-- Parametric optimal slot scale `ℓ(u₀) = (35 u₀ - 4) / (36 + 63 u₀)` of the `u₀`-roughened LP. -/
def roughenedOptSlot (u₀ : ℝ) : ℝ := (35 * u₀ - 4) / (36 + 63 * u₀)

/-- Parametric `x`-row scale `lx(u₀) = (13 ℓ(u₀) - 1) / 4`. -/
def roughenedOptLx (u₀ : ℝ) : ℝ := (13 * roughenedOptSlot u₀ - 1) / 4

/-- Parametric `y`-row scale `ly(u₀) = (5 - 17 ℓ(u₀)) / 4`. -/
def roughenedOptLy (u₀ : ℝ) : ℝ := (5 - 17 * roughenedOptSlot u₀) / 4

/-- **Parametric breakthrough below the `40535 / 46328` Farkas barrier across all
`u₀ ∈ (16556 / 40519, 1 / 2]`:**
whereas `TheTrueVertexBelowSevenEighths.endpointExponent_three_bin_pos_of_lowBoundaryGen_le` proves
`lowBoundaryGen ≤ 40535 / 46328` is impossible over all `(lx, ly, ℓ) ∈ ℝ³` under `rowCount`, for
**every** `u₀ ∈ (16556 / 40519, 1 / 2]` the scales `(roughenedOptLx u₀, roughenedOptLy u₀, roughenedOptSlot u₀)`
achieve `lowBoundaryGen < 40535 / 46328` while keeping `endpointExponent ≤ 0` across **every**
balanced bin `(δ, x) ∈ [0, 5 / 6] × [0, 1 / 2]` and **every** high bin `5 / 6 ≤ δ ≤ 1`, `q ≤ δ / 2`. -/
theorem roughened_LP_breaks_farkas_barrier_of_gt_threshold
    {u₀ : ℝ} (hu₀_lo : 16556 / 40519 < u₀) (hu₀_hi : u₀ ≤ 1 / 2) :
    let lx := roughenedOptLx u₀
    let ly := roughenedOptLy u₀
    let ℓ := roughenedOptSlot u₀
    lowBoundaryGen lx ly ℓ < 40535 / 46328 ∧
    (∀ {δ x : ℝ}, 0 ≤ δ → δ ≤ 5 / 6 → 0 ≤ x → x ≤ 1 / 2 →
      endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) δ (x * δ)
        (roughenedRowCount δ x u₀) ≤ 0) ∧
    (∀ {δ q : ℝ}, 5 / 6 ≤ δ → δ ≤ 1 → q ≤ δ / 2 →
      0 ≤ ℓ ∧ endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) δ q (1 - δ) ≤ 0) := by
  dsimp only
  have hden_pos : 0 < 36 + 63 * u₀ := by linarith
  have hrel : (36 + 63 * u₀) * roughenedOptSlot u₀ = 35 * u₀ - 4 := by
    unfold roughenedOptSlot
    exact mul_div_cancel₀ (35 * u₀ - 4) hden_pos.ne'
  have hℓ_pos : 0 < roughenedOptSlot u₀ := by
    unfold roughenedOptSlot
    exact div_pos (by linarith) hden_pos
  have hℓ_le : roughenedOptSlot u₀ ≤ 1 / 5 := by
    unfold roughenedOptSlot
    rw [div_le_iff₀ hden_pos]
    linarith
  have hlx_le_ly : roughenedOptLx u₀ ≤ roughenedOptLy u₀ := by
    unfold roughenedOptLx roughenedOptLy
    linarith
  have hlb_eq : lowBoundaryGen (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀) =
      11 / 12 - roughenedOptSlot u₀ / 4 := by
    rw [lowBoundaryGen_eq_of_le _ hlx_le_ly]
    unfold lowBoundary roughenedOptLx roughenedOptLy
    rw [show (13 * roughenedOptSlot u₀ - 1) / 4 + (5 - 17 * roughenedOptSlot u₀) / 4 +
        roughenedOptSlot u₀ - 1 = 0 by ring, max_self]
    ring
  have hlb_lt :
      lowBoundaryGen (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀) <
        40535 / 46328 := by
    rw [hlb_eq]
    have hgt : 5797 / 34746 < roughenedOptSlot u₀ := by
      unfold roughenedOptSlot
      rw [lt_div_iff₀ hden_pos]
      linarith
    linarith
  have hc0 : endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
      (11 / 12 - roughenedOptSlot u₀ / 4) 0 0 (roughenedRowCount 0 0 u₀) = 0 := by
    unfold endpointExponent roughenedRowCount roughenedOptLx roughenedOptLy
    ring
  have hc2 : endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
      (11 / 12 - roughenedOptSlot u₀ / 4) (5 / 6) (5 / 12)
      (roughenedRowCount (5 / 6) (1 / 2) u₀) = 0 := by
    unfold endpointExponent roughenedRowCount roughenedOptLx roughenedOptLy
    linear_combination (5 / 108 : ℝ) * hrel
  have hc1 : endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
      (11 / 12 - roughenedOptSlot u₀ / 4) (5 / 6) 0
      (roughenedRowCount (5 / 6) 0 u₀) ≤ 0 := by
    have hid : (36 + 63 * u₀) *
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) (5 / 6) 0
          (roughenedRowCount (5 / 6) 0 u₀) = (140 - 415 * u₀) / 12 := by
      unfold endpointExponent roughenedRowCount roughenedOptLx roughenedOptLy
      linear_combination (5 / 6 + 15 * u₀ / 4) * hrel
    have hprod_np : (36 + 63 * u₀) *
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) (5 / 6) 0
          (roughenedRowCount (5 / 6) 0 u₀) ≤ 0 := by
      rw [hid]; linarith
    exact nonpos_of_mul_nonpos_right hprod_np hden_pos
  refine ⟨hlb_lt, fun hδ0 hδ hx0 hx => ?_, fun {δ q} hδ0 _hδ1 hq => ⟨hℓ_pos.le, ?_⟩⟩
  · rw [hlb_eq]
    exact endpointExponent_roughened_le_max_three_corners hδ0 hδ hx0 hx hc0.le hc1 hc2.le
  · rw [hlb_eq]
    have hdiff_q :
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ q (1 - δ) -
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ (δ / 2) (1 - δ) =
        -(δ / 2 - q) * roughenedOptSlot u₀ := by
      unfold endpointExponent
      ring
    have hmono_q :
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ q (1 - δ) ≤
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ (δ / 2) (1 - δ) := by
      have hnn : 0 ≤ (δ / 2 - q) * roughenedOptSlot u₀ :=
        mul_nonneg (by linarith) hℓ_pos.le
      linarith
    have hid_hi :
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ (δ / 2) (1 - δ) =
        ((3 / 4) * δ) * (5 * roughenedOptSlot u₀ - 1) := by
      unfold endpointExponent roughenedOptLx roughenedOptLy
      ring
    have hhi_np :
        endpointExponent (roughenedOptLx u₀) (roughenedOptLy u₀) (roughenedOptSlot u₀)
          (11 / 12 - roughenedOptSlot u₀ / 4) δ (δ / 2) (1 - δ) ≤ 0 := by
      rw [hid_hi]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact hmono_q.trans hhi_np

/-- **Explicit strictly-negative `u₀ = 3 / 7` certificate at `σ₀ = 131 / 150 < 40535 / 46328`
(reflected `ζ`-wall `19 / 150 > 3001 / 24000`):**
at `(lx, ly, ℓ) = (19 / 60, 51 / 100, 13 / 75)`, `lowBoundary = lowBoundaryGen = 131 / 150`,
`probeThetaGen 6 = 112 / 125 < 8999 / 10000`, `tupleExponent_reflectedAllowance ≤ 0`, and
`endpointExponent ≤ -(1 / 900)` across all `[0, 5 / 6] × [0, 1 / 2]` and `≤ -(49 / 600)` across
all `[5 / 6, 1]` (plus `rowExponent` negativity across `d ≤ 257 / 300 + ζ`). -/
theorem roughened_three_sevenths_certificate :
    lowBoundary (19 / 60) (51 / 100) (13 / 75) = 131 / 150 ∧
    lowBoundaryGen (19 / 60) (51 / 100) (13 / 75) = 131 / 150 ∧
    probeThetaGen 6 (19 / 60) (51 / 100) (13 / 75) = 112 / 125 ∧
    (131 / 150 : ℝ) < 40535 / 46328 ∧
    (131 / 150 : ℝ) < 8733458561 / 10000000000 ∧
    (3001 / 24000 : ℝ) < 1 - 131 / 150 ∧
    (∀ {d : ℝ}, 0 ≤ d → tupleExponent d (reflectedAllowance (19 / 60 + 51 / 100) (13 / 75) d) ≤ 0) ∧
    (∀ {δ x d ζ : ℝ}, 0 ≤ δ → δ ≤ 5 / 6 → 0 ≤ x → x ≤ 1 / 2 → 0 ≤ ζ → d ≤ 257 / 300 + ζ →
      endpointExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) δ (x * δ)
        (roughenedRowCount δ x (3 / 7)) ≤ -(1 / 900) ∧
      rowExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) (17 / 50) δ (x * δ)
        (roughenedRowCount δ x (3 / 7)) d ≤ -(1 / 900) + 2 * ζ) ∧
    (∀ {δ q : ℝ}, 5 / 6 ≤ δ → δ ≤ 1 → q ≤ δ / 2 →
      endpointExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) δ q (1 - δ) ≤ -(49 / 600)) := by
  have hlb : lowBoundary (19 / 60) (51 / 100) (13 / 75) = 131 / 150 := by
    unfold lowBoundary
    rw [show (19 : ℝ) / 60 + 51 / 100 + 13 / 75 - 1 = 0 by ring, max_self]
    norm_num
  have hlb_gen : lowBoundaryGen (19 / 60) (51 / 100) (13 / 75) = 131 / 150 := by
    rw [lowBoundaryGen_eq_of_le (13 / 75) (by norm_num), hlb]
  have htheta : probeThetaGen 6 (19 / 60) (51 / 100) (13 / 75) = 112 / 125 := by
    norm_num [probeThetaGen]
  refine ⟨hlb, hlb_gen, htheta, by norm_num, by norm_num, by norm_num,
    fun hd => tupleExponent_reflectedAllowance_nonpos hd (by norm_num),
    fun {δ x d ζ} hδ0 hδ hx0 hx hζ hd => ?_,
    fun hδ0 _hδ1 hq => by unfold endpointExponent; linarith⟩
  have htop : endpointExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) δ (x * δ)
      (roughenedRowCount δ x (3 / 7)) ≤ -(1 / 900) :=
    endpointExponent_roughened_le_max_three_corners hδ0 hδ hx0 hx
      (by norm_num [endpointExponent, roughenedRowCount])
      (by norm_num [endpointExponent, roughenedRowCount])
      (by norm_num [endpointExponent, roughenedRowCount])
  refine ⟨htop, ?_⟩
  have hsl_lo : 73 / 300 ≤ roughenedRowCount δ x (3 / 7) + δ / 2 - 17 / 50 := by
    have hge : 1 - δ ≤ roughenedRowCount δ x (3 / 7) := by
      unfold roughenedRowCount
      have h1 : (4 / 9) * δ * x ≤ (4 / 9) * δ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hx (by linarith)
      linarith
    linarith
  have hsl_hi : roughenedRowCount δ x (3 / 7) + δ / 2 - 17 / 50 ≤ 2 := by
    have hle : roughenedRowCount δ x (3 / 7) ≤ 1 := by
      unfold roughenedRowCount
      have h1 : 0 ≤ (4 / 9) * δ * x := mul_nonneg (by linarith) hx0
      have h2 : 0 ≤ δ * (2 - 8 * x / 9) * (3 / 7) :=
        mul_nonneg (mul_nonneg hδ0 (by linarith)) (by norm_num)
      linarith
    linarith
  have hrel : rowExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) (17 / 50) δ (x * δ)
      (roughenedRowCount δ x (3 / 7)) d =
      endpointExponent (19 / 60) (51 / 100) (13 / 75) (131 / 150) δ (x * δ)
        (roughenedRowCount δ x (3 / 7)) +
      (d - 257 / 300) * (roughenedRowCount δ x (3 / 7) + δ / 2 - 17 / 50) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (257 / 300) with hd0 | hd0
  · have hnp : (d - 257 / 300) * (roughenedRowCount δ x (3 / 7) + δ / 2 - 17 / 50) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hbd : (d - 257 / 300) * (roughenedRowCount δ x (3 / 7) + δ / 2 - 17 / 50) ≤ ζ * 2 :=
      mul_le_mul (by linarith) hsl_hi (by linarith) (by linarith)
    linarith

/-- **Full sub-square-root roughening (`u₀ = 1 / 2`) collapses `roughenedRowCount` to `1 - δ`
and reaches the universal `13 / 15` (`1 - σ₀ = 2 / 15`) floor:**
at `u₀ = 1 / 2`, `roughenedRowCount δ x (1 / 2) = 1 - δ` identically, attaining `σ₀ = 13 / 15` at
`(2/5, 2/5, 1/5)` and certifying `σ₀ = 867 / 1000` (`1 - σ₀ = 133 / 1000 > 3001 / 24000`) with
uniform strict negativity `≤ -(1 / 1000)` across **all** `0 ≤ δ ≤ 1` and `q ≤ δ / 2`. -/
theorem roughened_half_certificate_and_floor_attainment :
    (∀ δ x : ℝ, roughenedRowCount δ x (1 / 2) = 1 - δ) ∧
    lowBoundaryGen (2 / 5) (2 / 5) (1 / 5) = 13 / 15 ∧
    (∀ {δ q : ℝ}, 0 ≤ δ → δ ≤ 1 → q ≤ δ / 2 →
      endpointExponent (2 / 5) (2 / 5) (1 / 5) (13 / 15) δ q (1 - δ) ≤ 0) ∧
    lowBoundaryGen (299 / 750) (151 / 375) (149 / 750) = 867 / 1000 ∧
    (3001 / 24000 : ℝ) < 1 - 867 / 1000 ∧
    (∀ {δ q : ℝ}, 0 ≤ δ → δ ≤ 1 → q ≤ δ / 2 →
      endpointExponent (299 / 750) (151 / 375) (149 / 750) (867 / 1000) δ q (1 - δ) ≤
        -(1 / 1000)) := by
  refine ⟨fun δ x => by unfold roughenedRowCount; ring, ?_, ?_, ?_, by norm_num, ?_⟩
  · unfold lowBoundaryGen; norm_num
  · intro δ q _hδ0 _hδ1 hq
    unfold endpointExponent
    linarith
  · unfold lowBoundaryGen
    rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 151 / 375 - 299 / 750),
      show (299 : ℝ) / 750 + 151 / 375 + 149 / 750 - 1 = 0 by ring, max_self]
    norm_num
  · intro δ q hδ0 hδ1 hq
    unfold endpointExponent
    linarith

end Part3RoughenedVertexLPBreakthroughBelowSubSevenEighths


/-! ### Part 4: Pointwise `HasStrictPrimeGasWitness` Transfer Across All Heights and Exact Obstructions -/

section Part4PointwiseWitnessTransferAndEulerDeletionObstruction

/-- **Unconditional pointwise `HasStrictPrimeGasWitness` across `0 < Re s < 3001 / 24000` at all
heights `Im s ∈ ℝ`:**
combining `riemannZeta_ne_zero_of_re_lt_sub_one_eighth` with `hasStrictPrimeGasWitness_iff_zeta_ne_zero`
yields a certified `HasStrictPrimeGasWitness` at **every** point `s` in `0 < Re s < 3001 / 24000`
and **every** horizon `L_hor > 0` across all ordinates. -/
theorem hasStrictPrimeGasWitness_below_sub_one_eighth_all_heights
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 3001 / 24000) {L_hor : ℝ} (hL : 0 < L_hor) :
    HasStrictPrimeGasWitness s hs0 L_hor := by
  have hs1 : s.re < 1 := by linarith
  exact (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL).mpr
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_one_eighth hs0 hhi)

/-- **Pointwise `HasStrictPrimeGasWitness` transfer beyond `3001 / 24000` across all heights
`|Im s| > 184` (and all `Im s ∈ ℝ`) from any sub-`20999 / 24000` zero-free right half-plane:**
for any `σ₀ ∈ [1 / 2, 20999 / 24000)` (such as `σ₀ = 131 / 150` from `u₀ = 3 / 7` giving
`1 - σ₀ = 19 / 150 > 3001 / 24000`, or `σ₀ = 13 / 15` from `u₀ = 1 / 2` giving `1 - σ₀ = 2 / 15`),
nonvanishing of `riemannZeta` on `Re z > σ₀` transfers by functional reflection to unconditional
`HasStrictPrimeGasWitness` at **every** `0 < Re s < 1 - σ₀` across all heights. -/
theorem hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane
    {σ₀ : ℝ} (_hσ_lo : 1 / 2 ≤ σ₀) (hσ_hi : σ₀ < 20999 / 24000)
    (hzf : ∀ z : ℂ, σ₀ < z.re → riemannZeta z ≠ 0) :
    (3001 / 24000 : ℝ) < 1 - σ₀ ∧
    ∀ {s : ℂ} (hs0 : 0 < s.re), s.re < 1 - σ₀ → ∀ {L_hor : ℝ}, 0 < L_hor →
      HasStrictPrimeGasWitness s hs0 L_hor := by
  refine ⟨by linarith, fun {s} hs0 hlt {L_hor} hL => ?_⟩
  have hs1 : s.re < 1 := by linarith
  refine (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL).mpr fun hζ0 => ?_
  have hζ1 : riemannZeta (1 - s) = 0 :=
    riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ0 hs0 hs1
  exact hzf (1 - s) (by simp; linarith) hζ1

/-- **Linear-mollifier prime-persistence rigidity vs. quadratic Vaughan prime annihilation:**
for **every** cutoff `W : ℕ` and **every** arithmetic function `q : ArithmeticFunction ℝ` supported
on `[1, W]` (`∀ d > W, q d = 0`) whose linear residual `1 - ζ * q` vanishes at `1`, **every** prime
`p > W` satisfies `(1 - ζ * q) p = -1 ≠ 0` — whereas `vaughanDualBilinear U V p = 0` for all
`U, V ≥ 1` and all primes `p`. -/
theorem linear_mollifier_prime_persistence_above_cutoff
    {W : ℕ} {q : ArithmeticFunction ℝ}
    (hsupp : ∀ d : ℕ, W < d → q d = 0)
    (hunit : ((1 : ArithmeticFunction ℝ) - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * q) 1 = 0)
    {p : ℕ} (hp : Nat.Prime p) (hp_gt : W < p) :
    ((1 : ArithmeticFunction ℝ) - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * q) p = -1 ∧
    ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → vaughanDualBilinear U V p = 0 := by
  have hsub_apply : ∀ n : ℕ,
      ((1 : ArithmeticFunction ℝ) - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * q) n =
      (1 : ArithmeticFunction ℝ) n - ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * q) n :=
    fun _ => rfl
  have hq1 : q 1 = 1 := by
    rw [hsub_apply 1, ArithmeticFunction.one_apply, if_pos rfl,
      ArithmeticFunction.coe_zeta_mul_apply, Nat.divisors_one, Finset.sum_singleton] at hunit
    linarith
  refine ⟨?_, fun hU hV => by
    simpa only [one_mul] using vaughanDualBilinear_mul_prime_eq_zero (U := _) (V := _) (m := 1)
      hp (le_min hU hV)⟩
  rw [hsub_apply p, ArithmeticFunction.one_apply, if_neg hp.ne_one,
    ArithmeticFunction.coe_zeta_mul_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm,
    hq1, hsupp p hp_gt]
  ring

private lemma prod_one_add_ge_one_add_sum_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hsum_nn : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    nlinarith [mul_nonneg hfa hsum_nn]

/-- **Euler-deletion multiplier blowup vs. the `‖H s - 1‖ ≤ 1 / 2` continuation gate:**
if a finite set `S` of integers `n ≥ 1` has `1 / 2 < ∑_{n ∈ S} n^{-σ}` and coherent antiphase
`χ_val n = -1` on `S`, then the finite Euler-deletion mask `H = ∏_{n ∈ S} (1 - χ_val n · n^{-σ})`
satisfies `1 / 2 < ‖H - 1‖`, strictly violating `‖H s - 1‖ ≤ 1 / 2` in `SubSevenEighthsZeroFreeHalfPlane`. -/
theorem euler_deletion_multiplier_violates_half_ball_of_harmonic_sum
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 1 ≤ n)
    (χ_val : ℕ → ℂ) (hanti : ∀ n ∈ S, χ_val n = -1)
    {σ : ℝ} (hsum_gt : 1 / 2 < ∑ n ∈ S, (n : ℝ) ^ (-σ)) :
    (1 / 2 : ℝ) < ‖(∏ n ∈ S, (1 - χ_val n * (n : ℂ) ^ (-(σ : ℂ)))) - 1‖ := by
  have hfac_eq :
      (∏ n ∈ S, (1 - χ_val n * (n : ℂ) ^ (-(σ : ℂ)))) =
        (((∏ n ∈ S, (1 + (n : ℝ) ^ (-σ)) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos n hn
    rw [hanti n hn, ← Complex.ofReal_natCast n, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hn_pos.le]
    push_cast; ring
  have hge : 1 + ∑ n ∈ S, (n : ℝ) ^ (-σ) ≤ ∏ n ∈ S, (1 + (n : ℝ) ^ (-σ)) :=
    prod_one_add_ge_one_add_sum_aux S (fun n => (n : ℝ) ^ (-σ))
      (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hdiff_nn : 0 ≤ (∏ n ∈ S, (1 + (n : ℝ) ^ (-σ))) - 1 := by linarith
  rw [hfac_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg hdiff_nn]
  linarith

end Part4PointwiseWitnessTransferAndEulerDeletionObstruction

#print axioms cglPrimitiveLFunction_eq_factor_mul_tsum_of_re_neg
#print axioms dirichletL_crossHeight_gaussian_singleScale_eq
#print axioms tsum_dirichlet_smoothAFECutoff_eq_LFunction_add_mellinAt_neg
#print axioms dirichletDualGaussianCoeff_mul_scale
#print axioms dirichletDualGaussianCoeff_zero_eq_neg_factor_add_criticalLine
#print axioms dirichletDualGaussianCoeff_eq_neg_factor_mul_add_criticalLine
#print axioms twisted_vaughanTypeII_divisor_sum_eq
#print axioms twisted_vaughan_dual_band_eq_offLine_add_criticalLine
#print axioms typeIIShort_smooth_mul_rough_eq_zero
#print axioms vaughanDualBilinear_smooth_mul_rough_eq_zero
#print axioms trigPoly_twistedBalancedBilinearDirichletPoly_re_nonneg
#print axioms deLaValleePoussin_both_signs_twistedBalancedBilinear_nonneg
#print axioms cyclic_orthogonality_twistedBalancedBilinear_eq_ker_rough_divisors
#print axioms LSeries_rough_divisors_sub_two_eq_sq
#print axioms plainMarked_slot_capacity_feasible
#print axioms roughened_witness_branch_domination
#print axioms roughened_farkas_bin_crossing_thresholds
#print axioms endpointExponent_roughened_three_corner_identity
#print axioms roughened_LP_breaks_farkas_barrier_of_gt_threshold
#print axioms roughened_three_sevenths_certificate
#print axioms roughened_half_certificate_and_floor_attainment
#print axioms hasStrictPrimeGasWitness_below_sub_one_eighth_all_heights
#print axioms hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane
#print axioms linear_mollifier_prime_persistence_above_cutoff
#print axioms euler_deletion_multiplier_violates_half_ball_of_harmonic_sum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
