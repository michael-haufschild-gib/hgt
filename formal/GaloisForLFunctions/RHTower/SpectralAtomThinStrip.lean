import GaloisForLFunctions.RHTower.CrystallineProducerRigidity
import GaloisForLFunctions.HTGeometry.HamburgerThetaDefect

/-!
# The thin-strip defect of an atomic Weil function

Let `Φ̃(s) = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` with `t_j ≥ 1` and `Σ |c_j|/t_j² < ∞`.  No
condition is placed on the ordinates `t_j`.  If `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = Φ̃(s)` on
`Re s > 1`, where `Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s`, then the theta series `θ` of `1 ⋆ (lam − Λ)` satisfies
`θ(x) + x^{−½} θ(1/x) = β (1 + x^{−½}) + K(x)` for `x > 0`, with
`K(x) = −Σ_j (c_j/π) (Λ(ρ_j)/2 · x^{−ρ_j/2} + Λ(ρ̄_j)/2 · x^{−ρ̄_j/2})`, `ρ_j = ½ + i t_j`
(`coeffTheta_spectral_defect_relation`).  Atoms at zeros of `ζ` contribute nothing to `K`.

* At distance `≥ ¼` from the critical line `Φ̃` grows at most like `(|Im s| + 1)³`
  (`norm_atomicPairSeries_le`), so `Λ Φ̃` decays there.
* The remainder `Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)` is holomorphic on `Re s > ½`
  (`differentiableOn_spectralRemainder`) and `O(1/(1 + t²))` on `¾ ≤ Re s ≤ 3/2`
  (`exists_decay_spectralRemainder`).
* `Λ ξ'/ξ` is holomorphic and decaying on `¼ ≤ Re s ≤ ¾`, so its inverse Mellin integrals on the
  two lines agree (`integral_completedZetaXiLogDeriv_thin_strip`).
* For one pair `ρ = ½ + iu`, `Λ(s)(1/(s − ρ) + 1/(s − ρ̄))` minus
  `(Λ(ρ)/2) Γ((s − ρ)/2) + (Λ(ρ̄)/2) Γ((s − ρ̄)/2)` is holomorphic on the strip
  (`differentiableOn_atomGammaRemainder`).  Since `Γ` is the Mellin transform of `e^{−y}` to the
  right of `0` and of `e^{−y} − 1` to the left, the jump across the strip is
  `Λ(ρ)/2 · x^{−ρ/2} + Λ(ρ̄)/2 · x^{−ρ̄/2}` (`atom_thin_strip`).  Summing over the atoms gives
  `atomic_thin_strip`.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

/-- At distance at least `¼` from the critical line the atom denominators are bounded below:
`‖(w − ½)² + u²‖ ≥ u²/(64(|Im w| + 1)²)` for `u ≥ 1`. -/
theorem norm_atomDenom_ge_off_line {u : ℝ} (hu : 1 ≤ u) {w : ℂ} (hw : 1 / 4 ≤ |w.re - 1 / 2|) :
    u ^ 2 / (64 * (|w.im| + 1) ^ 2) ≤ ‖(w - 1 / 2) ^ 2 + (u : ℂ) ^ 2‖ := by
  rw [← sub_atomPoint_mul_sub_atomMirror, norm_mul]
  have hP1 : 1 / 4 ≤ ‖w - atomPoint u‖ := by
    have := Complex.abs_re_le_norm (w - atomPoint u)
    rw [Complex.sub_re, atomPoint_re] at this
    linarith
  have hQ1 : 1 / 4 ≤ ‖w - atomMirror u‖ := by
    have := Complex.abs_re_le_norm (w - atomMirror u)
    rw [Complex.sub_re, atomMirror_re] at this
    linarith
  have hP2 := norm_sub_atomPoint_ge (t := u) w
  have hQ2 := norm_sub_atomMirror_ge (t := u) w
  set M := |w.im| + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg w.im; linarith
  have hMpos : 0 < 64 * M ^ 2 := by positivity
  rw [div_le_iff₀ hMpos]
  have him := abs_le.mp (le_refl |w.im|)
  by_cases hbig : 2 * M ≤ u
  · have h1 : u / 2 ≤ ‖w - atomPoint u‖ := by
      have : u / 2 ≤ |w.im - u| := by
        rw [abs_sub_comm]; refine le_abs.mpr (Or.inl ?_)
        have := le_abs_self w.im; rw [hM] at hbig; linarith
      linarith
    have h2 : u / 2 ≤ ‖w - atomMirror u‖ := by
      have : u / 2 ≤ |w.im + u| := by
        refine le_abs.mpr (Or.inl ?_)
        have := neg_abs_le w.im; rw [hM] at hbig; linarith
      linarith
    have hprod : u / 2 * (u / 2) ≤ ‖w - atomPoint u‖ * ‖w - atomMirror u‖ :=
      mul_le_mul h1 h2 (by linarith) (norm_nonneg _)
    have hM2 : 1 ≤ M ^ 2 := by nlinarith
    have h64 : u ^ 2 ≤ u / 2 * (u / 2) * (64 * M ^ 2) := by
      nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_left hM2 (sq_nonneg u)]
    have := mul_le_mul_of_nonneg_right hprod hMpos.le
    linarith
  · push Not at hbig
    have hprod : 1 / 4 * (1 / 4) ≤ ‖w - atomPoint u‖ * ‖w - atomMirror u‖ :=
      mul_le_mul hP1 hQ1 (by norm_num) (norm_nonneg _)
    have hu2 : u ^ 2 ≤ 4 * M ^ 2 := by nlinarith
    nlinarith

/-- **Polynomial growth of the atomic series off the critical line.**  For
`¼ ≤ |Re w − ½| ≤ 1`, `‖Φ̃(w)‖ ≤ (128/π) (|Im w| + 1)³ Σ |c_j|/t_j²`. -/
theorem norm_atomicPairSeries_le {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {w : ℂ} (hw1 : 1 / 4 ≤ |w.re - 1 / 2|)
    (hw2 : |w.re - 1 / 2| ≤ 1) :
    ‖atomicPairSeries c t w‖ ≤
      128 / Real.pi * (|w.im| + 1) ^ 3 * ∑' j, |c j| / t j ^ 2 := by
  set M := |w.im| + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg w.im; linarith
  have hpi := Real.pi_pos
  have hterm : ∀ j, ‖(c j : ℂ) / ((w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)‖ ≤
      64 * M ^ 2 * (|c j| / t j ^ 2) := by
    intro j
    have hd := norm_atomDenom_ge_off_line (hone j) hw1
    have ht2 : 0 < t j ^ 2 := by have := hone j; positivity
    have hpos : 0 < ‖(w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2‖ :=
      lt_of_lt_of_le (by positivity) hd
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hpos]
    have htj : t j ≠ 0 := by have := hone j; positivity
    have hM0 : M ≠ 0 := by positivity
    calc |c j| = 64 * M ^ 2 * (|c j| / t j ^ 2) * (t j ^ 2 / (64 * M ^ 2)) := by
          field_simp
      _ ≤ 64 * M ^ 2 * (|c j| / t j ^ 2) * ‖(w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2‖ := by
          gcongr
  have hS := (hsum.mul_left (64 * M ^ 2)).hasSum
  have htsum := tsum_of_norm_bounded hS hterm
  have hwh : ‖w - 1 / 2‖ ≤ M := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (w - 1 / 2)
    simp only [Complex.sub_re, Complex.sub_im] at h1
    have : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    have : ((1 : ℂ) / 2).im = 0 := by norm_num
    simp at h1
    rw [hM]; linarith
  unfold atomicPairSeries
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi, norm_mul,
    Complex.norm_two]
  rw [tsum_mul_left] at htsum
  calc 2 * ‖w - 1 / 2‖ / Real.pi * ‖∑' j, (c j : ℂ) / ((w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)‖
      ≤ 2 * M / Real.pi * (64 * M ^ 2 * ∑' j, |c j| / t j ^ 2) := by gcongr
    _ = 128 / Real.pi * M ^ 3 * ∑' j, |c j| / t j ^ 2 := by ring

/-- `Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)` for arbitrary atoms, before removing its singularity at `1`. -/
noncomputable def spectralRemainderRaw (c t : ℕ → ℝ) (s : ℂ) : ℂ :=
  completedZetaXiLogDeriv s - completedRiemannZeta s * atomicPairSeries c t s -
    crystallineResidue c t * Gammaℝ (s - 1)

/-- The remainder `Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)` with its removable singularity at `1` filled. -/
noncomputable def spectralRemainder (c t : ℕ → ℝ) : ℂ → ℂ :=
  Function.update (spectralRemainderRaw c t) 1 (limUnder (𝓝[≠] 1) (spectralRemainderRaw c t))

/-- The residue at `s = 1` cancels: `(s − 1)(Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)) → 0`. -/
theorem tendsto_sub_one_mul_spectralRemainderRaw {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) :
    Tendsto (fun z => (z - 1) * spectralRemainderRaw c t z) (𝓝[≠] 1) (𝓝 0) := by
  set Φ := atomicPairSeries c t with hΦ
  set β := crystallineResidue c t with hβ
  set H : ℂ → ℂ := fun z => (z - 1) * (deriv completedRiemannZeta₀ z +
      completedRiemannZeta₀ z * (1 / z)) + completedRiemannZeta₀ z -
      ((z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) * Φ z -
      β * (2 * ((Real.pi : ℂ) ^ (-(z - 1) / 2) * Gamma ((z - 1) / 2 + 1))) with hHdef
  have hH1 : H 1 = 0 := by
    simp only [hHdef, hβ, crystallineResidue, sub_self, zero_mul, zero_add, neg_zero, zero_div,
      cpow_zero, one_mul, Complex.Gamma_one]
    ring
  have hG : DifferentiableAt ℂ Gamma (((1 : ℂ) - 1) / 2 + 1) := by
    apply differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this; linarith
  have hΦc : ContinuousAt Φ 1 :=
    ((differentiableOn_atomicPairSeries hone hsum).differentiableAt
      ((isOpen_re_gt _).mem_nhds (by norm_num))).continuousAt
  have hL0 : Continuous completedRiemannZeta₀ := differentiable_completedZeta₀.continuous
  have hdL0 : Continuous (deriv completedRiemannZeta₀) :=
    differentiable_deriv_completedRiemannZeta₀.continuous
  have hinv : ContinuousAt (fun z : ℂ => 1 / z) 1 :=
    continuousAt_const.div continuousAt_id one_ne_zero
  have hpow : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z - 1) / 2)) 1 :=
    (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).continuousAt
  have hgam : ContinuousAt (fun z : ℂ => Gamma ((z - 1) / 2 + 1)) 1 :=
    hG.continuousAt.comp (f := fun z : ℂ => (z - 1) / 2 + 1) (by fun_prop)
  have hsub : ContinuousAt (fun z : ℂ => z - 1) 1 := by fun_prop
  have hHc : ContinuousAt H 1 := by
    refine (((hsub.mul (hdL0.continuousAt.add (hL0.continuousAt.mul hinv))).add
      hL0.continuousAt).sub (((hsub.mul (hL0.continuousAt.sub hinv)).add continuousAt_const).mul
      hΦc)).sub (continuousAt_const.mul (continuousAt_const.mul (hpow.mul hgam)))
  have hev : (fun z => (z - 1) * spectralRemainderRaw c t z) =ᶠ[𝓝[≠] 1] H := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)),
      self_mem_nhdsWithin] with z hz hz1
    have hz1' : z ≠ 1 := hz1
    rw [mem_ball, dist_eq_norm] at hz
    have hre : 3 / 4 < z.re := by
      have := (Complex.abs_re_le_norm (z - 1)).trans_lt hz
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_lt.mp this
      linarith [this.1]
    have hΓ := sub_one_mul_Gammaℝ_sub_one hz1'
    have e1 : (z - 1) * (1 / (z - 1)) = 1 := by
      field_simp [sub_ne_zero.mpr hz1']
    have e2 : (z - 1) * (1 / (1 - z)) = -1 := by
      rw [show (1 : ℂ) - z = -(z - 1) by ring, div_neg]
      field_simp [sub_ne_zero.mpr hz1']
    simp only [spectralRemainderRaw, completedZetaXiLogDeriv, completedRiemannZeta_eq, hHdef]
    rw [← hβ, ← hΦ]
    linear_combination completedRiemannZeta₀ z * e1 + Φ z * e2 - β * hΓ
  have := hHc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  rw [hH1] at this
  exact this.congr' hev.symm

/-- **Removable singularity at `s = 1`.**  The filled remainder is holomorphic on `Re s > ½`. -/
theorem differentiableOn_spectralRemainder {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) :
    DifferentiableOn ℂ (spectralRemainder c t) {s : ℂ | 1 / 2 < s.re} := by
  have hU : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) := (isOpen_re_gt _).mem_nhds (by norm_num)
  refine differentiableOn_update_limUnder_of_isLittleO hU ?_ ?_
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs0' : 1 / 2 < s.re := hs0
    have hne0 : s ≠ 0 := by intro h0; rw [h0] at hs0'; simp at hs0'; linarith
    have hne1 : s ≠ 1 := by simpa using hs1
    have hreg : s ∈ zetaRegular := by
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hne0, hne1⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    have hG := differentiableAt_Gammaℝ_sub_one (by linarith) hne1
    exact ((differentiableAt_completedZetaXiLogDeriv hne0 hne1).sub
      ((differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds hreg)).mul
        ((differentiableOn_atomicPairSeries hone hsum).differentiableAt
          ((isOpen_re_gt _).mem_nhds hs0')))).sub ((differentiableAt_const _).mul hG)
  · rw [Asymptotics.isLittleO_iff_tendsto']
    · have h1 := tendsto_sub_one_mul_spectralRemainderRaw hone hsum
      have h2 : Tendsto (fun z : ℂ => (z - 1) * spectralRemainderRaw c t 1) (𝓝[≠] 1)
          (𝓝 0) := by
        have : Tendsto (fun z : ℂ => (z - 1) * spectralRemainderRaw c t 1) (𝓝 1)
            (𝓝 ((1 - 1) * spectralRemainderRaw c t 1)) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      have := h1.sub h2
      rw [sub_zero] at this
      refine this.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      dsimp only
      rw [div_inv_eq_mul]
      ring
    · exact eventually_nhdsWithin_of_forall fun z hz h0 =>
        absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))

/-- **`Λ Φ̃` decays** on `¾ ≤ Re s ≤ 3/2`, `|Im s| ≥ 4`: `Λ` decays exponentially and `Φ̃` grows
polynomially there. -/
theorem exists_decay_completedRiemannZeta_mul_atomicPairSeries {c t : ℕ → ℝ}
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => |c j| / t j ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 3 / 4 ≤ w.re → w.re ≤ 3 / 2 → 4 ≤ |w.im| →
      ‖completedRiemannZeta w * atomicPairSeries c t w‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 3 + 2)
  set S : ℝ := ∑' j, |c j| / t j ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  have hpi := Real.pi_pos
  refine ⟨CΛ * (128 / Real.pi) * S * K, by positivity, fun w h1 h2 h3 => ?_⟩
  set τ := |w.im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hΛw := hΛ w (by linarith) (by linarith) (by linarith)
  have hΦw := norm_atomicPairSeries_le hone hsum (w := w)
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hK' := pow_mul_exp_neg_le_div hK hτ0
  rw [hτ, sq_abs] at hK'
  have hp1 : τ ^ N ≤ (τ + 4) ^ N := pow_le_pow_left₀ hτ0 (by linarith) N
  have hp2 : (τ + 1) ^ 3 ≤ (τ + 4) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  rw [norm_mul]
  calc ‖completedRiemannZeta w‖ * ‖atomicPairSeries c t w‖
      ≤ (CΛ * τ ^ N * Real.exp (-(Real.pi * τ / 4))) * (128 / Real.pi * (τ + 1) ^ 3 * S) :=
        mul_le_mul hΛw hΦw (norm_nonneg _) (by positivity)
    _ ≤ (CΛ * (τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4))) *
          (128 / Real.pi * (τ + 4) ^ 3 * S) := by gcongr
    _ = CΛ * (128 / Real.pi) * S * ((τ + 4) ^ (N + 3) * Real.exp (-(Real.pi * τ / 4))) := by
        ring
    _ ≤ CΛ * (128 / Real.pi) * S * (K / (1 + w.im ^ 2)) := by gcongr
    _ = _ := by ring

/-- **Decay of the remainder** on the closed strip `¾ ≤ Re s ≤ 3/2`. -/
theorem exists_decay_spectralRemainder {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) :
    ∃ C : ℝ, ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (3 / 4) (3 / 2),
      ‖spectralRemainder c t s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_decay_completedZetaXiLogDeriv
  obtain ⟨C₂, hC₂, h₂⟩ := exists_decay_completedRiemannZeta_mul_atomicPairSeries hone hsum
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  set K : Set ℂ := Set.Icc (3 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 with hKdef
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro z hz
    rw [hKdef, Complex.mem_reProdIm] at hz
    show 1 / 2 < z.re
    linarith [hz.1.1]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_spectralRemainder hone hsum).continuousOn.mono hsub)
  set β := crystallineResidue c t
  refine ⟨max (17 * max M 0) (C₁ + C₂ + ‖β‖ * C₃), fun s hs => ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : 4 ≤ |s.im|
  · have hs1 : s ≠ 1 := by intro h0; rw [h0] at hbig; norm_num at hbig
    rw [spectralRemainder, Function.update_of_ne hs1, spectralRemainderRaw]
    calc ‖completedZetaXiLogDeriv s - completedRiemannZeta s * atomicPairSeries c t s -
          β * Gammaℝ (s - 1)‖
        ≤ ‖completedZetaXiLogDeriv s‖ + ‖completedRiemannZeta s * atomicPairSeries c t s‖ +
            ‖β‖ * ‖Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ C₁ / (1 + s.im ^ 2) + C₂ / (1 + s.im ^ 2) + ‖β‖ * (C₃ / (1 + s.im ^ 2)) := by
          gcongr
          · exact h₁ s (by linarith [hs.1]) hs.2 hbig
          · exact h₂ s hs.1 hs.2 hbig
          · exact h₃ s (by linarith [hs.1]) hs.2 hbig
      _ = (C₁ + C₂ + ‖β‖ * C₃) / (1 + s.im ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hbig
    have hsK : s ∈ K := by
      rw [hKdef, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    calc ‖spectralRemainder c t s‖ ≤ max M 0 := hb
      _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

theorem differentiableOn_completedZetaXiLogDeriv_strip :
    DifferentiableOn ℂ completedZetaXiLogDeriv
      (GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4)) := by
  intro s hs
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  exact (differentiableAt_completedZetaXiLogDeriv h0 h1).differentiableWithinAt

/-- `Λ ξ'/ξ = O(1/(1 + t²))` on `¼ ≤ Re s ≤ ¾`, by oddness from the right half of the strip. -/
theorem exists_decay_completedZetaXiLogDeriv_strip :
    ∃ C : ℝ, ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4),
      ‖completedZetaXiLogDeriv s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_decay_completedZetaXiLogDeriv
  set K : Set ℂ := Set.Icc (1 / 4 : ℝ) (3 / 4) ×ℂ Set.Icc (-4 : ℝ) 4 with hKdef
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4) := by
    intro z hz
    rw [hKdef, Complex.mem_reProdIm] at hz
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip]
    exact hz.1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (differentiableOn_completedZetaXiLogDeriv_strip.continuousOn.mono hsub)
  refine ⟨max (17 * max M 0) C₁, fun s hs => ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : 4 ≤ |s.im|
  · rcases le_total (1 / 2) s.re with hre | hre
    · calc ‖completedZetaXiLogDeriv s‖ ≤ C₁ / (1 + s.im ^ 2) := h₁ s hre (by linarith) hbig
        _ ≤ _ := by gcongr; exact le_max_right _ _
    · have hodd := completedZetaXiLogDeriv_one_sub s
      have h1s : completedZetaXiLogDeriv s = -completedZetaXiLogDeriv (1 - s) := by
        rw [hodd, neg_neg]
      have him : (1 - s).im = -s.im := by simp
      have hb := h₁ (1 - s) (by simp; linarith) (by simp; linarith) (by rw [him, abs_neg]; exact hbig)
      rw [him, neg_sq] at hb
      rw [h1s, norm_neg]
      exact hb.trans (by gcongr; exact le_max_right _ _)
  · push Not at hbig
    have hsK : s ∈ K := by
      rw [hKdef, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    calc ‖completedZetaXiLogDeriv s‖ ≤ max M 0 := hb
      _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- **`Λ ξ'/ξ` crosses the thin strip.**  Its inverse Mellin integrals over `Re s = ¾` and
`Re s = ¼` agree, since it is holomorphic and decaying on `¼ ≤ Re s ≤ ¾`. -/
theorem integral_completedZetaXiLogDeriv_thin_strip {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      completedZetaXiLogDeriv (2 * (((3 / 8 : ℝ) : ℂ) + t * I))) =
    ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + t * I)) := by
  obtain ⟨C, hC⟩ := exists_decay_completedZetaXiLogDeriv_strip
  have hGd := GaloisForLFunctions.HTGeometry.differentiableOn_cpow_mul_comp
    differentiableOn_completedZetaXiLogDeriv_strip (c := 1 / 8) (d := 3 / 8)
    (by norm_num) (by norm_num) hx
  have hGc := hGd.continuousOn
  refine GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn
    (by norm_num) hGc (hGd.mono fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    (GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hC (by norm_num) (by norm_num) hx)
    (GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hC (by norm_num) (by norm_num) hx)
    ?_ ?_
  · exact GaloisForLFunctions.HTGeometry.tendsto_integral_horizontal_cpow_mul_comp hC
      (by norm_num) (by norm_num) (by norm_num) hx (h := fun T => -T) (fun T => by ring)
  · exact GaloisForLFunctions.HTGeometry.tendsto_integral_horizontal_cpow_mul_comp hC
      (by norm_num) (by norm_num) (by norm_num) hx (h := fun T => T) (fun T => rfl)

/-- `z ↦ Γ(z/2 + 1)`, holomorphic on `Re z > −2`; its divided difference at `0` is
`½ Γ(z/2) − 1/z`. -/
noncomputable def gammaHalfShift (z : ℂ) : ℂ := Complex.Gamma (z / 2 + 1)

theorem differentiableOn_gammaHalfShift :
    DifferentiableOn ℂ gammaHalfShift {z : ℂ | -1 < z.re} := by
  intro z hz
  have hz' : -1 < z.re := hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hG : DifferentiableAt ℂ Complex.Gamma (z / 2 + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this
    linarith
  exact hG.comp z (by fun_prop)

/-- The pole-free remainder of one atom pair:
`Λ(s)(1/(s−ρ) + 1/(s−ρ̄)) − (Λ(ρ)/2)Γ((s−ρ)/2) − (Λ(ρ̄)/2)Γ((s−ρ̄)/2)` with `ρ = ½ + iu`, written
through divided differences so that it is holomorphic across `ρ` and `ρ̄`. -/
noncomputable def atomGammaRemainder (u : ℝ) (s : ℂ) : ℂ :=
  dslope completedRiemannZeta (atomPoint u) s + dslope completedRiemannZeta (atomMirror u) s -
    completedRiemannZeta (atomPoint u) * dslope gammaHalfShift 0 (s - atomPoint u) -
    completedRiemannZeta (atomMirror u) * dslope gammaHalfShift 0 (s - atomMirror u)

theorem dslope_gammaHalfShift_eq {z : ℂ} (hz : z ≠ 0) :
    dslope gammaHalfShift 0 z = Complex.Gamma (z / 2) / 2 - 1 / z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  rw [dslope_of_ne _ hz, slope_def_module, sub_zero, gammaHalfShift, gammaHalfShift,
    zero_div, zero_add, Complex.Gamma_one, Complex.Gamma_add_one _ hz2, smul_eq_mul]
  field_simp

theorem atomGammaRemainder_eq {u : ℝ} {s : ℂ} (h1 : s ≠ atomPoint u) (h2 : s ≠ atomMirror u) :
    atomGammaRemainder u s = completedRiemannZeta s * (1 / (s - atomPoint u) +
      1 / (s - atomMirror u)) - completedRiemannZeta (atomPoint u) / 2 *
        Complex.Gamma ((s - atomPoint u) / 2) -
      completedRiemannZeta (atomMirror u) / 2 * Complex.Gamma ((s - atomMirror u) / 2) := by
  have h1' : s - atomPoint u ≠ 0 := sub_ne_zero.mpr h1
  have h2' : s - atomMirror u ≠ 0 := sub_ne_zero.mpr h2
  rw [atomGammaRemainder, dslope_of_ne _ h1, dslope_of_ne _ h2, slope_def_module, slope_def_module,
    dslope_gammaHalfShift_eq h1', dslope_gammaHalfShift_eq h2', smul_eq_mul, smul_eq_mul]
  field_simp
  ring

theorem differentiableOn_atomGammaRemainder (u : ℝ) :
    DifferentiableOn ℂ (atomGammaRemainder u)
      (GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4)) := by
  have hreg : GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4) ⊆ zetaRegular := by
    intro s hs
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; rw [h] at hs; norm_num at hs
    · intro h; rw [h] at hs; norm_num at hs
  have hd1 : DifferentiableOn ℂ (dslope completedRiemannZeta (atomPoint u)) zetaRegular :=
    (differentiableOn_dslope (isOpen_zetaRegular.mem_nhds
      (mem_zetaRegular_of_re_eq_half (atomPoint_re u)))).mpr
      differentiableOn_completedRiemannZeta_regular
  have hd2 : DifferentiableOn ℂ (dslope completedRiemannZeta (atomMirror u)) zetaRegular :=
    (differentiableOn_dslope (isOpen_zetaRegular.mem_nhds
      (mem_zetaRegular_of_re_eq_half (atomMirror_re u)))).mpr
      differentiableOn_completedRiemannZeta_regular
  have hUo : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hg : DifferentiableOn ℂ (dslope gammaHalfShift 0) {z : ℂ | -1 < z.re} :=
    (differentiableOn_dslope (hUo.mem_nhds (by simp))).mpr differentiableOn_gammaHalfShift
  have hmaps : ∀ (ρ : ℂ), ρ.re = 1 / 2 → ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip
      (1 / 4) (3 / 4), s - ρ ∈ {z : ℂ | -1 < z.re} := by
    intro ρ hρ s hs
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
    show -1 < (s - ρ).re
    rw [Complex.sub_re, hρ]; linarith [hs.1]
  unfold atomGammaRemainder
  refine (((hd1.mono hreg).add (hd2.mono hreg)).sub ((differentiableOn_const _).mul
    (hg.comp (differentiableOn_id.sub (differentiableOn_const _))
      (hmaps _ (atomPoint_re u))))).sub ((differentiableOn_const _).mul
    (hg.comp (differentiableOn_id.sub (differentiableOn_const _)) (hmaps _ (atomMirror_re u))))

/-- `Γ((s − ρ)/2)` decays in the thin strip away from `Im ρ`, uniformly after a shift. -/
theorem exists_decay_Gamma_half_sub {v : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → |v| + 3 ≤ |s.im| →
      ‖Complex.Gamma ((s - ((1 / 2 : ℂ) + (v : ℂ) * I)) / 2)‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨Cg, Ng, hCg, hg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip (-1 / 8) (1 / 8)
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (Ng + 2)
  have hpi := Real.pi_pos
  refine ⟨Cg * (|v| + 1) ^ Ng * Real.exp (Real.pi * |v| / 4) * K, by positivity,
    fun s h1 h2 h3 => ?_⟩
  set τ := |s.im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hre : ((s - ((1 / 2 : ℂ) + (v : ℂ) * I)) / 2).re = (s.re - 1 / 2) / 2 := by simp
  have him : ((s - ((1 / 2 : ℂ) + (v : ℂ) * I)) / 2).im = (s.im - v) / 2 := by simp
  have hsv : τ - |v| ≤ |s.im - v| := by
    have := abs_sub_abs_le_abs_sub s.im v; rw [hτ]; linarith
  have hG := hg ((s - ((1 / 2 : ℂ) + (v : ℂ) * I)) / 2) (by rw [hre]; linarith)
    (by rw [hre]; linarith) (by rw [him, abs_div, abs_two]; linarith)
  rw [him, abs_div, abs_two] at hG
  have hexp : Real.exp (-(Real.pi * (|s.im - v| / 2) / 2)) ≤
      Real.exp (Real.pi * |v| / 4) * Real.exp (-(Real.pi * τ / 4)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hpow : (|s.im - v| / 2) ^ Ng ≤ (|v| + 1) ^ Ng * (τ + 4) ^ Ng := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ Ng
    have := abs_sub (s.im) v
    rw [← hτ] at this
    nlinarith [abs_nonneg v]
  have hK' := pow_mul_exp_neg_le_div hK hτ0
  rw [hτ, sq_abs] at hK'
  calc ‖Complex.Gamma ((s - ((1 / 2 : ℂ) + (v : ℂ) * I)) / 2)‖
      ≤ Cg * (|s.im - v| / 2) ^ Ng * Real.exp (-(Real.pi * (|s.im - v| / 2) / 2)) := hG
    _ ≤ Cg * ((|v| + 1) ^ Ng * (τ + 4) ^ Ng) *
          (Real.exp (Real.pi * |v| / 4) * Real.exp (-(Real.pi * τ / 4))) := by gcongr
    _ = Cg * (|v| + 1) ^ Ng * Real.exp (Real.pi * |v| / 4) *
          ((τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4))) := by ring
    _ ≤ Cg * (|v| + 1) ^ Ng * Real.exp (Real.pi * |v| / 4) * (K / (1 + s.im ^ 2)) := by gcongr
    _ = _ := by ring

theorem atomPoint_eq (u : ℝ) : atomPoint u = (1 / 2 : ℂ) + (u : ℂ) * I := rfl

theorem atomMirror_eq (u : ℝ) : atomMirror u = (1 / 2 : ℂ) + ((-u : ℝ) : ℂ) * I := by
  simp [atomMirror]; ring

/-- **Decay of the atom-pair remainder** on the thin strip `¼ ≤ Re s ≤ ¾`. -/
theorem exists_decay_atomGammaRemainder (u : ℝ) :
    ∃ C : ℝ, ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4),
      ‖atomGammaRemainder u s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 2)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_decay_Gamma_half_sub (v := u)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_decay_Gamma_half_sub (v := -u)
  set K₀ : Set ℂ := Set.Icc (1 / 4 : ℝ) (3 / 4) ×ℂ Set.Icc (-(|u| + 3)) (|u| + 3) with hK₀def
  have hK₀c : IsCompact K₀ := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K₀ ⊆ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 4) (3 / 4) := by
    intro z hz
    rw [hK₀def, Complex.mem_reProdIm] at hz
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip]
    exact hz.1
  obtain ⟨M, hM⟩ := hK₀c.exists_bound_of_continuousOn
    ((differentiableOn_atomGammaRemainder u).continuousOn.mono hsub)
  set a₁ := ‖completedRiemannZeta (atomPoint u)‖
  set a₂ := ‖completedRiemannZeta (atomMirror u)‖
  refine ⟨max ((1 + (|u| + 3) ^ 2) * max M 0) (2 * CΛ * K + a₁ / 2 * C₁ + a₂ / 2 * C₂),
    fun s hs => ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : |u| + 3 ≤ |s.im|
  · have hsu : 3 ≤ |s.im - u| := by
      have := abs_sub_abs_le_abs_sub s.im u; linarith [le_abs_self u, neg_abs_le u]
    have hsu' : 3 ≤ |s.im + u| := by
      have := abs_sub_abs_le_abs_sub s.im (-u); rw [sub_neg_eq_add, abs_neg] at this; linarith
    have hn1 : s ≠ atomPoint u := by
      intro h; rw [h] at hsu; simp [atomPoint] at hsu; linarith
    have hn2 : s ≠ atomMirror u := by
      intro h; rw [h] at hsu'; simp [atomMirror] at hsu'; linarith
    have hd1 : 1 ≤ ‖s - atomPoint u‖ := by
      have := norm_sub_atomPoint_ge (t := u) s; linarith
    have hd2 : 1 ≤ ‖s - atomMirror u‖ := by
      have := norm_sub_atomMirror_ge (t := u) s; linarith
    have hi1 : ‖1 / (s - atomPoint u)‖ ≤ 1 := by
      rw [norm_div, norm_one]; exact div_le_one_of_le₀ hd1 (norm_nonneg _)
    have hi2 : ‖1 / (s - atomMirror u)‖ ≤ 1 := by
      rw [norm_div, norm_one]; exact div_le_one_of_le₀ hd2 (norm_nonneg _)
    have hΛs := hΛ s (by linarith) (by linarith) (by linarith [abs_nonneg u])
    have hK' := pow_mul_exp_neg_le_div hK (abs_nonneg s.im)
    rw [sq_abs] at hK'
    have hpow : |s.im| ^ N ≤ (|s.im| + 4) ^ N := pow_le_pow_left₀ (abs_nonneg _) (by linarith) N
    have hΛb : ‖completedRiemannZeta s‖ ≤ CΛ * K / (1 + s.im ^ 2) := by
      calc ‖completedRiemannZeta s‖ ≤ CΛ * |s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := hΛs
        _ ≤ CΛ * ((|s.im| + 4) ^ N * Real.exp (-(Real.pi * |s.im| / 4))) := by
            rw [← mul_assoc]; gcongr
        _ ≤ CΛ * (K / (1 + s.im ^ 2)) := by gcongr
        _ = _ := by ring
    have hG1 := h₁ s hs.1 hs.2 (by linarith)
    have hG2 := h₂ s hs.1 hs.2 (by rw [abs_neg]; linarith)
    rw [← atomPoint_eq] at hG1
    rw [← atomMirror_eq] at hG2
    rw [atomGammaRemainder_eq hn1 hn2]
    calc ‖completedRiemannZeta s * (1 / (s - atomPoint u) + 1 / (s - atomMirror u)) -
          completedRiemannZeta (atomPoint u) / 2 * Complex.Gamma ((s - atomPoint u) / 2) -
          completedRiemannZeta (atomMirror u) / 2 * Complex.Gamma ((s - atomMirror u) / 2)‖
        ≤ ‖completedRiemannZeta s‖ * (‖1 / (s - atomPoint u)‖ + ‖1 / (s - atomMirror u)‖) +
            a₁ / 2 * ‖Complex.Gamma ((s - atomPoint u) / 2)‖ +
            a₂ / 2 * ‖Complex.Gamma ((s - atomMirror u) / 2)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [norm_mul]; gcongr; exact norm_add_le _ _
          · rw [norm_mul, norm_div, Complex.norm_two]
          · rw [norm_mul, norm_div, Complex.norm_two]
      _ ≤ CΛ * K / (1 + s.im ^ 2) * (1 + 1) + a₁ / 2 * (C₁ / (1 + s.im ^ 2)) +
            a₂ / 2 * (C₂ / (1 + s.im ^ 2)) := by gcongr
      _ = (2 * CΛ * K + a₁ / 2 * C₁ + a₂ / 2 * C₂) / (1 + s.im ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hbig
    have hsK : s ∈ K₀ := by
      rw [hK₀def, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ (|u| + 3) ^ 2 := by
      have := abs_nonneg s.im
      nlinarith [sq_abs s.im]
    calc ‖atomGammaRemainder u s‖ ≤ max M 0 := hb
      _ ≤ (1 + (|u| + 3) ^ 2) * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- The inverse-Mellin integrand `x^{-(σ+it)} Γ(σ + it − ρ/2)` is integrable when
`σ − Re ρ/2` avoids the poles of `Γ`. -/
theorem integrable_cpow_mul_Gamma_sub_half {σ : ℝ} {ρ : ℂ} {x : ℝ} (hx : 0 < x)
    (hp : ∀ k : ℕ, σ - ρ.re / 2 ≠ -(k : ℝ)) :
    Integrable fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      Complex.Gamma ((σ : ℂ) + t * I - ρ / 2) := by
  have hΓ : Integrable fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I - ρ / 2) := by
    refine (GaloisForLFunctions.HTGeometry.integrable_Gamma_vertical_line (b := ρ.im / 2) hp).congr
      (Eventually.of_forall fun t => ?_)
    dsimp only
    congr 1
    apply Complex.ext <;> simp
  refine hΓ.bdd_mul (c := x ^ (-σ))
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The atom-pair factor `1/(s − ρ) + 1/(s − ρ̄) = 2(s − ½)/((s − ½)² + u²)`. -/
noncomputable def atomPairFactor (u : ℝ) (s : ℂ) : ℂ :=
  1 / (s - atomPoint u) + 1 / (s - atomMirror u)

theorem atomPairFactor_eq {u : ℝ} {s : ℂ} (h1 : s ≠ atomPoint u)
    (h2 : s ≠ atomMirror u) :
    atomPairFactor u s = 2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u : ℂ) ^ 2) := by
  have h1' : s - atomPoint u ≠ 0 := sub_ne_zero.mpr h1
  have h2' : s - atomMirror u ≠ 0 := sub_ne_zero.mpr h2
  rw [atomPairFactor, ← sub_atomPoint_mul_sub_atomMirror]
  field_simp
  simp only [atomPoint, atomMirror]
  ring

/-- **The thin-strip jump of one atom pair.**  For `ρ = ½ + iu`,
`(1/2π)[∫ x^{-(3/8+it)} Λ Q(¾ + 2it) dt − ∫ x^{-(1/8+it)} Λ Q(¼ + 2it) dt]
  = (Λ(ρ)/2) x^{-ρ/2} + (Λ(ρ̄)/2) x^{-ρ̄/2}`, with `Q = 1/(s − ρ) + 1/(s − ρ̄)`. -/
theorem atom_thin_strip (u : ℝ) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) • ((∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) *
          atomPairFactor u (2 * (((3 / 8 : ℝ) : ℂ) + t * I)))) -
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + t * I)) *
          atomPairFactor u (2 * (((1 / 8 : ℝ) : ℂ) + t * I)))) =
      completedRiemannZeta (atomPoint u) / 2 * (x : ℂ) ^ (-(atomPoint u / 2)) +
        completedRiemannZeta (atomMirror u) / 2 * (x : ℂ) ^ (-(atomMirror u / 2)) := by
  set ρ := atomPoint u with hρ
  set ρ' := atomMirror u with hρ'
  obtain ⟨CB, hCB⟩ := exists_decay_atomGammaRemainder u
  have hBd := differentiableOn_atomGammaRemainder u
  -- the pole-free part crosses the strip
  have hBshift : (∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      atomGammaRemainder u (2 * (((3 / 8 : ℝ) : ℂ) + t * I))) =
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        atomGammaRemainder u (2 * (((1 / 8 : ℝ) : ℂ) + t * I)) := by
    have hGd := GaloisForLFunctions.HTGeometry.differentiableOn_cpow_mul_comp hBd
      (c := 1 / 8) (d := 3 / 8) (by norm_num) (by norm_num) hx
    refine GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn
      (by norm_num) hGd.continuousOn (hGd.mono fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
      (GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line hBd.continuousOn hCB
        (by norm_num) (by norm_num) hx)
      (GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line hBd.continuousOn hCB
        (by norm_num) (by norm_num) hx) ?_ ?_
    · exact GaloisForLFunctions.HTGeometry.tendsto_integral_horizontal_cpow_mul_comp hCB
        (by norm_num) (by norm_num) (by norm_num) hx (h := fun T => -T) (fun T => by ring)
    · exact GaloisForLFunctions.HTGeometry.tendsto_integral_horizontal_cpow_mul_comp hCB
        (by norm_num) (by norm_num) (by norm_num) hx (h := fun T => T) (fun T => rfl)
  -- pointwise decomposition on the two lines
  have hdec : ∀ σ : ℝ, σ ≠ 1 / 4 → ∀ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + t * I)) * atomPairFactor u (2 * ((σ : ℂ) + t * I))) =
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) * atomGammaRemainder u (2 * ((σ : ℂ) + t * I)) +
        completedRiemannZeta ρ / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
          Complex.Gamma ((σ : ℂ) + t * I - ρ / 2)) +
        completedRiemannZeta ρ' / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
          Complex.Gamma ((σ : ℂ) + t * I - ρ' / 2)) := by
    intro σ hσ t
    have hre : (2 * ((σ : ℂ) + t * I)).re = 2 * σ := by simp
    have hn1 : 2 * ((σ : ℂ) + t * I) ≠ ρ := by
      intro h; have := congrArg Complex.re h; rw [hre, hρ, atomPoint_re] at this
      exact hσ (by linarith)
    have hn2 : 2 * ((σ : ℂ) + t * I) ≠ ρ' := by
      intro h; have := congrArg Complex.re h; rw [hre, hρ', atomMirror_re] at this
      exact hσ (by linarith)
    rw [atomGammaRemainder_eq hn1 hn2, atomPairFactor]
    rw [show (2 * ((σ : ℂ) + t * I) - ρ) / 2 = (σ : ℂ) + t * I - ρ / 2 by ring,
      show (2 * ((σ : ℂ) + t * I) - ρ') / 2 = (σ : ℂ) + t * I - ρ' / 2 by ring]
    ring
  -- integrability of the pieces
  have hB3 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line hBd.continuousOn hCB
    (σ := 3 / 8) (by norm_num) (by norm_num) hx
  have hB1 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line hBd.continuousOn hCB
    (σ := 1 / 8) (by norm_num) (by norm_num) hx
  have hpρ : ∀ (σ : ℝ) (z : ℂ), z.re = 1 / 2 → (σ = 3 / 8 ∨ σ = 1 / 8) →
      ∀ k : ℕ, σ - z.re / 2 ≠ -(k : ℝ) := by
    intro σ z hz hσ k h
    rw [hz] at h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rcases hσ with h' | h' <;> subst h' <;> norm_num at h
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rcases hσ with h' | h' <;> subst h' <;> linarith
  have hΓ3 := integrable_cpow_mul_Gamma_sub_half (σ := 3 / 8) (ρ := ρ) hx
    (hpρ _ _ (atomPoint_re u) (Or.inl rfl))
  have hΓ3' := integrable_cpow_mul_Gamma_sub_half (σ := 3 / 8) (ρ := ρ') hx
    (hpρ _ _ (atomMirror_re u) (Or.inl rfl))
  have hΓ1 := integrable_cpow_mul_Gamma_sub_half (σ := 1 / 8) (ρ := ρ) hx
    (hpρ _ _ (atomPoint_re u) (Or.inr rfl))
  have hΓ1' := integrable_cpow_mul_Gamma_sub_half (σ := 1 / 8) (ρ := ρ') hx
    (hpρ _ _ (atomMirror_re u) (Or.inr rfl))
  have hsplit : ∀ σ : ℝ, σ ≠ 1 / 4 →
      Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
        atomGammaRemainder u (2 * ((σ : ℂ) + t * I))) →
      Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
        Complex.Gamma ((σ : ℂ) + t * I - ρ / 2)) →
      Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
        Complex.Gamma ((σ : ℂ) + t * I - ρ' / 2)) →
      (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + t * I)) *
          atomPairFactor u (2 * ((σ : ℂ) + t * I)))) =
        (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * atomGammaRemainder u (2 * ((σ : ℂ) + t * I))) +
          completedRiemannZeta ρ / 2 * (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
            Complex.Gamma ((σ : ℂ) + t * I - ρ / 2)) +
          completedRiemannZeta ρ' / 2 * (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
            Complex.Gamma ((σ : ℂ) + t * I - ρ' / 2)) := by
    intro σ hσ hB hG hG'
    calc (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + t * I)) *
          atomPairFactor u (2 * ((σ : ℂ) + t * I))))
        = ∫ t : ℝ, ((x : ℂ) ^ (-((σ : ℂ) + t * I)) * atomGammaRemainder u (2 * ((σ : ℂ) + t * I)) +
            completedRiemannZeta ρ / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
              Complex.Gamma ((σ : ℂ) + t * I - ρ / 2))) +
            completedRiemannZeta ρ' / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
              Complex.Gamma ((σ : ℂ) + t * I - ρ' / 2)) :=
          integral_congr_ae (Eventually.of_forall (hdec σ hσ))
      _ = (∫ t : ℝ, ((x : ℂ) ^ (-((σ : ℂ) + t * I)) * atomGammaRemainder u (2 * ((σ : ℂ) + t * I)) +
            completedRiemannZeta ρ / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
              Complex.Gamma ((σ : ℂ) + t * I - ρ / 2)))) +
          ∫ t : ℝ, completedRiemannZeta ρ' / 2 * ((x : ℂ) ^ (-((σ : ℂ) + t * I)) *
              Complex.Gamma ((σ : ℂ) + t * I - ρ' / 2)) :=
          integral_add (hB.add (hG.const_mul _)) (hG'.const_mul _)
      _ = _ := by
          rw [integral_add hB (hG.const_mul _), integral_const_mul, integral_const_mul]
  have h3 := hsplit (3 / 8) (by norm_num) hB3 hΓ3 hΓ3'
  have h1 := hsplit (1 / 8) (by norm_num) hB1 hΓ1 hΓ1'
  have hg1 := GaloisForLFunctions.HTGeometry.gamma_thin_strip_inverse_mellin (ρ := ρ)
    (by rw [hρ, atomPoint_re]; norm_num) (by rw [hρ, atomPoint_re]; norm_num) hx
  have hg2 := GaloisForLFunctions.HTGeometry.gamma_thin_strip_inverse_mellin (ρ := ρ')
    (by rw [hρ', atomMirror_re]; norm_num) (by rw [hρ', atomMirror_re]; norm_num) hx
  rw [h3, h1, hBshift]
  rw [Complex.real_smul] at hg1 hg2 ⊢
  linear_combination completedRiemannZeta ρ / 2 * hg1 + completedRiemannZeta ρ' / 2 * hg2

/-- `‖Λ(s)‖ (|Im s| + 1)³ = O(1/(1 + t²))` on the thin strip `¼ ≤ Re s ≤ ¾`. -/
theorem exists_bound_completedRiemannZeta_mul_cube :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖completedRiemannZeta s‖ * (|s.im| + 1) ^ 3 ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 3 + 2)
  set K₀ : Set ℂ := Set.Icc (1 / 4 : ℝ) (3 / 4) ×ℂ Set.Icc (-2 : ℝ) 2 with hK₀def
  have hK₀c : IsCompact K₀ := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K₀ ⊆ zetaRegular := by
    intro z hz
    rw [hK₀def, Complex.mem_reProdIm] at hz
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; rw [h] at hz; norm_num at hz
    · intro h; rw [h] at hz; norm_num at hz
  obtain ⟨M, hM⟩ := hK₀c.exists_bound_of_continuousOn
    (differentiableOn_completedRiemannZeta_regular.continuousOn.mono hsub)
  refine ⟨max (135 * max M 0) (CΛ * K), by positivity, fun s h1 h2 => ?_⟩
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : 2 ≤ |s.im|
  · have hΛs := hΛ s (by linarith) (by linarith) hbig
    have hK' := pow_mul_exp_neg_le_div hK (abs_nonneg s.im)
    rw [sq_abs] at hK'
    have hp1 : |s.im| ^ N ≤ (|s.im| + 4) ^ N := pow_le_pow_left₀ (abs_nonneg _) (by linarith) N
    have hp2 : (|s.im| + 1) ^ 3 ≤ (|s.im| + 4) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc ‖completedRiemannZeta s‖ * (|s.im| + 1) ^ 3
        ≤ (CΛ * |s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 4))) * (|s.im| + 4) ^ 3 :=
          mul_le_mul hΛs hp2 (by positivity) (by positivity)
      _ ≤ (CΛ * (|s.im| + 4) ^ N * Real.exp (-(Real.pi * |s.im| / 4))) * (|s.im| + 4) ^ 3 := by
          gcongr
      _ = CΛ * ((|s.im| + 4) ^ (N + 3) * Real.exp (-(Real.pi * |s.im| / 4))) := by ring
      _ ≤ CΛ * (K / (1 + s.im ^ 2)) := by gcongr
      _ = CΛ * K / (1 + s.im ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hbig
    have hsK : s ∈ K₀ := by
      rw [hK₀def, Complex.mem_reProdIm]
      exact ⟨⟨h1, h2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ 4 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    have hcube : (|s.im| + 1) ^ 3 ≤ 27 := by
      have : |s.im| + 1 ≤ 3 := by linarith
      calc (|s.im| + 1) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 27 := by norm_num
    calc ‖completedRiemannZeta s‖ * (|s.im| + 1) ^ 3 ≤ max M 0 * 27 :=
          mul_le_mul hb hcube (by positivity) (le_max_right _ _)
      _ ≤ 135 * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]; nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- The atom-pair factor on the lines `Re s = ¼, ¾`: `‖Q_u(s)‖ ≤ 128 (|Im s| + 1)³ / u²`. -/
theorem norm_atomPairFactor_le_off_line {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (hs1 : 1 / 4 ≤ |s.re - 1 / 2|) (hs2 : |s.re - 1 / 2| ≤ 1) :
    ‖atomPairFactor u s‖ ≤ 128 * (|s.im| + 1) ^ 3 / u ^ 2 := by
  have hn1 : s ≠ atomPoint u := by
    intro h; rw [h, atomPoint_re] at hs1; norm_num at hs1
  have hn2 : s ≠ atomMirror u := by
    intro h; rw [h, atomMirror_re] at hs1; norm_num at hs1
  rw [atomPairFactor_eq hn1 hn2]
  have hd := norm_atomDenom_ge_off_line hu hs1
  have hu2 : 0 < u ^ 2 := by positivity
  have hM : 0 < 64 * (|s.im| + 1) ^ 2 := by positivity
  have hpos : 0 < ‖(s - 1 / 2) ^ 2 + (u : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hd
  have hwh : ‖s - 1 / 2‖ ≤ |s.im| + 1 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (s - 1 / 2)
    simp at h1
    linarith
  rw [norm_div, norm_mul, Complex.norm_two, div_le_div_iff₀ hpos hu2]
  calc 2 * ‖s - 1 / 2‖ * u ^ 2 ≤ 2 * (|s.im| + 1) * u ^ 2 := by gcongr
    _ = 2 * (|s.im| + 1) * (64 * (|s.im| + 1) ^ 2) * (u ^ 2 / (64 * (|s.im| + 1) ^ 2)) := by
        field_simp
    _ ≤ 2 * (|s.im| + 1) * (64 * (|s.im| + 1) ^ 2) * ‖(s - 1 / 2) ^ 2 + (u : ℂ) ^ 2‖ := by
        gcongr
    _ = 128 * (|s.im| + 1) ^ 3 * ‖(s - 1 / 2) ^ 2 + (u : ℂ) ^ 2‖ := by ring

/-- Off the critical line the atomic series is the sum of its atom-pair factors:
`Φ̃(s) = Σ_j (c_j/π) Q_{t_j}(s)`. -/
theorem atomicPairSeries_eq_tsum_atomPairFactor {c t : ℕ → ℝ} {s : ℂ} (hs : s.re ≠ 1 / 2) :
    atomicPairSeries c t s = ∑' j, (c j : ℂ) / Real.pi * atomPairFactor (t j) s := by
  have hn : ∀ j, s ≠ atomPoint (t j) ∧ s ≠ atomMirror (t j) := fun j =>
    ⟨fun h => hs (by rw [h, atomPoint_re]), fun h => hs (by rw [h, atomMirror_re])⟩
  unfold atomicPairSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [atomPairFactor_eq (hn j).1 (hn j).2]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **The thin-strip jump of the atomic series.**
`(1/2π)[∫ x^{-(3/8+it)} Λ Φ̃(¾ + 2it) dt − ∫ x^{-(1/8+it)} Λ Φ̃(¼ + 2it) dt]
  = Σ_j (c_j/π) ((Λ(ρ_j)/2) x^{-ρ_j/2} + (Λ(ρ̄_j)/2) x^{-ρ̄_j/2})`. -/
theorem atomic_thin_strip {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) • ((∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)) *
          atomicPairSeries c t (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)))) -
      ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          atomicPairSeries c t (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))) =
      ∑' j, (c j : ℂ) / Real.pi *
        (completedRiemannZeta (atomPoint (t j)) / 2 * (x : ℂ) ^ (-(atomPoint (t j) / 2)) +
          completedRiemannZeta (atomMirror (t j)) / 2 * (x : ℂ) ^ (-(atomMirror (t j) / 2))) := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  have hpi := Real.pi_pos
  -- the per-atom integrands on a line `Re w = σ`
  set F : ℝ → ℕ → ℝ → ℂ := fun σ j τ => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
    (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
      ((c j : ℂ) / Real.pi * atomPairFactor (t j) (2 * ((σ : ℂ) + τ * I)))) with hF
  have hline : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ τ : ℝ,
      1 / 4 ≤ |(2 * ((σ : ℂ) + τ * I)).re - 1 / 2| ∧ |(2 * ((σ : ℂ) + τ * I)).re - 1 / 2| ≤ 1 ∧
      1 / 4 ≤ (2 * ((σ : ℂ) + τ * I)).re ∧ (2 * ((σ : ℂ) + τ * I)).re ≤ 3 / 4 := by
    intro σ hσ τ
    have : (2 * ((σ : ℂ) + τ * I)).re = 2 * σ := by simp
    rw [this]
    rcases hσ with h | h <;> subst h <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have him2 : ∀ (σ τ : ℝ), (2 * ((σ : ℂ) + τ * I)).im = 2 * τ := by intro σ τ; simp
  -- a uniform bound for each atom
  have hbound : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ j τ,
      ‖F σ j τ‖ ≤ x ^ (-σ) * (|c j| / t j ^ 2) * (128 / Real.pi * CΛ) * (1 + τ ^ 2)⁻¹ := by
    intro σ hσ j τ
    obtain ⟨hl1, hl2, hl3, hl4⟩ := hline σ hσ τ
    have hP := norm_atomPairFactor_le_off_line (hone j) hl1 hl2
    have hΛ := hCΛ _ hl3 hl4
    rw [him2] at hP hΛ
    have ht2 : 0 < t j ^ 2 := by have := hone j; positivity
    have hden : 1 + τ ^ 2 ≤ 1 + (2 * τ) ^ 2 := by nlinarith
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((σ : ℂ) + τ * I)).re = -σ := by simp
    rw [hre]
    calc x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (|c j| / Real.pi * ‖atomPairFactor (t j) (2 * ((σ : ℂ) + τ * I))‖))
        ≤ x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (|c j| / Real.pi * (128 * (|2 * τ| + 1) ^ 3 / t j ^ 2))) := by gcongr
      _ = x ^ (-σ) * (|c j| / t j ^ 2) * (128 / Real.pi) *
          (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ * (|2 * τ| + 1) ^ 3) := by
          field_simp
      _ ≤ x ^ (-σ) * (|c j| / t j ^ 2) * (128 / Real.pi) * (CΛ / (1 + (2 * τ) ^ 2)) := by
          gcongr
      _ ≤ x ^ (-σ) * (|c j| / t j ^ 2) * (128 / Real.pi) * (CΛ / (1 + τ ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hcontF : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ j, Continuous (F σ j) := by
    intro σ hσ j
    have hreg : ∀ τ : ℝ, 2 * ((σ : ℂ) + τ * I) ∈ zetaRegular := by
      intro τ
      obtain ⟨_, _, hl3, hl4⟩ := hline σ hσ τ
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h; rw [h] at hl3; norm_num at hl3
      · intro h; rw [h] at hl4; norm_num at hl4
    have hoff : ∀ τ : ℝ, 2 * ((σ : ℂ) + τ * I) ≠ atomPoint (t j) ∧
        2 * ((σ : ℂ) + τ * I) ≠ atomMirror (t j) := by
      intro τ
      obtain ⟨hl1, _, _, _⟩ := hline σ hσ τ
      exact ⟨fun h => by rw [h, atomPoint_re] at hl1; norm_num at hl1,
        fun h => by rw [h, atomMirror_re] at hl1; norm_num at hl1⟩
    simp only [hF]
    refine Continuous.mul (Continuous.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast hx.ne'))) (Continuous.mul ?_ (continuous_const.mul ?_))
    · rw [continuous_iff_continuousAt]
      intro τ
      exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds (hreg τ))).continuousAt.comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
    · rw [continuous_iff_continuousAt]
      intro τ
      unfold atomPairFactor
      refine ContinuousAt.add ?_ ?_
      · exact continuousAt_const.div (by fun_prop) (sub_ne_zero.mpr (hoff τ).1)
      · exact continuousAt_const.div (by fun_prop) (sub_ne_zero.mpr (hoff τ).2)
  have hintF : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ j, Integrable (F σ j) := by
    intro σ hσ j
    exact Integrable.mono' ((integrable_inv_one_add_sq).const_mul _)
      (hcontF σ hσ j).aestronglyMeasurable (Eventually.of_forall (hbound σ hσ j))
  have hsumF : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) →
      Summable fun j => ∫ τ, ‖F σ j τ‖ := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun τ => norm_nonneg _)
      (fun j => ?_) ((hsum.mul_left (x ^ (-σ))).mul_right
        ((128 / Real.pi * CΛ) * ∫ τ : ℝ, (1 + τ ^ 2)⁻¹))
    calc ∫ τ, ‖F σ j τ‖ ≤ ∫ τ, x ^ (-σ) * (|c j| / t j ^ 2) * (128 / Real.pi * CΛ) *
          (1 + τ ^ 2)⁻¹ :=
        integral_mono (hintF σ hσ j).norm ((integrable_inv_one_add_sq).const_mul _)
          (hbound σ hσ j)
      _ = x ^ (-σ) * (|c j| / t j ^ 2) * ((128 / Real.pi * CΛ) * ∫ τ : ℝ, (1 + τ ^ 2)⁻¹) := by
          rw [integral_const_mul]; ring
  -- exchange sum and integral on each line
  have hsumeq : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) →
      (∫ τ : ℝ, (x : ℂ) ^ (-((σ : ℂ) + τ * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
          atomicPairSeries c t (2 * ((σ : ℂ) + τ * I)))) = ∑' j, ∫ τ, F σ j τ := by
    intro σ hσ
    rw [integral_tsum_of_summable_integral_norm (hintF σ hσ) (hsumF σ hσ)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    obtain ⟨hl1, _, _, _⟩ := hline σ hσ τ
    have hoffline : (2 * ((σ : ℂ) + τ * I)).re ≠ 1 / 2 := by
      intro h; rw [h] at hl1; norm_num at hl1
    simp only [hF]
    rw [atomicPairSeries_eq_tsum_atomPairFactor hoffline, ← tsum_mul_left, ← tsum_mul_left]
  have hHas : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → Summable fun j => ∫ τ, F σ j τ :=
    fun σ hσ => (hasSum_integral_of_summable_integral_norm (hintF σ hσ) (hsumF σ hσ)).summable
  -- each atom by `atom_thin_strip`
  have hatom : ∀ j, (1 / (2 * Real.pi) : ℝ) • ((∫ τ, F (3 / 8) j τ) - ∫ τ, F (1 / 8) j τ) =
      (c j : ℂ) / Real.pi *
        (completedRiemannZeta (atomPoint (t j)) / 2 * (x : ℂ) ^ (-(atomPoint (t j) / 2)) +
          completedRiemannZeta (atomMirror (t j)) / 2 * (x : ℂ) ^ (-(atomMirror (t j) / 2))) := by
    intro j
    have h := atom_thin_strip (t j) hx
    have hc : ∀ σ : ℝ, (∫ τ, F σ j τ) = (c j : ℂ) / Real.pi * ∫ τ : ℝ,
        (x : ℂ) ^ (-((σ : ℂ) + τ * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
          atomPairFactor (t j) (2 * ((σ : ℂ) + τ * I))) := by
      intro σ
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [hF]
      ring
    rw [hc, hc, ← mul_sub, Complex.real_smul] at *
    rw [← h]
    ring
  rw [hsumeq _ (Or.inl rfl), hsumeq _ (Or.inr rfl),
    ← (hHas _ (Or.inl rfl)).tsum_sub (hHas _ (Or.inr rfl)), Complex.real_smul, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← hatom j, Complex.real_smul]

/-- The atomic series is continuous on the lines `Re s = ¼` and `Re s = ¾`. -/
theorem continuousAt_atomicPairSeries_off_line {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    ContinuousAt (atomicPairSeries c t) s := by
  rcases lt_or_gt_of_ne hs with h | h
  · have h1 : 1 / 2 < (1 - s).re := by simp; linarith
    have hd : ContinuousAt (atomicPairSeries c t) (1 - s) :=
      ((differentiableOn_atomicPairSeries hone hsum).differentiableAt
        ((isOpen_re_gt _).mem_nhds h1)).continuousAt
    have hcomp : ContinuousAt (fun z => -atomicPairSeries c t (1 - z)) s :=
      (hd.comp (f := fun z : ℂ => 1 - z) (by fun_prop)).neg
    refine hcomp.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [atomicPairSeries_one_sub, neg_neg]
  · exact ((differentiableOn_atomicPairSeries hone hsum).differentiableAt
      ((isOpen_re_gt _).mem_nhds h)).continuousAt

/-- `x^{-w} Λ(2w) Φ̃(2w)` is integrable along `Re w = 3/8` and `Re w = 1/8`. -/
theorem integrable_cpow_mul_completedRiemannZeta_mul_atomicPairSeries {c t : ℕ → ℝ}
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => |c j| / t j ^ 2) {σ x : ℝ} (hx : 0 < x)
    (hσ : σ = 3 / 8 ∨ σ = 1 / 8) :
    Integrable fun τ : ℝ => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
        atomicPairSeries c t (2 * ((σ : ℂ) + τ * I))) := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  set S : ℝ := ∑' j, |c j| / t j ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  have hpi := Real.pi_pos
  have hre : ∀ τ : ℝ, (2 * ((σ : ℂ) + τ * I)).re = 2 * σ := by intro τ; simp
  have him : ∀ τ : ℝ, (2 * ((σ : ℂ) + τ * I)).im = 2 * τ := by intro τ; simp
  have h2σ : 2 * σ = 3 / 4 ∨ 2 * σ = 1 / 4 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hl1 : 1 / 4 ≤ |2 * σ - 1 / 2| := by
    rcases h2σ with h | h <;> rw [h] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have hl2 : |2 * σ - 1 / 2| ≤ 1 := by
    rcases h2σ with h | h <;> rw [h] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have hl3 : 1 / 4 ≤ 2 * σ := by rcases h2σ with h | h <;> linarith
  have hl4 : 2 * σ ≤ 3 / 4 := by rcases h2σ with h | h <;> linarith
  have hreg : ∀ τ : ℝ, 2 * ((σ : ℂ) + τ * I) ∈ zetaRegular := by
    intro τ
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    · intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hcont : Continuous fun τ : ℝ => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
        atomicPairSeries c t (2 * ((σ : ℂ) + τ * I))) := by
    refine Continuous.mul (Continuous.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast hx.ne'))) (Continuous.mul ?_ ?_)
    · rw [continuous_iff_continuousAt]
      intro τ
      exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds (hreg τ))).continuousAt.comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
    · rw [continuous_iff_continuousAt]
      intro τ
      have hoff : (2 * ((σ : ℂ) + τ * I)).re ≠ 1 / 2 := by
        rw [hre]; rcases h2σ with h | h <;> rw [h] <;> norm_num
      exact (continuousAt_atomicPairSeries_off_line hone hsum hoff).comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul
    (x ^ (-σ) * (128 / Real.pi * S * CΛ))) hcont.aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  have hΦ := norm_atomicPairSeries_le hone hsum (w := 2 * ((σ : ℂ) + τ * I))
    (by rw [hre]; exact hl1) (by rw [hre]; exact hl2)
  have hΛ := hCΛ (2 * ((σ : ℂ) + τ * I)) (by rw [hre]; exact hl3) (by rw [hre]; exact hl4)
  rw [him] at hΦ hΛ
  have hden : 1 + τ ^ 2 ≤ 1 + (2 * τ) ^ 2 := by nlinarith
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre' : (-((σ : ℂ) + τ * I)).re = -σ := by simp
  rw [hre']
  calc x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
        ‖atomicPairSeries c t (2 * ((σ : ℂ) + τ * I))‖)
      ≤ x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (128 / Real.pi * (|2 * τ| + 1) ^ 3 * S)) := by gcongr
    _ = x ^ (-σ) * (128 / Real.pi * S) *
          (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ * (|2 * τ| + 1) ^ 3) := by ring
    _ ≤ x ^ (-σ) * (128 / Real.pi * S) * (CΛ / (1 + (2 * τ) ^ 2)) := by gcongr
    _ ≤ x ^ (-σ) * (128 / Real.pi * S) * (CΛ / (1 + τ ^ 2)) := by gcongr
    _ = x ^ (-σ) * (128 / Real.pi * S * CΛ) * (1 + τ ^ 2)⁻¹ := by ring

/-- The thin-strip defect of a spectral system:
`K(x) = −Σ_j (c_j/π) ((Λ(ρ_j)/2) x^{-ρ_j/2} + (Λ(ρ̄_j)/2) x^{-ρ̄_j/2})`, `ρ_j = ½ + it_j`.  Atoms at
zeros of `ζ` contribute nothing. -/
noncomputable def spectralDefect (c t : ℕ → ℝ) (x : ℝ) : ℂ :=
  -∑' j, (c j : ℂ) / Real.pi *
    (completedRiemannZeta (atomPoint (t j)) / 2 * (x : ℂ) ^ (-(atomPoint (t j) / 2)) +
      completedRiemannZeta (atomMirror (t j)) / 2 * (x : ℂ) ^ (-(atomMirror (t j) / 2)))

/-- **The defect theta relation.**  If `Γ̃ + 1/(s − 1) − Σ lam(n) n^{-s} = Φ̃` on `Re s > 1`, the
theta series of `a = 1 ⋆ (lam − Λ)` satisfies
`θ(x) = −x^{-1/2} θ(1/x) + β + β x^{-1/2} + K(x)` for all `x > 0`, with `K` the spectral defect.
Unconditional: the ζ-multiplier removes every zero of `ζ`, on or off the line. -/
theorem coeffTheta_spectral_defect_relation {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) {x : ℝ} (hx : 0 < x) :
    GaloisForLFunctions.HTGeometry.coeffTheta (crystallineCoeff lam) x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
        GaloisForLFunctions.HTGeometry.coeffTheta (crystallineCoeff lam) x⁻¹) +
      crystallineResidue c t + crystallineResidue c t * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
      spectralDefect c t x := by
  set a := crystallineCoeff lam with ha_def
  set β := crystallineResidue c t with hβ
  set Φ := atomicPairSeries c t with hΦ
  obtain ⟨C, hC⟩ := exists_decay_spectralRemainder hone hsum
  have hdiff := differentiableOn_spectralRemainder hone hsum
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsl (by simpa using hσ))
  have hθc := GaloisForLFunctions.HTGeometry.continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (GaloisForLFunctions.HTGeometry.coeffTheta a) (3 / 4 : ℂ) :=
    GaloisForLFunctions.HTGeometry.mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hEc : ContinuousOn (spectralRemainder c t)
      (GaloisForLFunctions.HTGeometry.verticalStrip (3 / 4) (3 / 2)) := by
    refine hdiff.continuousOn.mono (fun z hz => ?_)
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hz
    show 1 / 2 < z.re
    linarith [hz.1]
  have hEd : DifferentiableOn ℂ (spectralRemainder c t) {s : ℂ | 3 / 4 < s.re ∧ s.re < 3 / 2} := by
    refine hdiff.mono (fun z hz => ?_)
    show 1 / 2 < z.re
    linarith [hz.1]
  have hR : ∀ s : ℂ, s.re = 3 / 2 → mellin (GaloisForLFunctions.HTGeometry.coeffTheta a) (s / 2) =
      spectralRemainder c t s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; norm_num at hs
    have hs' : 1 < s.re := by rw [hs]; norm_num
    have hlam : LSeries (fun n => (lam n : ℂ)) s =
        zetaArchimedeanDatum s + 1 / (s - 1) - atomicPairSeries c t s := by
      linear_combination -(hid s hs')
    rw [GaloisForLFunctions.HTGeometry.mellin_coeffTheta a ha hs', coeffDirichlet_eq_LSeries,
      LSeries_crystallineCoeff hsl hs',
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs', hlam,
      Gammaℝ_mul_riemannZeta_mul_eq hs', spectralRemainder, Function.update_of_ne hs1,
      spectralRemainderRaw]
    ring
  set G : ℂ → ℂ := fun s => completedZetaXiLogDeriv s - completedRiemannZeta s * Φ s with hGdef
  have hG : ∀ s : ℂ, s.re = 3 / 4 → G s = spectralRemainder c t s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; norm_num at hs
    rw [spectralRemainder, Function.update_of_ne hs1, spectralRemainderRaw]
    simp only [hGdef, hΦ, hβ]
    ring
  have hmain := GaloisForLFunctions.HTGeometry.theta_add_dual_eq_of_rightLine hθc hθm hEc hEd hC
    hR hG hx
  -- reflect the second integrand to the line `Re s = ¼`
  have hrefl : ∀ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)) =
      -((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
      (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := by
    intro τ
    have h1 : 2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) =
        1 - 2 * (((1 / 8 : ℝ) : ℂ) + τ * I) := by push_cast; ring
    simp only [hGdef]
    rw [h1, completedZetaXiLogDeriv_one_sub, completedRiemannZeta_one_sub, hΦ,
      atomicPairSeries_one_sub]
    ring
  have hsplit3 : (∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) =
      (∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) -
      ∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) := by
    obtain ⟨CG, hCG⟩ := exists_decay_completedZetaXiLogDeriv_strip
    have h1 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hCG (σ := 3 / 8)
      (by norm_num) (by norm_num) hx
    have h2 := integrable_cpow_mul_completedRiemannZeta_mul_atomicPairSeries hone hsum
      (σ := 3 / 8) hx (Or.inl rfl)
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hGdef]
    ring
  have hsplit1 : (∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I))) =
      -(∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
      ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := by
    obtain ⟨CG, hCG⟩ := exists_decay_completedZetaXiLogDeriv_strip
    have h1 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hCG (σ := 1 / 8)
      (by norm_num) (by norm_num) hx
    have h2 := integrable_cpow_mul_completedRiemannZeta_mul_atomicPairSeries hone hsum
      (σ := 1 / 8) hx (Or.inr rfl)
    calc (∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
          G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)))
        = ∫ τ : ℝ, (-((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
          (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
              Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))) :=
          integral_congr_ae (Eventually.of_forall hrefl)
      _ = (∫ τ : ℝ, -((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))) +
          ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
              Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := integral_add h1.neg h2
      _ = _ := by rw [integral_neg]
  have hG1 := integral_completedZetaXiLogDeriv_thin_strip hx
  have hat := atomic_thin_strip hone hsum hx
  rw [hsplit3, hsplit1, hG1] at hmain
  have hK : spectralDefect c t x = -((1 / (2 * Real.pi) : ℝ) •
      ((∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)))) -
      ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))))) := by
    rw [hΦ, hat, spectralDefect]
  rw [hK]
  rw [Complex.real_smul] at hmain ⊢
  linear_combination hmain

end RHTower
