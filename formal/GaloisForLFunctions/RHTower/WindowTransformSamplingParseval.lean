import Zeta23.ZeroSide
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriUnnormalized

/-!
# Sampling Parseval for window transforms and the cosh shift bound

For a continuous `ψ` supported in `[−L/2, L/2]`, the transform `ψ̂(z) = ∫ ψ(u) e^{izu} du` sampled
on the grid `γ − (T + 2πk/L)` is `L` times the Fourier coefficients of `u ↦ ψ(u)e^{i(γ−T)u}` on that
interval, so Parseval gives `Σ_k |ψ̂(γ − τ_k)|² = L ∫ |ψ|²` (`hasSum_norm_sq_paperFT_grid`).

Applied to `ψ = φ·(cosh(ε·) − 1)`, together with `φ̂(w + iε) = conj φ̂(w − iε)`, this shows that the
real parts of the sampled vectors of a point displaced by `ε` from the real axis stay within
`(cosh(εL/2) − 1)·√(aL²)` of the sampled vector of the axis point (`sum_sq_re_shift_sub_le`).

Polarising the same identity gives `Σ_k φ̂(w_k) Re ψ̂(w_k) = L ∫ φ Re ψ` for real `φ` with `φ̂`
real on the grid and any continuous `ψ` (`hasSum_re_mul_re_paperFT_grid`).  With
`ψ = φ·cosh(ε·)e^{iΔ·}`, whose transform on the grid is the real number `Re φ̂(w + Δ − iε)`, the
full-grid overlap of the sampled vectors of `γ` and of `γ + Δ − iε` is
`∫φ²cosh(ε·)cos(Δ·)/∫φ² ≥ cos(ΔL/2)·J`, `J = ∫φ²cosh(ε·)/∫φ² ≥ 1`, and the square norm of the second
is at most `cosh(εL/2)·J`.  The overlap criterion then gives `0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²` for every
truncation of the grid whenever `cosh(εL/2) ≤ 2cos²(ΔL/2)` and `|Δ|L/2 ≤ π/2`
(`lens_overlap_cost`; the case `Δ = 0` is `shift_overlap_cost`).
-/

open MeasureTheory Complex

namespace RHTower

noncomputable section

/-- paperFT of a function supported in `[-L/2, L/2]` is an interval integral. -/
theorem paperFT_eq_intervalIntegral {ψ : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (z : ℂ) :
    Zeta23.paperFT ψ z = ∫ u in (-(L / 2))..(L / 2), ψ u * cexp (I * z * u) := by
  rw [intervalIntegral.integral_of_le (by linarith), Zeta23.paperFT]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  have : L / 2 ≤ |u| := by
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hsupp u this, zero_mul]

theorem paperFT_grid_eq_mul_fourierCoeffOn {ψ : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (γ T : ℝ) (k : ℤ) :
    Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ) =
      L * fourierCoeffOn (show -(L / 2) < L / 2 by linarith)
        (fun u => ψ u * cexp (I * (γ - T : ℝ) * u)) k := by
  rw [fourierCoeffOn_eq_integral, paperFT_eq_intervalIntegral hL hsupp]
  have hba : L / 2 - -(L / 2) = L := by ring
  rw [Complex.real_smul, hba, ← mul_assoc]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [show (L : ℂ) * ((1 / L : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [smul_eq_mul]
  rw [fourier_coe_apply]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring


/-- **Sampling Parseval.**  For a continuous `ψ` supported in `[-L/2, L/2]`, the samples of its
Fourier transform on the grid `γ − (T + k·2π/L)` have square sum `L ∫ |ψ|²`. -/
theorem hasSum_norm_sq_paperFT_grid {ψ : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hc : Continuous ψ)
    (hsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (γ T : ℝ) :
    HasSum (fun k : ℤ => ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2)
      (L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2) := by
  have hab : -(L / 2) < L / 2 := by linarith
  set f : ℝ → ℂ := fun u => ψ u * cexp (I * (γ - T : ℝ) * u) with hf
  have hfc : Continuous f := hc.mul (by fun_prop)
  have hnorm : ∀ u, ‖f u‖ = ‖ψ u‖ := fun u => by
    simp only [hf, norm_mul]
    rw [show I * ((γ - T : ℝ) : ℂ) * (u : ℂ) = (((γ - T) * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- MemLp on the interval
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(L / 2)) (b := L / 2)).exists_bound_of_continuousOn
    hfc.continuousOn
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc (-(L / 2)) (L / 2))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(L / 2)) (L / 2))) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    refine MemLp.of_bound hfc.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun u hu => hC u (Set.Ioc_subset_Icc_self hu)
  have hP := hasSum_sq_fourierCoeffOn hab hmem
  have hba : L / 2 - -(L / 2) = L := by ring
  rw [hba] at hP
  have h2 := hP.mul_left (L ^ 2)
  have hF : (fun k : ℤ => ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2)
      = fun i => L ^ 2 * ‖fourierCoeffOn hab f i‖ ^ 2 := by
    funext k
    rw [paperFT_grid_eq_mul_fourierCoeffOn hL hsupp γ T k, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hV : L ^ 2 * L⁻¹ • ∫ x in (-(L / 2))..(L / 2), ‖f x‖ ^ 2
      = L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 := by
    rw [smul_eq_mul, ← mul_assoc, show L ^ 2 * L⁻¹ = L by field_simp]
    congr 1
    exact intervalIntegral.integral_congr fun u _ => by simp only [hnorm]
  rw [hF, ← hV]
  exact h2

/-- Finite version: any finite set of grid samples has square sum at most `L ∫ |ψ|²`. -/
theorem sum_norm_sq_paperFT_grid_le {ψ : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hc : Continuous ψ)
    (hsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (γ T : ℝ) (s : Finset ℤ) :
    ∑ k ∈ s, ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2
      ≤ L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 :=
  sum_le_hasSum s (fun _ _ => sq_nonneg _) (hasSum_norm_sq_paperFT_grid hL hc hsupp γ T)


theorem integrable_ofReal_mul_cexp {φ : ℝ → ℝ} {L : ℝ} (hc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (z : ℂ) :
    Integrable (fun u : ℝ => (φ u : ℂ) * cexp (I * z * u)) := by
  have hcs : HasCompactSupport (fun u : ℝ => (φ u : ℂ)) :=
    Zeta23.hasCompactSupport_of_support_subset_abs (Λ := L / 2) fun u hu => by
      by_contra h
      exact hu (by rw [hsupp u (le_of_lt (not_le.mp h))]; simp)
  have hcs' : HasCompactSupport (fun u : ℝ => (φ u : ℂ) * cexp (I * z * u)) :=
    HasCompactSupport.mul_right (f := fun u : ℝ => (φ u : ℂ)) (f' := fun u : ℝ => cexp (I * z * u)) hcs
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs'

/-- The even shift difference of a window transform:
`(φ̂(w − iε) + φ̂(w + iε))/2 − φ̂(w) = (φ·(cosh(ε·) − 1))^(w)`. -/
theorem paperFT_cosh_shift_sub {φ : ℝ → ℝ} {L : ℝ} (hc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w ε : ℝ) :
    (Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) - ε * I)
        + Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) + ε * I)) / 2
      - Zeta23.paperFT (fun u => (φ u : ℂ)) (w : ℂ)
      = Zeta23.paperFT (fun u => ((φ u * (Real.cosh (ε * u) - 1) : ℝ) : ℂ)) (w : ℂ) := by
  simp only [Zeta23.paperFT]
  have i1 := integrable_ofReal_mul_cexp hc hsupp ((w : ℂ) - ε * I)
  have i2 := integrable_ofReal_mul_cexp hc hsupp ((w : ℂ) + ε * I)
  have i3 := integrable_ofReal_mul_cexp hc hsupp (w : ℂ)
  have hadd : Integrable (fun a : ℝ => ((φ a : ℂ) * cexp (I * ((w : ℂ) - ε * I) * a)
      + (φ a : ℂ) * cexp (I * ((w : ℂ) + ε * I) * a)) / 2) := (i1.add i2).div_const 2
  rw [← integral_add i1 i2, ← integral_div, ← integral_sub hadd i3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have e1 : I * ((w : ℂ) - ε * I) * u = I * w * u + (ε * u : ℝ) := by push_cast; ring_nf; rw [I_sq]; ring
  have e2 : I * ((w : ℂ) + ε * I) * u = I * w * u + (-(ε * u) : ℝ) := by push_cast; ring_nf; rw [I_sq]; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  have hcosh : ((Real.cosh (ε * u) : ℝ) : ℂ) = (cexp ((ε * u : ℝ) : ℂ) + cexp ((-(ε * u) : ℝ) : ℂ)) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh]; push_cast; ring_nf
  push_cast
  rw [show ((Real.cosh (ε * u)) : ℂ) = Complex.cosh ((ε : ℂ) * u) by push_cast; rfl] at hcosh
  rw [hcosh]
  push_cast
  ring


theorem integral_sq_eq_intervalIntegral {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    ∫ u, φ u ^ 2 = ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  have : L / 2 ≤ |u| := by
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hsupp u this]; ring

/-- **The shifted real parts stay close.**  For a window `φ` supported in `[−L/2, L/2]` with the
conjugation symmetry of its transform, the grid vectors `Re φ̂(γ − iε − τ_k)` and `φ̂(γ − τ_k)` differ
in square sum by at most `(cosh(εL/2) − 1)² · aL²`. -/
theorem sum_sq_re_shift_sub_le (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (γ ε : ℝ) :
    ∑ k : Fin (Q.d T), ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re
        - (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re) ^ 2
      ≤ (Real.cosh (ε * (Q.L T / 2)) - 1) ^ 2 * (Q.a T * Q.L T ^ 2) := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set ψ : ℝ → ℂ := fun u => ((φ u * (Real.cosh (ε * u) - 1) : ℝ) : ℂ) with hψ
  have hψc : Continuous ψ := by simp only [hψ]; fun_prop
  have hψs : ∀ u, L / 2 ≤ |u| → ψ u = 0 := fun u hu => by simp [hψ, hsupp u hu]
  -- pointwise identity
  have hpt : ∀ k : Fin (Q.d T), ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re
      - (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re) ^ 2
      ≤ ‖Zeta23.paperFT ψ ((γ - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 := by
    intro k
    set w : ℝ := γ - Q.tau T k with hw
    have hz1 : (γ : ℂ) - ε * I - Q.tau T k = (w : ℂ) - ε * I := by rw [hw]; push_cast; ring
    have hz2 : (γ : ℂ) - Q.tau T k = (w : ℂ) := by simp [hw]
    have hwgrid : ((γ - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / L)) : ℝ) : ℂ) = (w : ℂ) := by
      simp only [hw, Zeta23.Params.tau, Zeta23.Params.hgrid, hLdef]
    rw [hz1, hz2, hwgrid]
    have hconj' : Q.phiHat T ((w : ℂ) + ε * I) = starRingEnd ℂ (Q.phiHat T ((w : ℂ) - ε * I)) := by
      rw [← hconj]; congr 1; simp [Complex.conj_ofReal]
    have hre : (Q.phiHat T ((w : ℂ) - ε * I)).re
        = ((Q.phiHat T ((w : ℂ) - ε * I) + Q.phiHat T ((w : ℂ) + ε * I)) / 2).re := by
      rw [hconj']; simp [Complex.add_re, Complex.conj_re, Complex.div_ofNat_re]
    have hdiff := paperFT_cosh_shift_sub (L := L) (φ := φ) (by simpa [hφ] using hc)
      (by simpa [hφ, hLdef] using hsupp) w ε
    have hdiff' : (Q.phiHat T ((w : ℂ) - ε * I)).re - (Q.phiHat T (w : ℂ)).re
        = (Zeta23.paperFT ψ (w : ℂ)).re := by
      rw [hre, ← Complex.sub_re]
      have : (Q.phiHat T ((w : ℂ) - ε * I) + Q.phiHat T ((w : ℂ) + ε * I)) / 2 - Q.phiHat T (w : ℂ)
          = Zeta23.paperFT ψ (w : ℂ) := by
        simpa [Zeta23.Params.phiHat, hφ, hψ] using hdiff
      rw [this]
    rw [hdiff']
    have := Complex.abs_re_le_norm (Zeta23.paperFT ψ (w : ℂ))
    have h0 := abs_nonneg (Zeta23.paperFT ψ (w : ℂ)).re
    rw [← sq_abs]
    exact pow_le_pow_left₀ h0 this 2
  -- sum over the grid
  have hinj : Function.Injective (fun k : Fin (Q.d T) => (((k : ℕ) : ℤ))) := by
    intro a b h; simp only [Nat.cast_inj] at h; exact Fin.ext h
  have hsum : ∑ k : Fin (Q.d T),
      ‖Zeta23.paperFT ψ ((γ - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2
      ≤ L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 := by
    have h := sum_norm_sq_paperFT_grid_le hL hψc hψs γ T
      (Finset.univ.image (fun k : Fin (Q.d T) => (((k : ℕ) : ℤ))))
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)] at h
    exact h
  -- the integral bound
  have hint : ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2
      ≤ (Real.cosh (ε * (L / 2)) - 1) ^ 2 * ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => ‖ψ u‖ ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => (Real.cosh (ε * (L / 2)) - 1) ^ 2 * φ u ^ 2).intervalIntegrable _ _
    intro u hu
    have hu' : |u| ≤ L / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [hψ, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hc1 : 0 ≤ Real.cosh (ε * u) - 1 := by linarith [Real.one_le_cosh (ε * u)]
    have hc2 : Real.cosh (ε * u) ≤ Real.cosh (ε * (L / 2)) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
      exact mul_le_mul_of_nonneg_left hu' (abs_nonneg ε)
    have : (Real.cosh (ε * u) - 1) ^ 2 ≤ (Real.cosh (ε * (L / 2)) - 1) ^ 2 :=
      pow_le_pow_left₀ hc1 (by linarith) 2
    nlinarith [sq_nonneg (φ u)]
  have ha : Q.a T * L ^ 2 = L * ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 := by
    simp only [Zeta23.Params.a, hLdef, hφ]
    rw [integral_sq_eq_intervalIntegral hL (by simpa [hφ, hLdef] using hsupp)]
    field_simp
    rfl
  calc _ ≤ ∑ k : Fin (Q.d T),
        ‖Zeta23.paperFT ψ ((γ - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hpt k
    _ ≤ L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 := hsum
    _ ≤ L * ((Real.cosh (ε * (L / 2)) - 1) ^ 2 * ∫ u in (-(L / 2))..(L / 2), φ u ^ 2) :=
        mul_le_mul_of_nonneg_left hint hL.le
    _ = _ := by rw [ha]; ring

/-- The cosh average of the shifted transforms is the transform of `φ·cosh(ε·)`. -/
theorem paperFT_cosh_avg {φ : ℝ → ℝ} {L : ℝ} (hc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w ε : ℝ) :
    (Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) - ε * I)
        + Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) + ε * I)) / 2
      = Zeta23.paperFT (fun u => ((φ u * Real.cosh (ε * u) : ℝ) : ℂ)) (w : ℂ) := by
  have h := paperFT_cosh_shift_sub hc hsupp w ε
  have hlin : Zeta23.paperFT (fun u => ((φ u * Real.cosh (ε * u) : ℝ) : ℂ)) (w : ℂ)
      = Zeta23.paperFT (fun u => ((φ u * (Real.cosh (ε * u) - 1) : ℝ) : ℂ)) (w : ℂ)
        + Zeta23.paperFT (fun u => (φ u : ℂ)) (w : ℂ) := by
    simp only [Zeta23.paperFT]
    have hc' : Continuous fun u => φ u * (Real.cosh (ε * u) - 1) := by fun_prop
    have hs' : ∀ u, L / 2 ≤ |u| → φ u * (Real.cosh (ε * u) - 1) = 0 := fun u hu => by
      rw [hsupp u hu, zero_mul]
    rw [← integral_add (integrable_ofReal_mul_cexp hc' hs' _) (integrable_ofReal_mul_cexp hc hsupp _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    push_cast
    ring
  rw [hlin, ← h]
  ring

/-- A real translation of the argument is a modulation of the window. -/
theorem paperFT_add_ofReal (ψ : ℝ → ℂ) (z : ℂ) (Δ : ℝ) :
    Zeta23.paperFT ψ (z + Δ) = Zeta23.paperFT (fun u => ψ u * cexp (I * Δ * u)) z := by
  simp only [Zeta23.paperFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc (ψ u), ← Complex.exp_add]
  congr 2
  ring

theorem integrable_mul_cexp {ψ : ℝ → ℂ} {L : ℝ} (hc : Continuous ψ)
    (hsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (z : ℂ) :
    Integrable (fun u : ℝ => ψ u * cexp (I * z * u)) := by
  have hcs : HasCompactSupport ψ :=
    Zeta23.hasCompactSupport_of_support_subset_abs (Λ := L / 2) fun u hu => by
      by_contra h
      exact hu (hsupp u (le_of_lt (not_le.mp h)))
  have hcs' : HasCompactSupport (fun u : ℝ => ψ u * cexp (I * z * u)) :=
    HasCompactSupport.mul_right (f := ψ) (f' := fun u : ℝ => cexp (I * z * u)) hcs
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs'

/-- **Polarised sampling Parseval, complex partner.**  For real continuous `φ` with `φ̂` real on
the grid and complex continuous `ψ`, both supported in `[−L/2, L/2]`,
`Σ_k φ̂(w_k) Re ψ̂(w_k) = L ∫ φ Re ψ`. -/
theorem hasSum_re_mul_re_paperFT_grid {φ : ℝ → ℝ} {ψ : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hφ : Continuous φ) (hψ : Continuous ψ) (hsφ : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hsψ : ∀ u, L / 2 ≤ |u| → ψ u = 0) (γ T : ℝ) (hreal : ∀ k : ℤ,
      (Zeta23.paperFT (fun u => (φ u : ℂ)) ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)).im = 0) :
    HasSum (fun k : ℤ =>
        (Zeta23.paperFT (fun u => (φ u : ℂ)) ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)).re
          * (Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)).re)
      (L * ∫ u in (-(L / 2))..(L / 2), φ u * (ψ u).re) := by
  set a : ℝ → ℂ := fun u => (φ u : ℂ) with ha
  have hac : Continuous a := by simp only [ha]; fun_prop
  have has : ∀ u, L / 2 ≤ |u| → a u = 0 := fun u hu => by simp [ha, hsφ u hu]
  have hp := hasSum_norm_sq_paperFT_grid (ψ := fun u => a u + ψ u) hL (hac.add hψ)
    (fun u hu => by simp [has u hu, hsψ u hu]) γ T
  have hm := hasSum_norm_sq_paperFT_grid (ψ := fun u => a u - ψ u) hL (hac.sub hψ)
    (fun u hu => by simp [has u hu, hsψ u hu]) γ T
  have hd := (hp.sub hm).div_const 4
  have hlin : ∀ z, Zeta23.paperFT (fun u => a u + ψ u) z
        = Zeta23.paperFT a z + Zeta23.paperFT ψ z ∧
      Zeta23.paperFT (fun u => a u - ψ u) z = Zeta23.paperFT a z - Zeta23.paperFT ψ z := by
    intro z
    have i1 := integrable_mul_cexp hac has z
    have i2 := integrable_mul_cexp hψ hsψ z
    simp only [Zeta23.paperFT]
    refine ⟨?_, ?_⟩
    · rw [← integral_add i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only; ring
    · rw [← integral_sub i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only; ring
  have hval : L * ∫ u in (-(L / 2))..(L / 2), φ u * (ψ u).re
      = ((L * ∫ u in (-(L / 2))..(L / 2), ‖a u + ψ u‖ ^ 2)
          - L * ∫ u in (-(L / 2))..(L / 2), ‖a u - ψ u‖ ^ 2) / 4 := by
    rw [← mul_sub, ← intervalIntegral.integral_sub]
    · rw [mul_div_assoc, ← intervalIntegral.integral_div]
      congr 1
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [ha]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
        Complex.normSq_sub]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    · exact (by fun_prop : Continuous fun u => ‖a u + ψ u‖ ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => ‖a u - ψ u‖ ^ 2).intervalIntegrable _ _
  rw [hval]
  refine hd.congr_fun fun k => ?_
  rw [(hlin _).1, (hlin _).2]
  set x := Zeta23.paperFT a ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)
  set y := Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)
  have hx : x.im = 0 := hreal k
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
    Complex.normSq_sub]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hx]
  ring
/-- `cosh(5/4) ≤ 2`. -/
theorem cosh_five_quarters_le_two : Real.cosh (5 / 4) ≤ 2 := by
  have he := Real.exp_one_lt_d9
  have hq : Real.exp (1 / 4) ≤ 4 / 3 := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    have h4 : Real.exp (1 / 4 : ℝ) * Real.exp (-(1 / 4 : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : 0 < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
    nlinarith
  have hy : Real.exp (5 / 4) ≤ 363 / 100 := by
    have : Real.exp (5 / 4) = Real.exp 1 * Real.exp (1 / 4) := by rw [← Real.exp_add]; norm_num
    rw [this]
    have := Real.exp_pos (1 / 4 : ℝ)
    nlinarith
  have hy1 : 1 ≤ Real.exp (5 / 4) := Real.one_le_exp (by norm_num)
  have hinv : Real.exp (5 / 4) * Real.exp (-(5 / 4)) = 1 := by rw [← Real.exp_add]; simp
  have hz := Real.exp_pos (-(5 / 4 : ℝ))
  rw [Real.cosh_eq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hy1)]

theorem a_mul_L_sq_eq (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0) :
    Q.a T * Q.L T ^ 2 = Q.L T * ∫ u in (-(Q.L T / 2))..(Q.L T / 2), Q.phi T u ^ 2 := by
  simp only [Zeta23.Params.a]
  rw [integral_sq_eq_intervalIntegral hL hsupp]
  field_simp

/-- Under the conjugation symmetry, the transform of `φ·cosh(ε·)` at a real point `w` is the real
number `Re φ̂(w − iε)`. -/
theorem paperFT_cosh_eq_re (Q : Zeta23.Params) (T : ℝ) (hc : Continuous (Q.phi T))
    (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0) (hconj : Zeta23.ZeroSide.PhiHatConj T Q)
    (w ε : ℝ) :
    Zeta23.paperFT (fun u => ((Q.phi T u * Real.cosh (ε * u) : ℝ) : ℂ)) (w : ℂ)
      = ((Q.phiHat T ((w : ℂ) - ε * I)).re : ℂ) := by
  rw [← paperFT_cosh_avg hc hsupp w ε]
  have hconj' : Q.phiHat T ((w : ℂ) + ε * I) = starRingEnd ℂ (Q.phiHat T ((w : ℂ) - ε * I)) := by
    rw [← hconj]; congr 1; simp [Complex.conj_ofReal]
  change (Q.phiHat T ((w : ℂ) - ε * I) + Q.phiHat T ((w : ℂ) + ε * I)) / 2 = _
  rw [hconj']
  apply Complex.ext <;> simp

theorem overlap_bound_aux_ge {L c I₀ I₁ I₂ C c₀ : ℝ} (hL : 0 < L) (hcI : c = L * I₀)
    (hI₀ : 0 < I₀) (hI₂ : 0 < I₂) (hC : 0 < C) (key : c₀ ^ 2 * (I₀ * I₂) ≤ C * I₁ ^ 2) :
    2 * c₀ ^ 2 / C - 1 ≤ 2 * (L * I₁ / c) ^ 2 / (L * I₂ / c) - 1 := by
  subst hcI
  have e : 2 * (L * I₁ / (L * I₀)) ^ 2 / (L * I₂ / (L * I₀)) = 2 * I₁ ^ 2 / (I₀ * I₂) := by
    field_simp
  rw [e, sub_le_sub_iff_right, div_le_div_iff₀ hC (mul_pos hI₀ hI₂)]
  nlinarith

open GaloisForLFunctions.HilbertMetric in
/-- **Lens overlap cost, quantitative.**  Let `f_k = Re φ̂(γ − τ_k)/√c` and
`g_k = Re φ̂(γ' − iε − τ_k)/√c`, `c = aL²`, on the grid `k < d`.  If `|γ' − γ|·L/2 ≤ π/2` and
`cos((γ' − γ)L/2) > 0`, then `2cos²((γ' − γ)L/2)/cosh(εL/2) − 1 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`.  On the full grid
`⟨f,g⟩ = ∫φ²cosh(ε·)cos((γ'−γ)·)/∫φ² ≥ cos((γ'−γ)L/2)·J`, `J = ∫φ²cosh(ε·)/∫φ² ≥ 1`, and
`‖g‖² = ∫φ²cosh²(ε·)/∫φ² ≤ cosh(εL/2)·J`; the overlap criterion transfers
its full-grid lower bound to the truncated grid. -/
theorem lens_overlap_cost_ge (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (hreal : Zeta23.ZeroSide.PhiHatReal T Q)
    (ha : 0 < Q.a T) (γ γ' ε : ℝ) (hΔ : |γ' - γ| * (Q.L T / 2) ≤ Real.pi / 2)
    (hpos : 0 < Real.cos ((γ' - γ) * (Q.L T / 2))) :
    2 * Real.cos ((γ' - γ) * (Q.L T / 2)) ^ 2 / Real.cosh (ε * (Q.L T / 2)) - 1
      ≤ 1 + 2 * (∑ k : Fin (Q.d T),
          (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)
            * ((Q.phiHat T ((γ' : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2))) ^ 2
        / (∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ' : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2)
      - 2 * ∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2 := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set c := Q.a T * L ^ 2 with hcdef
  set Δ := γ' - γ with hΔdef
  set C := Real.cosh (ε * (L / 2)) with hCdef
  set c₀ := Real.cos (Δ * (L / 2)) with hc₀def
  have hc0 : 0 < c := by positivity
  -- the modulated partner window
  set b : ℝ → ℂ := fun u => ((φ u * Real.cosh (ε * u) : ℝ) : ℂ) * cexp (I * Δ * u) with hb
  have hCc : Continuous fun u => φ u * Real.cosh (ε * u) := hc.mul (by fun_prop)
  have hCs : ∀ u, L / 2 ≤ |u| → φ u * Real.cosh (ε * u) = 0 := fun u hu => by
    rw [show φ u = 0 from hsupp u hu, zero_mul]
  have hbc : Continuous b := by simp only [hb]; fun_prop
  have hbs : ∀ u, L / 2 ≤ |u| → b u = 0 := fun u hu => by
    simp only [hb]; rw [hCs u hu, Complex.ofReal_zero, zero_mul]
  have hbre : ∀ u, (b u).re = φ u * Real.cosh (ε * u) * Real.cos (Δ * u) := fun u => by
    simp only [hb]
    rw [show I * (Δ : ℂ) * (u : ℂ) = ((Δ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hbnorm : ∀ u, ‖b u‖ ^ 2 = (φ u * Real.cosh (ε * u)) ^ 2 := fun u => by
    simp only [hb]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show I * (Δ : ℂ) * (u : ℂ) = ((Δ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, sq_abs]
  set I₀ := ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 with hI₀
  set J := ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.cosh (ε * u) with hJ
  set I₁ := ∫ u in (-(L / 2))..(L / 2), φ u * (b u).re with hI₁
  set I₂ := ∫ u in (-(L / 2))..(L / 2), ‖b u‖ ^ 2 with hI₂
  have hcI : c = L * I₀ := a_mul_L_sq_eq Q T hL hsupp
  have hI₀pos : 0 < I₀ := by
    have : 0 < L * I₀ := hcI ▸ hc0
    exact pos_of_mul_pos_right this hL.le
  set w : ℤ → ℝ := fun j => γ - (T + j * (2 * Real.pi / L)) with hw
  set F : ℤ → ℝ := fun j => (Zeta23.paperFT (fun u => (φ u : ℂ)) (w j)).re / Real.sqrt c with hF
  set G : ℤ → ℝ := fun j => (Zeta23.paperFT b (w j)).re / Real.sqrt c with hG
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hsqc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  -- `b̂` on the grid is the real number `Re φ̂(γ' − iε − τ)`
  have hbgrid : ∀ j : ℤ, Zeta23.paperFT b ((w j : ℝ) : ℂ)
      = ((Q.phiHat T ((((w j + Δ) : ℝ) : ℂ) - ε * I)).re : ℂ) := by
    intro j
    rw [← paperFT_cosh_eq_re Q T hc hsupp hconj (w j + Δ) ε]
    rw [show (((w j + Δ) : ℝ) : ℂ) = ((w j : ℝ) : ℂ) + (Δ : ℝ) by push_cast; ring,
      paperFT_add_ofReal]
  -- the full-grid square sum of `F` is at most one
  have hFt : ∀ t : Finset ℤ, ∑ j ∈ t, F j ^ 2 ≤ 1 := by
    intro t
    have h := sum_norm_sq_paperFT_grid_le (ψ := fun u => (φ u : ℂ)) hL (by fun_prop)
      (fun u hu => by simp [show φ u = 0 from hsupp u hu]) γ T t
    have hI : ∫ u in (-(L / 2))..(L / 2), ‖(φ u : ℂ)‖ ^ 2 = I₀ :=
      intervalIntegral.integral_congr fun u _ => by simp [Complex.norm_real, sq_abs]
    rw [hI, ← hcI] at h
    simp only [hF, div_pow, hsqc, ← Finset.sum_div]
    rw [div_le_one hc0]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) h
    have := Complex.abs_re_le_norm (Zeta23.paperFT (fun u => (φ u : ℂ)) (w j))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hreal' : ∀ j : ℤ, (Zeta23.paperFT (fun u => (φ u : ℂ)) ((w j : ℝ) : ℂ)).im = 0 := by
    intro j
    have := hreal (w j)
    change Q.phiHat T (w j) = _ at this
    change (Q.phiHat T (w j)).im = 0
    rw [this, Complex.ofReal_im]
  have hFG : HasSum (fun j => F j * G j) (L * I₁ / c) := by
    have h := (hasSum_re_mul_re_paperFT_grid hL hc hbc hsupp hbs γ T hreal').div_const c
    refine h.congr_fun fun j => ?_
    simp only [hF, hG]
    rw [div_mul_div_comm, hsq]
  have hGG : HasSum (fun j => G j ^ 2) (L * I₂ / c) := by
    have h := (hasSum_norm_sq_paperFT_grid (ψ := b) hL hbc hbs γ T).div_const c
    refine h.congr_fun fun j => ?_
    simp only [hG, div_pow, hsqc]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have him : (Zeta23.paperFT b ((w j : ℝ) : ℂ)).im = 0 := by
      rw [hbgrid j, Complex.ofReal_im]
    rw [him]
    ring
  -- the integral comparisons
  have hc₀nn : 0 ≤ c₀ := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have := neg_abs_le (Δ * (L / 2))
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)] at this
      linarith
    · have := le_abs_self (Δ * (L / 2))
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)] at this
      linarith
  have hI0J : I₀ ≤ J := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => φ u ^ 2 * Real.cosh (ε * u)).intervalIntegrable _ _
    intro u _
    have := Real.one_le_cosh (ε * u)
    nlinarith [sq_nonneg (φ u)]
  have hI1J : c₀ * J ≤ I₁ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => c₀ * (φ u ^ 2 * Real.cosh (ε * u))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => φ u * (b u).re).intervalIntegrable _ _
    intro u hu
    have hu' : |u| ≤ L / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    rw [hbre u]
    have hcos : c₀ ≤ Real.cos (Δ * u) := by
      rw [hc₀def, ← Real.cos_abs (Δ * (L / 2)), ← Real.cos_abs (Δ * u)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      · rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
        linarith [Real.pi_pos]
      · rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
        exact mul_le_mul_of_nonneg_left hu' (abs_nonneg Δ)
    have hpos : 0 ≤ φ u ^ 2 * Real.cosh (ε * u) :=
      mul_nonneg (sq_nonneg _) (by linarith [Real.one_le_cosh (ε * u)])
    have : φ u * (φ u * Real.cosh (ε * u) * Real.cos (Δ * u))
        = (φ u ^ 2 * Real.cosh (ε * u)) * Real.cos (Δ * u) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hcos hpos]
  have hI2J : I₂ ≤ C * J := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => ‖b u‖ ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => C * (φ u ^ 2 * Real.cosh (ε * u))).intervalIntegrable _ _
    intro u hu
    have hu' : |u| ≤ L / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    rw [hbnorm u]
    have hc1 := Real.one_le_cosh (ε * u)
    have hc2 : Real.cosh (ε * u) ≤ C := by
      rw [hCdef, Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
      exact mul_le_mul_of_nonneg_left hu' (abs_nonneg ε)
    have hφ2 := sq_nonneg (φ u)
    have : (φ u * Real.cosh (ε * u)) ^ 2 = φ u ^ 2 * Real.cosh (ε * u) * Real.cosh (ε * u) := by
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hc2 (mul_nonneg hφ2 (by linarith : (0:ℝ) ≤ Real.cosh (ε * u)))]
  have hC1 : 1 ≤ C := Real.one_le_cosh _
  have hc₀pos : 0 < c₀ := hpos
  have hJpos : 0 < J := lt_of_lt_of_le hI₀pos hI0J
  have hI₁pos : 0 < I₁ := lt_of_lt_of_le (mul_pos hc₀pos hJpos) hI1J
  have hKpos : 0 < L * I₁ / c := by positivity
  -- the overlap criterion on the image of the finite grid
  set s : Finset ℤ := Finset.univ.image (fun k : Fin (Q.d T) => ((k : ℕ) : ℤ)) with hs
  have hinj : Function.Injective (fun k : Fin (Q.d T) => ((k : ℕ) : ℤ)) := by
    intro a b h; simp only [Nat.cast_inj] at h; exact Fin.ext h
  have hcrit := overlap_criterion hFt hFG hGG hKpos s
  have hlow : 2 * c₀ ^ 2 / C - 1 ≤ 2 * (L * I₁ / c) ^ 2 / (L * I₂ / c) - 1 := by
    have hI₂pos : 0 < I₂ := by
      have h1 : I₀ ≤ I₂ := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u => ‖b u‖ ^ 2).intervalIntegrable _ _
        intro u _
        rw [hbnorm u]
        have := Real.one_le_cosh (ε * u)
        have h1 : 1 ≤ Real.cosh (ε * u) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (φ u)]
      linarith
    have k2 : c₀ * J * (c₀ * J) ≤ I₁ * I₁ := mul_le_mul hI1J hI1J (by positivity) hI₁pos.le
    have key : c₀ ^ 2 * (I₀ * I₂) ≤ C * I₁ ^ 2 :=
      calc c₀ ^ 2 * (I₀ * I₂) ≤ c₀ ^ 2 * (J * (C * J)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hI0J hI2J hI₂pos.le hJpos.le) (sq_nonneg _)
        _ = C * (c₀ * J * (c₀ * J)) := by ring
        _ ≤ C * (I₁ * I₁) := mul_le_mul_of_nonneg_left k2 (by linarith)
        _ = C * I₁ ^ 2 := by ring
    exact overlap_bound_aux_ge hL hcI hI₀pos hI₂pos (by linarith) key
  have hFk : ∀ k : Fin (Q.d T), F ((k : ℕ) : ℤ)
      = (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt c := by
    intro k
    have : ((w ((k : ℕ) : ℤ) : ℝ) : ℂ) = (γ : ℂ) - Q.tau T k := by
      simp only [hw, Zeta23.Params.tau, Zeta23.Params.hgrid, hLdef]; push_cast; ring
    simp only [hF]
    rw [this]; rfl
  have hGk : ∀ k : Fin (Q.d T), G ((k : ℕ) : ℤ)
      = (Q.phiHat T ((γ' : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt c := by
    intro k
    have : (γ' : ℂ) - ε * I - Q.tau T k = (((w ((k : ℕ) : ℤ) + Δ) : ℝ) : ℂ) - ε * I := by
      simp only [hw, hΔdef, Zeta23.Params.tau, Zeta23.Params.hgrid, hLdef]; push_cast; ring
    simp only [hG]
    rw [this, hbgrid, Complex.ofReal_re]
  rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_image (fun a _ b _ h => hinj h)] at hcrit
  simp only [hFk, hGk] at hcrit
  linarith

/-- **Lens overlap cost.**  If `|γ' − γ|·L/2 ≤ π/2` and `cosh(εL/2) ≤ 2cos²((γ' − γ)L/2)`, then
`0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²` for the sampled real vectors of `γ` and of `γ' − iε`. -/
theorem lens_overlap_cost (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (hreal : Zeta23.ZeroSide.PhiHatReal T Q)
    (ha : 0 < Q.a T) (γ γ' ε : ℝ) (hΔ : |γ' - γ| * (Q.L T / 2) ≤ Real.pi / 2)
    (hε : Real.cosh (ε * (Q.L T / 2)) ≤ 2 * Real.cos ((γ' - γ) * (Q.L T / 2)) ^ 2) :
    0 ≤ 1 + 2 * (∑ k : Fin (Q.d T),
          (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)
            * ((Q.phiHat T ((γ' : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2))) ^ 2
        / (∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ' : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2)
      - 2 * ∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2 := by
  set L := Q.L T
  set C := Real.cosh (ε * (L / 2))
  set c₀ := Real.cos ((γ' - γ) * (L / 2))
  have hC1 : 1 ≤ C := Real.one_le_cosh _
  have hc₀nn : 0 ≤ c₀ := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have := neg_abs_le ((γ' - γ) * (L / 2))
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)] at this
      linarith
    · have := le_abs_self ((γ' - γ) * (L / 2))
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)] at this
      linarith
  have hc₀pos : 0 < c₀ := by
    rcases hc₀nn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hε
      norm_num at hε
      linarith
  have h := lens_overlap_cost_ge Q T hL hc hsupp hconj hreal ha γ γ' ε hΔ hc₀pos
  have h1 : 1 ≤ 2 * c₀ ^ 2 / C := by rw [le_div_iff₀ (by linarith)]; linarith
  linarith

/-- **Shift overlap cost.**  The lens cost at equal ordinates: if `cosh(εL/2) ≤ 2` then the sampled
real vectors `f_k = Re φ̂(γ − τ_k)/√c` and `g_k = Re φ̂(γ − iε − τ_k)/√c` satisfy
`0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`. -/
theorem shift_overlap_cost (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (hreal : Zeta23.ZeroSide.PhiHatReal T Q)
    (ha : 0 < Q.a T) (γ ε : ℝ) (hε : Real.cosh (ε * (Q.L T / 2)) ≤ 2) :
    0 ≤ 1 + 2 * (∑ k : Fin (Q.d T),
          (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)
            * ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2))) ^ 2
        / (∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2)
      - 2 * ∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2 :=
  lens_overlap_cost Q T hL hc hsupp hconj hreal ha γ γ ε
    (by rw [sub_self, abs_zero, zero_mul]; positivity)
    (by rw [sub_self, zero_mul, Real.cos_zero]; linarith)

end

end RHTower
