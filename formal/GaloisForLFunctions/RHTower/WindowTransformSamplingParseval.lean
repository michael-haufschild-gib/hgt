import Zeta23.ZeroSide
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sampling Parseval for window transforms and the cosh shift bound

For a continuous `ψ` supported in `[−L/2, L/2]`, the transform `ψ̂(z) = ∫ ψ(u) e^{izu} du` sampled
on the grid `γ − (T + 2πk/L)` is `L` times the Fourier coefficients of `u ↦ ψ(u)e^{i(γ−T)u}` on that
interval, so Parseval gives `Σ_k |ψ̂(γ − τ_k)|² = L ∫ |ψ|²` (`hasSum_norm_sq_paperFT_grid`).

Applied to `ψ = φ·(cosh(ε·) − 1)`, together with `φ̂(w + iε) = conj φ̂(w − iε)`, this shows that the
real parts of the sampled vectors of a point displaced by `ε` from the real axis stay within
`(cosh(εL/2) − 1)·√(aL²)` of the sampled vector of the axis point (`sum_sq_re_shift_sub_le`).
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

end

end RHTower
