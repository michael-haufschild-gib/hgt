import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.HTGeometry.FlowTemperedGrowth
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Exact Paley--Wiener periodization at the shifted-Xi hard edge

This module proves the exact Poisson identity underlying Route U's hard-edge compactification.
The mass parameter is encoded as `1 + |r|`, so every declaration is premise-free while the family
remains cofinal. No numerical computation, asymptotic assumption, zero-location hypothesis, or
Riemann-hypothesis premise occurs.
-/

open scoped SchwartzMap FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

/-- Every angular character has temperate growth. -/
theorem hasTemperateGrowth_modulation (x : ℝ) :
    Function.HasTemperateGrowth (modulation x) := by
  refine ⟨contDiff_modulation x, fun n => ⟨0, |x| ^ n, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_modulation]
  simp

/-- Multiplication of a Schwartz amplitude by the positive angular character `exp(i ξ t)`. -/
def routeUAngularModulation (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (modulation (-ξ)) f

@[simp]
theorem routeUAngularModulation_apply
    (f : SchwartzMap ℝ ℂ) (ξ t : ℝ) :
    routeUAngularModulation f ξ t =
      Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * f t := by
  rw [routeUAngularModulation, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_modulation (-ξ))]
  rw [modulation, cexpLin]
  congr 2
  push_cast
  ring

/-- Angular modulation translates the Fourier transform by `ξ / (2π)`. -/
theorem fourier_routeUAngularModulation
    (f : SchwartzMap ℝ ℂ) (ξ w : ℝ) :
    𝓕 (routeUAngularModulation f ξ) w =
      𝓕 f (w - ξ / (2 * Real.pi)) := by
  rw [SchwartzMap.fourier_coe]
  rw [show ((routeUAngularModulation f ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      fun t : ℝ =>
        Complex.exp ((((2 * Real.pi * (ξ / (2 * Real.pi)) * t : ℝ) : ℂ)) *
          Complex.I) * f t by
    funext t
    rw [routeUAngularModulation_apply]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]]
  exact GaloisForLFunctions.HTGeometry.fourierIntegral_exp_mul
    (fun t : ℝ => f t) (ξ / (2 * Real.pi)) w

/-- Positive-exponent Fourier extension, in the angular-frequency convention of Route U. -/
def routeUPositiveFourierExtension (f : SchwartzMap ℝ ℂ) (ξ : ℝ) : ℂ :=
  𝓕 f (-ξ / (2 * Real.pi))

/-- Scaled modulated Poisson summation in Route U's angular-frequency convention. -/
theorem routeU_modulated_scaled_poisson
    (f : SchwartzMap ℝ ℂ) {h : ℝ} (hh : 0 < h) (ξ : ℝ) :
    (h : ℂ) *
        (∑' n : ℤ,
          Complex.exp (Complex.I * (ξ : ℂ) * ((h * (n : ℝ) : ℝ) : ℂ)) *
            f (h * (n : ℝ))) =
      ∑' m : ℤ,
        routeUPositiveFourierExtension f (ξ - 2 * Real.pi * (m : ℝ) / h) := by
  have hp := ccmRationalArchimedeanLatticeTrace_poisson
    (routeUAngularModulation f ξ) hh
  rw [ccmRationalArchimedeanLatticeTrace] at hp
  simp_rw [routeUAngularModulation_apply] at hp
  rw [show ccmRationalArchimedeanLatticeTrace (𝓕 (routeUAngularModulation f ξ)) h⁻¹ =
      ∑' m : ℤ, routeUPositiveFourierExtension f
        (ξ - 2 * Real.pi * (m : ℝ) / h) by
    rw [ccmRationalArchimedeanLatticeTrace]
    apply tsum_congr
    intro m
    rw [routeUPositiveFourierExtension]
    rw [fourier_routeUAngularModulation]
    congr 1
    field_simp [hh.ne', Real.pi_ne_zero]
    ring] at hp
  rw [hp]
  field_simp [hh.ne']

/-- Cofinal positive hard-edge mass, encoded without a positivity premise. -/
def routeUHardEdgeMass (r : ℝ) : ℝ := 1 + |r|

/-- Fourier mesh dual to the hard-edge alias period. -/
def routeUHardEdgeMesh (r : ℝ) : ℝ := 2 / routeUHardEdgeMass r

/-- Alias period corresponding to `routeUHardEdgeMesh`. -/
def routeUHardEdgeAliasPeriod (r : ℝ) : ℝ := Real.pi * routeUHardEdgeMass r

theorem routeUHardEdgeMass_pos (r : ℝ) : 0 < routeUHardEdgeMass r := by
  rw [routeUHardEdgeMass]
  positivity

theorem routeUHardEdgeMesh_pos (r : ℝ) : 0 < routeUHardEdgeMesh r := by
  rw [routeUHardEdgeMesh]
  exact div_pos two_pos (routeUHardEdgeMass_pos r)

theorem routeUHardEdgeMesh_mul_aliasPeriod (r : ℝ) :
    routeUHardEdgeMesh r * routeUHardEdgeAliasPeriod r = 2 * Real.pi := by
  rw [routeUHardEdgeMesh, routeUHardEdgeAliasPeriod]
  field_simp [ne_of_gt (routeUHardEdgeMass_pos r)]

/-- **Exact Route U hard-edge periodization (HEPW.8), premise-free form.**

The cofinal parameter `r` encodes positive mass as `1 + |r|`. The sampled modulated lattice
trace is exactly the complete Fourier alias packet with spacing `π (1 + |r|)`. -/
theorem routeU_hardEdge_periodization
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ) :
    ((routeUHardEdgeMesh r : ℝ) : ℂ) *
        (∑' n : ℤ,
          Complex.exp
              (Complex.I * (ξ : ℂ) *
                (((routeUHardEdgeMesh r) * (n : ℝ) : ℝ) : ℂ)) *
            f (routeUHardEdgeMesh r * (n : ℝ))) =
      ∑' m : ℤ,
        routeUPositiveFourierExtension f
          (ξ + routeUHardEdgeAliasPeriod r * (m : ℝ)) := by
  rw [routeU_modulated_scaled_poisson f (routeUHardEdgeMesh_pos r) ξ]
  calc
    (∑' m : ℤ, routeUPositiveFourierExtension f
        (ξ - 2 * Real.pi * (m : ℝ) / routeUHardEdgeMesh r)) =
        ∑' m : ℤ, routeUPositiveFourierExtension f
          (ξ - routeUHardEdgeAliasPeriod r * (m : ℝ)) := by
      apply tsum_congr
      intro m
      congr 2
      rw [← routeUHardEdgeMesh_mul_aliasPeriod r]
      field_simp [ne_of_gt (routeUHardEdgeMesh_pos r)]
    _ = ∑' m : ℤ, routeUPositiveFourierExtension f
          (ξ + routeUHardEdgeAliasPeriod r * (m : ℝ)) := by
      simpa only [Equiv.neg_apply, Int.cast_neg, mul_neg, sub_neg_eq_add] using
        ((Equiv.neg ℤ).tsum_eq
          (fun m : ℤ => routeUPositiveFourierExtension f
            (ξ - routeUHardEdgeAliasPeriod r * (m : ℝ)))).symm

/-- The positive-exponent Fourier extension as an actual Schwartz map. -/
def routeUPositiveFourierSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ccmRationalArchimedeanDilation (𝓕 f) (-(2 * Real.pi)⁻¹)
    (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)))

@[simp]
theorem routeUPositiveFourierSchwartz_apply
    (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    routeUPositiveFourierSchwartz f ξ = routeUPositiveFourierExtension f ξ := by
  rw [routeUPositiveFourierSchwartz,
    ccmRationalArchimedeanDilation_apply, routeUPositiveFourierExtension]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- Cayley angular phase, rescaled to the cofinal positive hard-edge mass. -/
def routeUHardEdgePhase (r α : ℝ) : ℝ :=
  routeUHardEdgeMass r * Real.arctan (α / routeUHardEdgeMass r)

/-- The Cayley phase always lies in the central half of the alias cell. -/
theorem abs_routeUHardEdgePhase_le_half_aliasPeriod (r α : ℝ) :
    |routeUHardEdgePhase r α| ≤ routeUHardEdgeAliasPeriod r / 2 := by
  have hmass := routeUHardEdgeMass_pos r
  have hatan := Real.arctan_mem_Ioo (α / routeUHardEdgeMass r)
  rw [routeUHardEdgePhase, abs_mul, abs_of_pos hmass,
    routeUHardEdgeAliasPeriod]
  have habs : |Real.arctan (α / routeUHardEdgeMass r)| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨hatan.1.le, hatan.2.le⟩
  nlinarith

/-- Noncentral aliases stay at least half a lattice spacing times their index from the origin. -/
theorem routeU_alias_separation
    {L ξ : ℝ} (hL : 0 < L) (hξ : |ξ| ≤ L / 2) {m : ℤ} (hm : m ≠ 0) :
    L * |(m : ℝ)| / 2 ≤ |ξ + L * (m : ℝ)| := by
  have hmone : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  have htri : L * |(m : ℝ)| ≤ |ξ + L * (m : ℝ)| + |ξ| := by
    calc
      L * |(m : ℝ)| = |L * (m : ℝ)| := by
        rw [abs_mul, abs_of_pos hL]
      _ = |(ξ + L * (m : ℝ)) + (-ξ)| := by
        congr 1
        ring
      _ ≤ |ξ + L * (m : ℝ)| + |-ξ| := abs_add_le _ _
      _ = |ξ + L * (m : ℝ)| + |ξ| := by rw [abs_neg]
  nlinarith [mul_nonneg hL.le (abs_nonneg (m : ℝ))]

/-- Alias period is always positive. -/
theorem routeUHardEdgeAliasPeriod_pos (r : ℝ) :
    0 < routeUHardEdgeAliasPeriod r := by
  rw [routeUHardEdgeAliasPeriod]
  exact mul_pos Real.pi_pos (routeUHardEdgeMass_pos r)

/-- Noncentral term in the Route U Fourier alias packet. -/
def routeUHardEdgeAliasTailTerm
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ) (m : ℤ) : ℂ :=
  if m = 0 then 0
  else routeUPositiveFourierSchwartz f
    (ξ + routeUHardEdgeAliasPeriod r * (m : ℝ))

/-- Complete noncentral Route U alias tail. -/
def routeUHardEdgeAliasTail
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ) : ℂ :=
  ∑' m : ℤ, routeUHardEdgeAliasTailTerm f r ξ m

/-- Coefficient in the arbitrary-power Route U alias-tail majorant. -/
def routeUHardEdgeAliasTailCoefficient
    (f : SchwartzMap ℝ ℂ) (N : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ (ccmRationalArchimedeanDecayExponent N) 0
      (routeUPositiveFourierSchwartz f) *
    2 ^ ccmRationalArchimedeanDecayExponent N

theorem routeUHardEdgeAliasTailCoefficient_nonneg
    (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    0 ≤ routeUHardEdgeAliasTailCoefficient f N := by
  rw [routeUHardEdgeAliasTailCoefficient]
  positivity

/-- Each noncentral alias is bounded by the fixed punctured integral `p`-series kernel. -/
theorem norm_routeUHardEdgeAliasTailTerm_le
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ)
    (hξ : |ξ| ≤ routeUHardEdgeAliasPeriod r / 2) (N : ℕ) (m : ℤ) :
    ‖routeUHardEdgeAliasTailTerm f r ξ m‖ ≤
      (routeUHardEdgeAliasTailCoefficient f N /
          routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N) *
        ccmRationalArchimedeanPSeriesKernel N m := by
  by_cases hm : m = 0
  · subst m
    simp [routeUHardEdgeAliasTailTerm,
      ccmRationalArchimedeanPSeriesKernel]
  · rw [routeUHardEdgeAliasTailTerm, if_neg hm,
      ccmRationalArchimedeanPSeriesKernel, if_neg hm]
    let p := ccmRationalArchimedeanDecayExponent N
    let L := routeUHardEdgeAliasPeriod r
    let v := ξ + L * (m : ℝ)
    let S := SchwartzMap.seminorm ℂ p 0 (routeUPositiveFourierSchwartz f)
    have hL : 0 < L := routeUHardEdgeAliasPeriod_pos r
    have hmone : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hm
    have hlowerpos : 0 < L * |(m : ℝ)| / 2 := by positivity
    have hsep : L * |(m : ℝ)| / 2 ≤ |v| := by
      exact routeU_alias_separation hL hξ hm
    have hvpos : 0 < |v| := lt_of_lt_of_le hlowerpos hsep
    have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ
      (routeUPositiveFourierSchwartz f) p v
    have hnorm :
        ‖routeUPositiveFourierSchwartz f v‖ ≤ S / |v| ^ p := by
      apply (le_div_iff₀ (pow_pos hvpos p)).2
      simpa only [S, Real.norm_eq_abs, norm_iteratedFDeriv_zero, mul_comm] using hsem
    have hden :
        S / |v| ^ p ≤ S / (L * |(m : ℝ)| / 2) ^ p := by
      gcongr
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have habspow : |(m : ℝ)| ^ p = (m : ℝ) ^ p := by
      change |(m : ℝ)| ^ (2 * (N + 1)) =
        (m : ℝ) ^ (2 * (N + 1))
      rw [pow_mul, pow_mul, sq_abs]
    calc
      ‖routeUPositiveFourierSchwartz f v‖ ≤ S / |v| ^ p := hnorm
      _ ≤ S / (L * |(m : ℝ)| / 2) ^ p := hden
      _ = (routeUHardEdgeAliasTailCoefficient f N /
            routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N) *
          (1 / (m : ℝ) ^ ccmRationalArchimedeanDecayExponent N) := by
        rw [routeUHardEdgeAliasTailCoefficient]
        change S / (L * |(m : ℝ)| / 2) ^ p =
          (S * 2 ^ p / L ^ p) * (1 / (m : ℝ) ^ p)
        rw [div_pow, mul_pow, habspow]
        field_simp [hL.ne', hmR]

/-- Full constant in the arbitrary-power Route U alias-tail bound. -/
def routeUHardEdgeAliasTailConstant
    (f : SchwartzMap ℝ ℂ) (N : ℕ) : ℝ :=
  routeUHardEdgeAliasTailCoefficient f N *
    ∑' m : ℤ, ccmRationalArchimedeanPSeriesKernel N m

theorem routeUHardEdgeAliasTailConstant_nonneg
    (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    0 ≤ routeUHardEdgeAliasTailConstant f N := by
  rw [routeUHardEdgeAliasTailConstant]
  exact mul_nonneg (routeUHardEdgeAliasTailCoefficient_nonneg f N)
    (tsum_nonneg (ccmRationalArchimedeanPSeriesKernel_nonneg N))

theorem summable_norm_routeUHardEdgeAliasTailTerm
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ)
    (hξ : |ξ| ≤ routeUHardEdgeAliasPeriod r / 2) (N : ℕ) :
    Summable (fun m : ℤ => ‖routeUHardEdgeAliasTailTerm f r ξ m‖) := by
  let C := routeUHardEdgeAliasTailCoefficient f N /
    routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N
  have hmajor : Summable (fun m : ℤ =>
      C * ccmRationalArchimedeanPSeriesKernel N m) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left C
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => norm_routeUHardEdgeAliasTailTerm_le f r ξ hξ N m) hmajor

/-- Uniform arbitrary-power bound for the complete noncentral Fourier alias tail. -/
theorem norm_routeUHardEdgeAliasTail_le
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ)
    (hξ : |ξ| ≤ routeUHardEdgeAliasPeriod r / 2) (N : ℕ) :
    ‖routeUHardEdgeAliasTail f r ξ‖ ≤
      routeUHardEdgeAliasTailConstant f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  have hnorm := summable_norm_routeUHardEdgeAliasTailTerm f r ξ hξ N
  let C := routeUHardEdgeAliasTailCoefficient f N /
    routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N
  have hmajor : Summable (fun m : ℤ =>
      C * ccmRationalArchimedeanPSeriesKernel N m) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left C
  calc
    ‖routeUHardEdgeAliasTail f r ξ‖ ≤
        ∑' m : ℤ, ‖routeUHardEdgeAliasTailTerm f r ξ m‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℤ, C * ccmRationalArchimedeanPSeriesKernel N m := by
      exact hnorm.tsum_le_tsum
        (fun m => norm_routeUHardEdgeAliasTailTerm_le f r ξ hξ N m) hmajor
    _ = routeUHardEdgeAliasTailConstant f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
      rw [tsum_mul_left, routeUHardEdgeAliasTailConstant]
      dsimp only [C]
      ring

/-- **Route U hard-edge alias decay (the noncentral part of HEPW.9), premise-free form.**

At the actual Cayley phase, every requested even power is available with one fixed Schwartz
seminorm constant, uniformly in the cofinal hard-edge mass. -/
theorem norm_routeUHardEdgeAliasTail_phase_le
    (f : SchwartzMap ℝ ℂ) (r α : ℝ) (N : ℕ) :
    ‖routeUHardEdgeAliasTail f r (routeUHardEdgePhase r α)‖ ≤
      routeUHardEdgeAliasTailConstant f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N :=
  norm_routeUHardEdgeAliasTail_le f r (routeUHardEdgePhase r α)
    (abs_routeUHardEdgePhase_le_half_aliasPeriod r α) N

/-- A complete alias packet is its central Fourier value plus the noncentral tail. -/
theorem tsum_routeUAlias_eq_extension_add_tail
    (f : SchwartzMap ℝ ℂ) (r ξ : ℝ)
    (hξ : |ξ| ≤ routeUHardEdgeAliasPeriod r / 2) :
    (∑' m : ℤ, routeUPositiveFourierExtension f
        (ξ + routeUHardEdgeAliasPeriod r * (m : ℝ))) =
      routeUPositiveFourierExtension f ξ + routeUHardEdgeAliasTail f r ξ := by
  let F : ℤ → ℂ := fun m => routeUPositiveFourierExtension f
    (ξ + routeUHardEdgeAliasPeriod r * (m : ℝ))
  have htailNorm := summable_norm_routeUHardEdgeAliasTailTerm f r ξ hξ 0
  have htail : Summable (routeUHardEdgeAliasTailTerm f r ξ) :=
    Summable.of_norm htailNorm
  have hsingle : Summable (fun m : ℤ =>
      if m = 0 then routeUPositiveFourierExtension f ξ else 0) := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) ?_
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [hm]
  have hF : Summable F := by
    refine (hsingle.add htail).congr ?_
    intro m
    by_cases hm : m = 0
    · subst m
      simp [F, routeUHardEdgeAliasTailTerm]
    · simp [F, routeUHardEdgeAliasTailTerm, hm]
  have hsplit := hF.tsum_eq_add_tsum_ite 0
  change (∑' m : ℤ, F m) = _
  rw [hsplit]
  have hFzero : F 0 = routeUPositiveFourierExtension f ξ := by
    simp [F]
  rw [hFzero, routeUHardEdgeAliasTail]
  congr 1
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    simp [routeUHardEdgeAliasTailTerm]
  · simp [F, routeUHardEdgeAliasTailTerm, hm]

/-- **Exact hard-edge sampling decomposition at the actual Cayley phase.** -/
theorem routeU_hardEdge_periodization_phase_eq_extension_add_tail
    (f : SchwartzMap ℝ ℂ) (r α : ℝ) :
    ((routeUHardEdgeMesh r : ℝ) : ℂ) *
        (∑' n : ℤ,
          Complex.exp
              (Complex.I * ((routeUHardEdgePhase r α : ℝ) : ℂ) *
                (((routeUHardEdgeMesh r) * (n : ℝ) : ℝ) : ℂ)) *
            f (routeUHardEdgeMesh r * (n : ℝ))) =
      routeUPositiveFourierExtension f (routeUHardEdgePhase r α) +
        routeUHardEdgeAliasTail f r (routeUHardEdgePhase r α) := by
  rw [routeU_hardEdge_periodization f r (routeUHardEdgePhase r α)]
  exact tsum_routeUAlias_eq_extension_add_tail f r (routeUHardEdgePhase r α)
    (abs_routeUHardEdgePhase_le_half_aliasPeriod r α)

/-- **Quantitative hard-edge Paley--Wiener sampling bound, premise-free form.**

The exact sampled trace differs from its central Fourier value by an arbitrarily high inverse
power of the hard-edge alias period. -/
theorem norm_routeU_hardEdge_periodization_phase_sub_extension_le
    (f : SchwartzMap ℝ ℂ) (r α : ℝ) (N : ℕ) :
    ‖((routeUHardEdgeMesh r : ℝ) : ℂ) *
          (∑' n : ℤ,
            Complex.exp
                (Complex.I * ((routeUHardEdgePhase r α : ℝ) : ℂ) *
                  (((routeUHardEdgeMesh r) * (n : ℝ) : ℝ) : ℂ)) *
              f (routeUHardEdgeMesh r * (n : ℝ))) -
        routeUPositiveFourierExtension f (routeUHardEdgePhase r α)‖ ≤
      routeUHardEdgeAliasTailConstant f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  rw [routeU_hardEdge_periodization_phase_eq_extension_add_tail]
  simpa only [add_sub_cancel_left] using
    norm_routeUHardEdgeAliasTail_phase_le f r α N

end RHTower
