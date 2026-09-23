import GaloisForLFunctions.RHTower.DeningerCapWeight
import GaloisForLFunctions.RHTower.DeningerPoissonSchwartz
import Mathlib.Analysis.MellinInversion

/-!
# The logarithmic weights of Meyer's space are Schwartz

Second-order vanishing at the origin controls the weight `e^{-su}f(e^{-u})` as `u → +∞`, and the
Schwartz decay of `f` controls it as `u → −∞`; in both regimes what is left after the exponentials
cancel is `uᵏe^{−u}`, bounded by `k!`.  Since every derivative of a weight is the weight of another
member of Meyer's space, the same bound holds at every order, so each weight is a Schwartz function
of the logarithmic coordinate.

Through `mellin_eq_fourier` this makes the Mellin transform of a member of Meyer's space integrable
on every vertical line `Re s = s₀` with `s₀ ≥ −1`: the transform on such a line is the Fourier
transform of a Schwartz function.

* `deningerCapSchwartz` : **the weight, as a Schwartz map.**
* `verticalIntegrable_mellin_cap` : **the Mellin transform is integrable on the line.**
-/

open scoped Real SchwartzMap ContDiff FourierTransform
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The two-sided bound -/

theorem norm_deningerCapWeight_le_of_nonneg {s : ℤ} (hs : -1 ≤ s) (k : ℕ) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerMeyerCap) {u : ℝ} (hu : 0 ≤ u) :
    ‖u‖ ^ k * ‖deningerCapWeight s h u‖
      ≤ SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM h)) * (Nat.factorial k : ℝ) := by
  obtain ⟨he, h0, _⟩ := (deningerMeyerCap_mem_iff h).mp hh
  set M : ℝ := SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM h)) with hM
  have hMnn : 0 ≤ M := apply_nonneg _ _
  have hx : ‖h (Real.exp (-u))‖ ≤ M * (Real.exp (-u)) ^ (2 : ℕ) :=
    norm_le_seminorm_mul_sq he h0 _
  have hsq : (Real.exp (-u)) ^ (2 : ℕ) = Real.exp (-(2 * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnormw : ‖deningerCapWeight s h u‖
      = Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖ := by
    rw [deningerCapWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hnormu : ‖u‖ = u := by
    rw [Real.norm_eq_abs, abs_of_nonneg hu]
  rw [hnormw, hnormu]
  have hstep : Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖
      ≤ M * Real.exp (-u) := by
    calc Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖
        ≤ Real.exp (-(s : ℝ) * u) * (M * Real.exp (-(2 * u))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [← hsq]
          exact hx
      _ = M * (Real.exp (-(s : ℝ) * u) * Real.exp (-(2 * u))) := by ring
      _ = M * Real.exp (-((s : ℝ) + 2) * u) := by
          rw [← Real.exp_add]
          congr 2
          ring
      _ ≤ M * Real.exp (-u) := by
          refine mul_le_mul_of_nonneg_left ?_ hMnn
          refine Real.exp_le_exp.mpr ?_
          have hs' : (1 : ℝ) ≤ (s : ℝ) + 2 := by
            have : (-1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
            linarith
          nlinarith
  calc u ^ k * (Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖)
      ≤ u ^ k * (M * Real.exp (-u)) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = M * (u ^ k * Real.exp (-u)) := by ring
    _ ≤ M * (Nat.factorial k : ℝ) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial k hu) hMnn

theorem norm_deningerCapWeight_le_of_nonpos {s : ℤ} (hs : -1 ≤ s) (k : ℕ) (h : 𝓢(ℝ, ℂ))
    {u : ℝ} (hu : u ≤ 0) :
    ‖u‖ ^ k * ‖deningerCapWeight s h u‖
      ≤ SchwartzMap.seminorm ℂ (s + 1).toNat 0 h * (Nat.factorial k : ℝ) := by
  set N : ℕ := (s + 1).toNat with hN
  set P : ℝ := SchwartzMap.seminorm ℂ N 0 h with hP
  have hPnn : 0 ≤ P := apply_nonneg _ _
  have hNs : (N : ℝ) = (s : ℝ) + 1 := by
    have hpos : (0 : ℤ) ≤ s + 1 := by omega
    have hint : ((N : ℤ)) = s + 1 := by
      rw [hN]
      exact Int.toNat_of_nonneg hpos
    have hcast : ((N : ℤ) : ℝ) = ((s + 1 : ℤ) : ℝ) := by rw [hint]
    push_cast at hcast
    exact hcast
  have hxpos : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ h N (Real.exp (-u))
  have hnormx : ‖Real.exp (-u)‖ = Real.exp (-u) := by
    rw [Real.norm_eq_abs, abs_of_pos hxpos]
  rw [hnormx] at hsem
  have hpow : (Real.exp (-u)) ^ N = Real.exp (-(N : ℝ) * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow] at hsem
  have hx : ‖h (Real.exp (-u))‖ ≤ P * Real.exp ((N : ℝ) * u) := by
    have hposexp : (0 : ℝ) < Real.exp (-(N : ℝ) * u) := Real.exp_pos _
    rw [← le_div_iff₀' hposexp] at hsem
    have hinv : P / Real.exp (-(N : ℝ) * u) = P * Real.exp ((N : ℝ) * u) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    rw [hinv] at hsem
    exact hsem
  have hnormw : ‖deningerCapWeight s h u‖
      = Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖ := by
    rw [deningerCapWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hnormu : ‖u‖ = -u := by
    rw [Real.norm_eq_abs, abs_of_nonpos hu]
  rw [hnormw, hnormu]
  have hstep : Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖ ≤ P * Real.exp u := by
    calc Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖
        ≤ Real.exp (-(s : ℝ) * u) * (P * Real.exp ((N : ℝ) * u)) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = P * (Real.exp (-(s : ℝ) * u) * Real.exp ((N : ℝ) * u)) := by ring
      _ = P * Real.exp (((N : ℝ) - (s : ℝ)) * u) := by
          rw [← Real.exp_add]
          congr 2
          ring
      _ = P * Real.exp u := by
          congr 2
          rw [hNs]
          ring
  have hunn : (0 : ℝ) ≤ -u := by linarith
  calc (-u) ^ k * (Real.exp (-(s : ℝ) * u) * ‖h (Real.exp (-u))‖)
      ≤ (-u) ^ k * (P * Real.exp u) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = P * ((-u) ^ k * Real.exp (-(-u))) := by
        rw [neg_neg]
        ring
    _ ≤ P * (Nat.factorial k : ℝ) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial k hunn) hPnn

theorem exists_bound_deningerCapWeight {s : ℤ} (hs : -1 ≤ s) (k : ℕ) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerMeyerCap) :
    ∃ C : ℝ, ∀ u : ℝ, ‖u‖ ^ k * ‖deningerCapWeight s h u‖ ≤ C := by
  refine ⟨max (SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM h)) * (Nat.factorial k : ℝ))
    (SchwartzMap.seminorm ℂ (s + 1).toNat 0 h * (Nat.factorial k : ℝ)), fun u => ?_⟩
  rcases le_total 0 u with hu | hu
  · exact (norm_deningerCapWeight_le_of_nonneg hs k hh hu).trans (le_max_left _ _)
  · exact (norm_deningerCapWeight_le_of_nonpos hs k h hu).trans (le_max_right _ _)

/-! ## The weight as a Schwartz map -/

/-- **The logarithmic weight of a member of Meyer's space, as a Schwartz map.** -/
def deningerCapSchwartz (s : ℤ) (hs : -1 ≤ s) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    𝓢(ℝ, ℂ) where
  toFun := deningerCapWeight s f
  smooth' := contDiff_deningerCapWeight s f
  decay' k n := by
    obtain ⟨C, hC⟩ := exists_bound_deningerCapWeight hs k
      (deningerMeyerCap_capShiftCLM_iterate hf s n)
    refine ⟨C, fun u => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_deningerCapWeight]
    exact hC u

@[simp] theorem deningerCapSchwartz_apply (s : ℤ) (hs : -1 ≤ s) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) (u : ℝ) :
    deningerCapSchwartz s hs f hf u = deningerCapWeight s f u := rfl

/-! ## Integrability on a vertical line -/

/-- **The Mellin transform of a member of Meyer's space is integrable on every vertical line to
the right of `−1`.** -/
theorem verticalIntegrable_mellin_cap (s : ℤ) (hs : -1 ≤ s) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) :
    Complex.VerticalIntegrable (mellin (f : ℝ → ℂ)) (s : ℝ) := by
  have hfun : (fun y : ℝ => mellin (f : ℝ → ℂ) ((s : ℝ) + y * I))
      = fun y : ℝ => 𝓕 ((deningerCapSchwartz s hs f hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (y / (2 * π)) := by
    funext y
    have hre : (((s : ℝ) : ℂ) + (y : ℂ) * I).re = (s : ℝ) := by simp
    have him : (((s : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hfunw : (fun u : ℝ => (Real.exp (-(s : ℝ) * u)) • (f : ℝ → ℂ) (Real.exp (-u)))
        = deningerCapWeight s f := by
      funext u
      rw [deningerCapWeight, Complex.real_smul]
    rw [mellin_eq_fourier, hre, him, hfunw]
    rfl
  have hschwartz : Integrable
      (fun z : ℝ => 𝓕 ((deningerCapSchwartz s hs f hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z) := by
    have hcoe : 𝓕 ((deningerCapSchwartz s hs f hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        = ((𝓕 (deningerCapSchwartz s hs f hf) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourier_coe _).symm
    rw [hcoe]
    exact (𝓕 (deningerCapSchwartz s hs f hf) : 𝓢(ℝ, ℂ)).integrable
  have hscale : Integrable
      (fun y : ℝ => 𝓕 ((deningerCapSchwartz s hs f hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (y / (2 * π))) := by
    have hne : (2 * π) ≠ 0 := by
      have := Real.pi_pos
      positivity
    have hcomp := hschwartz.comp_mul_left' (R := (2 * π)⁻¹) (inv_ne_zero hne)
    refine hcomp.congr ?_
    filter_upwards with y
    field_simp
  show Integrable (fun y : ℝ => mellin (f : ℝ → ℂ) ((s : ℝ) + y * I))
  rw [hfun]
  exact hscale

end RHTower

end
