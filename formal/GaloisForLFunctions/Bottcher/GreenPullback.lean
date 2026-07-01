/-
# The dynamical Green function: global functional equation, symmetry, far threshold,
# and the outside-winding certificate

Bricks for the band-tower sections:

* `greenFunctionDyn_quadratic` — `G_c(f_c z) = 2·G_c(z)` on ALL of `ℂ` (both sides `0` on `K_c`;
  on the basin via the orbit-pullback identity);
* `greenFunctionDyn_neg` — `G_c(−z) = G_c(z)`;
* `exists_green_far_threshold` — `{‖z‖ > R₁} ⊆ {G_c > s}`;
* `windInt_eq_zero_of_level_lt` — **the outside certificate**: a closed `C¹` loop at Green levels
  `≤ s` has winding `0` about any point at level `> s` (superlevel connectivity
  `isConnected_green_superlevel` + winding constancy + far-field vanishing).

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenSuperlevel
import GaloisForLFunctions.Bottcher.WindingCertificates
import GaloisForLFunctions.Bottcher.CylinderUnivalence

open Complex Set Filter Metric

namespace Bottcher

/-- Backward boundedness: if `f_c z` has bounded orbit then so does `z`. -/
theorem mem_filledJulia_of_quadratic {c z : ℂ} (h : quadratic c z ∈ filledJulia c) :
    z ∈ filledJulia c := by
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨max C ‖z‖, ?_⟩
  rintro x ⟨k, rfl⟩
  dsimp only
  cases k with
  | zero => simp only [Function.iterate_zero, id_eq]; exact le_max_right C ‖z‖
  | succ m =>
      rw [Function.iterate_succ_apply]
      exact le_trans (hC _ ⟨m, rfl⟩) (le_max_left _ _)

/-- Membership in `K_c` transports through `f_c`. -/
theorem quadratic_mem_filledJulia_iff (c z : ℂ) :
    quadratic c z ∈ filledJulia c ↔ z ∈ filledJulia c := by
  constructor
  · exact mem_filledJulia_of_quadratic
  · intro h
    have := filledJulia_forward h 1
    simpa using this

/-- **Global functional equation of the dynamical Green function**:
`G_c(f_c z) = 2·G_c(z)` on all of `ℂ`. -/
theorem greenFunctionDyn_quadratic (c z : ℂ) :
    greenFunctionDyn c (quadratic c z) = 2 * greenFunctionDyn c z := by
  by_cases hz : z ∈ filledJulia c
  · have hfz : quadratic c z ∈ filledJulia c := (quadratic_mem_filledJulia_iff c z).mpr hz
    unfold greenFunctionDyn
    rw [if_pos hz, if_pos hfz]
    ring
  · have hfz : quadratic c z ∉ filledJulia c := fun h =>
      hz (mem_filledJulia_of_quadratic h)
    unfold greenFunctionDyn
    rw [if_neg hz, if_neg hfz]
    -- pull both back to a common crude iterate
    obtain ⟨N, hNc, hN2, hNeq⟩ := greenLimit_eq_pullback hz
    -- greenLimit (f z) = 2^{-(N-1)}-type identity, via the approximants
    have hval : greenLimit c (quadratic c z)
        = (2 ^ N : ℝ)⁻¹ * (2 * greenLimit c ((quadratic c)^[N] z)) := by
      have htends : Tendsto (greenApprox c (quadratic c z)) atTop
          (nhds ((2 ^ N : ℝ)⁻¹ * (2 * greenLimit c ((quadratic c)^[N] z)))) := by
        rw [← tendsto_add_atTop_iff_nat N]
        have hrel : ∀ m, greenApprox c (quadratic c z) (m + N)
            = (2 ^ N : ℝ)⁻¹ * (2 * greenApprox c ((quadratic c)^[N] z) (m + 1)) := by
          intro m
          unfold greenApprox
          have harg : (quadratic c)^[m + N] (quadratic c z)
              = (quadratic c)^[m + 1] ((quadratic c)^[N] z) := by
            rw [← Function.iterate_succ_apply, ← Function.iterate_add_apply]
            congr 1
            omega
          rw [harg, pow_add, pow_succ]
          field_simp
        simp_rw [hrel]
        have h1 : Tendsto (fun m => greenApprox c ((quadratic c)^[N] z) (m + 1)) atTop
            (nhds (greenLimit c ((quadratic c)^[N] z))) := by
          rw [tendsto_add_atTop_iff_nat 1]
          exact greenApprox_tendsto hNc hN2
        have h2 := h1.const_mul (2 : ℝ)
        have h3 := h2.const_mul ((2 ^ N : ℝ)⁻¹)
        convert h3 using 2
      exact htends.limUnder_eq
    rw [hval, hNeq]
    ring

/-- **Symmetry of the dynamical Green function**: `G_c(−z) = G_c(z)`. -/
theorem greenFunctionDyn_neg (c z : ℂ) :
    greenFunctionDyn c (-z) = greenFunctionDyn c z := by
  have hK : -z ∈ filledJulia c ↔ z ∈ filledJulia c := by
    rw [← quadratic_mem_filledJulia_iff c (-z), ← quadratic_mem_filledJulia_iff c z,
      quadratic_neg]
  by_cases hz : z ∈ filledJulia c
  · unfold greenFunctionDyn
    rw [if_pos hz, if_pos (hK.mpr hz)]
  · unfold greenFunctionDyn
    rw [if_neg hz, if_neg (fun h => hz (hK.mp h))]
    exact greenLimit_neg c z

/-- **Far threshold for the superlevel set**: beyond radius
`max (‖c‖+3) (exp (s+2))`, the Green level exceeds `s`. -/
theorem green_far_gt (c : ℂ) (s : ℝ) :
    ∀ z : ℂ, max (‖c‖ + 3) (Real.exp (s + 2)) < ‖z‖ → s < greenFunctionDyn c z := by
  intro z hz
  have hc3 : ‖c‖ + 3 ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz)
  have hc : ‖c‖ ≤ ‖z‖ := by linarith
  have h2 : 2 < ‖z‖ := by linarith [norm_nonneg c]
  have hK : z ∉ filledJulia c := not_mem_filledJulia hc h2
  have hlb := greenLimit_lower_bound hc h2
  have hlog : s + 2 < Real.log ‖z‖ := by
    have h1 : Real.exp (s + 2) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
    calc s + 2 = Real.log (Real.exp (s + 2)) := (Real.log_exp _).symm
      _ < Real.log ‖z‖ := Real.log_lt_log (Real.exp_pos _) h1
  have hcorr : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 1 := by
    have hz2 : 2 * ‖c‖ ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg c]
    rw [div_le_one (by nlinarith [norm_nonneg c] : (0:ℝ) < ‖z‖ ^ 2)]
    exact hz2
  unfold greenFunctionDyn
  rw [if_neg hK]
  linarith

/-- **The outside-winding certificate.**  A closed `C¹` loop running at Green levels `≤ s`
(`0 < s`) has winding `0` about every point at level `> s`: the superlevel set is connected and
reaches the far field, where the winding vanishes by size. -/
theorem windInt_eq_zero_of_level_lt (c : ℂ) (ℓ : C1Loop) {s : ℝ} (hs : 0 < s)
    (hloop : ∀ θ : ℝ, greenFunctionDyn c (ℓ.γ θ) ≤ s)
    {p : ℂ} (hp : s < greenFunctionDyn c p) :
    windInt ℓ p = 0 := by
  set S : Set ℂ := {z : ℂ | s < greenFunctionDyn c z} with hSdef
  have hSA : ∀ z ∈ S, ℓ.Avoids z := by
    intro z hz θ h
    have h1 : greenFunctionDyn c (ℓ.γ θ) ≤ s := hloop θ
    rw [h] at h1
    exact absurd hz (by simp only [hSdef, mem_setOf_eq]; linarith)
  -- a far point where the winding vanishes by size
  obtain ⟨Mv, hMv0, hMv⟩ := ℓ.exists_velocity_bound
  obtain ⟨Mγ, hMγ0, hMγ⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖ℓ.γ θ‖ ≤ M := by
    obtain ⟨θ₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (by positivity)) (ℓ.cont.norm.continuousOn
        (s := Set.Icc (0:ℝ) (2 * Real.pi)))
    exact ⟨‖ℓ.γ θ₀‖, norm_nonneg _, fun θ hθ => hmax hθ⟩
  set Rq : ℝ := max (max (‖c‖ + 3) (Real.exp (s + 2))) (Mγ + Mv + 1) with hRqdef
  set q : ℂ := ((Rq + 1 : ℝ) : ℂ) with hqdef
  have hRqpos : 0 < Rq := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hqnorm : ‖q‖ = Rq + 1 := by
    rw [hqdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hqS : q ∈ S := by
    show s < greenFunctionDyn c q
    apply green_far_gt c s
    rw [hqnorm]
    exact lt_of_le_of_lt (le_max_left _ _) (by linarith)
  have hpS : p ∈ S := hp
  -- winding about q vanishes: the integrand is uniformly small
  have hqwind : windInt ℓ q = 0 := by
    apply windInt_eq_zero_of_norm_lt ℓ (hSA q hqS)
    have hbound : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * Real.pi),
        ‖(ℓ.γ θ - q)⁻¹ * ℓ.γ' θ‖ ≤ Mv / (Mv + 1) := by
      intro θ hθ
      have hθI : θ ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at hθ
        exact ⟨le_of_lt hθ.1, hθ.2⟩
      have hlow : Mv + 1 ≤ ‖ℓ.γ θ - q‖ := by
        have h1 : ‖q‖ - ‖ℓ.γ θ‖ ≤ ‖ℓ.γ θ - q‖ := by
          have := norm_sub_norm_le q (ℓ.γ θ)
          rw [show ‖q - ℓ.γ θ‖ = ‖ℓ.γ θ - q‖ from norm_sub_rev q (ℓ.γ θ)] at this
          linarith
        have h2 : Mγ + Mv + 1 ≤ Rq := le_max_right _ _
        have h3 : ‖ℓ.γ θ‖ ≤ Mγ := hMγ θ hθI
        rw [hqnorm] at h1
        linarith
      rw [norm_mul, norm_inv]
      have hnz : (0:ℝ) < ‖ℓ.γ θ - q‖ := by linarith
      calc ‖ℓ.γ θ - q‖⁻¹ * ‖ℓ.γ' θ‖
          ≤ (Mv + 1)⁻¹ * Mv := by
            apply mul_le_mul (inv_anti₀ (by linarith) hlow) (hMv θ hθI)
              (norm_nonneg _) (by positivity)
        _ = Mv / (Mv + 1) := by field_simp
    have hnorm : ‖windInt ℓ q‖ ≤ (Mv / (Mv + 1)) * |2 * Real.pi - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
      rw [sub_zero]; exact abs_of_pos (by positivity)
    rw [habs] at hnorm
    have hfrac : Mv / (Mv + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc ‖windInt ℓ q‖ ≤ (Mv / (Mv + 1)) * (2 * Real.pi) := hnorm
      _ < 1 * (2 * Real.pi) := by
          apply mul_lt_mul_of_pos_right hfrac (by positivity)
      _ = 2 * Real.pi := by ring
  -- transport by superlevel connectivity
  have hconn := (isConnected_green_superlevel c hs).isPreconnected
  calc windInt ℓ p = windInt ℓ q := windInt_eq_on_preconnected ℓ hconn hSA hpS hqS
    _ = 0 := hqwind

end Bottcher
