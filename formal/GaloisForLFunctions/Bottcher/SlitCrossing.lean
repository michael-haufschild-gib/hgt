/-
# Pinch-crossing square roots on slit annuli

An injective analytic `P` takes the critical value `c` at most once in its band annulus.  Slitting
the annulus along the ray of that single point (any ray if there is none) leaves a simply-connected
domain on which `P − c` is nonvanishing, so `exists_analyticOnNhd_pow_eq` extracts an analytic
square root — the crossing piece whose image spans two adjacent level octaves and bridges the
pinch levels `h/2ʲ` that separate consecutive sub-critical lobe sections.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SlitAnnulus

open Complex Set Filter Metric Topology

namespace Bottcher

/-- A nonzero point is never in the annulus slit along its own argument ray. -/
theorem notMem_slitAnnulus_arg {r R : ℝ} {z : ℂ} (hz : z ≠ 0) :
    z ∉ slitAnnulus r R (Complex.arg z) := by
  rintro ⟨ξ, ⟨-, -, h3, h4⟩, hexp⟩
  have hlog : Complex.exp (Complex.log z) = z := Complex.exp_log hz
  have heq : Complex.exp ξ = Complex.exp (Complex.log z) := by rw [hexp, hlog]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  have him : ξ.im = Complex.arg z + (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simpa [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.log_im] using h
  rw [him] at h3 h4
  have h5 : (0:ℝ) < (n : ℝ) * (2 * Real.pi) := by linarith
  have h6 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
  have h7 : (0:ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
  have h8 : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have h9 : (0:ℤ) < n := by exact_mod_cast h7
  have h10 : n < (1:ℤ) := by exact_mod_cast h8
  omega

/-- **The crossing root.**  For injective analytic `P` with nonvanishing derivative on a band,
some slit annulus carries an analytic square root of `P − c`, itself injective with nonvanishing
derivative. -/
theorem exists_slit_sqrt {P : ℂ → ℂ} {rA rB : ℝ} (hrA : 0 < rA) (hAB : rA < rB)
    (han : AnalyticOnNhd ℂ P (annulusSet rA rB)) (hinj : Set.InjOn P (annulusSet rA rB))
    (hdne : ∀ v ∈ annulusSet rA rB, deriv P v ≠ 0) (c : ℂ) :
    ∃ θ₀ : ℝ, ∃ σr : ℂ → ℂ,
      AnalyticOnNhd ℂ σr (slitAnnulus rA rB θ₀) ∧
      (∀ v ∈ slitAnnulus rA rB θ₀, σr v ^ (2 : ℕ) = P v - c) ∧
      (∀ v ∈ slitAnnulus rA rB θ₀, σr v ≠ 0) ∧
      Set.InjOn σr (slitAnnulus rA rB θ₀) ∧
      (∀ v ∈ slitAnnulus rA rB θ₀, deriv σr v ≠ 0) := by
  classical
  -- the shared construction, given a slit avoiding every c-preimage
  have hmain : ∀ θ₀ : ℝ, (∀ v ∈ slitAnnulus rA rB θ₀, P v ≠ c) →
      ∃ σr : ℂ → ℂ,
        AnalyticOnNhd ℂ σr (slitAnnulus rA rB θ₀) ∧
        (∀ v ∈ slitAnnulus rA rB θ₀, σr v ^ (2 : ℕ) = P v - c) ∧
        (∀ v ∈ slitAnnulus rA rB θ₀, σr v ≠ 0) ∧
        Set.InjOn σr (slitAnnulus rA rB θ₀) ∧
        (∀ v ∈ slitAnnulus rA rB θ₀, deriv σr v ≠ 0) := by
    intro θ₀ hne
    have hWsub : slitAnnulus rA rB θ₀ ⊆ annulusSet rA rB := slitAnnulus_subset hrA hAB
    have hWopen : IsOpen (slitAnnulus rA rB θ₀) := isOpen_slitAnnulus rA rB θ₀
    have hWsc : IsSimplyConnected (slitAnnulus rA rB θ₀) :=
      isSimplyConnected_slitAnnulus θ₀ hrA hAB
    have hg_an : AnalyticOnNhd ℂ (fun v => P v - c) (slitAnnulus rA rB θ₀) := fun v hv =>
      (han v (hWsub hv)).sub analyticAt_const
    have hg_ne : ∀ v ∈ slitAnnulus rA rB θ₀, P v - c ≠ 0 := fun v hv h =>
      hne v hv (sub_eq_zero.mp h)
    obtain ⟨s, hs_an, hs_sq⟩ := exists_analyticOnNhd_pow_eq hWsc hWopen hg_an hg_ne
      (by norm_num : 1 ≤ 2)
    have hs_ne : ∀ v ∈ slitAnnulus rA rB θ₀, s v ≠ 0 := by
      intro v hv h
      have h1 := hs_sq v hv
      rw [h, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
      exact hg_ne v hv h1.symm
    refine ⟨s, hs_an, hs_sq, hs_ne, ?_, ?_⟩
    · intro v₁ h₁ v₂ h₂ heq
      have h3 : P v₁ = P v₂ := by
        have e1 := hs_sq v₁ h₁
        have e2 := hs_sq v₂ h₂
        have h4 : P v₁ - c = P v₂ - c := by rw [← e1, ← e2, heq]
        linear_combination h4
      exact hinj (hWsub h₁) (hWsub h₂) h3
    · intro v hv
      have hs_d : HasDerivAt s (deriv s v) v := (hs_an v hv).differentiableAt.hasDerivAt
      have hLd : HasDerivAt (fun x => s x ^ (2 : ℕ)) (2 * s v * deriv s v) v := by
        have h4 := hs_d.pow 2
        have h5 : (2:ℕ) * s v ^ (2 - 1) * deriv s v = 2 * s v * deriv s v := by
          push_cast
          ring
        rwa [h5] at h4
      have hRd : HasDerivAt (fun x => P x - c) (deriv P v) v :=
        ((han v (hWsub hv)).differentiableAt.hasDerivAt).sub_const c
      have hEqF : (fun x => s x ^ (2 : ℕ)) =ᶠ[nhds v] (fun x => P x - c) := by
        filter_upwards [hWopen.mem_nhds hv] with z hz
        exact hs_sq z hz
      have h7 : HasDerivAt (fun x => P x - c) (2 * s v * deriv s v) v :=
        hLd.congr_of_eventuallyEq hEqF.symm
      have hEqD : deriv P v = 2 * s v * deriv s v := hRd.unique h7
      intro h0
      rw [h0, mul_zero] at hEqD
      exact hdne v (hWsub hv) hEqD
  by_cases hzero : ∃ vz ∈ annulusSet rA rB, P vz = c
  · obtain ⟨vz, hvz, hPvz⟩ := hzero
    have hvzne : vz ≠ 0 := by
      intro h
      rw [h] at hvz
      simp only [annulusSet, mem_setOf_eq, norm_zero] at hvz
      linarith [hvz.1]
    refine ⟨Complex.arg vz, ?_⟩
    apply hmain
    intro v hv h
    have hveq : v = vz := hinj (slitAnnulus_subset hrA hAB hv) hvz (by rw [h, hPvz])
    rw [hveq] at hv
    exact notMem_slitAnnulus_arg hvzne hv
  · refine ⟨0, ?_⟩
    apply hmain
    intro v hv h
    exact hzero ⟨v, slitAnnulus_subset hrA hAB hv, h⟩

end Bottcher
