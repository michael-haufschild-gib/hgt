import GaloisForLFunctions.RHTower.XiSpectralFamilyShell
import GaloisForLFunctions.RHTower.XiPoissonBottomOnLine

/-!
# A bounded vertical line puts an admissible family's bottom shell on the critical line

The assembly, over the interface.  With `v = |u| / (2 (g_2 - g_1))` the half-plane decay holds
`exp(g_1 v) ‖trace‖` bounded and the spectral gap holds `exp(g_1 v) ‖above-bottom‖` bounded, so the
bottom-shell sum is bounded uniformly in `u`.  Shell homogeneity turns it into a finite sum of real
exponentials whose coefficients have constant modulus, and phase-robust dominance forces every
displacement in the shell to be nonpositive; conjugation stability then makes it zero.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

/-- The bottom-shell sum regrouped by displacement. -/
theorem bottomShell_regroup (a u : ℝ) :
    (∑ q ∈ F.bottomShell,
        Complex.exp (-(a : ℂ) * I * ((F.pt q).im : ℂ)) *
          ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ))
      = ∑ j ∈ F.bottomShell.image (fun q => (F.pt q).im),
          ((((F.bottomShell.filter fun q => (F.pt q).im = j).card : ℝ) : ℂ) *
              Complex.exp (-(a : ℂ) * I * (j : ℂ))) *
            ((Real.exp (u * j) : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := F.bottomShell.image (fun q => (F.pt q).im))
    (fun q hq => Finset.mem_image_of_mem _ hq)
    (fun q => Complex.exp (-(a : ℂ) * I * ((F.pt q).im : ℂ)) *
      ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : ∀ q ∈ F.bottomShell.filter (fun q => (F.pt q).im = j),
      Complex.exp (-(a : ℂ) * I * ((F.pt q).im : ℂ)) *
          ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ)
        = Complex.exp (-(a : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ) :=
    fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- **The assembly over the interface.** -/
theorem im_nonpos_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ F.bottomShell, (F.pt q).im ≤ 0 := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ : ∃ g₂ : ℝ, F.bottomHeight < g₂ ∧
      ∀ q ∈ F.aboveBottom, g₂ ≤ (F.pt q).re := by
    rcases Set.eq_empty_or_nonempty F.aboveBottom with hE | hNE
    · refine ⟨F.bottomHeight + 1, by linarith, fun q hq => ?_⟩
      rw [hE] at hq
      exact absurd hq (by simp)
    · exact F.exists_secondHeight hNE
  set dgap : ℝ := g₂ - F.bottomHeight with hdgap
  have hdpos : 0 < dgap := by rw [hdgap]; linarith
  set K : ℝ := ∑' q : F.aboveBottom, F.weight σ (q : XiZeroCopy) with hK
  set M : ℝ := max C (F.traceReal σ) with hM
  set vfun : ℝ → ℝ := fun u => |u| / (2 * dgap) with hvfun
  have hvnn : ∀ u, 0 ≤ vfun u := fun u => div_nonneg (abs_nonneg u) (by linarith)
  have hmaster : ∀ u : ℝ,
      Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSum (σ + vfun u) u‖ ≤ M + K := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertical _ _
    have hΘ := F.norm_traceC_le_of_line_bound hσ hline
      (t := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith)
    rw [hre, show σ + vfun u - σ = vfun u from by ring] at hΘ
    have htail := F.exp_bottomHeight_mul_norm_aboveBottomSum_le hσ hg₂ hvnn' u
    have hcancel : Real.exp (|u| / 2) * Real.exp (-(dgap * vfun u)) = 1 := by
      rw [← Real.exp_add]
      have hz : |u| / 2 + -(dgap * vfun u) = 0 := by
        rw [hvfun]; field_simp; ring
      rw [hz, Real.exp_zero]
    have hsplit := F.traceC_vertical_split (s := σ + vfun u) (by linarith) u
    have hb : F.bottomShellSum (σ + vfun u) u =
        F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) -
          F.aboveBottomSum (σ + vfun u) u := by
      rw [hsplit]; ring
    have hA : Real.exp (F.bottomHeight * vfun u) *
        ‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M := by
      refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) ?_
      rw [← mul_assoc, mul_comm (Real.exp (F.bottomHeight * vfun u)) M, mul_assoc,
        ← Real.exp_add, show F.bottomHeight * vfun u + -(F.bottomHeight * vfun u) = 0 from by
          ring, Real.exp_zero, mul_one]
    have hB : Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSum (σ + vfun u) u‖ ≤ K := by
      refine le_trans htail (le_of_eq ?_)
      rw [← hdgap, ← hK, hcancel, one_mul]
    calc Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSum (σ + vfun u) u‖
        ≤ Real.exp (F.bottomHeight * vfun u) *
            (‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
              ‖F.aboveBottomSum (σ + vfun u) u‖) := by
          rw [hb]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (F.bottomHeight * vfun u) *
            ‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
          Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSum (σ + vfun u) u‖ := by ring
      _ ≤ M + K := add_le_add hA hB
  have hinner : ∀ u : ℝ,
      ‖∑ q ∈ F.bottomShell,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt q).im : ℂ)) *
            ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ)‖
        ≤ (M + K) * Real.exp (σ * F.bottomHeight) := by
    intro u
    have hfac := F.bottomShellSum_eq (σ + vfun u) u
    have hheight : ‖Complex.exp (-(((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) *
        (F.bottomHeight : ℂ))‖ = Real.exp (-((σ + vfun u) * F.bottomHeight)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
      ring
    have hcollapse : Real.exp (F.bottomHeight * vfun u) *
        Real.exp (-((σ + vfun u) * F.bottomHeight)) = Real.exp (-(σ * F.bottomHeight)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h := hmaster u
    rw [hfac, norm_mul, hheight, ← mul_assoc, hcollapse] at h
    have hEa : Real.exp (σ * F.bottomHeight) * Real.exp (-(σ * F.bottomHeight)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖∑ q ∈ F.bottomShell,
            Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt q).im : ℂ)) *
              ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ)‖
        = Real.exp (σ * F.bottomHeight) *
            (Real.exp (-(σ * F.bottomHeight)) *
              ‖∑ q ∈ F.bottomShell,
                Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt q).im : ℂ)) *
                  ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ)‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * F.bottomHeight) * (M + K) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = (M + K) * Real.exp (σ * F.bottomHeight) := by ring
  set T : Finset ℝ := F.bottomShell.image (fun q => (F.pt q).im) with hT
  set mult : ℝ → ℝ := fun j =>
    ((F.bottomShell.filter fun q => (F.pt q).im = j).card : ℝ) with hmult
  set Bco : ℝ → ℝ → ℂ := fun u j =>
    ((mult j : ℝ) : ℂ) * Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * (j : ℂ)) with hBco
  have hmpos : ∀ j ∈ T, 0 < mult j := by
    intro j hj
    obtain ⟨q, hqs, hqj⟩ := Finset.mem_image.mp hj
    have hc : 0 < (F.bottomShell.filter fun q => (F.pt q).im = j).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqs, hqj⟩⟩
    simp only [hmult]
    exact_mod_cast hc
  have hBnorm : ∀ (u : ℝ), ∀ j ∈ T, ‖Bco u j‖ = mult j := by
    intro u j _
    rw [hBco, norm_mul, norm_exp_neg_ofReal_mul_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hmult, abs_of_nonneg (Nat.cast_nonneg _)]
  have hbnd : ∀ u : ℝ, ‖∑ j ∈ T, Bco u j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      (M + K) * Real.exp (σ * F.bottomHeight) := by
    intro u
    rw [hBco, hmult, hT, ← F.bottomShell_regroup (σ + vfun u) u]
    exact hinner u
  have hkey := HTGeometry.le_zero_of_expSum_norm_le T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro q hq
  exact hkey ((F.pt q).im) (Finset.mem_image_of_mem _ hq)

/-- **A bounded vertical line puts the family's bottom shell on the critical line.** -/
theorem im_eq_zero_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ F.bottomShell, (F.pt q).im = 0 := by
  intro q hq
  have h1 := F.im_nonpos_of_line_bound hσ hline q hq
  have h2 := F.im_nonpos_of_line_bound hσ hline _ (F.mem_bottomShell_lineConj hq)
  rw [F.conj_stable, Complex.conj_im] at h2
  linarith

end

end SpectralFamily

end RHTower
