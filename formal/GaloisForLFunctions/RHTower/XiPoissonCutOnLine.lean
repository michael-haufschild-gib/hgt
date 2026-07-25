import GaloisForLFunctions.RHTower.XiPoissonCutBottomShell
import GaloisForLFunctions.RHTower.XiPoissonCutSplit
import GaloisForLFunctions.RHTower.XiPoissonBottomOnLine

/-!
# A bounded vertical line puts a cut's bottom shell on the critical line

The argument of `XiPoissonBottomOnLine`, run above a height cut.  When the cut is taken at an actual
height the cut's least height is that height, the cut's bottom shell is exactly the copies at that
height, and everything else transfers verbatim: half-plane decay from the cut Phragmén--Lindelöf, the
tail bound from the spectral gap above the cut, and the phase-robust dominance on the shell.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Regrouping a shell sum by displacement. -/
theorem xiShellSum_regroup (S : Finset XiZeroCopy) (a u : ℝ) :
    (∑ q ∈ S, Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
        ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ))
      = ∑ j ∈ S.image (fun q => (xiPoissonPoint q).im),
          ((((S.filter fun q => (xiPoissonPoint q).im = j).card : ℝ) : ℂ) *
              Complex.exp (-(a : ℂ) * I * (j : ℂ))) *
            ((Real.exp (u * j) : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := S.image (fun q => (xiPoissonPoint q).im))
    (fun q hq => Finset.mem_image_of_mem _ hq)
    (fun q => Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
      ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : ∀ q ∈ S.filter (fun q => (xiPoissonPoint q).im = j),
      Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
          ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)
        = Complex.exp (-(a : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ) :=
    fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- At an actual height the cut's bottom shell is the difference of the two lower sets. -/
theorem xiPoissonCutBottomShell_eq_sdiff {g : ℝ} (hg : xiPoissonCutHeight g = g) :
    xiPoissonCutBottomShell g = xiPoissonLower g \ xiPoissonStrictLower g := by
  classical
  ext q
  rw [Finset.mem_sdiff, mem_xiPoissonCutBottomShell, hg]
  simp only [xiPoissonLower, xiPoissonStrictLower, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    mem_xiPoissonCut, not_lt]
  constructor
  · rintro ⟨hge, heq⟩
    exact ⟨le_of_eq heq, le_of_eq heq.symm⟩
  · rintro ⟨hle, hge⟩
    exact ⟨hge, le_antisymm hle hge⟩

/-- **The cut assembly.**  If the cut trace is bounded on a vertical line, every copy in the cut's
bottom shell has nonpositive displacement. -/
theorem xiPoissonPoint_im_nonpos_of_cut_line_bound {g σ C : ℝ} (hσ : 0 < σ)
    (hg : xiPoissonCutHeight g = g)
    (hline : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ xiPoissonCutBottomShell g, (xiPoissonPoint q).im ≤ 0 := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ : ∃ g₂ : ℝ, g < g₂ ∧
      ∀ q ∈ xiPoissonStrictAbove g, g₂ ≤ (xiPoissonPoint q).re := by
    rcases Set.eq_empty_or_nonempty (xiPoissonStrictAbove g) with hE | hNE
    · refine ⟨g + 1, by linarith, fun q hq => ?_⟩
      rw [hE] at hq
      simp at hq
    · obtain ⟨q₀, hq₀, hmin⟩ := exists_min_xiPoissonPoint_re_of_nonempty hNE
      exact ⟨(xiPoissonPoint q₀).re, hq₀, hmin⟩
  set dgap : ℝ := g₂ - g with hdgap
  have hdpos : 0 < dgap := by rw [hdgap]; linarith
  set K : ℝ := ∑' q : xiPoissonStrictAbove g, xiPoissonWeight σ (q : XiZeroCopy) with hK
  set M : ℝ := max C (xiPoissonCutTraceReal g σ) with hM
  set vfun : ℝ → ℝ := fun u => |u| / (2 * dgap) with hvfun
  have hvnn : ∀ u, 0 ≤ vfun u := fun u => div_nonneg (abs_nonneg u) (by linarith)
  have hmaster : ∀ u : ℝ,
      Real.exp (g * vfun u) * ‖xiPoissonCutBottomShellSum g (σ + vfun u) u‖ ≤ M + K := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertical _ _
    have hΘ := norm_xiPoissonCutTraceC_le_of_line_bound (g := g) hσ hline
      (t := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith)
    rw [hre, hg, show σ + vfun u - σ = vfun u from by ring] at hΘ
    have htail := exp_mul_norm_xiPoissonStrictAboveSum_le (σ := σ) (g := g) (g₂ := g₂)
      hσ hg₂ hvnn' u
    have hcancel : Real.exp (|u| / 2) * Real.exp (-(dgap * vfun u)) = 1 := by
      rw [← Real.exp_add]
      have hz : |u| / 2 + -(dgap * vfun u) = 0 := by
        rw [hvfun]
        field_simp
        ring
      rw [hz, Real.exp_zero]
    have hsplit := xiPoissonCutTraceC_split
      (τ := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith) g
    rw [← xiPoissonCutBottomShell_eq_sdiff hg] at hsplit
    have hb : xiPoissonCutBottomShellSum g (σ + vfun u) u =
        xiPoissonCutTraceC g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) -
          xiPoissonStrictAboveSum g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) := by
      rw [hsplit, xiPoissonCutBottomShellSum]
      ring
    have hA : Real.exp (g * vfun u) *
        ‖xiPoissonCutTraceC g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M := by
      refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) ?_
      rw [← mul_assoc, mul_comm (Real.exp (g * vfun u)) M, mul_assoc, ← Real.exp_add,
        show g * vfun u + -(g * vfun u) = 0 from by ring, Real.exp_zero, mul_one]
    have hB : Real.exp (g * vfun u) *
        ‖xiPoissonStrictAboveSum g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ K := by
      refine le_trans htail (le_of_eq ?_)
      rw [← hdgap, ← hK, hcancel, one_mul]
    calc Real.exp (g * vfun u) * ‖xiPoissonCutBottomShellSum g (σ + vfun u) u‖
        ≤ Real.exp (g * vfun u) *
            (‖xiPoissonCutTraceC g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
              ‖xiPoissonStrictAboveSum g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖) := by
          rw [hb]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (g * vfun u) *
            ‖xiPoissonCutTraceC g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
          Real.exp (g * vfun u) *
            ‖xiPoissonStrictAboveSum g (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ := by ring
      _ ≤ M + K := add_le_add hA hB
  have hinner : ∀ u : ℝ,
      ‖∑ q ∈ xiPoissonCutBottomShell g,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
            ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖
        ≤ (M + K) * Real.exp (σ * g) := by
    intro u
    have hfac := xiPoissonCutBottomShellSum_eq g (σ + vfun u) u
    rw [hg] at hfac
    have hheight : ‖Complex.exp (-(((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) * (g : ℂ))‖ =
        Real.exp (-((σ + vfun u) * g)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
      ring
    have hcollapse : Real.exp (g * vfun u) * Real.exp (-((σ + vfun u) * g)) =
        Real.exp (-(σ * g)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h := hmaster u
    rw [hfac, norm_mul, hheight, ← mul_assoc, hcollapse] at h
    have hEa : Real.exp (σ * g) * Real.exp (-(σ * g)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc ‖∑ q ∈ xiPoissonCutBottomShell g,
            Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
              ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖
        = Real.exp (σ * g) *
            (Real.exp (-(σ * g)) *
              ‖∑ q ∈ xiPoissonCutBottomShell g,
                Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
                  ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * g) * (M + K) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = (M + K) * Real.exp (σ * g) := by ring
  set T : Finset ℝ := (xiPoissonCutBottomShell g).image (fun q => (xiPoissonPoint q).im) with hT
  set mult : ℝ → ℝ := fun j =>
    (((xiPoissonCutBottomShell g).filter fun q => (xiPoissonPoint q).im = j).card : ℝ) with hmult
  set Bco : ℝ → ℝ → ℂ := fun u j =>
    ((mult j : ℝ) : ℂ) * Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * (j : ℂ)) with hBco
  have hmpos : ∀ j ∈ T, 0 < mult j := by
    intro j hj
    obtain ⟨q, hqs, hqj⟩ := Finset.mem_image.mp hj
    have hc : 0 < ((xiPoissonCutBottomShell g).filter
        fun q => (xiPoissonPoint q).im = j).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqs, hqj⟩⟩
    simp only [hmult]
    exact_mod_cast hc
  have hBnorm : ∀ (u : ℝ), ∀ j ∈ T, ‖Bco u j‖ = mult j := by
    intro u j _
    rw [hBco, norm_mul, norm_exp_neg_ofReal_mul_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hmult, abs_of_nonneg (Nat.cast_nonneg _)]
  have hbnd : ∀ u : ℝ, ‖∑ j ∈ T, Bco u j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      (M + K) * Real.exp (σ * g) := by
    intro u
    rw [hBco, hmult, hT, ← xiShellSum_regroup (xiPoissonCutBottomShell g) (σ + vfun u) u]
    exact hinner u
  have hkey := HTGeometry.le_zero_of_expSum_norm_le T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro q hq
  exact hkey ((xiPoissonPoint q).im) (Finset.mem_image_of_mem _ hq)

/-- **A bounded cut line puts the cut's bottom shell on the critical line.** -/
theorem xiPoissonPoint_im_eq_zero_of_cut_line_bound {g σ C : ℝ} (hσ : 0 < σ)
    (hg : xiPoissonCutHeight g = g)
    (hline : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ xiPoissonCutBottomShell g, (xiPoissonPoint q).im = 0 := by
  intro q hq
  have h1 := xiPoissonPoint_im_nonpos_of_cut_line_bound hσ hg hline q hq
  have h2 := xiPoissonPoint_im_nonpos_of_cut_line_bound hσ hg hline _
    (mem_xiPoissonCutBottomShell_lineConj hq)
  rw [xiPoissonPoint_lineConj, Complex.conj_im] at h2
  linarith

end

end RHTower
