import GaloisForLFunctions.RHTower.XiPoissonVerticalSplit

/-!
# A bounded vertical line puts the bottom shell on the critical line

Chaining the pieces: half-plane decay holds `exp (g_1 v) ‖Theta‖` bounded, the spectral gap holds
`exp (g_1 v) ‖above-bottom‖` bounded once `v` grows linearly in `|u|`, so the bottom-shell sum is
bounded after the same weighting.  In the bottom shell every copy has the same height, so that sum
is a finite combination of real exponentials `exp (u J)` whose coefficients have modulus equal to the
multiplicity -- the phases move with `u`, the moduli do not.  Phase-robust dominance then forces
every displacement to be nonpositive.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

theorem norm_exp_neg_ofReal_mul_I_mul (a j : ℝ) :
    ‖Complex.exp (-(a : ℂ) * I * (j : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-(a : ℂ) * I * (j : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero]

/-- The bottom-shell sum regrouped by displacement. -/
theorem xiPoissonBottomShell_regroup (a u : ℝ) :
    (∑ q ∈ xiPoissonBottomShell,
        Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
          ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ))
      = ∑ j ∈ xiPoissonBottomShell.image (fun q => (xiPoissonPoint q).im),
          ((((xiPoissonBottomShell.filter
                fun q => (xiPoissonPoint q).im = j).card : ℝ) : ℂ) *
              Complex.exp (-(a : ℂ) * I * (j : ℂ))) *
            ((Real.exp (u * j) : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := xiPoissonBottomShell.image (fun q => (xiPoissonPoint q).im))
    (fun q hq => Finset.mem_image_of_mem _ hq)
    (fun q => Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
      ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : ∀ q ∈ xiPoissonBottomShell.filter (fun q => (xiPoissonPoint q).im = j),
      Complex.exp (-(a : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
          ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)
        = Complex.exp (-(a : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ) :=
    fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- **The assembly.**  If the Poisson trace is bounded on one vertical line, every copy in the bottom
shell has nonpositive displacement. -/
theorem xiPoissonPoint_im_nonpos_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ xiPoissonBottomShell, (xiPoissonPoint q).im ≤ 0 := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ : ∃ g₂ : ℝ, xiPoissonBottomHeight < g₂ ∧
      ∀ q ∈ xiPoissonAboveBottom, g₂ ≤ (xiPoissonPoint q).re := by
    rcases Set.eq_empty_or_nonempty xiPoissonAboveBottom with hempty | hne
    · refine ⟨xiPoissonBottomHeight + 1, by linarith, fun q hq => ?_⟩
      rw [hempty] at hq
      simp at hq
    · exact exists_xiPoissonSecondHeight hne
  set d : ℝ := g₂ - xiPoissonBottomHeight with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set K : ℝ := ∑' q : xiPoissonAboveBottom, xiPoissonWeight σ (q : XiZeroCopy) with hK
  set M : ℝ := max C (xiPoissonTraceReal σ) with hM
  set vfun : ℝ → ℝ := fun u => |u| / (2 * d) with hvfun
  have hvnn : ∀ u, 0 ≤ vfun u := fun u => div_nonneg (abs_nonneg u) (by linarith)
  -- Step A: the weighted bottom-shell sum is bounded uniformly in `u`.
  have hmaster : ∀ u : ℝ,
      Real.exp (xiPoissonBottomHeight * vfun u) *
        ‖xiPoissonBottomShellSum (σ + vfun u) u‖ ≤ M + K := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertical _ _
    have hΘ := norm_xiPoissonTraceC_le_of_line_bound hσ hline
      (t := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith)
    rw [hre, show σ + vfun u - σ = vfun u from by ring] at hΘ
    have htail := exp_bottomHeight_mul_norm_aboveBottomSum_le hσ hg₂ hvnn' u
    have hcancel : Real.exp (|u| / 2) * Real.exp (-(d * vfun u)) = 1 := by
      rw [← Real.exp_add]
      have hz : |u| / 2 + -(d * vfun u) = 0 := by
        rw [hvfun]
        field_simp
        ring
      rw [hz, Real.exp_zero]
    have hsplit := xiPoissonTraceC_vertical_split (s := σ + vfun u) (by linarith) u
    have hb : xiPoissonBottomShellSum (σ + vfun u) u =
        xiPoissonTraceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) -
          xiPoissonAboveBottomSum (σ + vfun u) u := by
      rw [hsplit]; ring
    have hA : Real.exp (xiPoissonBottomHeight * vfun u) *
        ‖xiPoissonTraceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M := by
      refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) ?_
      rw [← mul_assoc, mul_comm (Real.exp (xiPoissonBottomHeight * vfun u)) M, mul_assoc,
        ← Real.exp_add, show xiPoissonBottomHeight * vfun u +
          -(xiPoissonBottomHeight * vfun u) = 0 from by ring, Real.exp_zero, mul_one]
    have hB : Real.exp (xiPoissonBottomHeight * vfun u) *
        ‖xiPoissonAboveBottomSum (σ + vfun u) u‖ ≤ K := by
      refine le_trans htail (le_of_eq ?_)
      rw [← hd, ← hK, hcancel, one_mul]
    calc Real.exp (xiPoissonBottomHeight * vfun u) *
          ‖xiPoissonBottomShellSum (σ + vfun u) u‖
        ≤ Real.exp (xiPoissonBottomHeight * vfun u) *
            (‖xiPoissonTraceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
              ‖xiPoissonAboveBottomSum (σ + vfun u) u‖) := by
          rw [hb]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (xiPoissonBottomHeight * vfun u) *
            ‖xiPoissonTraceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
          Real.exp (xiPoissonBottomHeight * vfun u) *
            ‖xiPoissonAboveBottomSum (σ + vfun u) u‖ := by ring
      _ ≤ M + K := add_le_add hA hB
  -- Step B: strip the height factor.
  have hinner : ∀ u : ℝ,
      ‖∑ q ∈ xiPoissonBottomShell,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
            ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖
        ≤ (M + K) * Real.exp (σ * xiPoissonBottomHeight) := by
    intro u
    have hfac := xiPoissonBottomShellSum_eq (σ + vfun u) u
    have hheight : ‖Complex.exp (-(((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) *
        (xiPoissonBottomHeight : ℂ))‖ =
          Real.exp (-((σ + vfun u) * xiPoissonBottomHeight)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
      ring
    have hcollapse : Real.exp (xiPoissonBottomHeight * vfun u) *
        Real.exp (-((σ + vfun u) * xiPoissonBottomHeight)) =
          Real.exp (-(σ * xiPoissonBottomHeight)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h := hmaster u
    rw [hfac, norm_mul, hheight, ← mul_assoc, hcollapse] at h
    have hEa : Real.exp (σ * xiPoissonBottomHeight) *
        Real.exp (-(σ * xiPoissonBottomHeight)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc ‖∑ q ∈ xiPoissonBottomShell,
            Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
              ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖
        = Real.exp (σ * xiPoissonBottomHeight) *
            (Real.exp (-(σ * xiPoissonBottomHeight)) *
              ‖∑ q ∈ xiPoissonBottomShell,
                Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
                  ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ)‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * xiPoissonBottomHeight) * (M + K) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = (M + K) * Real.exp (σ * xiPoissonBottomHeight) := by ring
  -- Step C: regroup by displacement and apply phase-robust dominance.
  set T : Finset ℝ := xiPoissonBottomShell.image (fun q => (xiPoissonPoint q).im) with hT
  set mult : ℝ → ℝ := fun j =>
    ((xiPoissonBottomShell.filter fun q => (xiPoissonPoint q).im = j).card : ℝ) with hmult
  set Bco : ℝ → ℝ → ℂ := fun u j =>
    ((mult j : ℝ) : ℂ) * Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * (j : ℂ)) with hBco
  have hmpos : ∀ j ∈ T, 0 < mult j := by
    intro j hj
    obtain ⟨q, hqs, hqj⟩ := Finset.mem_image.mp hj
    have hc : 0 < (xiPoissonBottomShell.filter fun q => (xiPoissonPoint q).im = j).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqs, hqj⟩⟩
    simp only [hmult]
    exact_mod_cast hc
  have hBnorm : ∀ (u : ℝ), ∀ j ∈ T, ‖Bco u j‖ = mult j := by
    intro u j _
    rw [hBco, norm_mul, norm_exp_neg_ofReal_mul_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hmult, abs_of_nonneg (Nat.cast_nonneg _)]
  have hbnd : ∀ u : ℝ, ‖∑ j ∈ T, Bco u j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      (M + K) * Real.exp (σ * xiPoissonBottomHeight) := by
    intro u
    rw [hBco, hmult, hT, ← xiPoissonBottomShell_regroup (σ + vfun u) u]
    exact hinner u
  have hkey := HTGeometry.le_zero_of_expSum_norm_le T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro q hq
  exact hkey ((xiPoissonPoint q).im) (Finset.mem_image_of_mem _ hq)

/-- Line conjugation sends a Poisson point to its complex conjugate: it fixes the height and negates
the displacement. -/
theorem xiPoissonPoint_lineConj (q : XiZeroCopy) :
    xiPoissonPoint (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (xiPoissonPoint q) := by
  unfold xiPoissonPoint
  rw [xiSpectralPoint_lineConj, Complex.conj_re]
  split_ifs with h
  · rfl
  · rw [map_neg]

/-- The bottom shell is stable under line conjugation. -/
theorem mem_xiPoissonBottomShell_lineConj {q : XiZeroCopy} (hq : q ∈ xiPoissonBottomShell) :
    xiZeroCopyLineConjEquiv q ∈ xiPoissonBottomShell := by
  rw [mem_xiPoissonBottomShell, xiPoissonPoint_lineConj, Complex.conj_re]
  exact mem_xiPoissonBottomShell.mp hq

/-- **A bounded vertical line puts the bottom shell on the critical line.**  Combining the assembly
with the line-conjugation symmetry, which negates displacements while fixing heights. -/
theorem xiPoissonPoint_im_eq_zero_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ xiPoissonBottomShell, (xiPoissonPoint q).im = 0 := by
  intro q hq
  have h1 := xiPoissonPoint_im_nonpos_of_line_bound hσ hline q hq
  have h2 := xiPoissonPoint_im_nonpos_of_line_bound hσ hline _
    (mem_xiPoissonBottomShell_lineConj hq)
  rw [xiPoissonPoint_lineConj, Complex.conj_im] at h2
  linarith

/-- The same statement in the original spectral coordinate: the lowest zeros lie on the critical
line. -/
theorem xiSpectralPoint_im_eq_zero_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q ∈ xiPoissonBottomShell, (xiSpectralPoint q).im = 0 := by
  intro q hq
  have hzero := xiPoissonPoint_im_eq_zero_of_line_bound hσ hline q hq
  rw [xiPoissonPoint] at hzero
  split_ifs at hzero with hcase
  · exact hzero
  · rw [Complex.neg_im, neg_eq_zero] at hzero
    exact hzero

end

end RHTower
