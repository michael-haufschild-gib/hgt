import GaloisForLFunctions.HTGeometry.AbstractSpectralWeightedDecay

/-!
# A bounded vertical line makes a weighted abstract spectral family real

The rigidity theorem carried through a nowhere-vanishing subexponential weight.  Neither of the two
mechanisms of the unweighted proof is sensitive to coefficients: shell homogeneity still factors the
common height out of the bottom shell, and phase-robust dominance only needs the regrouped
coefficients to have positive moduli independent of the vertical variable.  A weight that does not
vanish on the open right half plane therefore hides nothing — boundedness of the weighted trace on
one vertical line still forces every point onto the real axis.
-/

open Complex Filter
open scoped BigOperators

namespace HTGeometry

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} [Nonempty ι] (F : AbstractSpectralFamily ι) (W : SpectralWeight)

/-! ## The weighted bottom shell -/

theorem pt_eq_of_mem_bottomShell {i : ι} (hi : i ∈ F.bottomShell) :
    F.pt i = ((F.bottomHeight : ℝ) : ℂ) + ((F.pt i).im : ℂ) * I := by
  rw [← F.mem_bottomShell.mp hi]
  exact (Complex.re_add_im _).symm

/-- The weighted bottom-shell sum on a vertical line. -/
def bottomShellSumW (σ u : ℝ) : ℂ :=
  ∑ i ∈ F.bottomShell, F.termW W ((σ : ℂ) + (u : ℂ) * I) i

/-- The weighted above-bottom part of the trace on a vertical line. -/
def aboveBottomSumW (s u : ℝ) : ℂ :=
  ∑' i : F.aboveBottom, F.termW W ((s : ℂ) + (u : ℂ) * I) (i : ι)

/-- **Weighted shell homogeneity.**  On the bottom shell the height still factors out. -/
theorem bottomShellSumW_eq (σ u : ℝ) :
    F.bottomShellSumW W σ u =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (F.bottomHeight : ℂ)) *
        ∑ i ∈ F.bottomShell, W.toFun (F.pt i) *
          (Complex.exp (-(σ : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)) := by
  rw [bottomShellSumW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hfac : F.term ((σ : ℂ) + (u : ℂ) * I) i
      = Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (F.bottomHeight : ℂ)) *
        (Complex.exp (-(σ : ℂ) * I * ((F.pt i).im : ℂ)) *
          ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)) := by
    rw [term]
    conv_lhs => rw [F.pt_eq_of_mem_bottomShell hi]
    exact vertLine_factor σ u F.bottomHeight (F.pt i).im
  rw [termW, hfac]
  ring

/-- The weighted trace on a vertical line is its bottom shell plus everything above. -/
theorem traceWC_vertical_split {s : ℝ} (hs : 0 < s) (u : ℝ) :
    F.traceWC W ((s : ℂ) + (u : ℂ) * I)
      = F.bottomShellSumW W s u + F.aboveBottomSumW W s u := by
  have hre : 0 < ((s : ℂ) + (u : ℂ) * I).re := by rw [re_vertLine]; exact hs
  have hsum : Summable (fun i : ι => F.termW W ((s : ℂ) + (u : ℂ) * I) i) :=
    (F.summable_norm_termW W hre).of_norm
  exact (hsum.sum_add_tsum_compl).symm

/-- **The weighted tail bound.**  Moving right by `v` costs the above-bottom part a factor
`exp (-(g₂ - g₁) v)`, which beats the `exp (g₁ v)` weight by the whole spectral gap. -/
theorem exp_bottomHeight_mul_norm_aboveBottomSumW_le {σ : ℝ} (hσ : 0 < σ)
    {g₂ : ℝ} (hg₂ : ∀ i ∈ F.aboveBottom, g₂ ≤ (F.pt i).re)
    {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSumW W (σ + v) u‖ ≤
      Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
        ∑' i : F.aboveBottom, ‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι) := by
  have hsv : 0 < σ + v := by linarith
  have hre : 0 < (((σ + v : ℝ) : ℂ) + (u : ℂ) * I).re := by rw [re_vertLine]; exact hsv
  have hsumnorm := F.summable_norm_termW W hre
  have hsumσ : Summable (fun i : F.aboveBottom =>
      ‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι)) :=
    (F.summable_weightedWeight W hσ).subtype _
  have hterm : ∀ i : F.aboveBottom,
      Real.exp (F.bottomHeight * v) * ‖F.termW W (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ ≤
        Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
          (‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι)) := by
    intro i
    have hR : g₂ ≤ (F.pt (i : ι)).re := hg₂ _ i.2
    have hJ : |(F.pt (i : ι)).im| < 1 / 2 := F.abs_im_lt _
    have hbase : Real.exp (F.bottomHeight * v) *
        ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖
        ≤ Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) * F.weight σ (i : ι) := by
      rw [norm_term, re_vertLine, im_vertLine, weight, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have huJ : u * (F.pt (i : ι)).im ≤ |u| / 2 := by
        calc u * (F.pt (i : ι)).im ≤ |u * (F.pt (i : ι)).im| := le_abs_self _
          _ = |u| * |(F.pt (i : ι)).im| := abs_mul _ _
          _ ≤ |u| * (1 / 2) := mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)
          _ = |u| / 2 := by ring
      nlinarith [hR, hv, huJ]
    rw [termW, norm_mul]
    calc Real.exp (F.bottomHeight * v) *
          (‖W.toFun (F.pt (i : ι))‖ * ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖)
        = ‖W.toFun (F.pt (i : ι))‖ * (Real.exp (F.bottomHeight * v) *
            ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖) := by ring
      _ ≤ ‖W.toFun (F.pt (i : ι))‖ * (Real.exp (|u| / 2) *
            Real.exp (-((g₂ - F.bottomHeight) * v)) * F.weight σ (i : ι)) :=
          mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
      _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
            (‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι)) := by ring
  calc Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSumW W (σ + v) u‖
      ≤ Real.exp (F.bottomHeight * v) *
          ∑' i : F.aboveBottom, ‖F.termW W (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ = ∑' i : F.aboveBottom,
          Real.exp (F.bottomHeight * v) *
            ‖F.termW W (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ := (tsum_mul_left).symm
    _ ≤ ∑' i : F.aboveBottom,
          Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
            (‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι)) :=
        Summable.tsum_le_tsum hterm ((hsumnorm.subtype _).mul_left _) (hsumσ.mul_left _)
    _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
          ∑' i : F.aboveBottom, ‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι) := tsum_mul_left

/-! ## Regrouping the weighted bottom shell -/

/-- The weighted bottom-shell sum regrouped by displacement. -/
theorem bottomShellW_regroup (a u : ℝ) :
    (∑ i ∈ F.bottomShell, W.toFun (F.pt i) *
        (Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
          ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)))
      = ∑ j ∈ F.bottomShell.image (fun i => (F.pt i).im),
          ((((F.bottomShell.filter fun i => (F.pt i).im = j).card : ℝ) : ℂ) *
              (W.toFun (((F.bottomHeight : ℝ) : ℂ) + (j : ℂ) * I) *
                Complex.exp (-(a : ℂ) * I * (j : ℂ)))) *
            ((Real.exp (u * j) : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := F.bottomShell.image (fun i => (F.pt i).im))
    (fun i hi => Finset.mem_image_of_mem _ hi)
    (fun i => W.toFun (F.pt i) *
      (Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
        ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : ∀ i ∈ F.bottomShell.filter (fun i => (F.pt i).im = j),
      W.toFun (F.pt i) *
          (Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))
        = W.toFun (((F.bottomHeight : ℝ) : ℂ) + (j : ℂ) * I) *
            (Complex.exp (-(a : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ)) := by
    intro i hi
    obtain ⟨hshell, hj⟩ := Finset.mem_filter.mp hi
    have hpt : F.pt i = ((F.bottomHeight : ℝ) : ℂ) + (j : ℂ) * I := by
      rw [F.pt_eq_of_mem_bottomShell hshell, hj]
    rw [hj, hpt]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-! ## The weighted rigidity theorem -/

/-- **The weighted assembly.**  A bounded vertical line for the weighted trace makes every
bottom-shell displacement nonpositive. -/
theorem im_nonpos_of_weightedLine_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceWC W ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ i ∈ F.bottomShell, (F.pt i).im ≤ 0 := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ : ∃ g₂ : ℝ, F.bottomHeight < g₂ ∧
      ∀ i ∈ F.aboveBottom, g₂ ≤ (F.pt i).re := by
    rcases Set.eq_empty_or_nonempty F.aboveBottom with hE | hNE
    · refine ⟨F.bottomHeight + 1, by linarith, fun i hi => ?_⟩
      rw [hE] at hi
      exact absurd hi (by simp)
    · exact F.exists_secondHeight hNE
  set dgap : ℝ := g₂ - F.bottomHeight with hdgap
  have hdpos : 0 < dgap := by rw [hdgap]; linarith
  set K : ℝ := ∑' i : F.aboveBottom, ‖W.toFun (F.pt (i : ι))‖ * F.weight σ (i : ι) with hK
  set M : ℝ := max C (F.traceWAbs W σ) with hM
  set vfun : ℝ → ℝ := fun u => |u| / (2 * dgap) with hvfun
  have hvnn : ∀ u, 0 ≤ vfun u := fun u => div_nonneg (abs_nonneg u) (by linarith)
  have hmaster : ∀ u : ℝ,
      Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSumW W (σ + vfun u) u‖ ≤ M + K := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertLine _ _
    have hΘ := F.norm_traceWC_le_of_line_bound W hσ hline
      (t := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith)
    rw [hre, show σ + vfun u - σ = vfun u from by ring] at hΘ
    have htail := F.exp_bottomHeight_mul_norm_aboveBottomSumW_le W hσ hg₂ hvnn' u
    have hcancel : Real.exp (|u| / 2) * Real.exp (-(dgap * vfun u)) = 1 := by
      rw [← Real.exp_add]
      have hz : |u| / 2 + -(dgap * vfun u) = 0 := by
        rw [hvfun]; field_simp; ring
      rw [hz, Real.exp_zero]
    have hsplit := F.traceWC_vertical_split W (s := σ + vfun u) (by linarith) u
    have hb : F.bottomShellSumW W (σ + vfun u) u =
        F.traceWC W (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) - F.aboveBottomSumW W (σ + vfun u) u := by
      rw [hsplit]; ring
    have hA : Real.exp (F.bottomHeight * vfun u) *
        ‖F.traceWC W (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M := by
      refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) ?_
      rw [← mul_assoc, mul_comm (Real.exp (F.bottomHeight * vfun u)) M, mul_assoc,
        ← Real.exp_add, show F.bottomHeight * vfun u + -(F.bottomHeight * vfun u) = 0 from by
          ring, Real.exp_zero, mul_one]
    have hB : Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSumW W (σ + vfun u) u‖ ≤ K := by
      refine le_trans htail (le_of_eq ?_)
      rw [← hdgap, ← hK, hcancel, one_mul]
    calc Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSumW W (σ + vfun u) u‖
        ≤ Real.exp (F.bottomHeight * vfun u) *
            (‖F.traceWC W (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
              ‖F.aboveBottomSumW W (σ + vfun u) u‖) := by
          rw [hb]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (F.bottomHeight * vfun u) *
            ‖F.traceWC W (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
          Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSumW W (σ + vfun u) u‖ := by ring
      _ ≤ M + K := add_le_add hA hB
  have hinner : ∀ u : ℝ,
      ‖∑ i ∈ F.bottomShell, W.toFun (F.pt i) *
          (Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))‖
        ≤ (M + K) * Real.exp (σ * F.bottomHeight) := by
    intro u
    have hfac := F.bottomShellSumW_eq W (σ + vfun u) u
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
    calc ‖∑ i ∈ F.bottomShell, W.toFun (F.pt i) *
            (Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
              ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))‖
        = Real.exp (σ * F.bottomHeight) *
            (Real.exp (-(σ * F.bottomHeight)) *
              ‖∑ i ∈ F.bottomShell, W.toFun (F.pt i) *
                (Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
                  ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * F.bottomHeight) * (M + K) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = (M + K) * Real.exp (σ * F.bottomHeight) := by ring
  set T : Finset ℝ := F.bottomShell.image (fun i => (F.pt i).im) with hT
  set mult : ℝ → ℝ := fun j =>
    ((F.bottomShell.filter fun i => (F.pt i).im = j).card : ℝ) with hmult
  set wt : ℝ → ℝ := fun j => ‖W.toFun (((F.bottomHeight : ℝ) : ℂ) + (j : ℂ) * I)‖ with hwt
  set Bco : ℝ → ℝ → ℂ := fun u j =>
    ((mult j : ℝ) : ℂ) * (W.toFun (((F.bottomHeight : ℝ) : ℂ) + (j : ℂ) * I) *
      Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * (j : ℂ))) with hBco
  have hwtpos : ∀ j : ℝ, 0 < wt j := by
    intro j
    rw [hwt]
    refine norm_pos_iff.mpr (W.ne_zero _ ?_)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero]
    simpa using F.bottomHeight_pos
  have hmpos : ∀ j ∈ T, 0 < mult j * wt j := by
    intro j hj
    obtain ⟨i, his, hij⟩ := Finset.mem_image.mp hj
    have hc : 0 < (F.bottomShell.filter fun i => (F.pt i).im = j).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨his, hij⟩⟩
    have hm : 0 < mult j := by
      simp only [hmult]
      exact_mod_cast hc
    exact mul_pos hm (hwtpos j)
  have hBnorm : ∀ (u : ℝ), ∀ j ∈ T, ‖Bco u j‖ = mult j * wt j := by
    intro u j _
    rw [hBco]
    simp only
    rw [norm_mul, norm_mul, norm_exp_neg_ofReal_mul_I_mul', mul_one, Complex.norm_real,
      Real.norm_eq_abs, hmult, hwt, abs_of_nonneg (Nat.cast_nonneg _)]
  have hbnd : ∀ u : ℝ, ‖∑ j ∈ T, Bco u j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      (M + K) * Real.exp (σ * F.bottomHeight) := by
    intro u
    rw [hBco, hmult, hT]
    simp only
    rw [← F.bottomShellW_regroup W (σ + vfun u) u]
    exact hinner u
  have hkey := le_zero_of_expSum_norm_le T (fun j => j) (fun j => mult j * wt j) hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro i hi
  exact hkey ((F.pt i).im) (Finset.mem_image_of_mem _ hi)

/-- **A bounded vertical line puts the weighted family's bottom shell on the real axis.** -/
theorem im_eq_zero_of_weightedLine_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceWC W ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ i ∈ F.bottomShell, (F.pt i).im = 0 := by
  intro i hi
  have h1 := F.im_nonpos_of_weightedLine_bound W hσ hline i hi
  have h2 := F.im_nonpos_of_weightedLine_bound W hσ hline _ (F.mem_bottomShell_inv hi)
  rw [F.conj_stable, Complex.conj_im] at h2
  linarith

/-- **Weighted spectral rigidity from one vertical line.**  If the weighted trace of an admissible
family is bounded on a single vertical line of the open right half-plane, every point of the family
is real. -/
theorem im_eq_zero_of_weightedLine_bound_all {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceWC W ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ i : ι, (F.pt i).im = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁⟩ := hcon
  obtain ⟨is, his, hmin⟩ := F.exists_min_re_of_nonempty
    (s := {i : ι | (F.pt i).im ≠ 0}) ⟨i₁, hi₁⟩
  set g : ℝ := (F.pt is).re with hgdef
  have hbase : F.base ≤ g := F.base_le is
  set G : AbstractSpectralFamily ι := F.lift g g hbase with hG
  have hlow : ∀ i, (F.pt i).re < g → (F.pt i).im = 0 := by
    intro i hi
    by_contra hne
    exact absurd (hmin i hne) (not_le.mpr hi)
  have hGre : ∀ i, g ≤ (G.pt i).re := by
    intro i
    by_cases h : g ≤ (F.pt i).re
    · rw [hG, F.lift_pt_of_le hbase h]; exact h
    · rw [hG, F.lift_pt_of_lt hbase (not_le.mp h), Complex.ofReal_re]
  have hGis : (G.pt is).re = g := by
    rw [hG, F.lift_pt_of_le hbase (le_refl _)]
  have hGheight : G.bottomHeight = g :=
    le_antisymm (hGis ▸ G.bottomHeight_le is) (hGre _)
  set s : Finset ι := (F.finite_below g).toFinset with hs
  have hmemcompl : ∀ i : ((s : Set ι)ᶜ : Set ι), g ≤ (F.pt (i : ι)).re := by
    intro i
    have h := i.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hs, Set.Finite.mem_toFinset,
      below, Set.mem_setOf_eq, not_lt] at h
    exact h
  have hline' : ∀ x : ℝ, ‖G.traceWC W ((σ : ℂ) + (x : ℂ) * I)‖ ≤
      C + ∑ i ∈ s, (‖W.toFun ((g : ℝ) : ℂ)‖ * Real.exp (-(σ * g))
        + ‖W.toFun (F.pt i)‖ * F.weight σ i) := by
    intro x
    set τ : ℂ := (σ : ℂ) + (x : ℂ) * I with hτ
    have hre : (0 : ℝ) < τ.re := by rw [hτ, re_vertLine]; exact hσ
    have hFsum : Summable (fun i : ι => F.termW W τ i) := (F.summable_norm_termW W hre).of_norm
    have hGsum : Summable (fun i : ι => G.termW W τ i) := (G.summable_norm_termW W hre).of_norm
    have hFsplit := hFsum.sum_add_tsum_compl (s := s)
    have hGsplit := hGsum.sum_add_tsum_compl (s := s)
    have hcompl : (∑' i : ((s : Set ι)ᶜ : Set ι), G.termW W τ (i : ι))
        = ∑' i : ((s : Set ι)ᶜ : Set ι), F.termW W τ (i : ι) := by
      refine tsum_congr fun i => ?_
      rw [termW, termW, term, term, hG, F.lift_pt_of_le hbase (hmemcompl i)]
    have hdiff : G.traceWC W τ
        = F.traceWC W τ + ((∑ i ∈ s, G.termW W τ i) - ∑ i ∈ s, F.termW W τ i) := by
      rw [traceWC, traceWC, ← hGsplit, ← hFsplit, hcompl]
      ring
    have hbound : ∀ i ∈ s, ‖G.termW W τ i‖ + ‖F.termW W τ i‖ ≤
        ‖W.toFun ((g : ℝ) : ℂ)‖ * Real.exp (-(σ * g)) + ‖W.toFun (F.pt i)‖ * F.weight σ i := by
      intro i hi
      have hlt : (F.pt i).re < g := by
        simpa [hs, Set.Finite.mem_toFinset, below, Set.mem_setOf_eq] using hi
      have hGpt : G.pt i = ((g : ℝ) : ℂ) := by rw [hG, F.lift_pt_of_lt hbase hlt]
      have h1 : ‖G.termW W τ i‖ = ‖W.toFun ((g : ℝ) : ℂ)‖ * Real.exp (-(σ * g)) := by
        rw [termW, norm_mul, hGpt, term, hGpt, Complex.norm_exp]
        congr 2
        rw [hτ]
        simp [Complex.mul_re]
      have h2 : ‖F.termW W τ i‖ = ‖W.toFun (F.pt i)‖ * F.weight σ i := by
        rw [termW, norm_mul, norm_term, weight, hτ, re_vertLine, im_vertLine, hlow i hlt]
        congr 2
        ring
      rw [h1, h2]
    calc ‖G.traceWC W τ‖
        ≤ ‖F.traceWC W τ‖ + ‖(∑ i ∈ s, G.termW W τ i) - ∑ i ∈ s, F.termW W τ i‖ := by
          rw [hdiff]; exact norm_add_le _ _
      _ ≤ C + ∑ i ∈ s, (‖W.toFun ((g : ℝ) : ℂ)‖ * Real.exp (-(σ * g))
            + ‖W.toFun (F.pt i)‖ * F.weight σ i) := by
          refine add_le_add (hline x) ?_
          refine le_trans (norm_sub_le _ _) ?_
          refine le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hbound
  have hshell : is ∈ G.bottomShell := G.mem_bottomShell.mpr (by rw [hGheight, hGis])
  have hzero := G.im_eq_zero_of_weightedLine_bound W hσ hline' is hshell
  rw [hG, F.lift_pt_of_le hbase (le_refl _)] at hzero
  exact his hzero

/-- **The weighted spectral criterion, both directions.** -/
theorem im_eq_zero_iff_exists_weightedLine_bound :
    (∀ i : ι, (F.pt i).im = 0) ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖F.traceWC W ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro him
    refine ⟨1, F.traceWAbs W 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertLine]; exact one_pos
    have h := F.norm_traceWC_le_of_abs_im_le W (lam := 0)
      (fun i => by rw [him i]; simp) hre
    rw [re_vertLine] at h
    simpa using h
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.im_eq_zero_of_weightedLine_bound_all W hσ hline

end

end AbstractSpectralFamily

end HTGeometry
