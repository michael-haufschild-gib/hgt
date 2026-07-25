import GaloisForLFunctions.HTGeometry.AbstractSpectralDecay
import GaloisForLFunctions.HTGeometry.RealExponentialSumRigidity
import GaloisForLFunctions.HTGeometry.AbstractSpectralDefect

/-!
# The bottom shell of an abstract spectral family

Shell structure over an arbitrary index type: the points at the least height form a finite set on
which the height factors out of the trace exactly, everything above it is separated by a spectral
gap, and the trace splits accordingly on a vertical line.

Shell homogeneity is the reason a displacement cannot hide: all points of one shell share a height,
so the height is a common factor and what remains is a finite sum of real exponentials `exp (u J)`
with coefficients of constant modulus.
-/

open Complex Filter
open scoped BigOperators

namespace HTGeometry

noncomputable section

theorem re_vertLine (s u : ℝ) : ((s : ℂ) + (u : ℂ) * I).re = s := by
  simp [Complex.mul_re]

theorem im_vertLine (s u : ℝ) : ((s : ℂ) + (u : ℂ) * I).im = u := by
  simp [Complex.mul_im]

theorem norm_exp_neg_ofReal_mul_I_mul' (a j : ℝ) :
    ‖Complex.exp (-(a : ℂ) * I * (j : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(a : ℂ) * I * (j : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [h, Real.exp_zero]

/-- On a vertical line the multiplier of a point splits into a height factor, a fixed phase and a
real exponential in the vertical variable. -/
theorem vertLine_factor (σ u R Jq : ℝ) :
    Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * ((R : ℂ) + (Jq : ℂ) * I)) =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (R : ℂ)) *
        (Complex.exp (-(σ : ℂ) * I * (Jq : ℂ)) * ((Real.exp (u * Jq) : ℝ) : ℂ)) := by
  have hu : ((Real.exp (u * Jq) : ℝ) : ℂ) = Complex.exp ((u : ℂ) * (Jq : ℂ)) := by
    rw [Complex.ofReal_exp]
    norm_cast
  rw [hu, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (-(u : ℂ) * (Jq : ℂ)) * hI

namespace AbstractSpectralFamily

variable {ι : Type*} [Nonempty ι] (F : AbstractSpectralFamily ι)

/-- The points at the family's least height. -/
def bottomShell : Finset ι := (F.shell_finite F.bottomHeight).toFinset

theorem mem_bottomShell {i : ι} : i ∈ F.bottomShell ↔ (F.pt i).re = F.bottomHeight := by
  rw [bottomShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => le_antisymm h (F.bottomHeight_le i), fun h => le_of_eq h⟩

theorem mem_bottomShell_inv {i : ι} (hi : i ∈ F.bottomShell) : F.inv i ∈ F.bottomShell := by
  rw [mem_bottomShell, F.conj_stable, Complex.conj_re]
  exact F.mem_bottomShell.mp hi

/-- The points strictly above the least height. -/
def aboveBottom : Set ι := ((F.bottomShell : Finset ι) : Set ι)ᶜ

theorem mem_aboveBottom {i : ι} : i ∈ F.aboveBottom ↔ F.bottomHeight < (F.pt i).re := by
  rw [aboveBottom, Set.mem_compl_iff, Finset.mem_coe, F.mem_bottomShell]
  constructor
  · intro h
    exact lt_of_le_of_ne (F.bottomHeight_le i) (fun heq => h heq.symm)
  · intro h heq
    exact absurd heq (ne_of_gt h)

/-- Above the bottom shell there is a spectral gap. -/
theorem exists_secondHeight (hne : F.aboveBottom.Nonempty) :
    ∃ g₂ : ℝ, F.bottomHeight < g₂ ∧ ∀ i ∈ F.aboveBottom, g₂ ≤ (F.pt i).re := by
  obtain ⟨i₀, hi₀, hmin⟩ := F.exists_min_re_of_nonempty hne
  exact ⟨(F.pt i₀).re, F.mem_aboveBottom.mp hi₀, hmin⟩

/-- The bottom-shell sum on a vertical line. -/
def bottomShellSum (σ u : ℝ) : ℂ :=
  ∑ i ∈ F.bottomShell, F.term ((σ : ℂ) + (u : ℂ) * I) i

/-- The above-bottom part of the trace on a vertical line. -/
def aboveBottomSum (s u : ℝ) : ℂ :=
  ∑' i : F.aboveBottom, F.term ((s : ℂ) + (u : ℂ) * I) (i : ι)

/-- **Shell homogeneity.**  On the bottom shell the height factors out, leaving only a phase. -/
theorem bottomShellSum_eq (σ u : ℝ) :
    F.bottomShellSum σ u =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (F.bottomHeight : ℂ)) *
        ∑ i ∈ F.bottomShell,
          Complex.exp (-(σ : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ) := by
  rw [bottomShellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsplit : F.pt i = ((F.bottomHeight : ℝ) : ℂ) + ((F.pt i).im : ℂ) * I := by
    rw [← F.mem_bottomShell.mp hi]
    exact (Complex.re_add_im _).symm
  rw [term]
  conv_lhs => rw [hsplit]
  exact vertLine_factor σ u F.bottomHeight (F.pt i).im

/-- The trace on a vertical line is its bottom shell plus everything above. -/
theorem traceC_vertical_split {s : ℝ} (hs : 0 < s) (u : ℝ) :
    F.traceC ((s : ℂ) + (u : ℂ) * I) = F.bottomShellSum s u + F.aboveBottomSum s u := by
  have hre : 0 < ((s : ℂ) + (u : ℂ) * I).re := by rw [re_vertLine]; exact hs
  have hsum : Summable (fun i : ι => F.term ((s : ℂ) + (u : ℂ) * I) i) :=
    (F.summable_norm_term hre).of_norm
  exact (hsum.sum_add_tsum_compl).symm

/-- **The weighted tail bound.**  Moving right by `v` costs the above-bottom part a factor
`exp (-(g₂ - g₁) v)`, which beats the `exp (g₁ v)` weight by the whole spectral gap. -/
theorem exp_bottomHeight_mul_norm_aboveBottomSum_le {σ : ℝ} (hσ : 0 < σ)
    {g₂ : ℝ} (hg₂ : ∀ i ∈ F.aboveBottom, g₂ ≤ (F.pt i).re)
    {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSum (σ + v) u‖ ≤
      Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
        ∑' i : F.aboveBottom, F.weight σ (i : ι) := by
  have hsv : 0 < σ + v := by linarith
  have hre : 0 < (((σ + v : ℝ) : ℂ) + (u : ℂ) * I).re := by rw [re_vertLine]; exact hsv
  have hsumnorm := F.summable_norm_term hre
  have hsumσ : Summable (fun i : F.aboveBottom => F.weight σ (i : ι)) :=
    (F.summable_weight hσ).subtype _
  have hterm : ∀ i : F.aboveBottom,
      Real.exp (F.bottomHeight * v) * ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ ≤
        Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) * F.weight σ (i : ι) := by
    intro i
    have hR : g₂ ≤ (F.pt (i : ι)).re := hg₂ _ i.2
    have hJ : |(F.pt (i : ι)).im| < 1 / 2 := F.abs_im_lt _
    rw [norm_term, re_vertLine, im_vertLine, weight, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have huJ : u * (F.pt (i : ι)).im ≤ |u| / 2 := by
      calc u * (F.pt (i : ι)).im ≤ |u * (F.pt (i : ι)).im| := le_abs_self _
        _ = |u| * |(F.pt (i : ι)).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)
        _ = |u| / 2 := by ring
    nlinarith [hR, hv, huJ]
  calc Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSum (σ + v) u‖
      ≤ Real.exp (F.bottomHeight * v) *
          ∑' i : F.aboveBottom, ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ = ∑' i : F.aboveBottom,
          Real.exp (F.bottomHeight * v) *
            ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (i : ι)‖ := (tsum_mul_left).symm
    _ ≤ ∑' i : F.aboveBottom,
          Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) * F.weight σ (i : ι) :=
        Summable.tsum_le_tsum hterm ((hsumnorm.subtype _).mul_left _) (hsumσ.mul_left _)
    _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
          ∑' i : F.aboveBottom, F.weight σ (i : ι) := tsum_mul_left

/-- The trace normalised by the least height. -/
def normalizedTraceReal (σ : ℝ) : ℝ := Real.exp (σ * F.bottomHeight) * F.traceReal σ

theorem normalizedTraceReal_eq {σ : ℝ} (hσ : 0 < σ) :
    F.normalizedTraceReal σ =
      (F.bottomShell.card : ℝ) +
        ∑' i : F.aboveBottom, Real.exp (-(σ * ((F.pt (i : ι)).re - F.bottomHeight))) := by
  classical
  have hsum : Summable fun i : ι => Real.exp (-(σ * ((F.pt i).re - F.bottomHeight))) := by
    refine ((F.summable_weight hσ).mul_left (Real.exp (σ * F.bottomHeight))).congr fun i => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit := hsum.sum_add_tsum_compl (s := F.bottomShell)
  have hfin : ∑ i ∈ F.bottomShell, Real.exp (-(σ * ((F.pt i).re - F.bottomHeight)))
      = (F.bottomShell.card : ℝ) := by
    rw [Finset.sum_congr rfl fun i hi => ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [F.mem_bottomShell.mp hi, sub_self, mul_zero, neg_zero, Real.exp_zero]
  have hnorm : F.normalizedTraceReal σ
      = ∑' i : ι, Real.exp (-(σ * ((F.pt i).re - F.bottomHeight))) := by
    rw [normalizedTraceReal, traceReal, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    show Real.exp (σ * F.bottomHeight) * Real.exp (-(σ * (F.pt i).re)) = _
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hnorm, ← hsplit, hfin]
  rfl

/-- **The least-height multiplicity is recoverable from the real-time trace.**  The trace normalised
by its least height converges to the number of points at that height: the spectral gap makes every
higher point exponentially negligible. -/
theorem tendsto_normalizedTraceReal :
    Filter.Tendsto F.normalizedTraceReal Filter.atTop (nhds (F.bottomShell.card : ℝ)) := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ : ∃ g₂ : ℝ, F.bottomHeight < g₂ ∧
      ∀ i ∈ F.aboveBottom, g₂ ≤ (F.pt i).re := by
    rcases Set.eq_empty_or_nonempty F.aboveBottom with hE | hNE
    · refine ⟨F.bottomHeight + 1, by linarith, fun i hi => ?_⟩
      rw [hE] at hi
      exact absurd hi (by simp)
    · exact F.exists_secondHeight hNE
  set d : ℝ := g₂ - F.bottomHeight with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set T : ℝ → ℝ := fun σ =>
    ∑' i : F.aboveBottom, Real.exp (-(σ * ((F.pt (i : ι)).re - F.bottomHeight))) with hT
  have hsummable : ∀ {σ : ℝ}, 0 < σ →
      Summable fun i : F.aboveBottom =>
        Real.exp (-(σ * ((F.pt (i : ι)).re - F.bottomHeight))) := by
    intro σ hσ
    refine (((F.summable_weight hσ).mul_left
      (Real.exp (σ * F.bottomHeight))).subtype _).congr fun i => ?_
    show Real.exp (σ * F.bottomHeight) * Real.exp (-(σ * (F.pt (i : ι)).re)) = _
    rw [← Real.exp_add]
    congr 1
    ring
  have hTnn : ∀ σ : ℝ, 0 ≤ T σ := fun σ => tsum_nonneg fun i => (Real.exp_pos _).le
  have hTle : ∀ σ : ℝ, 1 ≤ σ → T σ ≤ Real.exp (-((σ - 1) * d)) * T 1 := by
    intro σ hσ
    rw [hT]
    simp only
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (hsummable (by linarith))
      ((hsummable one_pos).mul_left _)
    have hre : g₂ ≤ (F.pt (i : ι)).re := hg₂ _ i.2
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : d ≤ (F.pt (i : ι)).re - F.bottomHeight := by rw [hd]; linarith
    nlinarith [h1, hσ]
  have hmaj : Filter.Tendsto (fun σ : ℝ => Real.exp (-((σ - 1) * d)) * T 1)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun σ : ℝ => σ - 1) Filter.atTop Filter.atTop := by
      simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id
    have hlin : Filter.Tendsto (fun σ : ℝ => (σ - 1) * d) Filter.atTop Filter.atTop :=
      h0.atTop_mul_const hdpos
    have hneg : Filter.Tendsto (fun σ : ℝ => -((σ - 1) * d)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hlin
    have hexp : Filter.Tendsto (fun σ : ℝ => Real.exp (-((σ - 1) * d)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
    simpa using hexp.mul_const (T 1)
  have hT0 : Filter.Tendsto T Filter.atTop (nhds 0) := by
    refine squeeze_zero' (g := fun σ : ℝ => Real.exp (-((σ - 1) * d)) * T 1) ?_ ?_ hmaj
    · filter_upwards with σ using hTnn σ
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with σ hσ using hTle σ hσ
  have hlim : Filter.Tendsto (fun σ : ℝ => (F.bottomShell.card : ℝ) + T σ)
      Filter.atTop (nhds ((F.bottomShell.card : ℝ) + 0)) :=
    Filter.Tendsto.const_add _ hT0
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with σ hσ
  exact (F.normalizedTraceReal_eq hσ).symm

theorem card_bottomShell_pos : 0 < F.bottomShell.card :=
  Finset.card_pos.mpr ⟨F.bottomIndex, F.mem_bottomShell.mpr rfl⟩

theorem le_normalizedTraceReal {σ : ℝ} (hσ : 0 < σ) :
    (F.bottomShell.card : ℝ) ≤ F.normalizedTraceReal σ := by
  rw [F.normalizedTraceReal_eq hσ]
  have h : 0 ≤ ∑' i : F.aboveBottom, Real.exp (-(σ * ((F.pt (i : ι)).re - F.bottomHeight))) :=
    tsum_nonneg fun i => (Real.exp_pos _).le
  linarith

/-- **A simple bottom shell is real.**  The conjugating bijection maps the bottom shell to itself, so
a one-point shell is fixed by it and its point equals its own conjugate. -/
theorem im_eq_zero_of_card_bottomShell_eq_one (h : F.bottomShell.card = 1) :
    (F.pt F.bottomIndex).im = 0 := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hb : F.bottomIndex ∈ F.bottomShell := F.mem_bottomShell.mpr rfl
  have hbi : F.bottomIndex = i := by rw [hi] at hb; exact Finset.mem_singleton.mp hb
  have hinv : F.inv F.bottomIndex ∈ F.bottomShell := F.mem_bottomShell_inv hb
  have hfix : F.inv F.bottomIndex = F.bottomIndex := by
    rw [hi] at hinv
    rw [Finset.mem_singleton.mp hinv, hbi]
  have hconj := F.conj_stable F.bottomIndex
  rw [hfix] at hconj
  have him : (F.pt F.bottomIndex).im = -(F.pt F.bottomIndex).im := by
    conv_lhs => rw [hconj]
    rw [Complex.conj_im]
  linarith

omit [Nonempty ι] in
theorem defect_le_of_abs_im_le {σ η : ℝ} (hσ : 0 < σ)
    (hall : ∀ i, |(F.pt i).im| ≤ η) (hpi : σ * η ≤ Real.pi) :
    F.defect σ ≤ (1 - Real.cos (σ * η)) * F.traceReal σ := by
  have hw : Summable fun i : ι => F.weight σ i := F.summable_weight hσ
  rw [F.defect_eq_tsum hσ, traceReal, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_defectTerm hσ) (hw.mul_left _)
  have hcos : Real.cos (σ * η) ≤ Real.cos (σ * (F.pt i).im) := by
    have habs : |σ * (F.pt i).im| ≤ σ * η := by
      rw [abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left (hall i) hσ.le
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (σ * (F.pt i).im)) hpi habs
    rwa [Real.cos_abs] at h
  calc F.weight σ i * (1 - Real.cos (σ * (F.pt i).im))
      ≤ F.weight σ i * (1 - Real.cos (σ * η)) := by
        refine mul_le_mul_of_nonneg_left ?_ (F.weight_pos σ i).le
        linarith
    _ = (1 - Real.cos (σ * η)) * F.weight σ i := by ring

/-- **The loop gain of the self-referential bound.**  A uniform displacement bound `η` returns, at any
least-height point, a bound whose gain is the normalised trace -- which is never below one, since the
point being bounded is itself a summand of the majorant that bounds it. -/
theorem one_sub_cos_bottomShell_le {σ η : ℝ} (hσ : 0 < σ)
    (hall : ∀ i, |(F.pt i).im| ≤ η) (hpi : σ * η ≤ Real.pi)
    {i : ι} (hi : i ∈ F.bottomShell) :
    1 - Real.cos (σ * (F.pt i).im) ≤ F.normalizedTraceReal σ * (1 - Real.cos (σ * η)) := by
  have hlow := F.defectTerm_le_defect hσ i
  have hup := F.defect_le_of_abs_im_le hσ hall hpi
  have hwi : F.weight σ i = Real.exp (-(σ * F.bottomHeight)) := by
    rw [weight, F.mem_bottomShell.mp hi]
  rw [hwi] at hlow
  have hchain : Real.exp (-(σ * F.bottomHeight)) * (1 - Real.cos (σ * (F.pt i).im)) ≤
      (1 - Real.cos (σ * η)) * F.traceReal σ := le_trans hlow hup
  have hpos : (0 : ℝ) < Real.exp (σ * F.bottomHeight) := Real.exp_pos _
  have hinv : Real.exp (σ * F.bottomHeight) * Real.exp (-(σ * F.bottomHeight)) = 1 := by
    rw [← Real.exp_add]; simp
  calc 1 - Real.cos (σ * (F.pt i).im)
      = Real.exp (σ * F.bottomHeight) *
          (Real.exp (-(σ * F.bottomHeight)) * (1 - Real.cos (σ * (F.pt i).im))) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ Real.exp (σ * F.bottomHeight) * ((1 - Real.cos (σ * η)) * F.traceReal σ) :=
        mul_le_mul_of_nonneg_left hchain hpos.le
    _ = F.normalizedTraceReal σ * (1 - Real.cos (σ * η)) := by
        rw [normalizedTraceReal]; ring

end AbstractSpectralFamily

end

end HTGeometry
