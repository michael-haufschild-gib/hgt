import GaloisForLFunctions.RHTower.XiSpectralFamilyGraded
import GaloisForLFunctions.RHTower.XiSpectralFamilyOnLine
import GaloisForLFunctions.RHTower.XiSpectralFamilyRH

/-!
# Graded assembly: a growth exponent on one line is a zero-free region

The assembly of `XiSpectralFamilyOnLine` with the hypothesis weakened from boundedness to
`exp (lam |x|)` growth.  The extra factor rides through the whole chain -- the half-plane decay
carries it, the tail bound does not see it, and the shell sum inherits it -- ending at
`HTGeometry.le_of_expSum_norm_le_exp` instead of its `lam = 0` special case.

At `lam = 0` this is the earlier statement.  For `lam > 0` it says: an explicit growth exponent for
the trace on one vertical line is an explicit bound on the displacements, with no reference to the
zeros in the hypothesis.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

/-- **The graded assembly.** -/
theorem im_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ q ∈ F.bottomShell, (F.pt q).im ≤ lam := by
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
  have hexpge : ∀ u : ℝ, (1 : ℝ) ≤ Real.exp (lam * |u|) :=
    fun u => Real.one_le_exp (mul_nonneg hlam (abs_nonneg u))
  have hmaster : ∀ u : ℝ,
      Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSum (σ + vfun u) u‖ ≤
        (M + K) * Real.exp (lam * |u|) := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertical _ _
    have him : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).im = u := im_vertical _ _
    have hΘ := F.norm_traceC_le_of_line_growth hσ hline
      (t := ((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) (by rw [hre]; linarith)
    rw [hre, him, show σ + vfun u - σ = vfun u from by ring] at hΘ
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
        ‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M * Real.exp (lam * |u|) := by
      refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) (le_of_eq ?_)
      rw [← mul_assoc, mul_comm (Real.exp (F.bottomHeight * vfun u)) (M * Real.exp (lam * |u|)),
        mul_assoc, ← Real.exp_add,
        show F.bottomHeight * vfun u + -(F.bottomHeight * vfun u) = 0 from by ring,
        Real.exp_zero, mul_one]
    have hB : Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSum (σ + vfun u) u‖ ≤ K := by
      refine le_trans htail (le_of_eq ?_)
      rw [← hdgap, ← hK, hcancel, one_mul]
    have hK0 : 0 ≤ K := tsum_nonneg fun q => (F.weight_pos σ (q : XiZeroCopy)).le
    calc Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSum (σ + vfun u) u‖
        ≤ Real.exp (F.bottomHeight * vfun u) *
            (‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
              ‖F.aboveBottomSum (σ + vfun u) u‖) := by
          rw [hb]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ = Real.exp (F.bottomHeight * vfun u) *
            ‖F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I)‖ +
          Real.exp (F.bottomHeight * vfun u) * ‖F.aboveBottomSum (σ + vfun u) u‖ := by ring
      _ ≤ M * Real.exp (lam * |u|) + K := add_le_add hA hB
      _ ≤ (M + K) * Real.exp (lam * |u|) := by nlinarith [hexpge u, hK0]
  have hinner : ∀ u : ℝ,
      ‖∑ q ∈ F.bottomShell,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt q).im : ℂ)) *
            ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ)‖
        ≤ ((M + K) * Real.exp (σ * F.bottomHeight)) * Real.exp (lam * |u|) := by
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
      _ ≤ Real.exp (σ * F.bottomHeight) * ((M + K) * Real.exp (lam * |u|)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = ((M + K) * Real.exp (σ * F.bottomHeight)) * Real.exp (lam * |u|) := by ring
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
      ((M + K) * Real.exp (σ * F.bottomHeight)) * Real.exp (lam * |u|) := by
    intro u
    rw [hBco, hmult, hT, ← F.bottomShell_regroup (σ + vfun u) u]
    exact hinner u
  have hkey := HTGeometry.le_of_expSum_norm_le_exp T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro q hq
  exact hkey ((F.pt q).im) (Finset.mem_image_of_mem _ hq)

/-- **The graded criterion at the bottom shell.** -/
theorem abs_im_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ q ∈ F.bottomShell, |(F.pt q).im| ≤ lam := by
  intro q hq
  have h1 := F.im_le_of_line_growth hσ hlam hline q hq
  have h2 := F.im_le_of_line_growth hσ hlam hline _ (F.mem_bottomShell_lineConj hq)
  rw [F.conj_stable, Complex.conj_im] at h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩

/-- **The graded wrapper.**  A growth exponent on one vertical line bounds *every* displacement. -/
theorem abs_im_le_of_line_growth_all {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ q : XiZeroCopy, |(F.pt q).im| ≤ lam := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q₁, hq₁⟩ := hcon
  obtain ⟨qs, hqs, hmin⟩ := F.exists_min_re_of_nonempty
    (s := {q : XiZeroCopy | lam < |(F.pt q).im|}) ⟨q₁, hq₁⟩
  set g : ℝ := (F.pt qs).re with hgdef
  have hbase : F.base ≤ g := F.base_le qs
  set G : SpectralFamily := F.lift g g hbase with hG
  have hlow : ∀ q, (F.pt q).re < g → |(F.pt q).im| ≤ lam := by
    intro q hq
    by_contra hne
    exact absurd (hmin q (not_le.mp hne)) (not_le.mpr hq)
  have hGre : ∀ q, g ≤ (G.pt q).re := by
    intro q
    by_cases h : g ≤ (F.pt q).re
    · rw [hG, F.lift_pt_of_le hbase h]; exact h
    · rw [hG, F.lift_pt_of_lt hbase (not_le.mp h), Complex.ofReal_re]
  have hGqs : (G.pt qs).re = g := by rw [hG, F.lift_pt_of_le hbase (le_refl _)]
  have hGheight : G.bottomHeight = g :=
    le_antisymm (hGqs ▸ G.bottomHeight_le qs) (hGre _)
  set s : Finset XiZeroCopy := (F.finite_below g).toFinset with hs
  have hmemcompl : ∀ q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy),
      g ≤ (F.pt (q : XiZeroCopy)).re := by
    intro q
    have hqc := q.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hs, Set.Finite.mem_toFinset,
      below, Set.mem_setOf_eq, not_lt] at hqc
    exact hqc
  have hline' : ∀ x : ℝ, ‖G.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
      (C + ∑ q ∈ s, (Real.exp (-(σ * g)) + F.weight σ q)) * Real.exp (lam * |x|) := by
    intro x
    set τ : ℂ := (σ : ℂ) + (x : ℂ) * I with hτ
    have hre : (0 : ℝ) < τ.re := by rw [hτ, re_vertical]; exact hσ
    have hFsum : Summable (fun q : XiZeroCopy => F.term τ q) :=
      (F.summable_norm_term hre).of_norm
    have hGsum : Summable (fun q : XiZeroCopy => G.term τ q) :=
      (G.summable_norm_term hre).of_norm
    have hFsplit := hFsum.sum_add_tsum_compl (s := s)
    have hGsplit := hGsum.sum_add_tsum_compl (s := s)
    have hcompl : (∑' q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy), G.term τ (q : XiZeroCopy))
        = ∑' q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy), F.term τ (q : XiZeroCopy) := by
      refine tsum_congr fun q => ?_
      rw [term, term, hG, F.lift_pt_of_le hbase (hmemcompl q)]
    have hdiff : G.traceC τ = F.traceC τ +
        ((∑ q ∈ s, G.term τ q) - ∑ q ∈ s, F.term τ q) := by
      rw [traceC, traceC, ← hGsplit, ← hFsplit, hcompl]
      ring
    have hbound : ∀ q ∈ s, ‖G.term τ q‖ + ‖F.term τ q‖ ≤
        (Real.exp (-(σ * g)) + F.weight σ q) * Real.exp (lam * |x|) := by
      intro q hq
      have hlt : (F.pt q).re < g := by
        simpa [hs, Set.Finite.mem_toFinset, below, Set.mem_setOf_eq] using hq
      have hge : (1 : ℝ) ≤ Real.exp (lam * |x|) :=
        Real.one_le_exp (mul_nonneg hlam (abs_nonneg x))
      have h1 : ‖G.term τ q‖ = Real.exp (-(σ * g)) := by
        rw [term, hG, F.lift_pt_of_lt hbase hlt, Complex.norm_exp]
        congr 1
        rw [hτ]
        simp [Complex.mul_re]
      have h2 : ‖F.term τ q‖ ≤ F.weight σ q * Real.exp (lam * |x|) := by
        rw [norm_term, weight, hτ, re_vertical, im_vertical, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hxJ : x * (F.pt q).im ≤ lam * |x| := by
          calc x * (F.pt q).im ≤ |x * (F.pt q).im| := le_abs_self _
            _ = |x| * |(F.pt q).im| := abs_mul _ _
            _ ≤ |x| * lam := mul_le_mul_of_nonneg_left (hlow q hlt) (abs_nonneg x)
            _ = lam * |x| := by ring
        linarith
      have h3 : Real.exp (-(σ * g)) ≤ Real.exp (-(σ * g)) * Real.exp (lam * |x|) := by
        nlinarith [Real.exp_pos (-(σ * g)), hge]
      rw [h1]
      nlinarith [h2, h3]
    calc ‖G.traceC τ‖
        ≤ ‖F.traceC τ‖ + ‖(∑ q ∈ s, G.term τ q) - ∑ q ∈ s, F.term τ q‖ := by
          rw [hdiff]; exact norm_add_le _ _
      _ ≤ (C + ∑ q ∈ s, (Real.exp (-(σ * g)) + F.weight σ q)) * Real.exp (lam * |x|) := by
          rw [add_mul, Finset.sum_mul]
          refine add_le_add (hline x) ?_
          refine le_trans (norm_sub_le _ _) ?_
          refine le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hbound
  have hshell : qs ∈ G.bottomShell := G.mem_bottomShell.mpr (by rw [hGheight, hGqs])
  have hzero := G.abs_im_le_of_line_growth hσ hlam hline' qs hshell
  rw [hG, F.lift_pt_of_le hbase (le_refl _)] at hzero
  exact absurd hzero (not_le.mpr hqs)

/-- The easy direction, graded: a displacement bound gives the growth bound. -/
theorem norm_traceC_le_of_abs_im_le {lam : ℝ} (him : ∀ q, |(F.pt q).im| ≤ lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceC τ‖ ≤ F.traceReal τ.re * Real.exp (lam * |τ.im|) := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_term hτ)) ?_
  rw [traceReal, mul_comm, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun q => ?_) (F.summable_norm_term hτ)
    ((F.summable_weight hτ).mul_left _)
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hkey : τ.im * (F.pt q).im ≤ lam * |τ.im| := by
    calc τ.im * (F.pt q).im ≤ |τ.im * (F.pt q).im| := le_abs_self _
      _ = |τ.im| * |(F.pt q).im| := abs_mul _ _
      _ ≤ |τ.im| * lam := mul_le_mul_of_nonneg_left (him q) (abs_nonneg _)
      _ = lam * |τ.im| := by ring
  linarith

/-- **The graded criterion, both directions.**  For any admissible family and any `lam >= 0`, the
displacements are bounded by `lam` exactly when the trace grows at most like `exp (lam |x|)` on some
vertical line of the open right half-plane. -/
theorem abs_im_le_iff_exists_line_growth {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ q : XiZeroCopy, |(F.pt q).im| ≤ lam) ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
        ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|) := by
  constructor
  · intro him
    refine ⟨1, F.traceReal 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertical]; exact one_pos
    have h := F.norm_traceC_le_of_abs_im_le him hre
    rwa [re_vertical, im_vertical] at h
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.abs_im_le_of_line_growth_all hσ hlam hline

/-- **Subexponential growth already forces reality.**  The hypothesis need not be boundedness: it is
enough that for every `eps > 0` the trace is `O(exp (eps |x|))` on *some* vertical line, with the
line allowed to depend on `eps`. -/
theorem im_eq_zero_of_subexponential
    (h : ∀ eps : ℝ, 0 < eps → ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
      ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (eps * |x|)) :
    ∀ q : XiZeroCopy, (F.pt q).im = 0 := by
  intro q
  have hall : ∀ eps : ℝ, 0 < eps → |(F.pt q).im| ≤ eps := by
    intro eps heps
    obtain ⟨σ, C, hσ, hline⟩ := h eps heps
    exact F.abs_im_le_of_line_growth_all hσ heps.le hline q
  have hzero : |(F.pt q).im| ≤ 0 := le_of_forall_pos_le_add fun eps heps => by
    simpa using hall eps heps
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

end

end SpectralFamily

end RHTower
