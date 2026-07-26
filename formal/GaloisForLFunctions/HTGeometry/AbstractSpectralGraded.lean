import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity

/-!
# The graded spectral criterion

The rigidity theorem with the hypothesis weakened from boundedness to `exp (lam |x|)` growth on one
vertical line.  Multiplying the least-height twist by `exp (lam y)` on the third quadrant and by
`exp (-lam y)` on the fourth turns both real-ray bounds back into constants while leaving the
imaginary-ray bounds untouched, so the same quadrant Phragmén--Lindelöf theorem applies; the extra
factor then rides through the tail bound and the shell sum, ending at phase-robust dominance with an
exponential majorant instead of a constant one.

The conclusion is an exact dictionary: for an admissible family the exponential type of the trace
along any vertical line of the open right half-plane equals the supremum of the displacements.  At
`lam = 0` this is the reality criterion.
-/

open Complex Filter Asymptotics
open scoped BigOperators

namespace HTGeometry

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} [Nonempty ι] (F : AbstractSpectralFamily ι)

/-- The least-height twist with an extra exponential factor. -/
def gtwist (σ l : ℝ) (y : ℂ) : ℂ := F.twist σ y * Complex.exp ((l : ℂ) * y)

theorem norm_gtwist (σ l : ℝ) (y : ℂ) :
    ‖F.gtwist σ l y‖ = ‖F.twist σ y‖ * Real.exp (l * y.re) := by
  rw [gtwist, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem differentiableOn_gtwist (σ l : ℝ) :
    DifferentiableOn ℂ (F.gtwist σ l) {y : ℂ | y.im < σ} := by
  intro y hy
  have h1 := F.differentiableOn_twist σ y hy
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((l : ℂ) * z)) y := by fun_prop
  exact h1.mul h2.differentiableWithinAt

theorem norm_gtwist_le {σ l : ℝ} (hσ : 0 < σ) {y : ℂ} (hy : y.im ≤ 0) :
    ‖F.gtwist σ l y‖ ≤ F.traceReal σ * Real.exp ((1 / 2 + F.bottomHeight + |l|) * ‖y‖) := by
  rw [norm_gtwist]
  have h1 := F.norm_twist_le hσ hy
  have h2 : Real.exp (l * y.re) ≤ Real.exp (|l| * ‖y‖) := by
    refine Real.exp_le_exp.mpr ?_
    calc l * y.re ≤ |l * y.re| := le_abs_self _
      _ = |l| * |y.re| := abs_mul _ _
      _ ≤ |l| * ‖y‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm y) (abs_nonneg _)
  calc ‖F.twist σ y‖ * Real.exp (l * y.re)
      ≤ (F.traceReal σ * Real.exp ((1 / 2 + F.bottomHeight) * ‖y‖)) * Real.exp (|l| * ‖y‖) := by
        refine mul_le_mul h1 h2 (Real.exp_pos _).le ?_
        exact mul_nonneg (F.traceReal_nonneg σ) (Real.exp_pos _).le
    _ = F.traceReal σ * Real.exp ((1 / 2 + F.bottomHeight + |l|) * ‖y‖) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **Graded Phragmén--Lindelöf.** -/
theorem norm_twist_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|))
    {y : ℂ} (hy : y.im ≤ 0) :
    ‖F.twist σ y‖ ≤ max C (F.traceReal σ) * Real.exp (lam * |y.re|) := by
  have hsub : ∀ (l : ℝ) (s t : Set ℝ), closure (s ×ℂ t) ⊆ {z : ℂ | z.im < σ} →
      DiffContOnCl ℂ (F.gtwist σ l) (s ×ℂ t) := by
    intro l s t hsu
    exact ⟨(F.differentiableOn_gtwist σ l).mono (subset_closure.trans hsu),
      ((F.differentiableOn_gtwist σ l).mono hsu).continuousOn⟩
  have hclos : ∀ s : Set ℝ, closure (s ×ℂ Set.Iio 0) ⊆ {z : ℂ | z.im < σ} := by
    intro s z hz
    rw [Complex.closure_reProdIm, closure_Iio] at hz
    have h := (Complex.mem_reProdIm.mp hz).2
    simp only [Set.mem_Iic] at h
    simp only [Set.mem_setOf_eq]
    linarith
  have hgrow : ∀ (l : ℝ) (S : Set ℂ), (∀ z ∈ S, z.im ≤ 0) →
      ∃ c < (2 : ℝ), ∃ B, (F.gtwist σ l) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
    intro l S hS
    refine ⟨1, by norm_num, 1 / 2 + F.bottomHeight + |l|, isBigO_iff.mpr ⟨F.traceReal σ, ?_⟩⟩
    rw [eventually_inf_principal]
    filter_upwards with z hz
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact F.norm_gtwist_le hσ (hS z hz)
  have him : ∀ (l : ℝ) (x : ℝ), x ≤ 0 →
      ‖F.gtwist σ l ((x : ℂ) * I)‖ ≤ max C (F.traceReal σ) := by
    intro l x hx
    rw [norm_gtwist]
    have hre : ((x : ℂ) * I).re = 0 := by simp
    rw [hre, mul_zero, Real.exp_zero, mul_one]
    exact le_trans (F.norm_twist_imaginary_ray hσ hx) (le_max_right _ _)
  rcases le_or_gt y.re 0 with hcase | hcase
  · have hreal : ∀ x : ℝ, x ≤ 0 → ‖F.gtwist σ lam ((x : ℝ) : ℂ)‖ ≤ max C (F.traceReal σ) := by
      intro x hx
      rw [norm_gtwist, Complex.ofReal_re, twist, norm_mul, F.norm_exp_twist]
      simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
      refine le_trans ?_ (le_max_left _ _)
      have h := hline x
      have habs : |x| = -x := abs_of_nonpos hx
      rw [habs] at h
      calc ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ * Real.exp (lam * x)
          ≤ (C * Real.exp (lam * -x)) * Real.exp (lam * x) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = C := by
            rw [mul_assoc, ← Real.exp_add,
              show lam * -x + lam * x = 0 from by ring, Real.exp_zero, mul_one]
    have hpl := PhragmenLindelof.quadrant_III
      (hsub lam (Set.Iio 0) (Set.Iio 0) (hclos (Set.Iio 0)))
      (hgrow lam (Set.Iio 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x hx => hreal x hx) (fun x hx => him lam x hx) hcase hy
    rw [norm_gtwist] at hpl
    have hpos : (0 : ℝ) < Real.exp (lam * y.re) := Real.exp_pos _
    rw [← le_div_iff₀ hpos] at hpl
    refine le_trans hpl (le_of_eq ?_)
    rw [abs_of_nonpos hcase, div_eq_mul_inv, ← Real.exp_neg,
      show lam * -y.re = -(lam * y.re) from by ring]
  · have hreal : ∀ x : ℝ, 0 ≤ x → ‖F.gtwist σ (-lam) ((x : ℝ) : ℂ)‖ ≤ max C (F.traceReal σ) := by
      intro x hx
      rw [norm_gtwist, Complex.ofReal_re, twist, norm_mul, F.norm_exp_twist]
      simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
      refine le_trans ?_ (le_max_left _ _)
      have h := hline x
      have habs : |x| = x := abs_of_nonneg hx
      rw [habs] at h
      calc ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ * Real.exp (-lam * x)
          ≤ (C * Real.exp (lam * x)) * Real.exp (-lam * x) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = C := by
            rw [mul_assoc, ← Real.exp_add,
              show lam * x + -lam * x = 0 from by ring, Real.exp_zero, mul_one]
    have hpl := PhragmenLindelof.quadrant_IV
      (hsub (-lam) (Set.Ioi 0) (Set.Iio 0) (hclos (Set.Ioi 0)))
      (hgrow (-lam) (Set.Ioi 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x hx => hreal x hx) (fun x hx => him (-lam) x hx) hcase.le hy
    rw [norm_gtwist] at hpl
    have hpos : (0 : ℝ) < Real.exp (-lam * y.re) := Real.exp_pos _
    rw [← le_div_iff₀ hpos] at hpl
    refine le_trans hpl (le_of_eq ?_)
    rw [abs_of_pos hcase, div_eq_mul_inv, ← Real.exp_neg,
      show -(-lam * y.re) = lam * y.re from by ring]

/-- **Graded half-plane decay.** -/
theorem norm_traceC_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|))
    {t : ℂ} (ht : σ ≤ t.re) :
    ‖F.traceC t‖ ≤
      max C (F.traceReal σ) * Real.exp (lam * |t.im|) *
        Real.exp (-(F.bottomHeight * (t.re - σ))) := by
  set y : ℂ := -I * (t - (σ : ℂ)) with hy
  have hyim : y.im = σ - t.re := by rw [hy]; simp [Complex.mul_im]
  have hyre : y.re = t.im := by rw [hy]; simp [Complex.mul_re]
  have hyle : y.im ≤ 0 := by rw [hyim]; linarith
  have harg : (σ : ℂ) + y * I = t := by
    rw [hy]
    have hxx : (-I * (t - (σ : ℂ))) * I = t - (σ : ℂ) := by
      rw [mul_comm (-I) _, mul_assoc]
      simp [Complex.I_mul_I]
    rw [hxx]; ring
  have hpl := F.norm_twist_le_of_line_growth hσ hline hyle
  rw [twist, harg, norm_mul, F.norm_exp_twist, hyim, hyre] at hpl
  rw [show Real.exp (-(F.bottomHeight * (σ - t.re))) =
      Real.exp (F.bottomHeight * (t.re - σ)) from by congr 1; ring] at hpl
  rw [← le_div_iff₀ (Real.exp_pos _)] at hpl
  refine le_trans hpl (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- **The graded assembly.** -/
theorem im_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ i ∈ F.bottomShell, (F.pt i).im ≤ lam := by
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
  set K : ℝ := ∑' i : F.aboveBottom, F.weight σ (i : ι) with hK
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
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertLine _ _
    have him : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).im = u := im_vertLine _ _
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
        F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) - F.aboveBottomSum (σ + vfun u) u := by
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
    have hK0 : 0 ≤ K := tsum_nonneg fun i => (F.weight_pos σ (i : ι)).le
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
      ‖∑ i ∈ F.bottomShell,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖
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
    calc ‖∑ i ∈ F.bottomShell,
            Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
              ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖
        = Real.exp (σ * F.bottomHeight) *
            (Real.exp (-(σ * F.bottomHeight)) *
              ‖∑ i ∈ F.bottomShell,
                Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
                  ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * F.bottomHeight) * ((M + K) * Real.exp (lam * |u|)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = ((M + K) * Real.exp (σ * F.bottomHeight)) * Real.exp (lam * |u|) := by ring
  set T : Finset ℝ := F.bottomShell.image (fun i => (F.pt i).im) with hT
  set mult : ℝ → ℝ := fun j =>
    ((F.bottomShell.filter fun i => (F.pt i).im = j).card : ℝ) with hmult
  set Bco : ℝ → ℝ → ℂ := fun u j =>
    ((mult j : ℝ) : ℂ) * Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * (j : ℂ)) with hBco
  have hmpos : ∀ j ∈ T, 0 < mult j := by
    intro j hj
    obtain ⟨i, his, hij⟩ := Finset.mem_image.mp hj
    have hc : 0 < (F.bottomShell.filter fun i => (F.pt i).im = j).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨his, hij⟩⟩
    simp only [hmult]
    exact_mod_cast hc
  have hBnorm : ∀ (u : ℝ), ∀ j ∈ T, ‖Bco u j‖ = mult j := by
    intro u j _
    rw [hBco, norm_mul, norm_exp_neg_ofReal_mul_I_mul', mul_one, Complex.norm_real,
      Real.norm_eq_abs, hmult, abs_of_nonneg (Nat.cast_nonneg _)]
  have hbnd : ∀ u : ℝ, ‖∑ j ∈ T, Bco u j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      ((M + K) * Real.exp (σ * F.bottomHeight)) * Real.exp (lam * |u|) := by
    intro u
    rw [hBco, hmult, hT, ← F.bottomShell_regroup (σ + vfun u) u]
    exact hinner u
  have hkey := le_of_expSum_norm_le_exp T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro i hi
  exact hkey ((F.pt i).im) (Finset.mem_image_of_mem _ hi)

/-- **The graded criterion at the bottom shell.** -/
theorem abs_im_le_of_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ i ∈ F.bottomShell, |(F.pt i).im| ≤ lam := by
  intro i hi
  have h1 := F.im_le_of_line_growth hσ hlam hline i hi
  have h2 := F.im_le_of_line_growth hσ hlam hline _ (F.mem_bottomShell_inv hi)
  rw [F.conj_stable, Complex.conj_im] at h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩

/-- **The graded wrapper.**  A growth exponent on one vertical line bounds *every* displacement. -/
theorem abs_im_le_of_line_growth_all {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)) :
    ∀ i : ι, |(F.pt i).im| ≤ lam := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁⟩ := hcon
  obtain ⟨is, his, hmin⟩ := F.exists_min_re_of_nonempty
    (s := {i : ι | lam < |(F.pt i).im|}) ⟨i₁, hi₁⟩
  set g : ℝ := (F.pt is).re with hgdef
  have hbase : F.base ≤ g := F.base_le is
  set G : AbstractSpectralFamily ι := F.lift g g hbase with hG
  have hlow : ∀ i, (F.pt i).re < g → |(F.pt i).im| ≤ lam := by
    intro i hi
    by_contra hne
    exact absurd (hmin i (not_le.mp hne)) (not_le.mpr hi)
  have hGre : ∀ i, g ≤ (G.pt i).re := by
    intro i
    by_cases h : g ≤ (F.pt i).re
    · rw [hG, F.lift_pt_of_le hbase h]; exact h
    · rw [hG, F.lift_pt_of_lt hbase (not_le.mp h), Complex.ofReal_re]
  have hGis : (G.pt is).re = g := by rw [hG, F.lift_pt_of_le hbase (le_refl _)]
  have hGheight : G.bottomHeight = g :=
    le_antisymm (hGis ▸ G.bottomHeight_le is) (hGre _)
  set s : Finset ι := (F.finite_below g).toFinset with hs
  have hmemcompl : ∀ i : ((s : Set ι)ᶜ : Set ι), g ≤ (F.pt (i : ι)).re := by
    intro i
    have hic := i.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hs, Set.Finite.mem_toFinset,
      below, Set.mem_setOf_eq, not_lt] at hic
    exact hic
  have hline' : ∀ x : ℝ, ‖G.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
      (C + ∑ i ∈ s, (Real.exp (-(σ * g)) + F.weight σ i)) * Real.exp (lam * |x|) := by
    intro x
    set τ : ℂ := (σ : ℂ) + (x : ℂ) * I with hτ
    have hre : (0 : ℝ) < τ.re := by rw [hτ, re_vertLine]; exact hσ
    have hFsum : Summable (fun i : ι => F.term τ i) := (F.summable_norm_term hre).of_norm
    have hGsum : Summable (fun i : ι => G.term τ i) := (G.summable_norm_term hre).of_norm
    have hFsplit := hFsum.sum_add_tsum_compl (s := s)
    have hGsplit := hGsum.sum_add_tsum_compl (s := s)
    have hcompl : (∑' i : ((s : Set ι)ᶜ : Set ι), G.term τ (i : ι))
        = ∑' i : ((s : Set ι)ᶜ : Set ι), F.term τ (i : ι) := by
      refine tsum_congr fun i => ?_
      rw [term, term, hG, F.lift_pt_of_le hbase (hmemcompl i)]
    have hdiff : G.traceC τ = F.traceC τ + ((∑ i ∈ s, G.term τ i) - ∑ i ∈ s, F.term τ i) := by
      rw [traceC, traceC, ← hGsplit, ← hFsplit, hcompl]
      ring
    have hbound : ∀ i ∈ s, ‖G.term τ i‖ + ‖F.term τ i‖ ≤
        (Real.exp (-(σ * g)) + F.weight σ i) * Real.exp (lam * |x|) := by
      intro i hi
      have hlt : (F.pt i).re < g := by
        simpa [hs, Set.Finite.mem_toFinset, below, Set.mem_setOf_eq] using hi
      have hge : (1 : ℝ) ≤ Real.exp (lam * |x|) :=
        Real.one_le_exp (mul_nonneg hlam (abs_nonneg x))
      have h1 : ‖G.term τ i‖ = Real.exp (-(σ * g)) := by
        rw [term, hG, F.lift_pt_of_lt hbase hlt, Complex.norm_exp]
        congr 1
        rw [hτ]
        simp [Complex.mul_re]
      have h2 : ‖F.term τ i‖ ≤ F.weight σ i * Real.exp (lam * |x|) := by
        rw [norm_term, weight, hτ, re_vertLine, im_vertLine, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hxJ : x * (F.pt i).im ≤ lam * |x| := by
          calc x * (F.pt i).im ≤ |x * (F.pt i).im| := le_abs_self _
            _ = |x| * |(F.pt i).im| := abs_mul _ _
            _ ≤ |x| * lam := mul_le_mul_of_nonneg_left (hlow i hlt) (abs_nonneg x)
            _ = lam * |x| := by ring
        linarith
      have h3 : Real.exp (-(σ * g)) ≤ Real.exp (-(σ * g)) * Real.exp (lam * |x|) := by
        nlinarith [Real.exp_pos (-(σ * g)), hge]
      rw [h1]
      nlinarith [h2, h3]
    calc ‖G.traceC τ‖
        ≤ ‖F.traceC τ‖ + ‖(∑ i ∈ s, G.term τ i) - ∑ i ∈ s, F.term τ i‖ := by
          rw [hdiff]; exact norm_add_le _ _
      _ ≤ (C + ∑ i ∈ s, (Real.exp (-(σ * g)) + F.weight σ i)) * Real.exp (lam * |x|) := by
          rw [add_mul, Finset.sum_mul]
          refine add_le_add (hline x) ?_
          refine le_trans (norm_sub_le _ _) ?_
          refine le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hbound
  have hshell : is ∈ G.bottomShell := G.mem_bottomShell.mpr (by rw [hGheight, hGis])
  have hzero := G.abs_im_le_of_line_growth hσ hlam hline' is hshell
  rw [hG, F.lift_pt_of_le hbase (le_refl _)] at hzero
  exact absurd hzero (not_le.mpr his)

/-- **The exponential type on a vertical line is the supremum of the displacements.**  For an
admissible family and any `lam ≥ 0`, a growth bound `exp (lam |x|)` for the trace on one vertical
line of the open right half-plane holds exactly when every displacement is at most `lam`. -/
theorem abs_im_le_iff_exists_line_growth {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ i : ι, |(F.pt i).im| ≤ lam) ↔
      ∃ σ C : ℝ, 0 < σ ∧
        ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|) := by
  constructor
  · intro him
    refine ⟨1, F.traceReal 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertLine]; exact one_pos
    have h := F.norm_traceC_le_of_abs_im_le him hre
    rwa [re_vertLine, im_vertLine] at h
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.abs_im_le_of_line_growth_all hσ hlam hline

/-- **Subexponential growth already forces reality.**  The hypothesis need not be boundedness: it is
enough that for every `eps > 0` the trace is `O(exp (eps |x|))` on *some* vertical line, with the
line allowed to depend on `eps`. -/
theorem im_eq_zero_of_subexponential
    (h : ∀ eps : ℝ, 0 < eps → ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
      ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (eps * |x|)) :
    ∀ i : ι, (F.pt i).im = 0 := by
  intro i
  have hall : ∀ eps : ℝ, 0 < eps → |(F.pt i).im| ≤ eps := by
    intro eps heps
    obtain ⟨σ, C, hσ, hline⟩ := h eps heps
    exact F.abs_im_le_of_line_growth_all hσ heps.le hline i
  have hzero : |(F.pt i).im| ≤ 0 := le_of_forall_pos_le_add fun eps heps => by
    simpa using hall eps heps
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

end

end AbstractSpectralFamily

end HTGeometry
