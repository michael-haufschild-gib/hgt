import GaloisForLFunctions.HTGeometry.AbstractSpectralShell

/-!
# A bounded vertical line makes an abstract spectral family real

The rigidity theorem over an arbitrary index type.  For an admissible family of spectral points --
heights bounded below, displacements below one half, summable real-time weight, finite shells,
conjugation-stable -- boundedness of the trace `t ↦ ∑ exp (-t α)` on a *single* vertical line of the
open right half-plane forces every point onto the real axis.

Three ingredients.  Half-plane decay from the order-one envelope gives `exp (g₁ v) ‖trace‖` bounded
where `g₁` is the least height; the spectral gap above the bottom shell gives the same for the
above-bottom part, so with `v = |u| / (2 (g₂ - g₁))` the bottom-shell sum is bounded uniformly in
`u`.  Shell homogeneity turns that sum into a finite sum of real exponentials with coefficients of
constant modulus, and phase-robust dominance forces every displacement in the shell to be
nonpositive; conjugation stability then makes it zero.  Finally, replacing all points below a cut by
a real point at the cut height produces another admissible family with the same line bound whose
bottom shell is the cut's own, so the conclusion propagates to every height.
-/

open Complex
open scoped BigOperators

namespace HTGeometry

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} [Nonempty ι] (F : AbstractSpectralFamily ι)

/-- The bottom-shell sum regrouped by displacement. -/
theorem bottomShell_regroup (a u : ℝ) :
    (∑ i ∈ F.bottomShell,
        Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
          ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))
      = ∑ j ∈ F.bottomShell.image (fun i => (F.pt i).im),
          ((((F.bottomShell.filter fun i => (F.pt i).im = j).card : ℝ) : ℂ) *
              Complex.exp (-(a : ℂ) * I * (j : ℂ))) *
            ((Real.exp (u * j) : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := F.bottomShell.image (fun i => (F.pt i).im))
    (fun i hi => Finset.mem_image_of_mem _ hi)
    (fun i => Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
      ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : ∀ i ∈ F.bottomShell.filter (fun i => (F.pt i).im = j),
      Complex.exp (-(a : ℂ) * I * ((F.pt i).im : ℂ)) *
          ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)
        = Complex.exp (-(a : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ) :=
    fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- **The assembly.**  A bounded vertical line makes every bottom-shell displacement nonpositive. -/
theorem im_nonpos_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
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
  set K : ℝ := ∑' i : F.aboveBottom, F.weight σ (i : ι) with hK
  set M : ℝ := max C (F.traceReal σ) with hM
  set vfun : ℝ → ℝ := fun u => |u| / (2 * dgap) with hvfun
  have hvnn : ∀ u, 0 ≤ vfun u := fun u => div_nonneg (abs_nonneg u) (by linarith)
  have hmaster : ∀ u : ℝ,
      Real.exp (F.bottomHeight * vfun u) * ‖F.bottomShellSum (σ + vfun u) u‖ ≤ M + K := by
    intro u
    have hvnn' : 0 ≤ vfun u := hvnn u
    have hre : (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I).re = σ + vfun u := re_vertLine _ _
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
        F.traceC (((σ + vfun u : ℝ) : ℂ) + (u : ℂ) * I) - F.aboveBottomSum (σ + vfun u) u := by
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
      ‖∑ i ∈ F.bottomShell,
          Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
            ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖
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
    calc ‖∑ i ∈ F.bottomShell,
            Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
              ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖
        = Real.exp (σ * F.bottomHeight) *
            (Real.exp (-(σ * F.bottomHeight)) *
              ‖∑ i ∈ F.bottomShell,
                Complex.exp (-((σ + vfun u : ℝ) : ℂ) * I * ((F.pt i).im : ℂ)) *
                  ((Real.exp (u * (F.pt i).im) : ℝ) : ℂ)‖) := by
          rw [← mul_assoc, hEa, one_mul]
      _ ≤ Real.exp (σ * F.bottomHeight) * (M + K) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = (M + K) * Real.exp (σ * F.bottomHeight) := by ring
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
      (M + K) * Real.exp (σ * F.bottomHeight) := by
    intro u
    rw [hBco, hmult, hT, ← F.bottomShell_regroup (σ + vfun u) u]
    exact hinner u
  have hkey := le_zero_of_expSum_norm_le T (fun j => j) mult hmpos
    (fun i _ j _ h => h) Bco hBnorm hbnd
  intro i hi
  exact hkey ((F.pt i).im) (Finset.mem_image_of_mem _ hi)

/-- **A bounded vertical line puts the family's bottom shell on the real axis.** -/
theorem im_eq_zero_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ i ∈ F.bottomShell, (F.pt i).im = 0 := by
  intro i hi
  have h1 := F.im_nonpos_of_line_bound hσ hline i hi
  have h2 := F.im_nonpos_of_line_bound hσ hline _ (F.mem_bottomShell_inv hi)
  rw [F.conj_stable, Complex.conj_im] at h2
  linarith

/-- The points below a height cut. -/
def below (g : ℝ) : Set ι := {i : ι | (F.pt i).re < g}

omit [Nonempty ι] in
theorem finite_below (g : ℝ) : (F.below g).Finite := by
  refine (F.shell_finite g).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq]
  exact le_of_lt hi

/-- The family with every point below `g` replaced by a real point of height `H`. -/
def lift (g H : ℝ) (hH : F.base ≤ H) : AbstractSpectralFamily ι where
  pt := fun i => if g ≤ (F.pt i).re then F.pt i else ((H : ℝ) : ℂ)
  inv := F.inv
  base := F.base
  base_pos := F.base_pos
  base_le := by
    intro i
    by_cases h : g ≤ (F.pt i).re
    · simpa [h] using F.base_le i
    · simpa [h] using hH
  abs_im_lt := by
    intro i
    by_cases h : g ≤ (F.pt i).re
    · simpa [h] using F.abs_im_lt i
    · simp [h]
  summable_weight := by
    intro σ hσ
    classical
    simp only [apply_ite Complex.re, Complex.ofReal_re]
    have hfin : (F.below g).Finite := F.finite_below g
    have h1 : Summable (fun i : (F.below g) =>
        Real.exp (-(σ * (if g ≤ (F.pt (i : ι)).re then (F.pt (i : ι)).re else H)))) := by
      have : Finite (F.below g) := hfin.to_subtype
      exact Summable.of_finite
    have h2 : Summable (fun i : ((F.below g)ᶜ : Set ι) =>
        Real.exp (-(σ * (if g ≤ (F.pt (i : ι)).re then (F.pt (i : ι)).re else H)))) := by
      refine ((F.summable_weight hσ).subtype _).congr fun i => ?_
      have hi : ¬ ((F.pt (i : ι)).re < g) := i.2
      rw [if_pos (not_lt.mp hi)]
      rfl
    exact summable_subtype_and_compl.mp ⟨h1, h2⟩
  shell_finite := by
    intro R
    classical
    refine Set.Finite.subset ((F.shell_finite R).union (F.finite_below g)) ?_
    intro i hi
    by_cases h : g ≤ (F.pt i).re
    · left
      simpa [h] using hi
    · right
      exact not_le.mp h
  conj_stable := by
    intro i
    have hre : (F.pt (F.inv i)).re = (F.pt i).re := by
      rw [F.conj_stable, Complex.conj_re]
    by_cases h : g ≤ (F.pt i).re
    · rw [if_pos (hre ▸ h), if_pos h, F.conj_stable]
    · rw [if_neg (by rw [hre]; exact h), if_neg h, Complex.conj_ofReal]

omit [Nonempty ι] in
theorem lift_pt_of_le {g H : ℝ} (hH : F.base ≤ H) {i : ι} (hi : g ≤ (F.pt i).re) :
    (F.lift g H hH).pt i = F.pt i := by
  simp [lift, hi]

omit [Nonempty ι] in
theorem lift_pt_of_lt {g H : ℝ} (hH : F.base ≤ H) {i : ι} (hi : (F.pt i).re < g) :
    (F.lift g H hH).pt i = ((H : ℝ) : ℂ) := by
  simp [lift, not_le.mpr hi]

/-- **Spectral rigidity from one vertical line.**  If the trace of an admissible family is bounded
on a single vertical line of the open right half-plane, every point of the family is real. -/
theorem im_eq_zero_of_line_bound_all {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
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
  have hline' : ∀ x : ℝ, ‖G.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
      C + ∑ i ∈ s, (Real.exp (-(σ * g)) + F.weight σ i) := by
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
        Real.exp (-(σ * g)) + F.weight σ i := by
      intro i hi
      have hlt : (F.pt i).re < g := by
        simpa [hs, Set.Finite.mem_toFinset, below, Set.mem_setOf_eq] using hi
      have h1 : ‖G.term τ i‖ = Real.exp (-(σ * g)) := by
        rw [term, hG, F.lift_pt_of_lt hbase hlt, Complex.norm_exp]
        congr 1
        rw [hτ]
        simp [Complex.mul_re]
      have h2 : ‖F.term τ i‖ = F.weight σ i := by
        rw [norm_term, weight, hτ, re_vertLine, im_vertLine, hlow i hlt]
        congr 1
        ring
      rw [h1, h2]
    calc ‖G.traceC τ‖
        ≤ ‖F.traceC τ‖ + ‖(∑ i ∈ s, G.term τ i) - ∑ i ∈ s, F.term τ i‖ := by
          rw [hdiff]; exact norm_add_le _ _
      _ ≤ C + ∑ i ∈ s, (Real.exp (-(σ * g)) + F.weight σ i) := by
          refine add_le_add (hline x) ?_
          refine le_trans (norm_sub_le _ _) ?_
          refine le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hbound
  have hshell : is ∈ G.bottomShell := G.mem_bottomShell.mpr (by rw [hGheight, hGis])
  have hzero := G.im_eq_zero_of_line_bound hσ hline' is hshell
  rw [hG, F.lift_pt_of_le hbase (le_refl _)] at hzero
  exact his hzero

/-- **The spectral criterion, both directions.**  For an admissible family of spectral points,
boundedness of the trace on some vertical line of the open right half-plane is equivalent to the
whole family being real.

The trace is `Tr exp (-t A)` for the operator with these eigenvalues, so the criterion says: a
non-self-adjoint admissible spectrum is detected by unbounded growth along every vertical line, and
one bounded line certifies reality of the entire spectrum. -/
theorem im_eq_zero_iff_exists_line_bound :
    (∀ i : ι, (F.pt i).im = 0) ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro him
    refine ⟨1, F.traceReal 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertLine]; exact one_pos
    have h := F.norm_traceC_le_of_abs_im_le (lam := 0) (fun i => by rw [him i]; simp) hre
    rw [re_vertLine] at h
    simpa using h
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.im_eq_zero_of_line_bound_all hσ hline

end

end AbstractSpectralFamily

end HTGeometry
