import GaloisForLFunctions.HTGeometry.ReciprocalTotalPositivityDeflation

/-!
# Reciprocally totally positive entire functions have only negative real zeros

**Theorem** (`ReciprocalTP.eq_neg_of_apply_eq_zero`).  Let `F` be entire with `F 0 ≠ 0`, and suppose
the Taylor coefficients of `1/F(−z)` at `0` are nonnegative and consecutive-row totally positive
(`ReciprocalTP`).  Then every zero of `F` is a negative real number.

**Finite order** (`ReciprocalTPUpTo.eq_neg_of_apply_eq_zero`).  Minors of order `≤ n` suffice for
the zeros `y₀` whose disk `‖z‖ ≤ ‖y₀‖` carries total multiplicity `≤ n`.  Each deflation step
lowers the order by one (`ReciprocalTPUpTo.deflate`), and when one unit of multiplicity is left
the nearest zero `−D` is the only zero in the disk.

This is the zero-location half of the Aissen–Schoenberg–Whitney–Edrei theorem, here for
consecutive-row minors of the reciprocal sequence.  Fix a zero `y₀` and induct on the total
multiplicity `μ` of the zeros of `F` in the closed disk of radius `‖y₀‖`.  Let `D` be the smallest
modulus of a zero.  Pringsheim (`ReciprocalTP.apply_neg_eq_zero`) gives `F(−D) = 0`.  If
`y₀ ≠ −D`, the deflated function `F(y)/(1 + y/D)` is again reciprocally totally positive
(`ReciprocalTP.deflate`), still vanishes at `y₀`, and has multiplicity `μ − 1` in the disk.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An entire function nonvanishing at `0` has finitely many zeros in every closed disk. -/
theorem zeros_finite_closedBall {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (r : ℝ) :
    {z ∈ closedBall (0 : ℂ) r | F z = 0}.Finite := by
  have han : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hcod := han.preimage_zero_mem_codiscrete (x := 0) h0
  have hK : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall _ _
  have hmem : F ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall (0 : ℂ) r) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine (hK.finite_sdiff_of_mem_codiscreteWithin hmem).subset ?_
  rintro z ⟨hz, hz0⟩
  exact ⟨hz, by simpa using hz0⟩

/-- The orders of an entire function nonvanishing at `0` are finite. -/
theorem analyticOrderAt_ne_top_of_entire_of_ne_zero_at_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
    (Set.mem_univ z) ?_
  rw [(hF.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
  exact ENat.zero_ne_top

/-- The order of `y + D` is `1` at `−D` and `0` elsewhere. -/
theorem analyticOrderNatAt_add_const (D z : ℂ) :
    analyticOrderNatAt (fun y => y + D) z = if z = -D then 1 else 0 := by
  have han : AnalyticAt ℂ (fun y : ℂ => y + D) z := by fun_prop
  split_ifs with h
  · subst h
    have : analyticOrderAt (fun y : ℂ => y + D) (-D) = (1 : ℕ) := by
      rw [han.analyticOrderAt_eq_natCast]
      refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun y => ?_⟩
      simp
    simp [analyticOrderNatAt, this]
  · have hz : z + D ≠ 0 := fun h' => h (by linear_combination h')
    have : analyticOrderAt (fun y : ℂ => y + D) z = 0 := han.analyticOrderAt_eq_zero.mpr hz
    simp [analyticOrderNatAt, this]

/-- A nonzero constant factor does not change the order. -/
theorem analyticOrderNatAt_const_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z) {c : ℂ} (hc : c ≠ 0) :
    analyticOrderNatAt (fun y => c * f y) z = analyticOrderNatAt f z := by
  have hconst : analyticOrderAt (fun _ : ℂ => c) z = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hc
  have h := analyticOrderAt_mul (analyticAt_const (v := c) (x := z)) hf
  have heq : (fun y => c * f y) = (fun _ : ℂ => c) * f := rfl
  rw [heq]
  simp only [analyticOrderNatAt]
  rw [h, hconst, zero_add]

/-- A zero of an entire function nonvanishing at `0` has positive order. -/
theorem analyticOrderNatAt_ne_zero_of_apply_eq_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {y₀ : ℂ} (hy₀ : F y₀ = 0) : analyticOrderNatAt F y₀ ≠ 0 := by
  intro hz
  have hne := analyticOrderAt_ne_top_of_entire_of_ne_zero_at_zero hF h0 y₀
  have : analyticOrderAt F y₀ = 0 := by
    rw [← ENat.coe_toNat hne]
    simpa [analyticOrderNatAt] using hz
  exact ((hF.analyticAt y₀).analyticOrderAt_eq_zero.mp this) hy₀

/-- The induction on the multiplicity of the zeros in the closed disk of radius `‖y₀‖`: total
positivity of order `n` locates a zero whose disk carries total multiplicity at most `n`. -/
theorem ReciprocalTPUpTo.eq_neg_of_apply_eq_zero_aux : ∀ (n : ℕ) (F : ℂ → ℂ) (S : Finset ℂ) (y₀ : ℂ),
    ReciprocalTPUpTo n F → F y₀ = 0 → (∀ z : ℂ, ‖z‖ ≤ ‖y₀‖ → F z = 0 → z ∈ S) →
      ∑ z ∈ S, analyticOrderNatAt F z ≤ n → ∃ D : ℝ, 0 < D ∧ y₀ = -(D : ℂ) := by
  intro n
  induction n with
  | zero =>
    intro F S y₀ hF hy₀ hS hsum
    have hmem : y₀ ∈ S := hS y₀ le_rfl hy₀
    have hord := analyticOrderNatAt_ne_zero_of_apply_eq_zero hF.differentiable hF.ne_zero hy₀
    have := Finset.single_le_sum (f := fun z => analyticOrderNatAt F z)
      (fun _ _ => Nat.zero_le _) hmem
    omega
  | succ m ih =>
    intro F S y₀ hF hy₀ hS hsum
    -- the nearest zero
    have hfin := zeros_finite_closedBall hF.differentiable hF.ne_zero ‖y₀‖
    have hne : ({z ∈ closedBall (0 : ℂ) ‖y₀‖ | F z = 0} : Set ℂ).Nonempty :=
      ⟨y₀, by simp [hy₀]⟩
    obtain ⟨z₁, ⟨hz₁b, hz₁0⟩, hz₁min⟩ := Set.exists_min_image _ (fun z => ‖z‖) hfin hne
    set D : ℝ := ‖z₁‖ with hDdef
    have hz₁ne : z₁ ≠ 0 := fun h => hF.ne_zero (h ▸ hz₁0)
    have hD : 0 < D := norm_pos_iff.mpr hz₁ne
    have hDle : D ≤ ‖y₀‖ := by simpa using hz₁b
    have hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0 := by
      intro z hz hz0
      have := hz₁min z ⟨by simp; linarith, hz0⟩
      linarith
    have hFD := hF.apply_neg_eq_zero hD hfree rfl hz₁0
    by_cases hy : y₀ = -(D : ℂ)
    · exact ⟨D, hD, hy⟩
    have hnormD : ‖-(D : ℂ)‖ ≤ ‖y₀‖ := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
      exact hDle
    have hmemD : -(D : ℂ) ∈ S := hS _ hnormD hFD
    -- with total multiplicity one, the two distinct zeros `y₀` and `−D` cannot both be in `S`
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      rcases m with _ | m'
      · exfalso
        have h1 := analyticOrderNatAt_ne_zero_of_apply_eq_zero hF.differentiable hF.ne_zero hy₀
        have h2 := analyticOrderNatAt_ne_zero_of_apply_eq_zero hF.differentiable hF.ne_zero hFD
        have hpair : ∑ z ∈ {y₀, -(D : ℂ)}, analyticOrderNatAt F z ≤
            ∑ z ∈ S, analyticOrderNatAt F z := by
          refine Finset.sum_le_sum_of_subset ?_
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hS z le_rfl hy₀
          · exact hmemD
        rw [Finset.sum_pair hy] at hpair
        omega
      · exact ⟨m', rfl⟩
    -- deflate
    have hG := hF.deflate hD hfree rfl hz₁0
    set G : ℂ → ℂ := fun y => (D : ℂ) * dslope F (-(D : ℂ)) y with hGdef
    have hfac : ∀ y : ℂ, F y = (y + D) * dslope F (-(D : ℂ)) y := by
      intro y
      have := sub_smul_dslope F (-(D : ℂ)) y
      rw [hFD, sub_zero, smul_eq_mul, sub_neg_eq_add] at this
      exact this.symm
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hGy₀ : G y₀ = 0 := by
      have h1 := hfac y₀
      rw [hy₀] at h1
      have hlin : y₀ + (D : ℂ) ≠ 0 := fun h => hy (by linear_combination h)
      have : dslope F (-(D : ℂ)) y₀ = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h hlin
        · exact h
      simp [hGdef, this]
    have hSG : ∀ z : ℂ, ‖z‖ ≤ ‖y₀‖ → G z = 0 → z ∈ S := by
      intro z hz hz0
      refine hS z hz ?_
      have : dslope F (-(D : ℂ)) z = 0 := by
        simpa [hGdef, hDc] using hz0
      rw [hfac z, this, mul_zero]
    -- the multiplicity drops by one
    have hdsl : Differentiable ℂ (dslope F (-(D : ℂ))) := differentiable_dslope_entire
      hF.differentiable _
    have hdsl0 : dslope F (-(D : ℂ)) 0 ≠ 0 := by
      intro h
      apply hF.ne_zero
      rw [hfac 0, h, mul_zero]
    have hordF : ∀ z, analyticOrderNatAt F z =
        (if z = -(D : ℂ) then 1 else 0) + analyticOrderNatAt G z := by
      intro z
      have hFeq : F = (fun y : ℂ => y + (D : ℂ)) * dslope F (-(D : ℂ)) := funext fun y => hfac y
      have hlin : AnalyticAt ℂ (fun y : ℂ => y + (D : ℂ)) z := by fun_prop
      have hdz : AnalyticAt ℂ (dslope F (-(D : ℂ))) z := hdsl.analyticAt z
      have hlin_ne : analyticOrderAt (fun y : ℂ => y + (D : ℂ)) z ≠ ⊤ := by
        by_cases h : z = -(D : ℂ)
        · subst h
          have : analyticOrderAt (fun y : ℂ => y + (D : ℂ)) (-(D : ℂ)) = (1 : ℕ) := by
            rw [hlin.analyticOrderAt_eq_natCast]
            exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
              Eventually.of_forall fun y => by simp⟩
          rw [this]
          exact ENat.coe_ne_top 1
        · have hz : z + (D : ℂ) ≠ 0 := fun h' => h (by linear_combination h')
          rw [hlin.analyticOrderAt_eq_zero.mpr hz]
          exact ENat.zero_ne_top
      rw [hFeq, analyticOrderNatAt_mul hlin hdz hlin_ne
        (analyticOrderAt_ne_top_of_entire_of_ne_zero_at_zero hdsl hdsl0 z), analyticOrderNatAt_add_const, hGdef,
        analyticOrderNatAt_const_mul hdz hDc]
    have hsumG : ∑ z ∈ S, analyticOrderNatAt G z ≤ m' + 1 := by
      have hsplit : ∑ z ∈ S, analyticOrderNatAt F z =
          1 + ∑ z ∈ S, analyticOrderNatAt G z := by
        rw [Finset.sum_congr rfl fun z _ => hordF z, Finset.sum_add_distrib,
          Finset.sum_ite_eq' S (-(D : ℂ)) (fun _ => (1 : ℕ)), if_pos hmemD]
      omega
    exact ih G S y₀ hG hGy₀ hSG hsumG

/-- **Finite-order zero location.**  If the reciprocal coefficients of `F` are nonnegative and
their consecutive-row minors of order `≤ n` are nonnegative, then every zero `y₀` of `F` whose
closed disk `‖z‖ ≤ ‖y₀‖` carries total multiplicity at most `n` is a negative real number. -/
theorem ReciprocalTPUpTo.eq_neg_of_apply_eq_zero {n : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo n F)
    {S : Finset ℂ} {y₀ : ℂ} (hy₀ : F y₀ = 0) (hS : ∀ z : ℂ, ‖z‖ ≤ ‖y₀‖ → F z = 0 → z ∈ S)
    (hsum : ∑ z ∈ S, analyticOrderNatAt F z ≤ n) : ∃ D : ℝ, 0 < D ∧ y₀ = -(D : ℂ) :=
  ReciprocalTPUpTo.eq_neg_of_apply_eq_zero_aux n F S y₀ hF hy₀ hS hsum

/-- **Every zero of a reciprocally totally positive entire function is negative real.** -/
theorem ReciprocalTP.eq_neg_of_apply_eq_zero {F : ℂ → ℂ} (hF : ReciprocalTP F) {y₀ : ℂ}
    (hy₀ : F y₀ = 0) : ∃ D : ℝ, 0 < D ∧ y₀ = -(D : ℂ) := by
  have hfin := zeros_finite_closedBall hF.differentiable hF.ne_zero ‖y₀‖
  exact (hF.upTo _).eq_neg_of_apply_eq_zero hy₀ (S := hfin.toFinset)
    (fun z hz hz0 => by simp [hz, hz0]) le_rfl

end

end GaloisForLFunctions.HTGeometry
