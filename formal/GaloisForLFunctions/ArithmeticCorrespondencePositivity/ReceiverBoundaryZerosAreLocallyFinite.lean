import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverSpectralDensityAtTheZeroAbscissa

/-!
# Finite boundary zeros and bounded complementary windows

On a compact height interval the actual zero frontier contains finitely many
zeros. Removing neighborhoods of these zeros leaves a compact region on which
the centered receiver symbol is uniformly bounded, including the frontier.
-/

open Complex Set Filter Topology MeasureTheory Metric
open RHTower RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- All zeros on a compact segment of the actual boundary form a finite set. -/
theorem exists_receiver_boundary_zero_finset (hΘ1 : zetaZeroAbscissa < 1) (a b : ℝ) :
    ∃ Z : Finset ℂ, ∀ ρ : ℂ, ρ ∈ Z ↔
      riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b := by
  classical
  let R : ℝ := |zetaZeroAbscissa| + |a| + |b| + 3
  have h1 : (1 : ℂ) ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right, norm_one]
    dsimp [R]
    linarith [abs_nonneg zetaZeroAbscissa, abs_nonneg a, abs_nonneg b]
  have hf := HTGeometry.finite_zeros_of_analyticOnNhd_closedBall
    (f := zetaResidueUnit) (fun z _ => analyticAt_zetaResidueUnit z) h1
    (by simp : zetaResidueUnit 1 ≠ 0)
  have hfinite : {ρ : ℂ | riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b}.Finite := by
    refine hf.subset ?_
    rintro ρ ⟨hz, hre, him⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      have hi : |ρ.im| ≤ |a| + |b| := abs_le.mpr
        ⟨by linarith [him.1, neg_abs_le a, abs_nonneg b],
          by linarith [him.2, le_abs_self b, abs_nonneg a]⟩
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ < R := by rw [hre]; dsimp [R]; linarith
    · change zetaResidueUnit ρ = 0
      have hρ1 : ρ ≠ 1 := by
        intro h
        rw [h, one_re] at hre
        linarith
      rw [zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
  exact ⟨hfinite.toFinset, fun ρ => hfinite.mem_toFinset⟩

/-- Away from the finitely many boundary ordinates, the actual centered symbol
is uniformly bounded on a compact rectangle reaching the zero frontier. -/
theorem exists_receiver_bound_away_boundary_zeros {ε : ℝ} (hε : 0 < ε)
    (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (hΘ1 : zetaZeroAbscissa < 1)
    (a b : ℝ) (Z : Finset ℂ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ e ∈ Ioo 0 η, ∀ y ∈ Icc a b,
      (∀ ρ ∈ Z, δ ≤ |y - ρ.im|) →
      ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ≤ B := by
  let σ : ℝ := zetaZeroAbscissa - ε
  let η : ℝ := (1 - zetaZeroAbscissa) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ + η < 1 := by dsimp [σ, η]; linarith
  let R : ℝ := |σ| + |a| + |b| + 3
  let K : Set ℂ := closedBall 0 R ∩
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ σ + η ∧ s.im ∈ Icc a b ∧
      ∀ ρ ∈ Z, δ ≤ |s.im - ρ.im|}
  have hsep : IsClosed {s : ℂ | ∀ ρ ∈ Z, δ ≤ |s.im - ρ.im|} := by
    have hrw : {s : ℂ | ∀ ρ ∈ Z, δ ≤ |s.im - ρ.im|} =
        ⋂ ρ : ℂ, ⋂ _ : ρ ∈ Z, {s : ℂ | δ ≤ |s.im - ρ.im|} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun ρ : ℂ => isClosed_iInter fun _ : ρ ∈ Z =>
      isClosed_le continuous_const
        (by fun_prop : Continuous fun s : ℂ => |s.im - ρ.im|)
  have hclosed : IsClosed {s : ℂ | σ ≤ s.re ∧ s.re ≤ σ + η ∧ s.im ∈ Icc a b ∧
      ∀ ρ ∈ Z, δ ≤ |s.im - ρ.im|} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_Icc.preimage Complex.continuous_im).inter hsep))
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right hclosed
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs h
    have := hs.2.1
    rw [h, zero_re] at this
    linarith
  have hs1 : ∀ s ∈ K, s ≠ 1 := by
    intro s hs h
    have := hs.2.2.1
    rw [h, one_re] at this
    linarith
  have hunit : ∀ s ∈ K, zetaResidueUnit (s + (ε : ℂ)) ≠ 0 := by
    intro s hs
    have hlo : zetaZeroAbscissa ≤ (s + (ε : ℂ)).re := by
      have := hs.2.1
      simp only [add_re, ofReal_re]
      dsimp only [σ] at this
      linarith
    rcases hlo.eq_or_lt with heq | hlt
    · intro hu
      have hρ1 : s + (ε : ℂ) ≠ 1 := by
        intro h
        rw [h, one_re] at heq
        linarith
      have hz : riemannZeta (s + (ε : ℂ)) = 0 := by
        by_contra hne
        exact (zetaResidueUnit_ne_zero_iff hρ1).mpr hne hu
      have hm : s + (ε : ℂ) ∈ Z := (hZ _).mpr
        ⟨hz, heq.symm, by simpa only [add_im, ofReal_im, add_zero] using hs.2.2.2.1⟩
      have hd := hs.2.2.2.2 _ hm
      simp only [add_im, ofReal_im, add_zero, sub_self, abs_zero] at hd
      linarith
    · exact zetaResidueUnit_ne_zero_of_zeroFree
        (fun _ ht => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt ht) hlt
  have hc : ContinuousOn (centeredReceiverSymbol ε) K := by
    have hq : ContinuousOn (fun s : ℂ => riemannZeta s *
        (invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))) / s) K := by
      intro s hs
      have hi : ContinuousAt (fun z : ℂ => invZeta (z + (ε : ℂ))) s :=
        (differentiableAt_invZeta (hunit s hs)).continuousAt.comp
          (f := fun z : ℂ => z + (ε : ℂ))
          (by fun_prop : ContinuousAt (fun z : ℂ => z + (ε : ℂ)) s)
      exact (((analyticOn_riemannZeta s (hs1 s hs)).continuousAt.mul
        (hi.sub continuousAt_const)).div continuousAt_id (hs0 s hs)).continuousWithinAt
    exact hq.congr (fun s hs => centeredReceiverSymbol_eq (hs1 s hs))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨η, hη, max B 0, le_max_right _ _, fun e he y hy hd => ?_⟩
  have he1 : e < 1 - zetaZeroAbscissa := by dsimp [η] at he; linarith [he.2]
  rw [lineSymbol_receiver_eq_centered_at_zeroAbscissa hε hθ he.1 he1]
  let s : ℂ := ((σ + e : ℝ) : ℂ) + (y : ℂ) * I
  have hre : s.re = σ + e := by simp [s]
  have him : s.im = y := by simp [s]
  have hmem : s ∈ K := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hyabs : |y| ≤ |a| + |b| := abs_le.mpr
        ⟨by linarith [hy.1, neg_abs_le a, abs_nonneg b],
          by linarith [hy.2, le_abs_self b, abs_nonneg a]⟩
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ R := by
          rw [hre, him, abs_of_pos (by linarith [he.1] : 0 < σ + e)]
          dsimp [R]
          linarith [he.2, le_abs_self σ]
    · rw [hre]; linarith [he.1]
    · rw [hre]; linarith [he.2]
    · simpa only [him] using hy
    · simpa only [him] using hd
  exact (hB s hmem).trans (le_max_left _ _)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
