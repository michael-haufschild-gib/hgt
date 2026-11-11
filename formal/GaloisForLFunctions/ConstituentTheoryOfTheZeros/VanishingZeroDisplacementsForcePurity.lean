import GaloisForLFunctions.ConstituentTheoryOfTheZeros.InfinitelyManyZerosOfAnExpansionAreNotZerosOfXi

/-!
# Vanishing zero displacements force purity

An off-line zero of a holomorphic almost-periodic function recurs in discs
at a positive density of heights. Moving those zeros by displacements tending
to zero still puts zeta zeros in slightly larger discs, contradicting the
density-zero theorem for off-line zeta-zero shifts.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

/-- An interior zero whose recurrent divisor can be moved to zeta zeros by
cofinitely vanishing displacements lies on the critical line. -/
theorem re_eq_half_of_zero_displacements_tendsto_zero {F : ℂ → ℂ} {τ₁ τ₂ : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | τ₁ < z.re ∧ z.re < τ₂})
    (hFne : ∃ z, (τ₁ < z.re ∧ z.re < τ₂) ∧ F z ≠ 0)
    {ρ₀ : ℂ} (hρ1 : τ₁ < ρ₀.re) (hρ2 : ρ₀.re < τ₂)
    (hpos : 0 < ρ₀.re) (hone : ρ₀.re < 1) (hFρ : F ρ₀ = 0)
    {R : ℝ} (hR : 0 < R) (hAP : IsStripAlmostPeriodicOn F ρ₀.re R)
    {η : {z ∈ {z : ℂ | τ₁ < z.re ∧ z.re < τ₂} | F z = 0} → ℂ}
    (hη : Tendsto η cofinite (𝓝 0))
    (hzero : ∀ᶠ p : {z ∈ {z : ℂ | τ₁ < z.re ∧ z.re < τ₂} | F z = 0} in cofinite,
      riemannZeta ((p : ℂ) + η p) = 0) :
    ρ₀.re = 1 / 2 := by
  by_contra hne
  let E : Set ℂ := {z ∈ {z : ℂ | τ₁ < z.re ∧ z.re < τ₂} | F z = 0}
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero (ρ₀ := ρ₀) hpos hone hne
  have hsmall : ∀ᶠ p in cofinite, ‖η p‖ < r / 2 := by
    have ht := hη.norm
    rw [norm_zero] at ht
    exact ht.eventually (gt_mem_nhds (half_pos hr))
  have hbad : {p : E | ¬ (‖η p‖ < r / 2 ∧ riemannZeta ((p : ℂ) + η p) = 0)}.Finite :=
    eventually_cofinite.mp (hsmall.and hzero)
  obtain ⟨B, hB⟩ := (hbad.image fun p : E => |(p : ℂ).im|).bddAbove
  let r' := min (r / 2) (min ((ρ₀.re - τ₁) / 2) ((τ₂ - ρ₀.re) / 2))
  have hr' : 0 < r' := lt_min (half_pos hr) (lt_min (by linarith only [hρ1])
    (by linarith only [hρ2]))
  have hrr : r' ≤ r / 2 := min_le_left _ _
  have hrτ₁ : r' ≤ (ρ₀.re - τ₁) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ₂ : r' ≤ (τ₂ - ρ₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts_on_strip hF hFne
    hρ1 hρ2 hFρ hR hAP hr'
  let T₂ := max B 0 + |ρ₀.im| + r' + 1
  have hT₂ : 0 ≤ T₂ := by dsimp [T₂]; positivity
  have hthick' : ∀ y : ℝ, ∃ τ ∈ Icc y (y + L),
      Ioo (τ - d) (τ + d) ⊆ zetaZeroShiftSet ρ₀ r ∪ Iic T₂ := by
    intro y
    obtain ⟨τ, hτ, hsub⟩ := hthick y
    refine ⟨τ, hτ, fun t ht => ?_⟩
    by_cases htT : t ≤ T₂
    · exact Or.inr htT
    left
    obtain ⟨z, hz, hz0⟩ := hsub ht
    have hn := mem_ball_iff_norm.mp hz
    have hre := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt hn)
    have him := abs_lt.mp ((abs_im_le_norm (z - ρ₀)).trans_lt hn)
    simp only [Complex.sub_re] at hre
    simp only [Complex.sub_im] at him
    have hmem : τ₁ < (z + t * I).re ∧ (z + t * I).re < τ₂ := by
      simp only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
      constructor <;> linarith only [hre.1, hre.2, hrτ₁, hrτ₂, hρ1, hρ2]
    let p : E := ⟨z + t * I, hmem, hz0⟩
    have hp : ‖η p‖ < r / 2 ∧ riemannZeta ((p : ℂ) + η p) = 0 := by
      by_contra hnot
      have hbound : |(p : ℂ).im| ≤ B := hB ⟨p, hnot, rfl⟩
      have hb : z.im + t ≤ B := by
        simpa only [p, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re]
          using (le_abs_self (p : ℂ).im).trans hbound
      dsimp [T₂] at htT
      linarith only [htT, hb, him.1, neg_abs_le ρ₀.im, le_max_left B 0]
    refine ⟨z + η p, ?_, ?_⟩
    · rw [mem_ball_iff_norm]
      calc ‖z + η p - ρ₀‖ = ‖(z - ρ₀) + η p‖ := by congr 1; ring
        _ ≤ ‖z - ρ₀‖ + ‖η p‖ := norm_add_le _ _
        _ < r := by linarith only [hn, hp.1, hrr]
    · have heq : z + η p + t * I = (p : ℂ) + η p := by dsimp [p]; ring
      rw [heq]
      exact hp.2
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  let κ := d / (L + 2 * d)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hup := hdens (κ / 2) (by positivity)
  obtain ⟨T, hTlow, hTup, hT0, hTlarge⟩ :=
    (hlow.and (hup.and ((eventually_gt_atTop (0 : ℝ)).and
      (eventually_gt_atTop (2 * T₂ / κ))))).exists
  have hsub : (zetaZeroShiftSet ρ₀ r ∪ Iic T₂) ∩ Icc 0 T ⊆
      (zetaZeroShiftSet ρ₀ r ∩ Icc 0 T) ∪ Icc 0 T₂ := by
    rintro t ⟨ht | ht, htI⟩
    · exact Or.inl ⟨ht, htI⟩
    · exact Or.inr ⟨htI.1, ht⟩
  have hvol : volume ((zetaZeroShiftSet ρ₀ r ∪ Iic T₂) ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ / 2 * T + T₂) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_add (by positivity) hT₂]
    exact add_le_add hTup le_rfl
  have h := hTlow.trans hvol
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  change κ * T ≤ κ / 2 * T + T₂ at h
  rw [div_lt_iff₀ hκ] at hTlarge
  nlinarith only [h, hTlarge]

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
