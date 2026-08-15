import GaloisForLFunctions.RHTower.SelbergClass.BarnesFiniteRectangle

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace RHTower

noncomputable section

private theorem analyticAt_barnesCpow (η w : ℂ) (hη : η ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => η ^ (-z)) w := by
  have hdiff : Differentiable ℂ (fun z : ℂ => η ^ (-z)) :=
    Differentiable.const_cpow differentiable_neg (Or.inl hη)
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) w (Set.mem_univ _)

private theorem analyticAt_barnesGammaLeft
    {ξ : ℂ} {c : ℝ} (hcξ : c < ξ.re) {w : ℂ} (hw : w.re ≤ c) :
    AnalyticAt ℂ (fun z : ℂ => Gamma (ξ - z)) w := by
  have hpos : 0 < (ξ - w).re := by
    simp only [sub_re]
    linarith
  have hcomp := (HTGeometry.analyticAt_Gamma_of_re_pos hpos).comp
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => ξ - z) w)
  simpa [Function.comp_def] using hcomp

private theorem meromorphicOrderAt_eq_zero_of_analytic_ne
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hz : f z ≠ 0) :
    meromorphicOrderAt f z = 0 := by
  rw [hf.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr hz)]
  simp

private theorem meromorphicOrderAt_barnesJ_eq_Gamma {ξ η : ℂ} {c : ℝ}
    (hcξ : c < ξ.re) (hη : η ≠ 0) {w : ℂ}
    (hw : w.re ≤ c) :
    meromorphicOrderAt (barnesJ ξ η) w = meromorphicOrderAt Gamma w := by
  have hleft : AnalyticAt ℂ (fun z : ℂ => Gamma (ξ - z)) w :=
    analyticAt_barnesGammaLeft hcξ hw
  have hleft_ne : Gamma (ξ - w) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      have hpos : 0 < (ξ - w).re := by
        simp only [sub_re]
        linarith
      exact hpos)
  have hpow : AnalyticAt ℂ (fun z : ℂ => η ^ (-z)) w :=
    analyticAt_barnesCpow η w hη
  have hpow_ne : η ^ (-w) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hη)
  have hleft_order : meromorphicOrderAt (fun z : ℂ => Gamma (ξ - z)) w = 0 :=
    meromorphicOrderAt_eq_zero_of_analytic_ne hleft hleft_ne
  have hpow_order : meromorphicOrderAt (fun z : ℂ => η ^ (-z)) w = 0 :=
    meromorphicOrderAt_eq_zero_of_analytic_ne hpow hpow_ne
  have hleft_mero : MeromorphicAt (fun z : ℂ => Gamma (ξ - z)) w := hleft.meromorphicAt
  have hpow_mero : MeromorphicAt (fun z : ℂ => η ^ (-z)) w := hpow.meromorphicAt
  have hgamma : MeromorphicAt Gamma w := Meromorphic.Gamma w
  change meromorphicOrderAt
    ((fun z : ℂ => Gamma (ξ - z)) * Gamma * (fun z : ℂ => η ^ (-z))) w = _
  rw [meromorphicOrderAt_mul (hleft_mero.mul hgamma) hpow_mero,
    meromorphicOrderAt_mul hleft_mero hgamma, hleft_order, hpow_order]
  simp

private theorem meromorphicOn_barnesJ (ξ η : ℂ) (hη : η ≠ 0) (S : Set ℂ) :
    MeromorphicOn (barnesJ ξ η) S := by
  intro w hw
  have hleft : MeromorphicAt (fun z : ℂ => Gamma (ξ - z)) w := by
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma (ξ - w)).comp_analyticAt
        (x := w) (g := fun z : ℂ => ξ - z) (by fun_prop)
  have hpow : MeromorphicAt (fun z : ℂ => η ^ (-z)) w :=
    (analyticAt_barnesCpow η w hη).meromorphicAt
  change MeromorphicAt ((fun z : ℂ => Gamma (ξ - z)) * Gamma *
    (fun z : ℂ => η ^ (-z))) w
  exact (hleft.mul (Meromorphic.Gamma w)).mul hpow

private theorem hasSimplePolesOn_barnesJ
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    HasSimplePolesOn (barnesJ ξ η)
      (Rectangle (barnesLeftCorner m T) (barnesRightCorner c T)) := by
  intro q hq
  have hRe : (barnesLeftCorner m T).re ≤ (barnesRightCorner c T).re := by
    simp [barnesLeftCorner, barnesRightCorner]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hIm : (barnesLeftCorner m T).im ≤ (barnesRightCorner c T).im := by
    simp [barnesLeftCorner, barnesRightCorner]
    linarith
  have hqre : q.re ≤ c := by
    simpa [barnesRightCorner] using (mem_Rect hRe hIm q).mp hq |>.2.1
  by_cases hqGamma : ∃ n : ℕ, q = -(n : ℂ)
  · rcases hqGamma with ⟨n, hn⟩
    rw [meromorphicOrderAt_barnesJ_eq_Gamma hcξ hη hqre, hn,
      Complex.meromorphicOrderAt_Gamma_neg_nat]
  · push Not at hqGamma
    rw [meromorphicOrderAt_barnesJ_eq_Gamma hcξ hη hqre,
      Complex.meromorphicOrderAt_Gamma_of_not_neg_nat hqGamma]
    exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega)

private theorem barnesPoles_disjoint_border
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    Disjoint (RectangleBorder (barnesLeftCorner m T) (barnesRightCorner c T))
      {z | meromorphicOrderAt (barnesJ ξ η) z < 0} := by
  have hRe : (barnesLeftCorner m T).re ≤ (barnesRightCorner c T).re := by
    simp [barnesLeftCorner, barnesRightCorner]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hIm : (barnesLeftCorner m T).im ≤ (barnesRightCorner c T).im := by
    simp [barnesLeftCorner, barnesRightCorner]
    linarith
  refine Set.disjoint_left.2 ?_
  intro q hqborder hqpole
  have hqR : q ∈ Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) :=
    rectangleBorder_subset_rectangle _ _ hqborder
  have hqP : q ∈ (barnesPoleFinset m : Set ℂ) := by
    rw [← barnesPoleSet_eq hc hcξ hT hη]
    exact ⟨hqR, hqpole⟩
  change q ∈ barnesPoleFinset m at hqP
  rcases Finset.mem_image.mp hqP with ⟨n, hnrange, hnq⟩
  subst q
  have hlt : n < m + 1 := Finset.mem_range.mp hnrange
  have hnm : n ≤ m := by omega
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  apply (not_mem_rectangleBorder_of_rectangle_mem_nhds ?_) hqborder
  rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le hRe, Set.uIoo_of_le hIm]
  constructor
  · constructor
    · have hleft : -((m : ℝ) + 1 / 2) < -(n : ℝ) := by linarith
      simpa [barnesLeftCorner] using hleft
    · have hright : -(n : ℝ) < c := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      simpa [barnesRightCorner] using hright
  · constructor
    · have himleft : -T < (0 : ℝ) := by linarith
      simpa [barnesLeftCorner] using himleft
    · have himright : (0 : ℝ) < T := hT
      simpa [barnesRightCorner] using himright

private theorem barnesPoleSet_finite
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    (Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) ∩
      {z | meromorphicOrderAt (barnesJ ξ η) z < 0}).Finite := by
  rw [barnesPoleSet_eq hc hcξ hT hη]
  exact (barnesPoleFinset m).finite_toSet

/-- Finite Barnes rectangle residue theorem for the concrete integrand.
No contour limit or continuation is asserted here. -/
theorem rectangleIntegral_barnesJ_eq_sumResiduesIn
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) =
      sumResiduesIn (barnesJ ξ η) (barnesPoleFinset m : Set ℂ) := by
  have hRe : (barnesLeftCorner m T).re ≤ (barnesRightCorner c T).re := by
    simp [barnesLeftCorner, barnesRightCorner]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hIm : (barnesLeftCorner m T).im ≤ (barnesRightCorner c T).im := by
    simp [barnesLeftCorner, barnesRightCorner]
    linarith
  calc
    RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) =
        sumResiduesIn (barnesJ ξ η)
          (Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) ∩
            {z | meromorphicOrderAt (barnesJ ξ η) z < 0}) :=
      RectangleIntegral'_eq_sumResiduesIn hRe hIm
        (meromorphicOn_barnesJ ξ η hη _)
        (barnesPoles_disjoint_border hc hcξ hT hη)
        (barnesPoleSet_finite hc hcξ hT hη)
        (hasSimplePolesOn_barnesJ hc hcξ hT hη)
    _ = sumResiduesIn (barnesJ ξ η) (barnesPoleFinset m : Set ℂ) := by
      rw [barnesPoleSet_eq hc hcξ hT hη]

/-- Finite-sum form of `rectangleIntegral_barnesJ_eq_sumResiduesIn`. -/
theorem rectangleIntegral_barnesJ_eq_finset_sum
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) =
      ∑ p ∈ barnesPoleFinset m, residue (barnesJ ξ η) p := by
  calc
    RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) =
        sumResiduesIn (barnesJ ξ η) (barnesPoleFinset m : Set ℂ) :=
      rectangleIntegral_barnesJ_eq_sumResiduesIn hc hcξ hT hη
    _ = ∑ p ∈ barnesPoleFinset m, residue (barnesJ ξ η) p := by
      rw [sumResiduesIn,
        tsum_fintype (f := fun p : (barnesPoleFinset m : Set ℂ) => residue (barnesJ ξ η) p),
        ← Finset.sum_coe_sort (barnesPoleFinset m)]
      rfl

end

end RHTower
