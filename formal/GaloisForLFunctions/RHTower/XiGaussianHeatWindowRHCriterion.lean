import GaloisForLFunctions.RHTower.XiGaussianHeatWindowNyquistExclusion

/-!
# RH is nonnegativity of every heat Hankel window on real polynomials

**Theorem** (`riemannHypothesis_iff_forall_heatWindowNonneg`). RH holds if and only if, for every
`K > 0`, the heat Hankel form `H_{K/n}(P, P)` is eventually nonnegative on real polynomials of
degree `≤ n` vanishing at the pole node `−1/4`.

This weakens the hypothesis of `riemannHypothesis_iff_forall_eventually_poleHyperplane_pos` in two
ways: real polynomials in place of complex coefficient vectors, and `≥ 0` in place of `> 0`.
The Hermitian form of the real heat section splits over real and imaginary parts.
-/

open Complex MeasureTheory Filter Topology Set Polynomial Matrix
open scoped Real
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad)

namespace RHTower

noncomputable section

/-- **Real nonnegativity gives Hermitian nonnegativity on the pole hyperplane.** -/
theorem hermQuad_heatMomentSection_nonneg_of_real {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hreal : ∀ P : ℝ[X], P.natDegree ≤ n → P.eval (-1 / 4) = 0 →
      0 ≤ (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re)
    (x : Fin (n + 1) → ℂ) (hx : poleFunctional (n + 1) x = 0) :
    0 ≤ hermQuad (heatMomentSection a (n + 1)) x := by
  have hsplit := hermQuad_map_ofReal_eq_add (leadingMatrix (heatMomentArray a) (n + 1)) x
  change hermQuad (heatMomentSection a (n + 1)) x = hermQuad (heatMomentSection a (n + 1)) _ +
    hermQuad (heatMomentSection a (n + 1)) _ at hsplit
  have hpart : ∀ r : Fin (n + 1) → ℝ, ∑ i : Fin (n + 1), r i * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 →
      0 ≤ hermQuad (heatMomentSection a (n + 1)) (fun i => ((r i : ℝ) : ℂ)) := fun r hr => by
    rw [hermQuad_heatMomentSection ha (Nat.succ_pos n), heatCoeffPoly_ofReal]
    exact hreal _ (natDegree_realCoeffPoly_le r) (by rw [eval_realCoeffPoly]; exact hr)
  have hsum : ∑ i : Fin (n + 1), x i * (-1 / 4 : ℂ) ^ (i : ℕ) = 0 := hx
  have hsum' : ∑ i : Fin (n + 1), x i * (((-1 / 4 : ℝ) ^ (i : ℕ) : ℝ) : ℂ) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hre : ∑ i : Fin (n + 1), (x i).re * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 := by
    have := congrArg Complex.re hsum'
    simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re] using this
  have him : ∑ i : Fin (n + 1), (x i).im * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 := by
    have := congrArg Complex.im hsum'
    simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im] using this
  rw [hsplit]
  exact add_nonneg (hpart _ hre) (hpart _ him)

/-- **RH is nonnegativity of every heat Hankel window on real polynomials.** -/
theorem riemannHypothesis_iff_forall_heatWindowNonneg :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → HeatWindowNonneg K := by
  constructor
  · intro hRH K hK
    filter_upwards [(riemannHypothesis_iff_forall_eventually_poleHyperplane_pos.mp hRH) K hK,
      eventually_gt_atTop 0] with n hn hn0 P hPd hPe
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    set Q := P.map (algebraMap ℝ ℂ) with hQ
    have hQd : Q.natDegree ≤ n := (natDegree_map_le).trans hPd
    have hQe : Q.eval (-1 / 4) = 0 := by
      have e : (-1 / 4 : ℂ) = algebraMap ℝ ℂ (-1 / 4) := by push_cast; ring
      rw [hQ, e, Polynomial.eval_map, Polynomial.eval₂_at_apply, hPe, map_zero]
    by_cases hx0 : (fun i : Fin (n + 1) => Q.coeff i) = 0
    · have hQ0 : Q = 0 := by
        rw [← heatCoeffPoly_coeff_eq hQd, hx0]
        simp [heatCoeffPoly]
      rw [hQ0]
      simp [heatHankel, heatHankelTermAt]
    · have h := hn (K / n) (div_pos hK hn') le_rfl (fun i => Q.coeff i)
        (by rw [poleFunctional_coeff_eq hQd, hQe]) hx0
      rw [hermQuad_heatMomentSection (div_pos hK hn') (Nat.succ_pos n),
        heatCoeffPoly_coeff_eq hQd] at h
      exact h.le
  · intro h
    by_contra hRH
    obtain ⟨K, hK, hev⟩ := exists_eventually_poleHyperplane_neg_of_not_riemannHypothesis hRH
    obtain ⟨n, ⟨x, hx, hneg⟩, hW, hn0⟩ :=
      (hev.and ((h K hK).and (eventually_gt_atTop 0))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have := hermQuad_heatMomentSection_nonneg_of_real (div_pos hK hn') hW x hx
    linarith

end

end RHTower
