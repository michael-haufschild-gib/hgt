import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitCauchy

/-!
# A Gamma monomial is analytic on the right half plane

`Γ` is differentiable off its poles, so on `{Re z > 0}` it is analytic and nonvanishing; integer
powers and finite products keep both properties.  This is what lets the orbit limit of a Gamma
monomial be identified as an analytic function — the first half of the periodicity argument that
pins that limit to `1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gamma s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z fun m => ?_).differentiableWithinAt
    intro hcon
    rw [hcon] at hz
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact hdiff.analyticAt (hopen.mem_nhds hs)

theorem analyticAt_Gamma_shift_zpow {lam : ℂ} (n : ℤ) {s : ℂ} (hs : 0 < (s + lam).re) :
    AnalyticAt ℂ (fun u : ℂ => (Complex.Gamma (u + lam)) ^ n) s := by
  have hne : Complex.Gamma (s + lam) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcon
    rw [hcon] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hshift : AnalyticAt ℂ (fun u : ℂ => u + lam) s := analyticAt_id.add analyticAt_const
  have hbase : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (u + lam)) s := by
    have hc := AnalyticAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u + lam) (x := s)
      (analyticAt_Gamma_of_re_pos hs) hshift
    have hrw : (Complex.Gamma ∘ fun u : ℂ => u + lam) = fun u : ℂ => Complex.Gamma (u + lam) := by
      funext u; rfl
    rwa [hrw] at hc
  rcases n with m | m
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hbase.pow m
  · simp only [zpow_negSucc]
    exact (hbase.pow (m + 1)).inv (pow_ne_zero _ hne)

/-- **A Gamma monomial is analytic wherever every shifted argument has positive real part.** -/
theorem analyticAt_gammaMonomial {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hre : ∀ k, 0 < (s + lam k).re) :
    AnalyticAt ℂ (gammaMonomial lam g) s := by
  have hprod0 : AnalyticAt ℂ (∏ k : Fin r, fun u : ℂ => (Complex.Gamma (u + lam k)) ^ (g k)) s :=
    Finset.analyticAt_prod _ fun k _ => analyticAt_Gamma_shift_zpow (g k) (hre k)
  have hfun : (∏ k : Fin r, fun u : ℂ => (Complex.Gamma (u + lam k)) ^ (g k))
      = gammaMonomial lam g := by
    funext u
    simp [Finset.prod_apply, gammaMonomial]
  rwa [hfun] at hprod0

/-- The monomial is analytic on the half plane where the ladder lives. -/
theorem analyticAt_gammaMonomial_of_gt_sum_abs {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) : AnalyticAt ℂ (gammaMonomial lam g) s :=
  analyticAt_gammaMonomial lam g fun k => re_pos_of_gt_sum_abs lam hs k

end

end GaloisForLFunctions.HTGeometry
