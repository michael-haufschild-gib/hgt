import GaloisForLFunctions.HTGeometry.MeromorphicPlaneSquareRoot
import GaloisForLFunctions.HTGeometry.AnalyticBallZeroSet
import GaloisForLFunctions.RHTower.RootExistence

/-!
# Odd divisors witness nonsquare entire functions

An entire function nonzero at the origin has a global meromorphic square root
exactly when all zero orders are even. The existing analytic root-existence
construction supplies the converse needed here. An odd-order zero also detects
nonsquareness after multiplication by any entire function nonzero there.
-/

open Complex Filter Topology Metric
namespace GaloisForLFunctions.HTGeometry

/-- A nonsquare entire function nonzero at the origin has an odd-order zero. -/
theorem exists_odd_zero_of_not_isSquare_plane {f : ℂ → ℂ}
    (hd : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hns : ¬ IsSquare (ofMeromorphic f (fun z => (hd.analyticAt z).meromorphicAt))) :
    ∃ z : ℂ, f z = 0 ∧ Odd (analyticOrderAt f z).toNat := by
  by_contra hn
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hd.analyticAt z
  have hfinite (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
    intro ht
    have he : f = (fun _ => 0) := han.eq_of_eventuallyEq
      (fun _ _ => analyticAt_const) (analyticOrderAt_eq_top.mp ht)
    exact hf0 (congrFun he 0)
  have hloc (R : ℕ) :
      {s ∈ Set.univ ∩ ball (0 : ℂ) ((R : ℝ) + 1) | f s = 0}.Finite := by
    have hb := _root_.HTGeometry.finite_zeros_of_analyticOnNhd_closedBall
      (fun z _ => hd.analyticAt z) (mem_ball_self (by positivity : (0 : ℝ) < (R : ℝ) + 1)) hf0
    exact hb.subset (fun z hz => ⟨hz.1.2, hz.2⟩)
  have hdvd (z : ℂ) (_ : z ∈ Set.univ) (hz : f z = 0) :
      (2 : ℕ∞) ∣ analyticOrderAt f z := by
    have he : Even (analyticOrderAt f z).toNat := by
      by_contra hne
      exact hn ⟨z, hz, Nat.not_even_iff_odd.mp hne⟩
    obtain ⟨k, hk⟩ := he
    rw [← ENat.coe_toNat (hfinite z)]
    refine ⟨(k : ℕ∞), ?_⟩
    norm_cast
    omega
  obtain ⟨g, hgan, hsq⟩ := (RHTower.exists_root_iff_orders_dvd
    (by norm_num : 0 < (2 : ℕ)) isOpen_univ (convex_univ : Convex ℝ (Set.univ : Set ℂ))
    (Set.mem_univ 0) han hf0 hloc).mpr hdvd
  apply hns
  refine ⟨ofMeromorphic g (fun z => (hgan z (Set.mem_univ z)).meromorphicAt), ?_⟩
  rw [ofMeromorphic_mul]
  apply (ofMeromorphic_eq_iff _ _).mpr
  intro z
  exact Filter.Eventually.of_forall (fun w => by simpa [pow_two] using (hsq w (Set.mem_univ w)).symm)

/-- A factor with odd zero order remains nonsquare after multiplication by a unit there. -/
theorem not_isSquare_plane_mul_of_odd_order {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {z : ℂ}
    (hodd : Odd (analyticOrderAt f z).toNat) (hg0 : g z ≠ 0) :
    ¬ IsSquare (ofMeromorphic f (fun z => (hf.analyticAt z).meromorphicAt) *
      ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt)) := by
  intro hs
  obtain ⟨u, hud, hsq⟩ := entire_sqrt_of_isSquare_plane (hf.mul hg) hs
  have hord : analyticOrderAt (fun w => u w ^ 2) z = analyticOrderAt f z := by
    rw [show (fun w => u w ^ 2) = f * g from funext hsq,
      analyticOrderAt_mul (hf.analyticAt z) (hg.analyticAt z),
      (hg.analyticAt z).analyticOrderAt_eq_zero.mpr hg0, add_zero]
  have heven : Even (analyticOrderAt f z).toNat := by
    rw [← hord, show (fun w => u w ^ 2) = u ^ (2 : ℕ) by rfl,
      analyticOrderAt_pow (hud.analyticAt z)]
    rw [show (2 • analyticOrderAt u z).toNat = 2 * (analyticOrderAt u z).toNat by
      rw [nsmul_eq_mul, ENat.toNat_mul]
      norm_num]
    exact even_two.mul_right _
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end GaloisForLFunctions.HTGeometry
