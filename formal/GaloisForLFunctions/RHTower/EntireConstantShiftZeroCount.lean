import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireLocalDivisor
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRouche
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

/-!
# Zero count of a small constant shift

Around a zero of order `n` of an entire function `f` there are arbitrarily small discs such that,
for every sufficiently small constant `w`, the zeros of `f + w` in the disc have total
multiplicity exactly `n` (Rouché's theorem via the argument principle).
-/

open Complex Filter Topology Set Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Rouché count for a small constant shift.** Around a zero of order `n` of an entire function
there are arbitrarily small discs such that, for every sufficiently small constant `w`, the shifted
function `f + w` has zeros in the disc of total multiplicity exactly `n`. -/
theorem exists_zeroCount_add_const {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {n : ℕ}
    (hord : analyticOrderAt f c = (n : ℕ∞)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R δ₀ : ℝ, 0 < R ∧ R < ρ ∧ 0 < δ₀ ∧ ∀ w : ℂ, ‖w‖ < δ₀ →
      ∃ Z : Finset ℂ, (∀ z ∈ Z, z ∈ ball c R) ∧
        (∀ z ∈ ball c R, f z + w = 0 ↔ z ∈ Z) ∧
        (∀ z ∈ Z, 1 ≤ zeroMult (fun u => f u + w) z) ∧
        ∑ z ∈ Z, zeroMult (fun u => f u + w) z = n := by
  have hfin : analyticOrderAt f c ≠ ⊤ := by rw [hord]; exact ENat.coe_ne_top n
  obtain ⟨R, hR, hRρ, hzero, hint⟩ :=
    RiemannGaussian.AnalyticAt.exists_lt_circleIntegral_logDeriv_eq_order (hf.analyticAt c) hfin hρ
  have hnat : analyticOrderNatAt f c = n := by
    rw [analyticOrderNatAt, hord, ENat.toNat_coe]
  rw [hnat] at hint
  have hsph : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz =>
    hzero z (sphere_subset_closedBall hz) (by
      intro h; rw [h, mem_sphere, dist_self] at hz; linarith)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) (hf.continuous.norm.continuousOn)
  refine ⟨R, ‖f z₀‖, hR, hRρ, norm_pos_iff.mpr (hsph z₀ hz₀), fun w hw => ?_⟩
  set g : ℂ → ℂ := fun u => f u + w with hg
  have hgd : Differentiable ℂ g := hf.add_const w
  have hbd : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖ := fun z hz => by
    simp only [hg, add_sub_cancel_left]
    exact lt_of_lt_of_le hw (hmin hz)
  have heq := RiemannGaussian.circleIntegral_logDeriv_eq_of_norm_sub_lt hf hgd hR.le hbd
  have hgne := (RiemannGaussian.ne_zero_on_sphere_of_norm_sub_lt hbd).2
  obtain ⟨Z, hZball, hZiff, hZint⟩ := exists_zeroSet_circleIntegral_logDeriv hR
    (lt_add_one R) isOpen_univ (subset_univ _) hgd.differentiableOn hgne
  have hsum : ∑ z ∈ Z, zeroMult g z = n := by
    have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    rw [heq, hint] at hZint
    have : ((∑ z ∈ Z, zeroMult g z : ℕ) : ℂ) = (n : ℂ) := by
      push_cast
      apply mul_left_cancel₀ h2
      rw [← hZint]; push_cast; ring
    exact_mod_cast this
  have hz1 : ∃ z₁, g z₁ ≠ 0 := ⟨c + R, hgne _ (by simp [abs_of_pos hR])⟩
  obtain ⟨z₁, hz₁⟩ := hz1
  refine ⟨Z, hZball, hZiff, fun z hz => ?_, hsum⟩
  have hgz : g z = 0 := (hZiff z (hZball z hz)).mpr hz
  have htop := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hgd hz₁ z
  have hne0 : analyticOrderAt g z ≠ 0 := by
    intro h; exact ((hgd.analyticAt z).analyticOrderAt_eq_zero.mp h) hgz
  rw [zeroMult]
  rcases ENat.ne_top_iff_exists.mp htop with ⟨m, hm⟩
  rw [← hm] at hne0 ⊢
  simp only [ENat.toNat_coe]
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)

end RHTower
