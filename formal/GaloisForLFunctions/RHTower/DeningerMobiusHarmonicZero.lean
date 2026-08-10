import GaloisForLFunctions.RHTower.DeningerDirichletLimit
import GaloisForLFunctions.RHTower.DeningerInvZetaPole
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# The Möbius harmonic series sums to zero

The Dirichlet series `∑ μ(n) n^{-1-σ}` is `ζ(1+σ)⁻¹`, which tends to zero as `σ ↓ 0` because `ζ`
has a pole at `1`.  It is also the Abel average of the harmonic partial sums, which tends to their
limit by the Abelian theorem.  Uniqueness of limits therefore forces

`∑ μ(n)/n = 0`.

Note this value does *not* follow from the prime number theorem alone: partial summation turns
`A_N → S` into `M(N)/N → S - S = 0` for **any** `S`, so `M(N) = o(N)` is consistent with every
constant.  Only the pole pins it.

* `deningerDirichlet_cast` : the real Dirichlet series is `ζ(1+σ)⁻¹`.
* `deningerHarmonicLimit_eq_zero` : **`∑ μ(n)/n = 0`.**
-/

namespace RHTower

open ArithmeticFunction Filter Topology

noncomputable section

/-- The Dirichlet term in reciprocal-power form. -/
theorem deningerDirichletTerm_eq (σ : ℝ) (n : ℕ) :
    deningerDirichletTerm σ n = ((moebius n : ℤ) : ℝ) / ((n : ℝ) ^ (1 + σ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [deningerDirichletTerm_zero]
    simp
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [deningerDirichletTerm, Real.rpow_add hnr, Real.rpow_one, Real.rpow_neg hnr.le]
    field_simp

/-- **The real Dirichlet series of the Möbius function is the reciprocal of zeta.** -/
theorem deningerDirichlet_cast {σ : ℝ} (hσ : 0 < σ) :
    ((∑' n : ℕ, deningerDirichletTerm σ n : ℝ) : ℂ) = (riemannZeta (1 + (σ : ℂ)))⁻¹ := by
  have hs : (1 : ℝ) < ((1 : ℂ) + (σ : ℂ)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  rw [← LSeries_moebius_eq_inv_riemannZeta hs]
  have hcast := Complex.ofRealCLM.map_tsum (deningerMobiusDirichlet_summable hσ)
  rw [show ((∑' n : ℕ, deningerDirichletTerm σ n : ℝ) : ℂ)
      = Complex.ofRealCLM (∑' n : ℕ, deningerDirichletTerm σ n) from rfl, hcast]
  rw [LSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero]
    simp [deningerDirichletTerm_zero]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), deningerDirichletTerm_eq]
    show ((((moebius n : ℤ) : ℝ) / ((n : ℝ) ^ (1 + σ)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, Complex.ofReal_cpow hnr.le]
    congr 2
    push_cast
    ring

/-- **The Möbius harmonic series sums to zero.** -/
theorem deningerHarmonicLimit_eq_zero : deningerHarmonicLimit = 0 := by
  have habel := deningerHarmonicAbel_tendsto
  have hzeta := deningerInvZetaRay_tendsto_zero
  have hreal : Tendsto (fun σ : ℝ => ∑' n : ℕ, deningerDirichletTerm σ n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcast : Tendsto (fun σ : ℝ => ((∑' n : ℕ, deningerDirichletTerm σ n : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine hzeta.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact (deningerDirichlet_cast hσ).symm
    have hre := (Complex.reCLM.continuous.tendsto (0 : ℂ)).comp hcast
    rw [_root_.map_zero] at hre
    refine hre.congr fun σ => ?_
    simp
  have hmatch : Tendsto (fun σ : ℝ =>
      ∑' m : ℕ, deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hreal.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact deningerDirichlet_eq_abelAverage hσ
  exact tendsto_nhds_unique habel hmatch

end

end RHTower
