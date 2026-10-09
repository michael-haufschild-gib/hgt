import GaloisForLFunctions.RHTower.BaezDuarteDistanceBurnolLowerBound
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Burnol's lower bound over all critical zeros

Let `d_N` be the Báez-Duarte distance (`bdDistDiscrete`). For every real `c` below the full sum
`∑ 2/|ρ|²` over the distinct zeros `ρ` of `ζ` on the critical line in the upper half-plane,

`c ≤ d_N² log N` for all large `N`,

that is, `liminf d_N² log N ≥ ∑_ρ 2/|ρ|²`.

**Proof.** The sum converges: a critical zero has `|ρ| ≥ |ρ - 1/2|`, and the centered inverse
squares are summable over the Xi divisor. A real number below the sum of a nonnegative summable
family lies below some finite partial sum, and Burnol's bound for finite packets applies.
-/

open Complex Filter Topology

namespace RHTower

/-- The distinct zeros of `ζ` on the critical line in the upper half-plane. -/
def criticalUpperZeros : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im}

theorem criticalUpperZeros_mem_xiSupport {ρ : ℂ} (hρ : ρ ∈ criticalUpperZeros) :
    ρ ∈ (MeromorphicOn.divisor xi Set.univ).support := by
  have hre : 0 < ρ.re := by rw [hρ.2.1]; norm_num
  have h1 : ρ ≠ 1 := by
    intro h; have := hρ.2.1; rw [h] at this; norm_num at this
  exact mem_xi_divisor_support_of_eq_zero ((xi_eq_zero_iff hre h1).mpr hρ.1)

theorem summable_criticalUpperZeros_inv_sq :
    Summable fun ρ : criticalUpperZeros => 2 / ‖(ρ : ℂ)‖ ^ 2 := by
  set ι : criticalUpperZeros → ↥(MeromorphicOn.divisor xi Set.univ).support :=
    fun ρ => ⟨ρ, criticalUpperZeros_mem_xiSupport ρ.2⟩ with hι
  have hinj : Function.Injective ι := by
    intro a b h
    have hval : (a : ℂ) = (b : ℂ) := by
      have := congrArg (fun x : ↥(MeromorphicOn.divisor xi Set.univ).support => (x : ℂ)) h
      simpa [hι] using this
    exact Subtype.ext hval
  have hbase := (xi_zero_multiplicity_centered_inv_sq_summable.comp_injective hinj).mul_left 2
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) hbase
  have hρ := ρ.2
  have hm : (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    have := xi_divisor_pos_on_support ⟨ρ, criticalUpperZeros_mem_xiSupport ρ.2⟩
    exact_mod_cast this
  have hpos : 0 < ‖(ρ : ℂ) - 1 / 2‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have := hρ.2.2
    rw [h] at this
    norm_num at this
  have hnorm : ‖(ρ : ℂ) - 1 / 2‖ ≤ ‖(ρ : ℂ)‖ := by
    have h1 : ‖(ρ : ℂ) - 1 / 2‖ ^ 2 = ((ρ : ℂ).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hρ.2.1]
      ring
    have h2 : ((ρ : ℂ).im) ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg (ρ : ℂ).re]
    nlinarith [norm_nonneg ((ρ : ℂ) - 1 / 2), norm_nonneg (ρ : ℂ)]
  simp only [Function.comp_apply, hι]
  calc 2 / ‖(ρ : ℂ)‖ ^ 2 ≤ 2 / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 := by gcongr
    _ ≤ 2 * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
        rw [mul_div_assoc']
        gcongr
        linarith

/-- **Burnol's bound over all critical zeros.** -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum {c : ℝ}
    (hc : c < ∑' ρ : criticalUpperZeros, 2 / ‖(ρ : ℂ)‖ ^ 2) :
    ∀ᶠ N : ℕ in atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  classical
  have hsum := summable_criticalUpperZeros_inv_sq.hasSum
  have hev : ∀ᶠ s : Finset criticalUpperZeros in atTop,
      c < ∑ ρ ∈ s, 2 / ‖(ρ : ℂ)‖ ^ 2 := hsum.eventually (lt_mem_nhds hc)
  obtain ⟨s, hs⟩ := hev.exists
  set Z : Finset ℂ := s.map (Function.Embedding.subtype _) with hZ
  have hZsum : ∑ ρ ∈ Z, 2 / ‖ρ‖ ^ 2 = ∑ ρ ∈ s, 2 / ‖(ρ : ℂ)‖ ^ 2 := by
    rw [hZ, Finset.sum_map]
    rfl
  refine eventually_le_bdDistDiscrete_sq_mul_log_of_zeros (Z := Z) ?_ (by rw [hZsum]; exact hs)
  intro ρ hρ
  rw [hZ, Finset.mem_map] at hρ
  obtain ⟨σ, -, rfl⟩ := hρ
  exact σ.2

end RHTower
