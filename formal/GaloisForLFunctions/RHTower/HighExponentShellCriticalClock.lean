import GaloisForLFunctions.RHTower.HighExponentShellZeroFree
import GaloisForLFunctions.HTGeometry.CriticalClockSourceUniversality

/-!
# The critical clock of a high-exponent shell

The shell source `S_m(σ) = ∑ a_m(n) n^{-σ}` of `HighExponentShellZeroFree` is a nonnegative
Mellin source with a simple pole at `σ = 1` whose residue is the positive real number
`H_m(1) = ζ(m+1)⁻¹ - ζ(m)⁻¹`.  Feeding this into the source-independent critical clock law of
`HTGeometry.CriticalClockSourceUniversality` gives:

* `RHTower.shellMellin_eq_tsum` — the analytic source is the arithmetic Dirichlet series of the
  shell indicator on `re s > 1`;
* `RHTower.shellMellin_nonneg` — the source is nonnegative;
* `RHTower.tendsto_shellMellin_residue` — `(σ-1)S_m(σ) → H_m(1) > 0` as `σ ↓ 1`;
* `RHTower.tendsto_shellCriticalClockLaplace` — hence the clock `(σ-1)·log n` of every shell with
  `m ≥ 12` has the unit-rate exponential Laplace transform `1/(1+u)` in the critical limit.

Since the shell supports are pairwise disjoint, this exhibits infinitely many mutually orthogonal
positive arithmetic sources with one and the same critical clock.
-/

noncomputable section

namespace RHTower

open Complex Filter
open scoped Topology LSeries.notation

/-- The real Mellin source of the high-exponent shell, `S_m(σ) = ζ(σ)H_m(σ)`. -/
def shellMellin (m : ℕ) (σ : ℝ) : ℝ := (riemannZeta (σ : ℂ) * shellMultiplier m (σ : ℂ)).re

/-- On `σ > 1` the analytic shell source is the arithmetic Dirichlet series of the shell
indicator. -/
theorem shellMellin_eq_tsum {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    shellMellin m σ = ∑' n : ℕ, (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ := by
  have h1 : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
  have hL := LSeries_shellIndicator hm h1
  have hcast : ((∑' n : ℕ, (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ : ℝ) : ℂ)
      = LSeries ↗(shellIndicator m) (σ : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.ofReal_natCast, div_eq_mul_inv]
      norm_num
  rw [shellMellin, ← hL, ← hcast, Complex.ofReal_re]

/-- The shell source is nonnegative on its half-plane of convergence. -/
theorem shellMellin_nonneg {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) : 0 ≤ shellMellin m σ := by
  rw [shellMellin_eq_tsum hm hσ]
  refine tsum_nonneg fun n => ?_
  have hInd : (0 : ℝ) ≤ (shellIndicator m n : ℝ) := by
    rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
  have hpow : (0 : ℝ) ≤ ((((n : ℝ)) ^ σ)⁻¹) := by positivity
  exact mul_nonneg hInd hpow

/-- The residue of the shell source at `σ = 1` is a positive real number. -/
theorem shellResidue_pos {m : ℕ} (hm : 2 ≤ m) : 0 < (shellMultiplier m 1).re := by
  obtain ⟨r, hr, hEq⟩ := shellMultiplier_one_eq_ofReal_pos hm
  rw [hEq, Complex.ofReal_re]
  exact hr

private theorem tendsto_ofReal_nhdsWithin_one :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
  have h : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt).tendsto
  rw [Complex.ofReal_one] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Simple pole of the shell source.**  As `σ ↓ 1` the rescaled shell source converges to the
positive shell residue `H_m(1)`. -/
theorem tendsto_shellMellin_residue {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun σ : ℝ => (σ - 1) * shellMellin m σ) (𝓝[>] 1)
      (𝓝 ((shellMultiplier m 1).re)) := by
  have hhalf : (1 : ℝ) / 2 < ((1 : ℂ)).re := by norm_num
  have hHcont : Tendsto (fun σ : ℝ => shellMultiplier m (σ : ℂ)) (𝓝[>] 1)
      (𝓝 (shellMultiplier m 1)) :=
    ((analyticAt_shellMultiplier hm hhalf).continuousAt).tendsto.comp
      tendsto_ofReal_nhdsWithin_one
  have hne : ∀ᶠ σ : ℝ in 𝓝[>] 1, (σ : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hre : σ = 1 := by
      have := congrArg Complex.re h
      simpa using this
    rw [hre] at hσ
    exact lt_irrefl 1 (Set.mem_Ioi.mp hσ)
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_ofReal_nhdsWithin_one hne
  have hζ : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hmap
  have hprod : Tendsto
      (fun σ : ℝ => (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) * shellMultiplier m (σ : ℂ))
      (𝓝[>] 1) (𝓝 (1 * shellMultiplier m 1)) := hζ.mul hHcont
  have hre : Tendsto
      (fun σ : ℝ => ((((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) * shellMultiplier m (σ : ℂ)).re)
      (𝓝[>] 1) (𝓝 ((1 * shellMultiplier m 1).re)) :=
    (Complex.continuous_re.continuousAt).tendsto.comp hprod
  rw [one_mul] at hre
  refine hre.congr fun σ => ?_
  rw [shellMellin, show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring, mul_assoc]
  simp [Complex.mul_re]

/-- **Every high-exponent shell has the unit-rate exponential critical clock.**  For `m ≥ 12`
the clock Laplace transform of the shell source converges to `1/(1+u)` as `σ ↓ 1`: the shell
clock `(σ-1)·log n` becomes a unit-rate exponential.  The shell supports being pairwise disjoint,
this produces infinitely many mutually orthogonal positive sources with one common critical
clock. -/
theorem tendsto_shellCriticalClockLaplace {m : ℕ} (hm : 12 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (GaloisForLFunctions.HTGeometry.criticalClockLaplace (shellMellin m) u)
      (𝓝[>] 1) (𝓝 (1 / (1 + u))) :=
  GaloisForLFunctions.HTGeometry.tendsto_criticalClockLaplace_of_simplePole
    (ne_of_gt (shellResidue_pos (by omega))) (tendsto_shellMellin_residue hm) hu

end RHTower
