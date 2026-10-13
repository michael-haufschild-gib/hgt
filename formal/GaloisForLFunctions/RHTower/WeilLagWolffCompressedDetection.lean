import GaloisForLFunctions.RHTower.WeilLagSingleBaseWolffConfiguration
import GaloisForLFunctions.RHTower.WeilLagCompressedMultiplierCriterion

/-!
# Compressed lags see what single-base lags cannot

For `ℓ > 0` and `0 < Θ ≤ ½` there is a countable, injective, locally finite configuration `ρ_i`
with positive summable weights `c_i` and real parts in `(½, ½ + Θ)`, whose supremum `½ + Θ` is not
attained, such that every lag sample vanishes: `Σ c_i e^{mℓ(ρ_i − ½)} = 0` for all `m ≥ 1`
(`exists_positive_lag_configuration_vanishing_progression`).

The same configuration is detected by the logarithmically compressed lag: with
`H(z) = z / log(2 − z²)`, `Re Σ c_i e^{n H(ρ_i − ½)}` is unbounded above along the integers.
Local finiteness makes `H(ρ − ½)` compressing, so its largest real part is attained, and
`exists_re_tsum_mul_exp_ge` applies (`exists_lag_vanishing_logCompressed_unbounded`).

So the attainment gap of single-base lag sampling comes from the coordinate, not from the zero
configuration: one thin family of a compressed multiplier separates exactly the configurations that
every single-base lag progression misses.
-/

open Complex Filter Real Topology

namespace RHTower

noncomputable section

/-- On a locally finite configuration in `½ < Re ρ ≤ 1`, the multiplier `H(ρ − ½)` is
compressing. -/
theorem logCompressed_compressing_of_locallyFinite {ι : Type*} {ρ : ι → ℂ}
    (hre : ∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re ≤ 1) (hfin : ∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) :
    ∀ ε : ℝ, 0 < ε → {i | ε < (logCompressedMultiplier (ρ i - 1 / 2)).re}.Finite := by
  intro ε hε
  refine (hfin (1 + Real.exp (max 1 (3 / (2 * ε))))).subset fun i hi => ?_
  have hi' : ε < (logCompressedMultiplier (ρ i - 1 / 2)).re := hi
  have hzre : (ρ i - 1 / 2).re = (ρ i).re - 1 / 2 := by simp
  have hzim : (ρ i - 1 / 2).im = (ρ i).im := by simp
  have hx0 : 0 ≤ (ρ i - 1 / 2).re := by rw [hzre]; linarith [(hre i).1]
  have hx : (ρ i - 1 / 2).re ^ 2 ≤ 1 / 4 := by
    rw [hzre]; nlinarith [(hre i).1, (hre i).2]
  have h := abs_im_le_of_lt_re_logCompressedMultiplier hx0 hx hε hi'
  rw [hzim] at h
  exact h

/-- **The Wolff configuration is invisible to the `ℓ`-lag progression and visible to the
logarithmically compressed lag.** -/
theorem exists_lag_vanishing_logCompressed_unbounded {ℓ Θ : ℝ} (hℓ : 0 < ℓ) (hΘ : 0 < Θ)
    (hΘ2 : Θ ≤ 1 / 2) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧
      (∀ m : ℕ, 1 ≤ m →
        HasSum (fun i => (c i : ℂ) * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0) ∧
      ∀ M : ℝ, ∃ n : ℕ,
        M < (∑' i, (c i : ℂ) *
          Complex.exp ((n : ℂ) * logCompressedMultiplier (ρ i - 1 / 2))).re := by
  obtain ⟨ι, hι, ρ, c, hinj, hre, hsup, hfin, hc, hcs, hlag⟩ :=
    exists_positive_lag_configuration_vanishing_progression hℓ hΘ
  refine ⟨ι, hι, ρ, c, hinj, hre, hsup, hfin, hc, hcs, hlag, fun M => ?_⟩
  have hre' : ∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re ≤ 1 := fun i =>
    ⟨(hre i).1, by linarith [(hre i).2]⟩
  have hcomp := logCompressed_compressing_of_locallyFinite hre' hfin
  obtain ⟨i₀, hi₀⟩ := hsup (1 / 2) (by linarith)
  have hpos : ∃ i, 0 < (logCompressedMultiplier (ρ i - 1 / 2)).re := by
    refine ⟨i₀, re_logCompressedMultiplier_pos (by simp; linarith) ?_⟩
    have hzre : (ρ i₀ - 1 / 2).re = (ρ i₀).re - 1 / 2 := by simp
    rw [hzre]; nlinarith [(hre' i₀).1, (hre' i₀).2]
  have hws : Summable fun i => ‖(c i : ℂ)‖ := by
    refine hcs.congr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc i)]
  obtain ⟨M₀, hM₀, κ, hκ, hgrow⟩ :=
    exists_re_tsum_mul_exp_ge (w := fun i => (c i : ℂ)) (fun i => by simpa using hc i) hws hcomp
      hpos
  have hunb : Tendsto (fun n : ℕ => κ * Real.exp ((n : ℝ) * M₀)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hM₀)).const_mul_atTop
      hκ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunb.eventually_gt_atTop M)
  obtain ⟨n, hn, hle⟩ := hgrow N
  exact ⟨n, (hN n hn).trans_le hle⟩

end

end RHTower
