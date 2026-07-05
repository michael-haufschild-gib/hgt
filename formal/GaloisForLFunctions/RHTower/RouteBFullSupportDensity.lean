/-
The certificate carrier's full-support caustic floor: cofinally many on-line heights where
`dirichletPoly N` exceeds a fixed floor `t₀`.

The full-support small-ball law `fullCarrier_smallball_caustic` bounds the Steinhaus small-ball of the
whole carrier `∑_{n≤N} aₙ Xₙ` by the explicit four-phase constant; the deterministic density machine
(`floorFailure_timeDensity_le_unconditional`) transfers that ensemble bound to the Cesàro upper time
density of the floor-failure set, and the density-to-cofinality bridge turns a density `< 1` into a
cofinal set of floor-holding heights. On the critical line with `aₙ = n^{-1/2}`, this is the
deterministic on-line center-floor set the movable-window ball-floor machinery (`DpolyBallFloor`)
consumes.
-/
import GaloisForLFunctions.RHTower.RouteBFullSupportMeasure
import GaloisForLFunctions.RHTower.FloorFailureCaustic
import GaloisForLFunctions.RHTower.FloorFailureCofinal
import GaloisForLFunctions.RHTower.DpolyBallFloor

open MeasureTheory intervalIntegral Filter Topology Complex Finset Metric
open scoped Classical

namespace RHTower
open Weyl SteinhausModel Sublevel

/-- **Full-support caustic floor-failure density bound.** The full carrier `dpoly a (Icc 1 N)` has
Cesàro floor-failure density at most `(2π)⁻⁴·fourPhaseConst`, supplied by the full-support caustic
small-ball law with four dominant primes in `(N/2, N]`. -/
theorem floorFailure_timeDensity_le_caustic_fullSupport {N : ℕ} (a : ℕ → ℝ)
    {t₀ σ0 sstar : ℝ} {J : ℕ}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4 : ℂ) ≠ 0) (hB : (a p3 : ℂ) ≠ 0) (hC : (a p2 : ℂ) ≠ 0) (hD : (a p1 : ℂ) ≠ 0)
    (hρB : ‖(a p3 : ℂ)‖ < ‖(a p4 : ℂ)‖) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ‖(a p4 : ℂ)‖ + t₀)
        / ((‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) * ‖(a p3 : ℂ)‖))
        ≤ σ0 * Sublevel.causticKappa ‖(a p4 : ℂ)‖ ‖(a p3 : ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1 : ℂ)‖)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a (Finset.Icc 1 N) τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) :
    cesaroUpperDensity fail
      ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
          * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ)
              t₀ σ0 sstar J).toReal := by
  have hs1 : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set B : ENNReal := ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
      * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ) t₀ σ0 sstar J with hBdef
  have hBtop : B ≠ ⊤ := by
    rw [hBdef]
    apply ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    unfold Sublevel.fourPhaseConst
    finiteness
  have hmodel : steinhausMeasure {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t₀} ≤ B :=
    SteinhausModel.fullCarrier_smallball_caustic a hp1P hp2P hp3P hp4P hp1I hp2I hp3I hp4I
      hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34 hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0 hss hss2
  have ht0R : t₀ ≤ ∑ n ∈ Finset.Icc 1 N, |a n| := by
    have hnp4 : ‖(a p4 : ℂ)‖ = |a p4| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : t₀ ≤ |a p4| := by
      rw [← hnp4]; nlinarith [hr2, norm_nonneg (a p3 : ℂ), hr0.le]
    have h2 : |a p4| ≤ ∑ n ∈ Finset.Icc 1 N, |a n| :=
      Finset.single_le_sum (f := fun n => |a n|) (fun n _ => abs_nonneg _) hp4I
    linarith
  exact floorFailure_timeDensity_le_unconditional a (Finset.Icc 1 N) hs1 t₀ (le_of_lt hr0) ht0R
    B hBtop hmodel fail hfail0 hfle1 hfsupp hfail_int


/-- **Full-support caustic cofinal floor.** If the explicit four-phase constant is `< 1`, then the
full carrier `dpoly a (Icc 1 N)` exceeds `t₀` at cofinally many heights: above every bound there is a
height where the full-support carrier's floor holds. Composes the full-support caustic density bound
with the density-to-cofinality bridge. -/
theorem good_height_cofinal_of_caustic_fullSupport {N : ℕ} (a : ℕ → ℝ)
    {t₀ σ0 sstar : ℝ} {J : ℕ}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4 : ℂ) ≠ 0) (hB : (a p3 : ℂ) ≠ 0) (hC : (a p2 : ℂ) ≠ 0) (hD : (a p1 : ℂ) ≠ 0)
    (hρB : ‖(a p3 : ℂ)‖ < ‖(a p4 : ℂ)‖) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ‖(a p4 : ℂ)‖ + t₀)
        / ((‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) * ‖(a p3 : ℂ)‖))
        ≤ σ0 * Sublevel.causticKappa ‖(a p4 : ℂ)‖ ‖(a p3 : ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1 : ℂ)‖)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a (Finset.Icc 1 N) τ‖ → fail τ = 0)
    (hfailfull : ∀ τ, ‖dpoly a (Finset.Icc 1 N) τ‖ ≤ t₀ → fail τ = 1)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hnum : (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
        * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ)
            t₀ σ0 sstar J).toReal < 1) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dpoly a (Finset.Icc 1 N) τ‖ :=
  good_height_cofinal_of_density_lt_one a (Finset.Icc 1 N) t₀ fail hfail_int hfailfull
    (lt_of_le_of_lt
      (floorFailure_timeDensity_le_caustic_fullSupport a hp1P hp2P hp3P hp4P hp1I hp2I hp3I hp4I
        hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34 hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0 hss hss2
        fail hfail0 hfle1 hfsupp hfail_int)
      hnum)

/-- **Cofinal on-line floor for the certificate carrier.** With coefficients `aₙ = n^{-1/2}` and four
dominant primes in `(N/2, N]` in strict caustic position (four-phase constant `< 1`), the certificate
Dirichlet part `dirichletPoly N` exceeds `t₀` at cofinally many heights on the critical line. This is
the deterministic on-line center-floor set the movable-window ball-floor machinery consumes. -/
theorem dirichletPoly_floor_cofinal_of_caustic {N : ℕ}
    {t₀ σ0 sstar : ℝ} {J : ℕ}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hρB : ((p3 : ℝ) ^ (-(1/2:ℝ)) : ℝ) < ((p4 : ℝ) ^ (-(1/2:ℝ)) : ℝ)) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ((p4 : ℝ) ^ (-(1/2:ℝ))) - ((p3 : ℝ) ^ (-(1/2:ℝ)))) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((((p4:ℝ)^(-(1/2:ℝ))) + ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2
        - (((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2) / 3)
    (hJ : ((((p4:ℝ)^(-(1/2:ℝ))) + ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2
        - (((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ((p4:ℝ)^(-(1/2:ℝ))) + t₀)
        / ((((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) * ((p3:ℝ)^(-(1/2:ℝ)))))
        ≤ σ0 * Sublevel.causticKappa ((p4:ℝ)^(-(1/2:ℝ))) ((p3:ℝ)^(-(1/2:ℝ))))
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ((p1:ℝ)^(-(1/2:ℝ))))
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly (fun n => (n:ℝ)^(-(1/2:ℝ))) (Finset.Icc 1 N) τ‖ → fail τ = 0)
    (hfailfull : ∀ τ, ‖dpoly (fun n => (n:ℝ)^(-(1/2:ℝ))) (Finset.Icc 1 N) τ‖ ≤ t₀ → fail τ = 1)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hnum : (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
        * Sublevel.fourPhaseConst ((((p4:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) ((((p3:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ)
            ((((p2:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) ((((p1:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) t₀ σ0 sstar J).toReal < 1) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dirichletPoly N (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  have hane : ∀ p : ℕ, p ∈ Finset.Icc 1 N → ((((p:ℝ)^(-(1/2:ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    intro p hp
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    exact_mod_cast ne_of_gt (Real.rpow_pos_of_pos hppos _)
  have hnormeq : ∀ p : ℕ, p ∈ Finset.Icc 1 N →
      ‖(((p:ℝ)^(-(1/2:ℝ)) : ℝ) : ℂ)‖ = (p:ℝ)^(-(1/2:ℝ)) := by
    intro p hp
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hppos _)]
  have hcof := good_height_cofinal_of_caustic_fullSupport (fun n => (n:ℝ)^(-(1/2:ℝ)))
    hp1P hp2P hp3P hp4P hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34
    (hane p4 hp4I) (hane p3 hp3I) (hane p2 hp2I) (hane p1 hp1I)
    (by rw [hnormeq p3 hp3I, hnormeq p4 hp4I]; exact hρB) hr0
    (by rw [hnormeq p4 hp4I, hnormeq p3 hp3I]; exact hr2) hσ0
    (by rw [hnormeq p4 hp4I, hnormeq p3 hp3I]; exact hσ0G)
    (by rw [hnormeq p4 hp4I, hnormeq p3 hp3I]; exact hJ)
    (by rw [hnormeq p4 hp4I, hnormeq p3 hp3I]; exact hHσ0) hss
    (by rw [hnormeq p1 hp1I]; exact hss2)
    fail hfail0 hfle1 hfsupp hfailfull hfail_int
    hnum
  intro M
  obtain ⟨τ, hτM, hτ⟩ := hcof M
  refine ⟨τ, hτM, ?_⟩
  rw [dirichletPoly_line_eq]
  exact hτ

/-- **Cofinal circle-gate floors from the caustic geometry.** Combining the full-support caustic
cofinal on-line floor for `dirichletPoly N` with the movable-window ball-Lipschitz spreading: under the
caustic numeral `< 1`, the ball-variation budget to real part `½ − R`, and the reflected-χ budget on
each window ball, the certificate floor `CarrierFloorOn` holds on BOTH the annulus charts and the two
boundary circles at cofinally many heights — the deterministic pair the circle-data pinning RH gate
consumes. -/
theorem windowFloor_cofinal_of_caustic {N : ℕ}
    {t₀ t₁ ε σ0 sstar r₀ R : ℝ} {J : ℕ}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hρB : ((p3 : ℝ) ^ (-(1/2:ℝ)) : ℝ) < ((p4 : ℝ) ^ (-(1/2:ℝ)) : ℝ)) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ((p4 : ℝ) ^ (-(1/2:ℝ))) - ((p3 : ℝ) ^ (-(1/2:ℝ)))) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((((p4:ℝ)^(-(1/2:ℝ))) + ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2
        - (((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2) / 3)
    (hJ : ((((p4:ℝ)^(-(1/2:ℝ))) + ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2
        - (((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ((p4:ℝ)^(-(1/2:ℝ))) + t₀)
        / ((((p4:ℝ)^(-(1/2:ℝ))) - ((p3:ℝ)^(-(1/2:ℝ)))) * ((p3:ℝ)^(-(1/2:ℝ)))))
        ≤ σ0 * Sublevel.causticKappa ((p4:ℝ)^(-(1/2:ℝ))) ((p3:ℝ)^(-(1/2:ℝ))))
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ((p1:ℝ)^(-(1/2:ℝ))))
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly (fun n => (n:ℝ)^(-(1/2:ℝ))) (Finset.Icc 1 N) τ‖ → fail τ = 0)
    (hfailfull : ∀ τ, ‖dpoly (fun n => (n:ℝ)^(-(1/2:ℝ))) (Finset.Icc 1 N) τ‖ ≤ t₀ → fail τ = 1)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hnum : (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
        * Sublevel.fourPhaseConst ((((p4:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) ((((p3:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ)
            ((((p2:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) ((((p1:ℝ)^(-(1/2:ℝ)):ℝ)) : ℂ) t₀ σ0 sstar J).toReal < 1)
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1/2 - R))) * R ≤ t₀ - t₁)
    (hrefl : ∀ τ : ℝ, ∀ z ∈ closedBall (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    ∀ M : ℝ, ∃ τ, M < τ ∧
      CarrierFloorOn (chartRA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R
        ∪ chartLA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R) N ε ∧
      CarrierFloorOn (Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀
        ∪ Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R) N ε :=
  window_floor_cofinal_of_line_cofinal N hR hr₀R hbudget
    (by
      intro M
      obtain ⟨τ, hτM, hτ⟩ := dirichletPoly_floor_cofinal_of_caustic hp1P hp2P hp3P hp4P
        hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34 hρB hr0 hr2 hσ0 hσ0G hJ hHσ0
        hss hss2 fail hfail0 hfle1 hfsupp hfailfull hfail_int hnum M
      exact ⟨τ, hτM, by rwa [dirichletPoly_line_eq] at hτ⟩)
    hrefl

end RHTower

