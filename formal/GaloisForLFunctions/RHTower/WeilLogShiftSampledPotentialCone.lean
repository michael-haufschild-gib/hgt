import GaloisForLFunctions.RHTower.WeilLogShiftCauchyPotentialCone

/-!
# Countable sampled convergence recovers the log-shift potential cone

With summable excess, convergent potential samples covering the logarithmic
blocks and a common lower bound recover Cauchy control. For log-shift positivity,
convergence only at `floor(exp j)+1` suffices when the integer-log potential
inequalities hold. Origin convergence and uniform whole-panel convergence follow.
-/

namespace RHTower

open WeilExcess

private theorem excess_potential_control {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    (Summable fun n : ℕ => deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ∧
    kernelPotential (deviationExcess lam) y ≤ 2 * riemannAutocorr 0 * ∑' n, deviationExcess lam n := by
  have hnn (n : ℕ) : 0 ≤ deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) :=
    mul_nonneg (deviationExcess_nonneg _ _)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))
  have hterm (n : ℕ) : deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) ≤
      deviationExcess lam n * (2 * riemannAutocorr 0) := by
    apply mul_le_mul_of_nonneg_left _ (deviationExcess_nonneg _ _)
    linarith only [riemannAutocorr_le_zero (y + Real.log n),
      riemannAutocorr_le_zero (y - Real.log n)]
  have hs := Summable.of_nonneg_of_le hnn hterm (hexc.mul_right _)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, deviationExcess lam n * (2 * riemannAutocorr 0) :=
      hs.tsum_le_tsum hterm (hexc.mul_right _)
    _ = _ := by rw [tsum_mul_right]; ring

private theorem deficit_potential_control_of_sample {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (y : ℝ)
    (hs : Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) :
    (Summable fun n : ℕ => deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ∧
    kernelPotential (deviationDeficit lam) y ≤
      2 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) - deviationPotential lam y := by
  obtain ⟨hsE, hE⟩ := excess_potential_control hexc y
  have hdiff (n : ℕ) : deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) -
      weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) =
      deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
    rw [weilDeviation_eq_sub lam n]
    ring
  have hsV := (hsE.sub hs).congr hdiff
  have hid : kernelPotential (deviationExcess lam) y - deviationPotential lam y =
      kernelPotential (deviationDeficit lam) y := by
    change (∑' n, deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) -
      (∑' n, weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) = _
    rw [← hsE.tsum_sub hs]
    exact tsum_congr hdiff
  refine ⟨hsV, ?_⟩
  rw [← hid]
  exact sub_le_sub_right hE _

private theorem exists_kernel_lower_bound_on_radius (R : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z : ℝ, |z| ≤ R → κ ≤ riemannAutocorr z := by
  obtain ⟨z, _, hmin⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith only [abs_nonneg R]))
    continuous_riemannAutocorr.continuousOn
  refine ⟨riemannAutocorr z, riemannAutocorr_pos z, fun t ht => ?_⟩
  exact hmin (Set.mem_Icc.mpr (abs_le.mp (ht.trans (le_abs_self R))))

/-- Convergent potential samples covering the logarithmic blocks within any fixed
radius, with a common lower bound, control every deficit block. The centers are real shifts. -/
theorem exists_deficit_logBlock_bound_of_potential_cover {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (y : ℕ → ℝ) {R : ℝ} (hcover : ∀ j n : ℕ, ⌊Real.log n⌋₊ = j → |y j - Real.log n| ≤ R)
    (hsample : ∀ j : ℕ, Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (y j + Real.log n) + riemannAutocorr (y j - Real.log n)))
    {b : ℝ} (hpotential : ∀ j : ℕ, b ≤ deviationPotential lam (y j)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ∀ F : Finset ℕ,
      (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, deviationDeficit lam n ≤ B := by
  let S := 2 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) - b
  have hcontrol (j : ℕ) :
      (Summable fun n : ℕ => deviationDeficit lam n *
        (riemannAutocorr (y j + Real.log n) + riemannAutocorr (y j - Real.log n))) ∧
      kernelPotential (deviationDeficit lam) (y j) ≤ S := by
    obtain ⟨hsV, hV⟩ := deficit_potential_control_of_sample hexc (y j) (hsample j)
    refine ⟨hsV, ?_⟩
    have hp := hpotential j
    dsimp only [S]
    linarith only [hV, hp]
  have hnn (y : ℝ) (n : ℕ) : 0 ≤ deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) :=
    mul_nonneg (deviationDeficit_nonneg _ _)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))
  have hS : 0 ≤ S := (tsum_nonneg (hnn (y 0))).trans (hcontrol 0).2
  obtain ⟨κ, hκ, hκK⟩ := exists_kernel_lower_bound_on_radius R
  refine ⟨S / κ, div_nonneg hS hκ.le, fun j F hF => ?_⟩
  obtain ⟨hsV, hV⟩ := hcontrol j
  have hlocal : κ * ∑ n ∈ F, deviationDeficit lam n ≤
      kernelPotential (deviationDeficit lam) (y j) := by
    calc
      _ = ∑ n ∈ F, κ * deviationDeficit lam n := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ F, deviationDeficit lam n *
          (riemannAutocorr (y j + Real.log n) +
            riemannAutocorr (y j - Real.log n)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hk := hκK (y j - Real.log n) (hcover j n (hF n hn))
        have hp : κ ≤ riemannAutocorr (y j + Real.log n) +
            riemannAutocorr (y j - Real.log n) := by
          linarith only [hk, riemannAutocorr_nonneg (y j + Real.log n)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (deviationDeficit_nonneg lam n)
      _ ≤ _ := hsV.sum_le_tsum F (fun n _ => hnn (y j) n)
  apply (le_div_iff₀ hκ).mpr
  simpa only [mul_comm] using hlocal.trans hV

/-- Summable excess and convergent covering samples bounded below recover Cauchy
control of absolute deviation. No comparison with the origin is needed. -/
theorem exists_cauchyBounded_absDeviation_of_potential_cover {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (y : ℕ → ℝ) {R : ℝ} (hcover : ∀ j n : ℕ, ⌊Real.log n⌋₊ = j → |y j - Real.log n| ≤ R)
    (hsample : ∀ j : ℕ, Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (y j + Real.log n) + riemannAutocorr (y j - Real.log n)))
    {b : ℝ} (hpotential : ∀ j : ℕ, b ≤ deviationPotential lam (y j)) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (fun n => |weilDeviation lam n|) D := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_deficit_logBlock_bound_of_potential_cover hexc y hcover hsample hpotential
  let E := ∑' n, deviationExcess lam n
  have hE0 : 0 ≤ E := tsum_nonneg fun n => deviationExcess_nonneg lam n
  apply exists_cauchyBounded_of_logBlock (fun n => abs_nonneg (weilDeviation lam n))
    (by rw [weilDeviation_zero, abs_zero]) (add_nonneg hE0 hB0)
  intro j F hF
  have ha (n : ℕ) : |weilDeviation lam n| ≤ deviationExcess lam n + deviationDeficit lam n := by
    rw [weilDeviation_eq_sub lam n]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (deviationExcess_nonneg _ _),
      abs_of_nonneg (deviationDeficit_nonneg _ _)])
  calc
    _ ≤ ∑ n ∈ F, (deviationExcess lam n + deviationDeficit lam n) :=
      Finset.sum_le_sum fun n _ => ha n
    _ = (∑ n ∈ F, deviationExcess lam n) + ∑ n ∈ F, deviationDeficit lam n :=
      Finset.sum_add_distrib
    _ ≤ E + B := add_le_add (hexc.sum_le_tsum F (fun n _ => deviationExcess_nonneg lam n)) (hB j F hF)

/-- Convergence and lower bounds at the integer-log samples control every deficit
block. No growth bound or convergence at the origin is assumed. -/
theorem exists_deficit_logBlock_bound_of_sampled_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (hsample : ∀ m : ℕ, 2 ≤ m → Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (Real.log m + Real.log n) + riemannAutocorr (Real.log m - Real.log n)))
    (hpotential : ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ∀ F : Finset ℕ,
      (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, deviationDeficit lam n ≤ B := by
  exact exists_deficit_logBlock_bound_of_potential_cover hexc
    (fun j => Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ)) integer_log_probe_covers_block
    (fun j => hsample _ (integer_log_probe_bounds j).1)
    (fun j => hpotential _ (integer_log_probe_bounds j).1)

/-- Countable sampled convergence and potential inequalities recover Cauchy control
of the absolute deviation from summable excess. -/
theorem exists_cauchyBounded_absDeviation_of_sampled_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (hsample : ∀ m : ℕ, 2 ≤ m → Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (Real.log m + Real.log n) + riemannAutocorr (Real.log m - Real.log n)))
    (hpotential : ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m)) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (fun n => |weilDeviation lam n|) D := by
  exact exists_cauchyBounded_absDeviation_of_potential_cover hexc
    (fun j => Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ)) integer_log_probe_covers_block
    (fun j => hsample _ (integer_log_probe_bounds j).1)
    (fun j => hpotential _ (integer_log_probe_bounds j).1)

/-- On the summable-excess domain, asymptotic positivity is equivalent to convergent
integer-log samples satisfying the potential inequalities. Origin convergence and
Cauchy control are recovered, so neither is an extra premise of this criterion. -/
theorem weilLogShiftAsymptoticPositive_iff_sampled_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔ ∀ m : ℕ, 2 ≤ m →
      (Summable fun n : ℕ => weilDeviation lam n *
        (riemannAutocorr (Real.log m + Real.log n) + riemannAutocorr (Real.log m - Real.log n))) ∧
      deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos m hm
    exact ⟨summable_potential_of_logShiftAsymptoticPositive hpos hexc (Real.log m),
      logShiftAsymptotic_potential_le_of_summable_excess hpos hexc m hm⟩
  · intro hs
    have hD := exists_cauchyBounded_absDeviation_of_sampled_potential hexc
      (fun m hm => (hs m hm).1) (fun m hm => (hs m hm).2)
    exact (weilLogShiftAsymptoticPositive_iff_cauchyBounded_potential hexc).mpr
      ⟨hD, fun m hm => (hs m hm).2⟩

/-- Convergence is needed only at the explicit exponentially spaced probes
`floor(exp j)+1`. Keep the potential inequalities at all integer-log samples;
convergence at the intermediate samples is then recovered. -/
theorem weilLogShiftAsymptoticPositive_iff_sparse_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      (∀ j : ℕ, Summable fun n : ℕ => weilDeviation lam n *
        (riemannAutocorr (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) + Real.log n) +
          riemannAutocorr (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) - Real.log n))) ∧
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos
    exact ⟨fun j => summable_potential_of_logShiftAsymptoticPositive hpos hexc _,
      logShiftAsymptotic_potential_le_of_summable_excess hpos hexc⟩
  · rintro ⟨hsample, hpotential⟩
    have hD := exists_cauchyBounded_absDeviation_of_potential_cover hexc
      (fun j => Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ)) integer_log_probe_covers_block
      hsample (fun j => hpotential _ (integer_log_probe_bounds j).1)
    exact (weilLogShiftAsymptoticPositive_iff_cauchyBounded_potential hexc).mpr ⟨hD, hpotential⟩

end RHTower
