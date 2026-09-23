import GaloisForLFunctions.RHTower.DeningerHalfDensityFloquetEnergy
import GaloisForLFunctions.HTGeometry.PeriodicRotationEnergy

/-!
# Euler depletion is a bounded-below embedding for the half-density Floquet energy

Ordinary Euler depletion `Δ_p = 1 - τ_p` acts on the trivialized half-density trace as
`I - p^{-1/2}R_{p,q}`, a rotation multiplier of the `q`-circle.  Rotation preserves the energy over
one period, so the two-sided bound

`(1-p^{-1/2})² E_Fl(h) ≤ E_Fl(Δ_p h) ≤ (1+p^{-1/2})² E_Fl(h)`

follows termwise and sums.  In particular the Poisson boundaries leak by the nonzero scalar
`1 - p^{-1/2}`.

* `deningerHalfDensityLift_defect` : **`U Δ_M = 1 - e^{-M/2}τ_M` after trivialization.**
* `deningerHalfDensityTrace_defect` : **the rotation-multiplier form.**
* `deningerHalfDensityTrace_defect_same` : **`Per_{p,1/2}Δ_p = (1-p^{-1/2})Per_{p,1/2}`.**
* `deningerHalfDensityFloquetEnergy_defect_bounds` : **the two-sided energy bound.**
-/

namespace RHTower

open SchwartzMap MeasureTheory GaloisForLFunctions

noncomputable section

/-- **After trivialization the Euler defect becomes a rotation multiplier.** -/
theorem deningerHalfDensityLift_defect (M : ℝ) (h : DeningerExpSchwartz) :
    deningerHalfDensityLift (deningerPeriodizationDefect M h)
      = deningerHalfDensityLift h
        - ((Real.exp (-(M / 2)) : ℝ) : ℂ)
          • deningerExpShiftSource M (deningerHalfDensityLift h) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  show ((deningerHalfDensityLift (deningerPeriodizationDefect M h) : DeningerExpSchwartz) :
      𝓢(ℝ, ℂ)) t
    = ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      - ((Real.exp (-(M / 2)) : ℝ) : ℂ)
        * ((deningerExpShiftSource M (deningerHalfDensityLift h) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) t
  rw [deningerHalfDensityLift_apply, deningerPeriodizationDefect_apply,
    deningerHalfDensityLift_apply, deningerExpShiftSource_apply, deningerHalfDensityLift_apply]
  have hkR : Real.exp (-(M / 2)) * Real.exp ((t + M) / 2) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hk : ((Real.exp (-(M / 2)) : ℝ) : ℂ) * ((Real.exp ((t + M) / 2) : ℝ) : ℂ)
      = ((Real.exp (t / 2) : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hkR
  linear_combination (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + M)) * hk

/-- **The rotation-multiplier form of `(19a)`.** -/
theorem deningerHalfDensityTrace_defect {L : ℝ} (hL : 0 < L) (M : ℝ) (h : DeningerExpSchwartz)
    (t : ℝ) :
    deningerPeriodizationSum
        ((deningerHalfDensityLift (deningerPeriodizationDefect M h) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) L t
      = deningerPeriodizationSum
          ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t
        - ((Real.exp (-(M / 2)) : ℝ) : ℂ)
          * deningerPeriodizationSum
            ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L (t + M) := by
  have hcoe : ((deningerHalfDensityLift (deningerPeriodizationDefect M h) : DeningerExpSchwartz)
      : 𝓢(ℝ, ℂ))
      = ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
        - ((Real.exp (-(M / 2)) : ℝ) : ℂ)
          • ((deningerExpShiftSource M (deningerHalfDensityLift h) : DeningerExpSchwartz)
            : 𝓢(ℝ, ℂ)) := by
    rw [deningerHalfDensityLift_defect]
    rfl
  have hmem : (((Real.exp (-(M / 2)) : ℝ) : ℂ)
      • ((deningerExpShiftSource M (deningerHalfDensityLift h) : DeningerExpSchwartz)
        : 𝓢(ℝ, ℂ))) ∈ DeningerExpSchwartz :=
    Submodule.smul_mem _ _ (deningerExpShiftSource M (deningerHalfDensityLift h)).2
  rw [hcoe, deningerPeriodizationSum_sub (deningerHalfDensityLift h).2 hmem hL,
    deningerPeriodizationSum_smul]
  congr 2
  exact deningerPeriodizationSum_expShift
    ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) M L t

/-- **`(19)`: the same-prime Euler comparison.**  On its own circle the Euler defect multiplies the
half-density trace by the nonzero scalar `1 - p^{-1/2}`. -/
theorem deningerHalfDensityTrace_defect_same {L : ℝ} (hL : 0 < L) (h : DeningerExpSchwartz)
    (t : ℝ) :
    deningerPeriodizationSum
        ((deningerHalfDensityLift (deningerPeriodizationDefect L h) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) L t
      = (1 - ((Real.exp (-(L / 2)) : ℝ) : ℂ))
        * deningerPeriodizationSum
          ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t := by
  rw [deningerHalfDensityTrace_defect hL L h t,
    deningerPeriodizationSum_periodic
      ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t]
  ring

/-! ## The two-sided energy bound -/

theorem deningerFloquetTerm_defect_le (h : DeningerExpSchwartz) (M : ℝ) {q : ℕ}
    (hq : 2 ≤ q) :
    deningerFloquetTerm (deningerHalfDensityLift (deningerPeriodizationDefect M h)) q
      ≤ (1 + Real.exp (-(M / 2))) ^ (2 : ℕ)
        * deningerFloquetTerm (deningerHalfDensityLift h) q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLpos : 0 < Real.log q := Real.log_pos (by linarith)
  set F := deningerPeriodizationSum
    ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) with hF
  have hcont : Continuous F := deningerPeriodizationSum_continuous
    (h := deningerHalfDensityLift h) hLpos
  have hper : Function.Periodic F (Real.log q) := fun s =>
    deningerPeriodizationSum_periodic
      ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) s
  have hfun : (fun t : ℝ => ‖deningerPeriodizationSum
      ((deningerHalfDensityLift (deningerPeriodizationDefect M h) : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ (2 : ℕ))
      = fun t : ℝ => ‖F t - ((Real.exp (-(M / 2)) : ℝ) : ℂ) * F (t + M)‖ ^ (2 : ℕ) := by
    funext t
    rw [deningerHalfDensityTrace_defect hLpos M h t]
  rw [deningerFloquetTerm, deningerFloquetTerm, hfun]
  have hbnd := intervalIntegral_normSq_sub_rotate_le hcont hLpos hper M
    (Real.exp_pos (-(M / 2))).le
  have hnn : (0 : ℝ) ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
  calc ((q : ℝ) ^ (2 : ℕ))⁻¹ * ∫ t in (0 : ℝ)..Real.log q,
        ‖F t - ((Real.exp (-(M / 2)) : ℝ) : ℂ) * F (t + M)‖ ^ (2 : ℕ)
      ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹ * ((1 + Real.exp (-(M / 2))) ^ (2 : ℕ)
          * ∫ t in (0 : ℝ)..Real.log q, ‖F t‖ ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hbnd hnn
    _ = (1 + Real.exp (-(M / 2))) ^ (2 : ℕ)
          * (((q : ℝ) ^ (2 : ℕ))⁻¹ * ∫ t in (0 : ℝ)..Real.log q, ‖F t‖ ^ (2 : ℕ)) := by ring

theorem le_deningerFloquetTerm_defect (h : DeningerExpSchwartz) (M : ℝ) {q : ℕ}
    (hq : 2 ≤ q) :
    (1 - Real.exp (-(M / 2))) ^ (2 : ℕ) * deningerFloquetTerm (deningerHalfDensityLift h) q
      ≤ deningerFloquetTerm (deningerHalfDensityLift (deningerPeriodizationDefect M h)) q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLpos : 0 < Real.log q := Real.log_pos (by linarith)
  set F := deningerPeriodizationSum
    ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) with hF
  have hcont : Continuous F := deningerPeriodizationSum_continuous
    (h := deningerHalfDensityLift h) hLpos
  have hper : Function.Periodic F (Real.log q) := fun s =>
    deningerPeriodizationSum_periodic
      ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) s
  have hfun : (fun t : ℝ => ‖deningerPeriodizationSum
      ((deningerHalfDensityLift (deningerPeriodizationDefect M h) : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ (2 : ℕ))
      = fun t : ℝ => ‖F t - ((Real.exp (-(M / 2)) : ℝ) : ℂ) * F (t + M)‖ ^ (2 : ℕ) := by
    funext t
    rw [deningerHalfDensityTrace_defect hLpos M h t]
  rw [deningerFloquetTerm, deningerFloquetTerm, hfun]
  have hbnd := le_intervalIntegral_normSq_sub_rotate hcont hLpos hper M
    (Real.exp_pos (-(M / 2))).le
  have hnn : (0 : ℝ) ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
  calc (1 - Real.exp (-(M / 2))) ^ (2 : ℕ)
        * (((q : ℝ) ^ (2 : ℕ))⁻¹ * ∫ t in (0 : ℝ)..Real.log q, ‖F t‖ ^ (2 : ℕ))
      = ((q : ℝ) ^ (2 : ℕ))⁻¹ * ((1 - Real.exp (-(M / 2))) ^ (2 : ℕ)
          * ∫ t in (0 : ℝ)..Real.log q, ‖F t‖ ^ (2 : ℕ)) := by ring
    _ ≤ ((q : ℝ) ^ (2 : ℕ))⁻¹ * ∫ t in (0 : ℝ)..Real.log q,
          ‖F t - ((Real.exp (-(M / 2)) : ℝ) : ℂ) * F (t + M)‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hbnd hnn

/-- **`(19d)`: Euler depletion is a bounded-below embedding for the half-density Floquet
energy.** -/
theorem deningerHalfDensityFloquetEnergy_defect_bounds (h : DeningerExpSchwartz) (M : ℝ) :
    (1 - Real.exp (-(M / 2))) ^ (2 : ℕ) * deningerHalfDensityFloquetEnergy h
        ≤ deningerHalfDensityFloquetEnergy (deningerPeriodizationDefect M h)
      ∧ deningerHalfDensityFloquetEnergy (deningerPeriodizationDefect M h)
        ≤ (1 + Real.exp (-(M / 2))) ^ (2 : ℕ) * deningerHalfDensityFloquetEnergy h := by
  have hsum := deningerFloquetTerm_summable (deningerHalfDensityLift h)
  have hsum' := deningerFloquetTerm_summable
    (deningerHalfDensityLift (deningerPeriodizationDefect M h))
  constructor
  · rw [deningerHalfDensityFloquetEnergy, deningerHalfDensityFloquetEnergy,
      deningerFloquetEnergy, deningerFloquetEnergy, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => le_deningerFloquetTerm_defect h M q.2.two_le)
      (hsum.mul_left _) hsum'
  · rw [deningerHalfDensityFloquetEnergy, deningerHalfDensityFloquetEnergy,
      deningerFloquetEnergy, deningerFloquetEnergy, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => deningerFloquetTerm_defect_le h M q.2.two_le)
      hsum' (hsum.mul_left _)

end

end RHTower
