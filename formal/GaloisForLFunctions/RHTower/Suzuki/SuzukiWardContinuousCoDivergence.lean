import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardUnconditionalMassEscape
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalSignedCompensationSaturation

/-!
# Unconditional co-divergence of Suzuki's atomic and continuous Ward masses

The literal unit-Riesz Ward source is the difference of a positive finite
von-Mangoldt mass and a positive regular-screw continuum mass.  The atomic
mass is already known to have leading scale `sqrt N / 3`, while their exact
Ward displacement is sub-root.  This file transfers that leading law to the
continuous mass without an RH premise.

Thus neither absolute sector can be the target of a cofinal completion: both
diverge at the same forced leading scale.  The unresolved SP-E content remains
the boundedness of their signed relative displacement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The positive regular-screw Ward mass has exactly the same leading
`sqrt N / 3` scale as the literal positive prime Ward mass. -/
theorem tendsto_suzukiUnitRieszRegularWardMass_logNat_div_sqrt_atTop_one_third :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) /
        Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop (nhds (1 / 3 : ℝ)) := by
  have hshift : Tendsto (fun N : ℕ => N + 2) atTop atTop :=
    Filter.tendsto_add_atTop_nat 2
  have hprime :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third.comp hshift
  have hgreen :=
    tendsto_unitRieszSuzukiGreen_logNat_div_sqrt_atTop_zero.comp hshift
  have hsub : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2) /
          Real.sqrt ((N + 2 : ℕ) : ℝ) -
        unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) /
          Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop (nhds (1 / 3 : ℝ)) := by
    simpa using hprime.sub hgreen
  apply hsub.congr'
  filter_upwards with N
  rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass N]
  ring

/-- The regular-screw Ward mass diverges to `+∞` unconditionally. -/
theorem tendsto_suzukiUnitRieszRegularWardMass_logNat_atTop :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ))) atTop atTop := by
  have hratio := tendsto_suzukiUnitRieszRegularWardMass_logNat_div_sqrt_atTop_one_third
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 2))
  rw [tendsto_atTop] at hsqrt ⊢
  intro b
  filter_upwards [hsqrt (6 * b),
    hratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 6 : ℝ) < 1 / 3))] with N hroot hratioN
  have hsqrtpos : 0 < Real.sqrt ((N + 2 : ℕ) : ℝ) := by positivity
  have hmass : (1 / 6 : ℝ) * Real.sqrt ((N + 2 : ℕ) : ℝ) <
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) :=
    (lt_div_iff₀ hsqrtpos).mp hratioN
  linarith

/-- No literal regular-screw Ward mass can converge to a finite real limit. -/
theorem no_finite_absolute_suzukiRegularWardMassLimit
    (regularLimit : ℝ) :
    ¬ Tendsto (fun N : ℕ =>
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)))
      atTop (nhds regularLimit) := by
  intro hlimit
  have hatTop := tendsto_suzukiUnitRieszRegularWardMass_logNat_atTop
  have hlarge : ∀ᶠ N in atTop,
      regularLimit + 1 ≤ suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) :=
    (tendsto_atTop.1 hatTop) _
  have hsmall : ∀ᶠ N in atTop,
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) < regularLimit + 1 / 2 :=
    hlimit (Iio_mem_nhds (by linarith : regularLimit < regularLimit + 1 / 2))
  rcases (hlarge.and hsmall).exists with ⟨N, hlargeN, hsmallN⟩
  linarith

end GaloisForLFunctions.RHTower
