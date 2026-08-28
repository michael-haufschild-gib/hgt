# HC74 pre-divisor optical-cancellation holomorphy obstruction (2026-08-28)

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPreDivisorOpticalCancellationHolomorphyObstruction.lean`.
Card: `docs/drafts/pipeline/3-formalized/hb-predivisor-optical-cancellation-holomorphy-obstruction.md`.

Result: defined the unique scalar coefficient that cancels the moving-horizon/AIME optical triangle on the full open pre-divisor critical strip using the exact reflected horizon shifts `x(3-x)` and `(1-x)(2+x)`, the existing third-mass cross numerator, and theta-mirror AIME denominator. Proved coefficient-for-coefficient specialization to `d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q` on every Xi copy. Proved a general strip identity theorem: a function holomorphic on `{z : ℂ | 0 < z.re ∧ z.re < 1}` and agreeing everywhere there with a profile depending only on `z.re` is constant. The exact susceptibility has distinct values at interior points `1/4` and `1/2`; hence no holomorphic scalar pre-divisor coefficient can track the physical cancellation profile throughout the strip.

Scope: does not prove RH, does not exclude holomorphic interpolation only on the discrete Xi divisor, and does not claim the cancellation profile is the complete Einstein coefficient. It proves a sharp regularity boundary: source-global scalar cancellation must be singular, antiholomorphic/non-holomorphic, support-discontinuous, or operator-valued.

Verification: direct `lake env lean` passed; target-only build passed `12138/12138`; all 4 theorem axiom audits use only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint has no HC74 finding and fails only pre-existing unrelated unreachable modules.