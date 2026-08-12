# Step 49: the bootstrap proof attempt — executed, killed, formalized

Directive: attempt the RH proof via the cone/floor gaining loop. Outcome: NO PROOF — the loop
is impossible for two provable reasons; both extracted with exact constants and the Lean-able
part formalized (appended to GaussHodgeWeilPositivityCone.lean, axiom-clean).

## Kill 1: the vacuity theorem [LEAN-PROVED]

- `logDeriv_xi_ray_re_pos {c} (hc : 1/2 ≤ c) : 0 < Re logDeriv ξ(1/2+c)` — from
  `xiSquaredEulerFullQ_eq_logDeriv_re` + `xiSquaredEulerFullResponse_pos`.
- `deviation_moment_eq_zero_of_cone_of_even_energy_eq_zero`: a test satisfying the cone
  hypotheses with vanishing even energy is forced to C = 0 (jet and prefactor positive) and
  identically zero deviation (tail: domination by 0; off-tail: support lemma).
- `xiWeilPolarization_re_eq_zero_of_cone_of_even_energy_eq_zero`: its Weil diagonal is 0.

MEANING: unconditional positivity cones are spectrally silent by construction — cone tests
can never witness ¬RH; the corpus's detectors (divisor-odd, even energy zero) can never enter
any cone. Cone ∩ detectors = ∅ tautologically. Weil-side twin of the step-46
supply/certificate disjointness. General principle: unconditional theorems carry no spectral
information beyond their inputs; bootstrap gain REQUIRES a conditional ingredient discharged
by something other than positivity.

## Kill 2: the floor ceiling law [mechanism-exact numerics]

Single-probe Ward floor: floor(c) = 8c/B(c) − (c+1/2)², B(c) = 2Re logDeriv ξ(1/2+c). Linear
regime (c ≪ γ₁): B(c) ≈ 2c·density with density = B(1/2)/1 ≈ 0.0462 (true Λ₀(1) ≈ 0.023096) —
8c/B(c) ≈ 86.6 PROBE-INVARIANT. Ceiling: height² ≈ 85.6. Certified floor 65 (from the 3/50
bound) is already 77% of the mechanism's absolute ceiling. Only finite improvement available:
certify true Λ₀(1) → floor ~85.6, then the mechanism stalls forever (pair deposit ∝ c, budget
∝ c: scale invariance). Floors ≠ route to RH.

## Survivors (exact residue)

(i) True-Λ₀(1) certification (bounded value, Layer-1 sized). (ii) Multi-probe profile
separation: off-line copies have Poisson-kernel probe-profiles with poles OFF the imaginary
axis (f_{u,v}(c) = g_u(c−v) + g_u(c+v)); ray data separates in principle but extraction =
analytic continuation = k → ∞ derivative asymptotics = explicit formula backwards. Pole-beat
reformulation: RH ⟺ no off-axis beat in the ray-jet derivative asymptotics — the infinity
persists. (iii) THE entry point (unchanged, now confirmed from a new direction): Gauss lane
step 7 — independent bilinear evaluation of the vertical pencil (autocorrelated explicit
formulas / definitizable Krein intertwiner).

Card: xic-order-one-growth-organ.md step 49; Gauss hub step 15.
