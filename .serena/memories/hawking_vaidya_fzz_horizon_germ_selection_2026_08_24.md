# Hawking Vaidya/FZZ horizon-germ selection (2026-08-24)

Created:
- `formal/GaloisForLFunctions/HTGeometry/FZZCigarReplicaKreinScale.lean`
- `formal/GaloisForLFunctions/HTGeometry/VaidyaEvaporationFZZHorizonScale.lean`
- imports added to `HTGeometry.lean`.

Exact unconditional results:
1. Finite-level FZZ fractional-winding mismatch coefficient is
   `b(a)=2a/(1-2a)`, `a=1/k in (0,1/2)`.
   It bijects physical level range to every positive scale, inverse
   `a(beta)=beta/(2(1+beta))`.
2. Level-universal nonpositive-real odd Hawking square selects
   `omega.re=0`; every fixed level has an explicit off-axis blind point.
3. Constant-rate outgoing Vaidya conformal radial factor:
   `f_epsilon(x)=1-1/x-4 epsilon x`.
   Parametrize by `q in (0,1)`:
   `epsilon=q/(4(1+q)^2)`,
   event root `x_H=1+q`, outer root `x_C=(1+q)/q`.
   Negative outer/event slope ratio equals `q`.
4. Repeated horizon scattering fixed-point scale is `q/(1-q)`.
   Under `q=2a=2/k`, this is exactly the FZZ replica scale.
   This equality is algebraic only; Hawking dynamics has NOT been shown to enforce `q=2/k`.
5. Strongest survivor: passive odd-square sign on ANY early evaporation interval
   `0<q<qCap<1` already implies `omega.re=0`.
   Proof is infinitesimal: the small-scale square reads the nonpositive-real chamber of
   `omega^2`. Thus horizon coalescence, Planckian extrapolation, and full positive scale
   are unnecessary. Every fixed q remains blind.

Hostile audit / open physical producer:
- Generic KMS, CCR, group, inverse, Krein, Cayley, and stationary temperature variation remain insufficient.
- Need coefficient-faithful outgoing-Vaidya/FZZ dynamics proving the same transported theta resonance obeys odd-square passive confinement on a nonempty early mass-loss interval.
- Alternative falsifiable matching: derive `q=2/k` from Hawking flux plus finite-k cigar backreaction.
- Varying k changes cigar CFT unless tied to one evaporating black-hole trajectory.
- Capuano--Santoni--Barausse only control constant-rate Vaidya and leave polar gravitational sector open; small-rate QNM calculations cannot justify coalescence, but germ theorem avoids coalescence.
- Halder--Jafferis torus one-point stringy area operator remains expected/open and may provide same-resonance transport.

Validation:
- targeted `lake env lean` passed for both new modules.
- all new public theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- lint has only pre-existing unrelated unreachable module:
  `GaloisForLFunctions.HTGeometry.FiniteExponentialHankel`.
- no sorry/admit/axiom/opaque/unsafe in new files.
- temp scratch removed; no git used.
