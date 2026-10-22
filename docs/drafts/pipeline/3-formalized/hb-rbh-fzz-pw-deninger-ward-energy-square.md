# HB–RBH–FZZ–PW–Deninger Ward-energy square

## Status

Paper-proved and formalized in Lean 4 on 2026-08-28. HC42 closed.

Lean module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSharedWardEnergySquare`.

## Corpus provenance

Mandatory corpus searches included:

- `HB canonical left action covariance endpoint shared Ward charge`
- `Hawking Burnol Hedenmalm response producer source Ward critical line`
- `canonical left response covariance Xi divisor zero iff RH`
- `Hedenmalm Burnol physical symmetry force reflect gauge commutator`
- `HB canonical orbit optical power exact formula centered displacement square`
- `unsquared source reflection current norm sign critical line`
- `HB Peierls current Deninger Ward charge real part`
- `HB source covariance defect norm exact critical displacement`
- `canonical optical power reflection invariant`
- `gauge fixed horizon orthogonal helicity flux reflect`
- `radiation norm reflect XiZeroCopyReflectEquiv`

The corpus gives canonical HB optical power as a positive multiple of the squared orthogonal
helicity-mixing coefficient and the identity

`normSq(mixing(q)) = Im(q)^2 (1-2 Re(q))^2`.

HC38–HC41 identify `1-2 Re(q)` with the shared signed Deninger/FZZ/PW/RBH Ward coordinate.

## HC42 theorem

Define the source-faithful HB factor

`K_HB(n,q) = 4(8n+5) Im(q)^2 ||R_q(carrier_q,0)||^2`,

where `R_q` is the actual gauge-fixed second-harmonic radiation map. Then:

- `K_HB(n,q)>0` for every actual Xi divisor copy;
- `HBOpticalPower(n,q) = K_HB(n,q) Re(D(q))^2`;
- HB power is an exact positive multiple of the squared FZZ reflected-Fermi information force;
- HB power is an exact positive multiple of the squared PW-B partner imbalance at every Borel
  grade;
- on canonical first copies, HB power is an exact positive multiple of squared actual RBH
  multiplicity-leading norm imbalance;
- HB darkness is pointwise equivalent to Deninger Ward cancellation, FZZ equilibrium, PW-B
  balance, and RBH balance.

All conversion ratios are strictly positive because the Xi height, full-Einstein radiation norm,
FZZ multiplier, PW-B multiplier, and RBH multiplier are nonzero with proved positive signs.

## Positive survivor and no-go

HC42 identifies one common transverse coordinate in five route languages:

- Deninger, FZZ-P, PW-B, and RBH see it linearly and retain orientation;
- canonical passive HB optics sees its square and therefore retains energy and zero locus but loses
  orientation.

This is the strongest positive survivor of the passive-HB producer obstruction. Optical positivity
does not imply darkness; tilted Xi fibres have strictly positive Ward energy. Hence passive energy
is an exact receiver, not an independent vanishing producer.

## Dependency-closed proof

1. Expand canonical optical power through the Peierls–Darboux radiation-flux identity.
2. Substitute the exact helicity-mixing norm-square formula.
3. Group grade, Xi height, and radiation norm into `K_HB`; nonzero Xi height and nonzero
   full-Einstein radiation prove `K_HB>0`.
4. Substitute the Deninger charge formula `D=1-2 Re(q)` to obtain the exact square identity.
5. Substitute HC38, HC40, and HC41 factorizations and clear denominators using their proved strict
   positivity.
6. Transport existing exact zero-locus theorems to all five route observables.

## Literature audit

Bounded primary-source search through 2026-08-28 checked:

- Glampedakis–Johnson–Kennefick, *The Darboux transformation in black hole perturbation theory*
  ([arXiv:1702.06459](https://arxiv.org/abs/1702.06459));
- Masaood, *A Scattering Theory for Linearised Gravity on the Exterior of the Schwarzschild Black
  Hole I* ([arXiv:2007.13658](https://arxiv.org/abs/2007.13658));
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*
  ([arXiv:2210.15935](https://arxiv.org/abs/2210.15935));
- Sberna et al., *Nonlinear effects in the black hole ringdown: absorption-induced mode
  excitation* ([arXiv:2112.11168](https://arxiv.org/abs/2112.11168));
- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*
  ([arXiv:1402.1282](https://arxiv.org/abs/1402.1282));
- Betzios–Gaddam–Papadoulaki, *Black holes, quantum chaos, and the Riemann hypothesis*
  ([arXiv:2004.09523](https://arxiv.org/abs/2004.09523));
- Hikida–Schomerus, *The FZZ-Duality Conjecture — A Proof*
  ([arXiv:0805.3931](https://arxiv.org/abs/0805.3931));
- Parikh–Wilczek, *Hawking Radiation as Tunneling*
  ([arXiv:hep-th/9907001](https://arxiv.org/abs/hep-th/9907001));
- Deninger, *A note on arithmetic topology and dynamical systems*
  ([arXiv:math/0204274](https://arxiv.org/abs/math/0204274)).

Exact searches for Teukolsky/Peierls optical energy combined with Riemann-zero Deninger, FZZ,
Parikh–Wilczek, or reflected bi-heat Ward charges found no matching construction. Located work
supplies neighboring frameworks separately. No located source contains this coefficient-exact
five-route Ward-energy square. This is bounded-search novelty, not exhaustive bibliographic proof.

## Lean audit

- Direct `lake env lean` check passed.
- Target `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSharedWardEnergySquare` passed:
  12,000 jobs.
- `#print axioms` for all nine public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Module wired into `GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.
- Global lint remains blocked only by unrelated pre-existing umbrella reachability errors; HC42 is
  reachable and has no lint finding.

## Remaining producer burden

HC42 closes exact receiver unification across all named routes. It does not prove that the common
Ward energy vanishes. A source-native physical or arithmetic identity imposing zero total energy
without assuming critical-line placement remains the next open core; no RH proof is claimed.
