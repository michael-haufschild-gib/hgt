# RBH–FZZ–Deninger multiplicity-information Ward transmutation

## Status

Paper-proved and formalized in Lean 4 on 2026-08-28. HC41 closed.

Lean module:
`GaloisForLFunctions.RHTower.ReflectedBiHeatFZZDeningerInformationWardTransmutation`.

## Corpus provenance

Mandatory corpus searches:

- `RBH Riemann black hole route open core critical line detector`
- `RBH reflection Ward charge horizon response Xi divisor`
- `RBH real black hole resonance critical line rho real part`
- `route RBH endpoint remaining producer`
- `RBH Hawking Mellin FZZ Deninger Ward`
- `RBH reflection partner imbalance zero iff critical line`
- `RBH source-native response sign transverse displacement`

The theorem is forced by exact formulas in `ReflectedBiHeatMultiplicityLeadingJetBalance.lean`,
the FZZ/Deninger Ward charge in `FZZCigarParityDeningerInformationWardTransmutation.lean`, and the
PW-B bridge in `ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation.lean`.

## HC41 theorem

For an actual Xi divisor `rho`, let

`B(rho) = ||left multiplicity-leading jet at aperture 2||
          - ||right multiplicity-leading jet at aperture 2||`.

The corpus identities imply

`B(rho) = |A_rho| (2^L(rho) - 2^R(rho))`,

where `A_rho != 0` and `L(rho)-R(rho)=Re(rho)-1/2`. The formalized theorem constructs a multiplier
`C_RBH(rho)` and proves

- `C_RBH(rho) > 0` at every actual Xi divisor, including the center;
- `B(rho) = (Re(rho)-1/2) C_RBH(rho)`;
- `B(rho) = -(C_RBH(rho)/2) D(rho)` after embedding in `C`, where `D` is the Deninger
  reflect-gauge Ward charge;
- `B(rho)` is an exact positive multiple of the nonlinear FZZ information force;
- `B(rho)` is an exact positive multiple of the PW-B recoil imbalance at every Borel grade;
- away from center, RBH imbalance and FZZ force have strictly positive product;
- RBH balance, FZZ equilibrium, PW-B balance, and Deninger reflect-gauge equivariance have the
  same pointwise zero locus;
- universal RBH imbalance cancellation is equivalent to RH.

The center branch uses `|A_rho|`, rather than an arbitrary constant, so the multiplier remains
source-faithful even where the quotient formula has a removable zero-over-zero singularity.

## Dependency-closed proof

1. Existing multiplicity-leading jet formulas give the exact common-coefficient difference.
2. Strict monotonicity of `x -> 2^x`, the identity `L-R=Re(rho)-1/2`, and `|A_rho|>0` prove the
   strict sign of `B` on both sides of center.
3. Off-center define `C_RBH=B/(Re(rho)-1/2)`; at center define it as `|A_rho|`.
4. Case splitting proves exact factorization and strict positivity.
5. The canonical first divisor copy has Deninger eigenvalue exactly `rho`; elementary algebra gives
   the Deninger transmutation.
6. Existing positive FZZ and PW-B multipliers yield exact positive ratio identities and common
   zero-locus classifications.
7. Existing global RBH multiplicity-leading balance theorem converts universal cancellation to RH.

## Literature audit

Bounded primary-source search through 2026-08-28 checked:

- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*
  ([arXiv:1904.12438](https://arxiv.org/abs/1904.12438));
- Hikida–Schomerus, *The FZZ-Duality Conjecture — A Proof*
  ([arXiv:0805.3931](https://arxiv.org/abs/0805.3931));
- Parikh–Wilczek, *Hawking Radiation as Tunneling*
  ([arXiv:hep-th/9907001](https://arxiv.org/abs/hep-th/9907001));
- Deninger, *A note on arithmetic topology and dynamical systems*
  ([arXiv:math/0204274](https://arxiv.org/abs/math/0204274));
- Connes–Consani, *The Scaling Hamiltonian*
  ([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)).

Exact searches for Riemann bi-heat/reflected-heat multiplicity-leading jets and Deninger Ward
identities returned no matches. Neighboring literature studies Xi heat flow, FZZ duality,
nonthermal tunneling, or conjectural flow/cohomology separately. No located source contains this
actual-divisor four-route magnitude-and-orientation transmutation. This is bounded-search novelty,
not a claim of exhaustive bibliographic proof.

## Lean audit

- `lake env lean GaloisForLFunctions/RHTower/ReflectedBiHeatFZZDeningerInformationWardTransmutation.lean`
  passed.
- `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatFZZDeningerInformationWardTransmutation`
  passed: 11,485 jobs.
- `#print axioms` for all 14 public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Module wired into `GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.

## Remaining producer burden

HC41 unifies receiver observables and preserves exact magnitude and orientation. It does not supply
an independent physical or arithmetic law forcing the shared Ward charge to vanish. That source law
is the next open core; no RH proof is claimed.
