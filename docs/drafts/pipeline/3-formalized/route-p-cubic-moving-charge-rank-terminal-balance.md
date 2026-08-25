# Route P cubic moving-charge rank--terminal balance

## Status

- Pipeline stage: formalized in Lean 4
- Conjecture label: `CUBIC-MOVING-CHARGE-RANK-TERMINAL-BALANCE`
- Scope: arbitrary moving coefficient-generated irregular-Stokes landing pairs of the first negative cubic wall--Xi Malgrange residual
- Frontier-map status: read-only; no ledger edit made

## Exact theorem

Let `x₀` land at the cubic Xi residual under complete threshold contraction and `x₁` land at the same residual under unit Rees activation.  No relation between their charges or physical ranks is assumed.  Write

- `T_j = ∑_a terminalEnergy_a(x_j)`;
- `B₁ = ∑_a blockEnergy_a(x₁)`;
- `r_j = commonRank(x_j)`;
- `A = -globalRankCoefficient`.

Then

`T₀ + A r₁² = T₁ + B₁ + A r₀²`, with `A > 0` and `B₁ > 0`.

Consequently, every terminal-isometric moving landing pair satisfies

`r₀² < r₁²`.

Thus unitary/terminal-isometric Rees transport can land the same cubic Xi target only by strictly inflating physical-rank magnitude.  Rank-magnitude-preserving transport is instead forced into the previously proved strict terminal-energy dissipation law.

## Dependency-closed proof

1. Contracted positive energy is `T₀`; unit positive energy is `T₁+B₁`.
2. The two global Rees Witt decompositions land at the same cubic Xi target:
   `T₀ + c r₀² = T₁ + B₁ + c r₁²`.
3. Set `A=-c` and rearrange to obtain the exact balance.
4. Either landing forces `c<0`, hence `A>0`.
5. The unit landing charge is nonzero.  Orbit surjectivity and coefficient-generated pendant-cut faithfulness force `B₁>0`.
6. If `T₀=T₁`, exact balance gives `A(r₁²-r₀²)=B₁>0`; since `A>0`, `r₀²<r₁²`.

No conservation or source-incidence hypothesis enters the theorem.

## Hostile audit

- Charge movement is arbitrary; neither equality nor linear transport is assumed.
- Physical-rank sign changes are handled because the balance uses rank squares.
- Terminal isometry is only a derived corollary condition, not needed for exact balance.
- The theorem does not identify any existing source-side isometry with a Stokes charge map; corpus audit shows that coefficient-faithful bridge is still absent.
- Result does not assert landing-pair existence or prove RH.

## Novelty audit

Corpus search found fixed-charge Rees transversality, the new rank-preserving dissipation theorem, and several source-side polarization isometries, but no arbitrary moving-pair rank--terminal--block conservation law.  Parent irregular-RH/wild-twistor literature does not state this completed-Xi balance.  Absence is an audit inference, not a universal priority claim.

## Lean formalization

Implemented in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMovingChargeReesDissipation.lean`.  Added one public balance theorem and refactored the existing rank-magnitude-preserving dissipation theorem to use it.

Targeted module check passed.  Both affected public declarations have trust base exactly
`[propext, Classical.choice, Quot.sound]`; no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration was introduced.
