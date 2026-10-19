# No horizon-uniform coercivity from the complete selected Fermi trace

- **ID:** thim-horizon-uniform-selected-fermi-coercivity
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Source:** `../3-formalized/thim-full-trace-valuation-depth-stability.md`
- **Failed claim:** A fixed real C bounds every finite-horizon sieve pronic
  energy by C times the complete odd/four-divisible selected Fermi jump energy.

## Exact obstruction

`fermiSelectedTotal_no_uniform_inverse` refutes the claim unconditionally.
At horizon `2^(L+1)`, `fermiDyadicRampWeight L` has
`P >= L*(L+1)*(2*L+1)/12`, `0<Q<=2*L` for L>0. Thus every universal inverse
constant would exceed an unbounded quadratic expression in L.

This uses the complete infinite selected trace. The earlier local-pair alias
example alone did not establish this obstruction.

## Strongest verified positive survivor

For every N and every real coefficient function c, both energies converge and

`P(N,c) <= (D+4)*(D+1)*Q(N,c)`, where `D=Nat.log 2 N+1`.

The completed sharp survivor now identifies the leading constant: the optimal
physical inverse constants for signed and nonnegative coefficients both obey
`K_N / (Real.logb 2 N)^2 -> 4/pi^2`. This does not claim an exact value at each
finite horizon. The paper and Lean certificate are in
`../3-formalized/thim-sharp-physical-fermi-asymptotic.md`. Finite-window recovery and stability
are also verified. Four-free-supported weights retain the earlier uniform
physical bounds, while unrestricted coefficients retain exact algebraic recovery
and the separate 3/2 inverse coefficient-energy bound after divisor inversion.

## Exact insight and status

Selected readings act as first differences of normalized sieve values along
arithmetic valuation chains. Finite-horizon saturation closes the inverse;
long chains make its physical conditioning deteriorate. Injectivity and
coefficient-space stability therefore do not imply uniform physical coercivity.

Paper proof is dependency-closed. The finite upper, complete upper, and matching
ramp lower statements are formalized in the three leaves named on the source
card. All source and public-axiom audits passed; only standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound` occur. Leaves are wired and formal
lint with generated-file checking passed. The positive survivor is formalized;
this route is not retired on its negative statement alone.

Removing the last negative coefficient proves the obstruction also survives
inside the nonnegative coefficient cone. The separate formalized card
`../3-formalized/thim-nonnegative-fermi-trace-conditioning.md` records its
dependency-closed proof and verified seventh Lean leaf. Source, all seven public
axioms, and umbrella wiring passed. Fresh index regeneration and global generated
lint passed after the concurrent BiScale umbrella was completed.

The sharp physical package is counted once as C1 in the active programme.
Finite-chain Hardy theory remains prior mathematics; its wrappers and the
negative statement add no separate contribution. The bounded prior-work audit
does not assert global external priority.
