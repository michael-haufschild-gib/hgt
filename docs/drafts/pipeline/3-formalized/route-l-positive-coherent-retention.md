# Route L: positive complete coherent repairs retain prime mass

Status: formalized; full scratch Lean, targeted final build, all-theorem axiom audit and repository lint passed.
Date: 2026-09-11.

Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPositiveCoherentRepair`.

## Mathematical target

The explicit signed star correction cancels reciprocal energy by losing the
original row's anchor marginal. This audit tests whether a repair preserving
nonnegative real edge parts can do the same. The test permits an arbitrary
moving profile and finite set, but subtracts one complete coherent packet at
each stage. It does not assume a retained marginal or energy limit.

## Exact statements

Let `r_(a,n)` be the existing normalized fixed-left Big-Witt row, anchored at
`p=nthPrimeSubtype a`, with positive raw row mass `M_n`. Its nonzero coefficient
at `(p,q)` is `1/(p*q*M_n)`.

For any profile `b` and finite prime set `S`, set `g=r_(a,n)-R(b,S)`.
Assume only that `Re g(i)>=0` for every ordered edge `i`. The theorem does not
require all coefficients to be real. Define `K_n=(1/p)/M_n`.

Lean proves:

- `0 <= Re marginal(R(b,S))(p) <= K_n`.
- `1-K_n <= Re marginal(g)(p) <= 1`.
- For `A>=0`, `(A/p)*(1-K_n) <= Re E_A(g)` for the existing reporter.

The original source theorem gives `M_n -> infinity`, hence `K_n -> 0`.
For arbitrary moving profiles `b_n` and sets `S_n` satisfying the same edge
condition, the repaired anchor mass therefore tends to one. Its energy real
part is eventually at least `A/(2p)`. For `A>0`, the complex energy cannot tend
to zero.

## Dependency-closed paper proof

First consider any fixed-left row with `Re f(p,q)<=K/q`, `K>=0`, and zero real
coefficients off that row. If `p` is not in the coherent set, its removed anchor
marginal is zero. Otherwise, compare both orientations between any two leaves
`q,r` distinct from `p`. The original row is zero on both edges. Nonnegativity
of the repaired real parts forces `Re b(q)=Re b(r)`.

The real correction on every edge from `p` to a leaf is consequently a common
amplitude `t`. The reverse orientation gives `t>=0`; the outgoing orientation
gives `t<=K/q` for each leaf. For `k` leaves and their largest integer label
`Q`, distinct positive labels give `k<=Q`. The removed anchor marginal is
exactly `k*t`, so `0<=k*t<=Q*(K/Q)=K`. Empty leaf sets are handled separately.

The existing source support and reciprocal coefficient formula instantiate
this lemma with `K=K_n`. The original row has marginal `delta_p`, so subtraction
gives the retained interval. Divergence of the actual raw mass squeezes that
interval to one without an additional retention assumption.

Finally, regroup the finite reporter by its left-prime label. For nonnegative
real edge parts and nonnegative reciprocal weights, the contribution of the
anchor alone is a lower bound on the complete real energy. Combining that
bound with the retained interval proves the displayed energy inequality.
Since `K_n` is eventually below one half, the eventual positive floor follows;
uniqueness/order of real limits excludes a zero complex energy limit.

## Positive survivor and boundary of the result

This is a quantitative source-derived retention law for the specified repair
domain. Positivity of every repaired edge is essential to the proof; positivity
of the original row alone does not suffice, as the signed star demonstrates.
Only real parts enter, so the theorem is stronger than the version assuming
nonnegative real-valued coefficients.

The result does not establish the missing cyclic-to-fixed-physical comparison,
assert that its correction belongs to this domain, or prove RH. It does not
cover an arbitrary finite sum of complete coherent packets with different
finite sets. The active transpose-row test examines that additive enlargement:
[research card](../1-in-progress/route-l-source-selected-completion-attack.md).

## Verification

- `lake env lean /tmp/route_l_positive_repair.lean` — passed.
- `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPositiveCoherentRepair` — passed; only the target module's Lean child ran.
- `lake env lean /tmp/route_l_positive_repair_axioms.lean` — all 16 theorems use only `propext`, `Classical.choice` and `Quot.sound`.
- `scripts/formal_tools.py lint` — passed.
- `RHTower.lean` import is wired; no full or umbrella build ran. C11 build and audit processes completed.
