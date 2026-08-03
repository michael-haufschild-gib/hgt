# Cyclic Puiseux stabilizer coarea source law

- **ID:** puiseux-cyclic-stabilizer-coarea
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Douçot, *New nonabelian Hodge graphs from twisted irregular connections*, Lemmas 2.1--2.2; Boalch--Douçot--Rembado, fission-tree denominator filtration
- **Statement:** The weighted Puiseux loop term is exactly the finite coarea mass of losses in the cyclic Galois-sheet stabilizer filtration; minimal denominator is equivalent to trivial final stabilizer.

## Goal

Remove the remaining source-level abstraction in the Airy-tower manuscript.  Derive the
characteristic weight

`S = sum_i beta_i (e_(i-1) - e_i)`

from a genuine cyclic action on a Puiseux polynomial, rather than postulating `Characteristic` and
its weight.  This is source infrastructure for the universal contact law; it is not itself claimed
as new.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: `StokesPuiseuxSourceLaw.lean`; targeted build green; axiom audit baseline only
- [ ] 3 → 4  publication-ready: integrated source theorem, Lean certificate and hostile audit

## Exact theorem surface

Fix `R > 0`, a finite Puiseux polynomial

`q(t) = sum_(j in S) c_j t^j`, `c_j != 0`, `S subset Nat_{>0}`,

viewed as `q(z^(1/R))`, and the primitive root
`zeta_R = exp(2 pi i/R)`.  For `a in Z/R`, put

`sigma_a(q)(t) = sum_(j in S) c_j zeta_R^(a j) t^j`.

For a finite list `P` of exponent numerators define

`H_R(P) = {a in Z/R : sigma_a fixes every monomial with exponent in P}`

and `g_R(P) = gcd(R,P)` (iterated gcd, with `g_R(empty)=R`).  Then:

1. `[BRIDGE CS1]` `sigma_a` fixes exponent `j` iff `R | a j`.
2. `[BRIDGE CS2]` `H_R(P)` is the kernel of multiplication by `g_R(P)` on `Z/R`, and
   `|H_R(P)| = g_R(P)`.
3. `[BRIDGE CS3]` If `beta_1 > ... > beta_m > 0` and
   `e_i=gcd(R,beta_1,...,beta_i)`, then the sheets whose first difference from a fixed sheet occurs
   at `beta_i/R` are exactly `H_R(P_(i-1)) \ H_R(P_i)` and number
   `e_(i-1)-e_i`.
4. `[BRIDGE CS4]` Summing the slopes of all ordered differences of Galois sheets gives
   `Irr(End(q)) = sum_i beta_i(e_(i-1)-e_i)`.
5. `[BRIDGE CS5]` The denominator `R` is minimal iff `e_m=1`; in that case the stabilizer is
   trivial and the orbit has `R` sheets.
6. `[BRIDGE CS6]` Consequently Douçot's loop normalization is
   `B_(I,I)=Irr(End(q))-R^2+1 = sum_i beta_i(e_(i-1)-e_i)-R^2+1`.

The Lean implementation must expose actual finitely supported complex coefficients, the complex
primitive root action, fixed-sheet subtypes, stabilizer cardinalities, first-break layers, and the
ordered-pair slope sum.  A theorem beginning from a pre-certified characteristic or decorated core
does not discharge CS1--CS5.

## Dependency-closed paper proof

`[PROVED HERE]` Let `zeta=zeta_R`.  Since `zeta` is a primitive `R`-th root,
`zeta^n=1` iff `R|n`.  The coefficient of `t^j` in `sigma_a(q)` equals
`c_j zeta^(aj)`.  Because `c_j` is nonzero on the support, it equals `c_j` iff `R|aj`.  This proves
CS1 without any genericity assumption on coefficients.

Write `o(a)` for the additive order of `a in Z/R`.  The condition `R|aj` is equivalent to
`j a=0`, hence to `o(a)|j`.  Also `o(a)|R`.  Therefore, for
`g_R(P)=gcd(R,P)`,

`a in H_R(P)  iff  o(a)|j for every j in P  iff  o(a)|g_R(P)`.

Thus `H_R(P)=ker([g_R(P)] : Z/R -> Z/R)`.  Multiplication by `d` on a finite cyclic group of order
`R` has kernel order `gcd(R,d)`.  Since `g_R(P)|R`, this order is `g_R(P)`.  This proves CS2.

Let `P_i=[beta_1,...,beta_i]`.  A shift first changes `q` at `beta_i` precisely when it fixes all
higher support exponents but does not fix `beta_i`, i.e. when it lies in
`H_R(P_(i-1)) \ H_R(P_i)`.  The stabilizers are nested.  CS2 gives the layer cardinality
`|H_R(P_(i-1))|-|H_R(P_i)|=e_(i-1)-e_i`, proving CS3.  Exponents which do not lower the gcd have
empty first-break layer, explaining directly why only levels contribute.

For a fixed base sheet, every shift in the `i`-th layer gives a difference with slope
`beta_i/R`.  Translation in `Z/R` shows that every shift occurs for exactly `R` ordered pairs of
sheets.  Hence the ordered-pair slope sum is

`R * sum_i (beta_i/R)(e_(i-1)-e_i)
 = sum_i beta_i(e_(i-1)-e_i)`.

This is CS4.  The full stabilizer has order `e_m`; it is trivial iff `e_m=1`.  Equivalently no
proper divisor of `R` supports all exponent denominators, which is exactly minimality of `R`.
Orbit--stabilizer then gives orbit size `R`, proving CS5.  Substitution into the published Stokes
loop normalization proves CS6.

## Novelty and hostile audit

- **Verdict:** `[BRIDGE / REDISCOVERED MECHANISM]`, not a novelty claim.  It is the cyclic
  conductor--discriminant/layer-cake mechanism behind the published loop formula.
- **Why retain it:** it closes a genuine formal source gap.  The new claims remain the factorisation
  from source stabilizer filtration through complementary contact to exact tomography, energy-tree
  metric, four-point law, strict negative type and canonical squared embedding.
- **Theatre test:** fails unless Lean contains the complex root action and proves fixed-sheet
  equivalence and cardinality from that action.  Restating the gcd sum is insufficient.
- **Hard obstruction attacked next:** two-orbit common-part/fission source formula (Douçot Lemma
  2.2) after the one-orbit theorem is compiled.

## Log

- 2026-08-03 — created in 1-in-progress after primary-source audit.
- 2026-08-03 — paper proof dependency-closed; ready to move to 2-fully-proven.
- 2026-08-03 — formalized genuine complex action, stabilizers, orbit, first-break and ordered-pair
  slope mass; `lake build GaloisForLFunctions.HTGeometry.StokesPuiseuxSourceLaw` passed; all promoted
  theorems use only `propext`, `Classical.choice`, `Quot.sound`.
