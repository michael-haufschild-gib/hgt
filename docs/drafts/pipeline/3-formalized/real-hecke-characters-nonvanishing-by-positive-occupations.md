# Every Hecke L-function is nonzero on the closed right half-plane

- **ID:** real-hecke-characters-nonvanishing-by-positive-occupations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Lean:** `GaloisForLFunctions/HeckeLFunctions/HeckeLFunctionsDoNotVanishOnTheLineReOne.lean`
- **Statement:** Every nontrivial finite-order ray class character has nonzero L-value at one. Every character's globally continued L-function is nonzero on `Re s >= 1`, away from the trivial pole.

## Quadratic characters

The [actual positive occupation expansion](quadratic-hecke-products-have-positive-occupation-expansions.md)
expresses `L(s,1)L(s,psi)` for `psi^2=1` as a general Dirichlet series
indexed by finitely supported particle occupations. Every coefficient is
one, every frequency is nonnegative, and absolute convergence holds on
`Re s>1`. There is an actual particle: otherwise the trivial Euler
product would be identically one, contradicting its positive residue.

Suppose `psi!=1` and `L(1,psi)=0`. The
[global continuation](hecke-global-continuation-from-ordinary-classes.md)
gives an entire `L(s,psi)` and `L(s,1)=H(s)+rho/(s-1)`, with `H` entire.
Thus `F(s)=H(s)L(s,psi)+rho*dslope(L(.,psi),1,s)` is entire and agrees
with the positive occupation series on `Re s>2`.

`HTGeometry.general_landau_summable_transfer` applies on the disk centered
at three with radius four. Summability at two therefore forces summability
at zero. At zero every occupation contributes one. Restricting to
`Finsupp.single j n` at one actual particle gives a summable constant-one
sequence on the natural numbers, whose terms would have to tend to zero.
This contradiction proves `heckeLFunction_one_ne_zero_of_sq_eq_one`.
The established nonquadratic result gives `heckeLFunction_one_ne_zero`
for every nontrivial character.

## Other boundary points

At `1+it`, `t!=0`, both `L(s,psi)` and `L(s,psi^2)` are holomorphic at
the required points `1+it` and `1+2it`; the only possible pole is one.
If `L(1+it,psi)=0`, the derivative quotient has a finite limit. The
three-four-one product
`L(sigma,1)^3 L(sigma+it,psi)^4 L(sigma+2it,psi^2)` then tends to zero,
contradicting its norm being at least one. Together with the value at one
and the Euler-product interior, this proves
`heckeLFunction_ne_zero_of_one_le_re`.

Agreement with the counting continuation gives `heckeLCont_one_ne_zero`
and `heckeLCont_ne_zero` for every nontrivial character.

## Audit

The complete scratch passes without warnings. The five exported results
above have transitive axiom sets exactly
`[propext, Classical.choice, Quot.sound]`. No missing arithmetic or analytic
input is assumed. The new module uses default elaboration limits and is
wired into the Hecke umbrella. Its final direct source check is pending.

Mertens bounds, the primitive completed functional equation, and class
field theory remain separate open programme gates.
