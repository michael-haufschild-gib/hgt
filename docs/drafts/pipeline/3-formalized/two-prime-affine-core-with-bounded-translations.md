# Two-prime affine core with bounded p-adic translations

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [three-prime core](three-prime-principal-unit-core.md).
- **Module:** `AdelicKreinGeometry/TwoPrimesCarryTheWholeAffineState.lean`.

For distinct primes `p,q,r`, let `H_n` be the subgroup of positive `q,r`-units
satisfying the p-adic principal-unit condition at resolution `n`, and let
`R=ℤ[1/(qr)]`. Then, for every `c>0`,

`κ(weilPadicState p c | {x↦ux+b : u∈H_n, b∈R}) = κ(ratCorr)+1`.

Every translation in this subgroup has p-adic norm at most one. Expanding
p-adic translations are unnecessary: the two shifts `0,1` already supply
the extra square. No RH or finite-index assumption is added.

## Proof

For any subgroup `H` of positive rationals with dense logarithms, write
`K=ratCorr|H`. The stronger intermediate identity is
`κ(K-d)=κ(ratCorr)+1` for every real `d>0`.

The mass-zero index of `K` equals the full global Weil index. Subtracting a
constant leaves this mass-zero index unchanged, so the usual hyperplane bound
gives the upper bound. If the global index is infinite, it also gives equality.

For finite global index, the zero-count identity makes the right-zero set
finite. Decompose `K` into its summable critical-line Bohr series and finitely
many reflected character pairs. Dense logarithms make every off-critical
character nontrivial. For each character `χ`, choose `u` with `χ(u)≠1`; the
finite measure `(δ_u−χ(u)δ_1)/(1−χ(u))` has mass one and annihilates `χ`.
Convolving these measures annihilates both characters of every pair.

Prepend the trivial character to the critical-character enumeration and use
finite Bohr box averages on `H`. Density separates the characters, and the
absence of real nontrivial zeta zeros separates every critical character from
the trivial one. Convolving these averages with the finite annihilator keeps
mass one and all pair evaluations zero. Absolute summability of the critical
weights and a uniform bound on the filtered character evaluations imply that
both self-energy and interaction with each fixed point tend to zero.

Append these mass-one families to any fixed negative family of total mass zero.
For `K-d`, the compressed Gram matrices converge to the block diagonal matrix
formed by the original negative block and the scalar `−d`. Lower
semicontinuity of negative inertia supplies one additional square.

Finally, for each slope coefficient `a_i`, put `a_i/2` at each of the shifts
`0,1`. Unit p-adic slopes make the successor term independent of the slopes;
the compressed Gram matrix is exactly that of `K−c/2`. The constant-subtraction
identity gives the affine lower bound. Restriction of the unrestricted native
state gives the matching upper bound. Closure of the p-adic unit ball under
ring operations proves `|b|_p≤1` throughout `R`.

## Certified declarations

- `negIndex_ratCorr_sub_constant_of_dense_log`
- `padic_le_one_twoPrimeRing`
- `twoPrimePrincipalAffine_shift_le_one`
- `negIndex_weilPadicState_twoPrimePrincipalAffine`

Direct source check and transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`. Umbrella import wired; no umbrella build.

## Consequence

Both full global negative index and the native successor square survive inside
a fixed two-prime affine group whose translations remain p-adically bounded.
Local boundedness therefore supplies no index reduction. Minimal prime support
and a source-specific two-place comparison remain separate questions.
