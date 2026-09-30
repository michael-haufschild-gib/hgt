# Prime and prime-square normal jets give a two-level line classifier

- **ID:** `theta-prime-square-two-level-normal-jet-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM and sharp arithmetic phase receiver
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist
- **Status:** `[ALGEBRAIC CORE LEAN-PROVED] [SOURCE-JET BRIDGE LEAN-PROVED: GaloisForLFunctions.RHTower.ThetaPrimeSquareNormalJetRigidity] [NOT AN RH PROOF]`
- **Dependencies:** exact finite theta deletion factorization in [prime-deletion spectral escape](theta-prime-deletion-spectral-escape.md); the reflected local-factor cosine identity in `PrimeEulerCommonClockRigidity.lean`; the all-power comparison in `PrimePowerCommonClockRigidity.lean`.

## Exact source-jet action

Write `F(w)=∫ℝ exp(wx)k(x)dx=XiC(iw)`. For a prime `p` and
`j=1,2`, let

```text
D_(p^j)=1−p^(−j/2)T_(j log p),
k_(p^j)=D_(p^j)k.
```

These are literal source operations: `k_(p^j)` removes exactly
the Gaussian atoms whose integer labels are divisible by
`p^j`. Writing `A=p^(−1/2)T_(log p)` gives the source identity
`D_(p²)=1−A²=(1+A)D_p`; the second level is a polynomial in
the same prime translation, so its phase is exactly doubled.
Their entire transforms are

```text
F_(p^j)(w)=F(w)(1−p^(−j(1/2+w))).                 (1)
```

Let `w₀` be an interior Xi zero of multiplicity `m`. The first
nonzero transform jet is transported by the same factor:

```text
F_(p^j)⁽ᵐ⁾(w₀)
  = F⁽ᵐ⁾(w₀)(1−p^(−j(1/2+w₀))),   j=1,2.         (2)
```

Indeed every lower derivative of `F` vanishes at `w₀`, so all
other Leibniz terms disappear. No simple-zero assumption is
needed. The factor in (1) is nonzero for `|Re w₀|<1/2`, so this
really is the first nonzero jet at both deleted stages.
Functional equation and realness give equal magnitudes
for the base normal jets at `w₀` and `−conj(w₀)`.

## Two-level rigidity

Write `w₀=σ+it` with `|σ|<1/2`, and put

```text
r₊=p^(−1/2+σ),  r₋=p^(−1/2−σ),  θ=t log p.
```

Suppose the **deleted** normal jets in (2) have equal reflected
magnitudes at both levels `j=1` and `j=2`. After canceling the
nonzero equal-magnitude base jets, this says

```text
|1−r₊ exp(iθ)|=|1−r₋ exp(iθ)|,
|1−r₊² exp(2iθ)|=|1−r₋² exp(2iθ)|.             (3)
```

Then `σ=0`.

For `σ≠0` the radii are distinct. Squaring the first equality
gives `cos θ=(r₊+r₋)/2`; squaring the second gives
`cos(2θ)=(r₊²+r₋²)/2`. The double-angle identity forces
`r₊r₋=1`, but the literal Euler normalization fixes
`r₊r₋=1/p<1`. Contradiction. This proof uses only one prime,
its square, and a shared phase; no prime distribution, power
recurrence, or limit is involved. The algebraic implication is
proved in Lean as
`epsilon_eq_zero_of_prime_and_square_reflected_modulus_neutral`
in `PrimeSquareTwoLevelReflectedRigidity.lean`.

One level is insufficient: for any physical distinct radii
`0<r₊,r₋<1`, their average lies in `(0,1)`, so choosing
`θ=arccos((r₊+r₋)/2)` satisfies the first equality in (3).
The second level is therefore the first possible rigidity
test of this type.

## What remains hard

Equation (3) is **not** a property of finite deleted theta
sources supplied by evenness of `k`: one-sided deletion breaks
reflection. Symmetric deletion restores reflection but the
[prime-deletion card](theta-prime-deletion-spectral-escape.md)
proves it loses positivity and endpoint charge. Thus (2)–(3)
reduce the desired phase law to a concrete two-grade boundary
comparison, but do not prove that comparison. The graded
admission theorem in
[terminal admission](theta-prime-deletion-graded-terminal-admission.md)
shows the `p` and `p²` sources live at different weighted
thresholds, `2/p²` and `2/p⁴`; a source-faithful comparison must
cross those grades without discarding the singular cusp term.
The [two-packet interpolation countermodel](theta-compact-critical-strip-zero-engineering.md)
also preserves positivity on the right ray after every finite
literal prime deletion while forcing an off-line zero; right-ray
positivity cannot supply the missing reflected jet balance.

This is a sharper finite receiver than all-power neutrality,
not an RH proof. External novelty has not been established.
No computation or zero-location premise was used. The frontier
map was read only. The new Lean module passed `lake env lean`
and targeted `lake build ...:olean`; repository formal lint also
passed. No umbrella build or axiom audit was run.

## Log
- 2026-09-27 — source identities (1), jet transport (2), reflected base-jet moduli, two-level classifier (3) on source jets and one-level insufficiency formalized unconditionally (`ThetaPrimeSquareNormalJetRigidity`, certificate `theta-prime-square-two-level-normal-jet-rigidity-formalized.md`); moved to 3-formalized.
