# The centralizer of prime translations

- **ID:** galois-zero-prime-translation-centralizer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Arithmetic symmetries of the full zero motive; Frobenius-compatible actions.

## Theorem

Let `Δ` be the entire integer zero group, `A=ℂ[Δ]`, and let prime
translation act by `T_p([z])=p^z[z]`. The complex-linear operators
commuting with `T_2,T_3` are exactly arbitrary diagonal multipliers.
The complex-algebra endomorphisms among them are exactly translations
by complex characters of `Δ`. An algebra endomorphism fixing
the identity point must therefore be the identity. The only ideals stable under both prime translations are `0` and `A`. Consequently
every nonnegative two-prime orbit through every complex motive point is
Zariski dense. In particular, the times `log(2^m 3^n)`, `m,n≥0`, determine
every regular function on the entire motive.

## Paper argument

If `2^z=2^w` and `3^z=3^w`, there are integers `a,b` with
`(z-w)log 2=2πia` and `(z-w)log 3=2πib`. Eliminating `z-w` gives
`a log 3-b log 2=0`. Prime-log independence forces `a=b=0`, hence `z=w`.
Thus the joint eigenspaces of `T_2,T_3` on `A` are precisely its individual
character lines. A commuting linear map preserves each such line; conversely
every diagonal multiplier commutes.

For an algebra endomorphism write `F([z])=c_z[z]`. Multiplicativity and
preservation of one give `c_(z+w)=c_z c_w`, `c_0=1`, and `c_z c_(-z)=1`.
Hence `c` is a complex unit-valued character, with no additional condition.
Conversely every such character gives a translation automorphism, whose
inverse uses the inverse character. Evaluation at the identity reads
`[z]↦1`; preserving that evaluation forces every `c_z=1`.

A nonzero stable ideal contains a nonzero element of least coefficient-support
size. If two distinct exponents occur, choose a prime translation whose
eigenvalues distinguish them. Subtracting one eigenvalue times the element
kills one coefficient without killing the other, contradicting minimality.
Thus the ideal contains a nonzero single character, which is a unit. This
proves difference simplicity on the full algebra.

The ideal of regular functions vanishing on a nonnegative two-prime orbit
is stable under both translations. It is proper because one does not vanish.
Difference simplicity therefore makes it zero, proving orbit density.

## Boundary

The statement concerns complex-linear operators and complex-algebra maps.
It does not exclude semilinear arithmetic actions. Prime translations are
operators on the full infinite coordinate algebra; no finite-height zero
model is substituted. The classification does not establish purity.

## Formalization

`GaloisForLFunctions/GaloisTheoryOfZeros/TheCentralizerOfPrimeTranslations.lean`:

- `two_prime_exponential_injective`, `zeroMotive_joint_eigenvector`.
- `primeTranslation_linear_centralizer`.
- `primeTranslation_algebra_centralizer`.
- `primeTranslation_commuting_endomorphism_bijective`.
- `primeTranslation_pointed_centralizer`.
- `primeTranslation_stable_ideal_iff`.
- `zeroMotivePrimeOrbitEvaluation_injective`.
- `zeroMotive_eq_iff_twoPrimePower_values`.

Final direct source check passed without warnings. All 11 dependency audits
use only `propext`, `Classical.choice`, `Quot.sound`.
