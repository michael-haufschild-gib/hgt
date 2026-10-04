# PM prime-square source decomposition

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeSquareDecomposition.lean`.
- **Frontier effect:** the canonical source on the square scale now has an exact full-source/prime/semiprime decomposition and a square-inclusive mass bound. The joint sign and complete signed-energy compensation remain open.

## Exact statements

For every real epsilon, natural P>=2 and P^2<=X<2*P^2,

`F_<P,epsilon(1/X) = A_epsilon(1/X) + sum_(P<=q<=X prime) q^(-epsilon)*A_epsilon(q/X) + mass_epsilon(P,X)`.

The positive mass sums n^(-epsilon) over rough composite integers n<=X
whose prime factors are all at least P. Every such integer is a product
of two primes at least P, including equal primes. For epsilon>=0,

`mass_epsilon(P,X) <= (J^2+J)/2 * P^(-2*epsilon)`,

where J counts primes in `[P,X/P]`. These are statements about the actual
finite-prime source, without RH, convergence or L2-admission premises.

## Proof

An integer with at least three prime factors, counted with multiplicity,
all at least P is at least P^3. Thus below 2*P^2 the rough inverse has
only its unit, prime and two-prime sectors. On each composite term the
actual source lies in its first band and equals one. This gives the exact
decomposition. Each rough composite belongs to the product image of the
unordered pairs of primes in `[P,X/P]`. The finite symmetric square has
cardinality `(J^2+J)/2`; this includes its diagonal. Finally n>=P^2 and
epsilon>=0 give the pointwise weight bound.

## Audit

- Scratch and targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSquareDecomposition:olean` passed; only this leaf newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeSquareDecomposition.lean` passed with empty output.
- All three exports have only `propext`, `Classical.choice`, `Quot.sound` in the `/tmp` axiom audit.
- Wired once into RHTower; no umbrella build. Index passed, all three exports present.
- Global lint reports twelve unrelated unreachable modules, no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, resource-limit increase, commit or push.

## Next hard step

Combine the actual negative prime-convolution limit with uniform prime
counting and the negligible full source. The target is uniform negative
core sign on `3*P^2/2<=X<=7*P^2/4` for sufficiently small positive epsilon.
The complete signed prime-update energy still requires compensation.
