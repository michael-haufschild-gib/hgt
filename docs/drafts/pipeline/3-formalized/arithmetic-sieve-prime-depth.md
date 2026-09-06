# Exact information retained by the arithmetic coprime sieve

**Stage:** 3-formalized. **Scope:** finite inverse, exact two-point ambiguity, and a separating prime-depth observation. No RH implication is established. [Candidate and mechanism audit](../1-in-progress/arithmetic-sieve-prime-depth.md).

## The complete sieve family is a change of coordinates

For `Re(s)>0`, `s!=1`, retain the literal quantities from `ArithmeticPrimeSievePhase`:

`g_s(n)=n^(-s)conjugate(R_s(n))/D`, `D=conjugate(s)(conjugate(s)+1)`,

`R_s(n)=sum_(1<=j<=n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`,

`W_m=m^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(mn))`,

`b_m=mu(m)W_m/(mD)`, `C_M=sum_(gcd(M,n)=1)g_s(n)`.

The existing forward identity is `C_M=sum_(d|M)b_d`. The new finite inverse is

`b_m=sum_(uv=m)mu(u)C_v`.

Both hold for every positive modulus. Consequently the full coprime-sieve record and the full earlier Möbius-weighted modulus record determine each other. Finite combinations or nonlinear functions of the first record cannot count as additional independent data merely because they use a new representation. Such a representation could still help prove an estimate; no such estimate is supplied here.

## Exact two-point ambiguity

For an arbitrary absolutely summable complex sequence `f` on positive integers, write

`C_M(f)=sum_(gcd(M,n)=1)f(n)`.

Let `h=z delta_a-z delta_b`, with positive integers `a,b` and `z!=0`. Its observation is exactly

`C_M(h)=z[gcd(M,a)=1]-z[gcd(M,b)=1]`.

Lean proves that `C_M(h)=0` for every positive `M` **if and only if** `a` and `b` have the same set of prime divisors. Forward: any prime dividing precisely one endpoint supplies a separating modulus. Reverse: coprimality depends only on the two prime-divisor sets. This includes the unit and identical-endpoint cases correctly; a zero transfer amplitude is explicitly excluded from this equivalence.

Thus the coefficient-recovery conjecture N is false even when every coprime modulus is observed. No numerical witness is used.

## Literal-source application, with its limits retained

For any complex amplitude `z`, define the auxiliary sequence

`f_(s,z)(n)=g_s(n)+z[n=2]-z[n=4]`.

Lean proves:

- `f_(s,z)` is absolutely summable on the admitted half-plane.
- `C_M(f_(s,z))=C_M(g_s)` for **every** natural modulus `M`.
- `f_(s,z)(1)=g_s(1)` and `f_(s,z)(n)=g_s(n)` for every `n>4`.
- Its scaled first coefficient is therefore exactly the same: `n^(2 Re(s)+1)f_(s,z)(n)->-1/[12(conjugate(s)+1)]`.
- Given any desired complex value `w`, choosing `z=w-g_s(2)` sets `f_(s,z)(2)=w` while preserving the preceding observations, unit value, and eventual tail.

The zero-boundary relation of the unit term is consequently preserved as well. **The unit coefficient is not hidden by this example.** This ambiguity does not prove that a sign law for that unit term is impossible.

For nonzero transfer, the auxiliary sequence differs from the literal remainder at indices 2 and 4. It is not asserted to satisfy the ordinary remainder's exact finite recurrence, its full set of source identities, or the same pointwise error constants at those indices. It is not a counterexample to RH or an alternative zeta function. The theorem identifies the insufficiency of the listed observations for recovering finite coefficients, not the insufficiency of every property of the actual arithmetic source.

## Positive survivor: prime-depth measurements separate the ambiguity

Define `D_d(f)=sum_(d divides n)f(n)`. Then

`D_d(h)=z[d divides a]-z[d divides b]`.

Lean proves that these values vanish for every positive `d` **if and only if** `a=b`. The two directions `d=a` and `d=b` give mutual divisibility, hence equality. This is a sharp two-point classification, not a claim of a newly proved full infinite inversion theorem.

For the literal-source perturbation,

`D_4(f_(s,z))=D_4(g_s)-z`.

The measurement at prime depth two therefore detects the whole amplitude lost by coprime sieving. The corpus already provides full Möbius inversion of the actual multiples family under its proved summability conditions; recovering that data alone still does not supply an RH exclusion law.

## Formal certificate

Module: `GaloisForLFunctions.RHTower.ArithmeticSievePrimeDepth`; namespace: `RHTower.DeletionMixedRefinement`.

Principal theorems:

- `minimumBalanceTerm_eq_finite_sieve_inverse`
- `coefficientTransfer_invisible_iff`
- `coprimeObservation_redistributedRemainder`
- `tendsto_redistributedRemainder_scaled`
- `exists_redistribution_with_prescribed_coefficient`
- `coefficientTransfer_divisibility_invisible_iff`
- `divisibilityObservation_redistributedRemainder_four`

The complete scratch development and published source passed `lake env lean`. The single leaf passed `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticSievePrimeDepth`; it is wired into the RHTower umbrella. No full or umbrella build was run.

All eleven public declarations—seven theorems and four definitions—passed a separate `/tmp` `#print axioms` audit. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. No new mathematical axiom, unproved arithmetic premise, numerical result, or computational certificate is used. All owned Lean invocations completed; no owned Lean process remained after verification.

The refreshed corpus index retrieves the finite inverse. `scripts/formal_tools.py lint --check-generated` passed with exit code 0 and reported 132 existing large-file warnings. The proof mechanisms are elementary divisor inversion, exact coprimality, finite support, and the previously checked remainder asymptotic. No exploratory computation was needed, and no literature novelty claim is made.
