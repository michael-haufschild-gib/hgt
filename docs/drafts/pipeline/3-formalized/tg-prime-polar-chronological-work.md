# TG C9.11v — actual chronological ground work

- **ID:** tg-prime-polar-chronological-work
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** Exact native ordered-block cross work, prime-entry energy jump and continuous polar energy flow, with all original coefficients and signs.
- **Status:** final production leaf and all eight public axiom checks pass; wired and indexed; global lint reports eleven unrelated unwired leaves, no finding in this leaf.

## Hard problem and result

The hard problem remains unconditional Cauchy decay of the original ground
tails. C9.11u identified their critical arithmetic energy. This result now
identifies the actual work changing that energy.

Let f_a be the physical indicator of [-a,a], B_a(u)=exp(-u/2)D_exp(u)f_a,
and K(P,b,R) the original positive-logarithmic prime–polar source. Then

`<B_a(u),B_a(v)> = 2a exp(-v)` for u<=v,

and the actual source is

`K(P,b,R)f_a = sum_(p in P) B_a(log p) - integral_b^R ((exp(u)+1)/u)B_a(u) du`.

Write C(P,b,R;t) for the literal cumulative discrepancy proved in C9.11u.
For two chronologically ordered native blocks, with every earlier prime
logarithm <=R, every later prime logarithm >=R and later polar lower
endpoint c>=R,

`<K(P,b,R)f_a,K(Q,c,S)f_a> = 2a C(P,b,R;R) H(Q,c,S)`,

where the genuine later harmonic discrepancy is

`H(Q,c,S)=sum_(q in Q)1/q - integral_c^S (1+exp(-u))/u du`.

At a new prime p beyond all primes already in P, with the original polar
interval unchanged through log p, the energy jump is exactly

`2a (2 C(P,b,log p;log p)+1)/p`.

For fixed P and R>b beyond all prime logarithms in P, continuous polar
motion has exact energy derivative

`-4a (1+exp(-R)) C(P,b,R;R)/R`.

The interval/ordering conditions specify the finite configuration. There
is no arithmetic sign, decay, decorrelation or limiting-admission premise.
Neither result asserts a cutoff-uniform bound. The full symmetric source
still retains its separate nonnegative moment square from C9.11q.

## Dependency-closed paper proof

1. Multiply both sides of the audited normalized ground covariance by
   exp(-u/2) and exp(-v/2). For u<=v, all exponentials combine to exp(-v).
   The audited physical ground mass is 2a. This proves the entering-interval
   covariance on actual SoninL2.
2. At p, exp(-log(p)/2)=1/sqrt(p). For the polar integrand,
   `((exp(u)+1)/u)exp(-u/2)=2cosh(u/2)/u`. Thus the original source equals
   its entering-vector expression exactly. On a finite positive polar
   interval its vector integrand is continuous, hence strongly integrable.
3. Pair the earlier source with B_a(v) at v>=R. Every actual prime term
   contributes 2a exp(-v); the continuum contributes the same factor times
   its complete counting density integral. This is
   `2a C(P,b,R;R)exp(-v)`. Moving this identity through the entire later
   source gives the ordered-block factorization. The later exponential
   yields exactly 1/q and (1+exp(-u))/u; both polar terms remain.
4. Inserting a new prime adds B_a(log p) to the actual source vector.
   Expand its Hilbert norm square, use step 3 for the mixed term and step 1
   for the diagonal. The resulting jump retains both signed interaction
   and the harmonic diagonal 2a/p.
5. For R>b, the original Icc polar integral locally equals its oriented
   interval integral. Banach-valued FTC differentiates the source itself:
   its derivative is `-((exp(R)+1)/R)B_a(R)`. Differentiate the Hilbert norm
   square. The real L2 inner product equals the real part of the complex
   L2 pairing by integrability and scalar Fubini. Step 3 then gives the
   stated signed polar energy derivative.

## Frontier consequence and limit

An earlier counting discrepancy multiplies the later harmonic discrepancy.
An estimate for the latter alone cannot control arbitrary moving heads.
The actual energy must compensate its accumulated harmonic prime diagonal
through signed prime interaction and polar work. This is now an identity
of the original physical source, not a supplied scalar model.

The corpus's `CCMPrimeDeficitChronologicalWork` supplies only a lower work
bound for its Chebyshev storage; `CCMPrimeEntryWorkSampling` proves that
midpoint sampling only transfers the jump budget into work. Neither is an
upper bound for the native TG work. They were inspected, not assumed.

The complete finite integrated prime–polar work balance and its unconditional
cutoff-uniform cancellation remain to be proved. Full-response transport,
Gamma completion, Hardy compatibility and strict sub-unit control remain
open. RH has neither been proved nor falsified.

## Lean evidence

Leaf: `formal/GaloisForLFunctions/RHTower/SoninPrimePolarChronologicalWork.lean`.
Eight public declarations: entering vector, ordered covariance, source/entry
pairing, harmonic discrepancy, ordered native cross work, prime jump, vector
polar derivative and energy polar derivative. Wired into the RHTower umbrella.

Scratch audit `/tmp/tg-c911v-ordered.log` exited 0. Final leaf audit, public
axiom audit, index and global lint results are recorded below when complete.

Final foreground audit `lake --old env lean
GaloisForLFunctions/RHTower/SoninPrimePolarChronologicalWork.lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPrimePolarChronologicalWork.olean`
passed with exit 0 and empty diagnostics (`/tmp/tg-c911v-final.log`).
All eight public `#print axioms` queries passed with only `propext`,
`Classical.choice`, and `Quot.sound`: `/tmp/tg-c911v-axioms.lean` and
`/tmp/tg-c911v-axioms.log`. No added axiom, hole, numerical experiment,
heartbeat increase, full build or umbrella build was used.

Index refresh passed and all eight public names were verified in
`formal/LEAN_API.md`: `/tmp/tg-c911v-index.log`. Superseded owned proof drafts
were removed; audit scratch/logs and corpus search evidence are retained.

Global lint exited 1 with eleven unrelated modules unreachable from their
umbrella and no finding in this leaf: `/tmp/tg-c911v-lint.log`. All owned
processes have exited. The RH goal remains active and unmet.
