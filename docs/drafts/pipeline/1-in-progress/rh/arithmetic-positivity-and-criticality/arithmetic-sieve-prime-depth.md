# Prime-depth information in the arithmetic sieve family

**Stage:** candidate audit complete; parent RH exclusion problem remains open. **Outcome:** N refuted symbolically; P and Q proved in `ArithmeticSievePrimeDepth`. [Formal scope and certificate](../../../3-formalized/arithmetic-sieve-prime-depth.md). **RH chain:** complete arithmetic data -> independent source constraint -> exclusion of off-line zeros. The existing phase sign is still only a location equivalence. This audit tests whether the entire coprime-sieve family retains the finite coefficient data proposed as the next source of such a constraint.

## Candidate and falsification

**N — coefficient recovery from complete coprime data.** For absolutely summable complex sequences on positive integers, equality of every coprime sum `C_M(f)=sum_(gcd(M,n)=1)f(n)` determines every coefficient. All positive moduli, not just initial prime prefixes, are included.

The symbolic attack identifies a counterexample: `delta_p-delta_(p^2)` is invisible to every coprime test because `gcd(M,p)=1` iff `gcd(M,p^2)=1`. This is an auxiliary coefficient perturbation, not a new ordinary zeta remainder. It disproves N and does not disprove an identity restricted to the literal source.

The already established first coefficient and unit value do not remove this ambiguity. A transfer between indices 2 and 4 changes neither the unit coefficient nor any eventual tail value. Thus the same transfer applied to the literal normalized remainder preserves the entire sieve history, its limiting unit term, its exact zero-boundary relation, and its first asymptotic coefficient, while changing finite coefficients. This observation is a consequence of the counterexample, not a silently weakened replacement for N.

## Frozen sharp survivor

**P — exact two-point classification and a separating measurement.** A nonzero transfer `z delta_a-z delta_b`, for positive integers `a,b`, is invisible to every positive-modulus coprime sum if and only if `a` and `b` have the same set of prime divisors. In particular, all primes and their positive powers are indistinguishable by these tests. For the transfer from 4 to 2, the sum over multiples of 4 changes by exactly `-z`, so a divisibility measurement retaining prime depth separates it.

Paper proof: the sum against one coprime test is `z[gcd(M,a)=1]-z[gcd(M,b)=1]`. Equality of prime-divisor sets makes those two indicators equal. Conversely choose `M` equal to a prime dividing precisely one of `a,b`; the nonzero transfer is then visible. At multiples of 4, the coefficient at 2 is absent and the coefficient at 4 is present. The asymptotic preservation follows from exact equality after the larger modified index, and summability is preserved by finite support.

Formalize this classification and the literal-source perturbation package, without introducing any computed values or unproved arithmetic premise.

## Independently frozen finite inverse

**Q — exact equivalence with the earlier arithmetic family.** For the literal normalized terms `b_m=mu(m)W_m/[m conjugate(s)(conjugate(s)+1)]`, the already proved identity is `C_M=sum_(d|M)b_d`. Finite divisor inversion should recover every `b_m` from the same data as `b_m=sum_(d|m)mu(d)C_(m/d)`. This is a candidate exact inverse, motivated by the source identity and the corpus's finite Möbius inversion. It is not an extra estimate.

The paper proof is finite Möbius inversion on the positive divisors of each modulus. If established, it proves that the entire prime-sieve family and the earlier Möbius-weighted modulus family contain precisely the same information. It does not equate either family with the unweighted depth-sensitive multiples data. Thus changing to all coprime moduli is a potentially useful coordinate change, but cannot by itself add a new arithmetic premise.

## Interpretation and limits

The unit coefficient is recoverable by increasingly exhaustive coprime sieving; it is **not** hidden by this example. Therefore this information-loss theorem does not explain or solve the missing unit-phase sign. Its precise consequence is that all coprime observations cannot reconstruct detailed prime-power coefficients or certify the ordinary remainder's finite recurrence. Any proposed argument using those coefficients must retain the corresponding source information separately. The actual multiples family already has a proved Möbius inversion; merely recovering the coefficients is also not an RH exclusion law.

## Corpus audit

Searches covered signed cycles, remainder differences, finite holonomy, prime exchange, conditional expectation, noncommuting arithmetic, finite nonlinear reconstruction, prime derivatives, chronological orientation, radical sums, prime depth, and valuation cylinders. Reads included `FinitePrimeCoefficientDifferentialField`, `EulerDeletionFiniteStatisticLaw`, `EulerDeletionMixedRefinementCarry`, `EulerDeletionJointNilpotentWitness`, the prior mixed-area rank card, and `ArithmeticPrimeSievePhase`.

Finite prime-derivative stability and static Boolean statistics already have source laws in the corpus; they did not supply a new zero-specific constraint. The mixed-area rank candidate already failed numerical diagnostics and is not reopened. The new precise target is the information retained by **all** coprime-sieve observations of the actual remainder package. No exhaustive literature novelty claim is made, and no excluded spectral or completed-function route is adopted.

## Closure and positive residue

The coefficient-recovery assertion N fails by an exact, finite, symbolic transfer. Its positive residue is fully formalized: the exact same-prime-support classification, a prime-depth measurement recovering the transfer amplitude, and an arbitrary prescribed finite coefficient with all listed sieve/unit/tail data retained. Independently, Q proves the complete finite inverse between the actual old and new arithmetic records. These results do not retire every use of those records, and do not prove that an arithmetic RH identity is impossible.

The scratch and source checks, serialized leaf build, all eleven public axiom audits, index refresh, and `lint --check-generated` passed. Only standard logical axioms were reported; no numerical inputs were used. No new exploratory computation was needed because the counterexample and separating test follow exactly from divisibility by 2 and 4.

The hard source problem remains unchanged: derive an independent arithmetic constraint on the actual remainder that excludes off-line zeros. The current coordinate change does not supply one, and the auxiliary redistributions must not be presented as alternate actual remainders. Exact prime-power data and the source's finite recurrence remain available information; no theorem here proves that they force the needed sign.
