# EDQ reflected logarithmic Gram boundary

Stage: 3-formalized; dependency-closed paper proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
RH status: the reflected pairing below retains a universal arithmetic boundary; no horizontal selector.

The critical-line partner is r=1-conjugate(s). Its phase agrees with that of s, so the actual
pointwise Hermitian pairing of deletion jumps at s and r is exactly a_p(n)*a_q(n)/n, where
p,q are literal positive moduli and a_p(n)=1-p[p divides n]. No zero premise enters this identity.

Write g=gcd(p,q), l=lcm(p,q). The full pointwise coefficient identity is

`a_p(n)*a_q(n) = (g-1)+a_p(n)+a_q(n)-g*a_l(n)`.

It follows from p*q=g*l and the equivalence l|n iff p|n and q|n. With H_N=sum_(1<=n<=N)1/n,
the exact reflected bracket is

`B_pq(N)=(g-1)*H_N+D_p(N)+D_q(N)-g*D_l(N)`,

where D_p is the ordinary harmonic deletion prefix. The corpus proves D_p(N)→log(p).
Therefore B_pq(N)-(g-1)*H_N has limit

`K(p,q)=log(p)+log(q)-g*log(l)`.

For coprime p,q, K=0 and there is no logarithmic divergence. For p=q>1 the logarithmic
coefficient is p-1 and the finite part is (2-p)*log(p). In particular the modulus-three finite
part is strictly negative. Removing the divergent positive covariance does not leave a
positive inner product automatically. The finite Gram is positive for every real linear
combination, by its literal sum-of-squares representation. The finite part is indefinite:
on moduli 2 and 4 its matrix is log(2) times [[0,-1],[-1,-4]]. The vector (-3,1)
has quadratic value 2*log(2)>0, whereas (0,1) has value -4*log(2)<0.
Thus neither global sign of the renormalized form can supply an inner product.
This follows symbolically from gcd/lcm and log(4)=2*log(2), without numerical evidence.

The exact finite quasi-shuffle identity transfers this full bracket into the symmetric sum of
the two actual chronological cross prefixes. In the positive strip both ordinary endpoints
converge. Thus the symmetric cross sum plus (g-1)*H_N tends to its full endpoint product
minus K(p,q). Replacing H_N by log(N) changes the limit by
-(g-1)*EulerMascheroniConstant; this constant is retained. At simultaneous zero landing the endpoint product vanishes. For distinct
coprime channels the individual chronological cross limits already exist on the whole positive
quadrant, and the reflected symmetric limit is zero. These statements retain their full
chronological cutoff and all diagonal terms; they provide no off-line contradiction.

Corpus inputs inspected: EulerDeletionCoprimeCrossCompletion, EulerDeletionQuasiShuffleCrossDomain,
EulerDeletionQuasiShuffleSecondConvergence, EulerDeletionCurvatureCriticalBoundary,
EulerDeletionWeightedFifthCirculation, and EulerDeletionMixedDecompositionFinite.

Remaining task: an independent comparison beyond this displacement-independent symmetric
pairing, retaining the logarithmic diagonal and the actual nonsymmetric chronological part.


## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionReflectedLogarithmicGram.lean`
(298 lines; 17 public theorems, five public definitions, three private lemmas).
Namespace: `RHTower.DeletionReflectedGram`.

- `coefficient_product`, `gramPrefix_decomposition`, `gramPrefix_sub_harmonic_tendsto`: exact gcd/lcm coefficient law, finite cutoff decomposition, and complete finite part.
- `coprime_boundary`, `diagonal_boundary`, `finitePart_three_neg`, `finitePart_two_four_indefinite`: sharp coprime and diagonal values, with explicit opposite signs on the moduli-two-and-four plane.
- `reflected_jump_pair`, `reflected_bracket_eq`, `reflected_chronological_decomposition`: literal complex reflected source, full bracket, and both chronological orders at every cutoff.
- `gram_quadratic_eq`, `gram_quadratic_nonneg`: full finite sum-of-squares identity and positivity for arbitrary real channel combinations.
- `symmetricCross_harmonic_tendsto`, `symmetricCross_log_tendsto`: strip limits with actual endpoint product, full gcd residue, and Euler constant retained.
- `symmetricCross_at_nontrivial_zero`, `symmetricCross_log_at_nontrivial_zero`: unconditional specializations to every actual nontrivial zero, without a simplicity or location premise.
- `coprime_cross_limits_at_nontrivial_zero`: separate actual ordered limits and their adjoint-negative relation.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_loggram.lean`, exit 0, no diagnostics.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionReflectedLogarithmicGram`, exit 0. The new leaf rebuilt in 5.7 seconds; three required dependencies also rebuilt (`EulerDeletionFullEnergyFactorization`, `EulerDeletionCoprimeCrossCompletion`, `EulerDeletionCurvatureCriticalBoundary`). Other dependencies were cached/replayed. Umbrella import added; no full or umbrella build.
New-only axiom audit: `lake env lean /tmp/edq_loggram_axioms.lean`, exit 0. All 22 public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; private lemmas are covered by that closure. No added axioms, admissions, numerical premises, or external computation certificates.

Repository `scripts/formal_tools.py lint` ran once and passed, with existing file-size warnings.
The search index was refreshed once. Owned scratch Lean sources were removed after validation;
logs remain under `/tmp/edq_loggram` with `.api.log`, `.check.log`, `.build.log`, `.axioms.log`,
`.lint.log`, and `.index.log` suffixes.

RH remains unproved and unfalsified. The positive survivor is the exact reflected arithmetic
covariance and complete chronological boundary law. It prevents silently discarding a divergent
diagonal or inheriting positivity after subtraction; it does not supply the missing location
comparison. No whole route is retired.
