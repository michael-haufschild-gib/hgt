# BAG connected-pair versus signed-cubic separation

- **ID:** BAG-C28.56v
- **Stage:** 3-formalized
- **Status:** unconditional positive counterexample family; production and axiom audits pass.
- **Failed conjecture:** uniform connected quadratic mixing plus actual prime support,
  unit coefficient energy and vanishing individual coefficients controls the signed cubic.
- **Positive survivor:** the SAME actual-prime packets have uniform connected quadratic
  decay and divergent signed noncontracting physical cubic.

## Exact unconditional theorem

Leaf: formal/GaloisForLFunctions/RHTower/ChiPrimePacketConnectedCubicSeparation.lean.
Namespace: RHTower.PrimePacketThinning.

exists_prime_packets_connected_mixing_cubic_divergence constructs one C>0 such
that eventually for every natural K there exist N and a finite actual-prime set S:

    64K^64 <= N <= 128K^64,
    card(S) > K^23/2,
    S subset primes intersect [N,N+K^32].

The normalized coherent prime polynomial has coefficient energy exactly1 and
maximum coefficient<=1/K. Simultaneously:

- For EVERY real beta in[1/2,2] and EVERY centre t, its complete critical-height
  Gaussian average minus the EXACT diagonal Gaussian packet has norm<=C/K.
- Its ORIGINAL signed physical chi cubic, with both repeated-prime contraction
  families removed (p!=r and q!=r), is at least T*K^2/1024, T=4piN/3.

packetAverage is the literal height integral of the normalized prime polynomial
and its conjugate, with the real twist and the full Gaussian. packetDiagonal
retains the complete p=q packet even arbitrarily near beta=1.
packetAverage_sub_diagonal identifies their difference with the complete
connected spectral sum. No frequency, tail, physical remainder or contraction
exclusion is omitted. No sampling, prime-location, moment or cancellation
premise occurs in the capstone.

This does NOT determine the full Gaussian band's cubic or prove/falsify RH.
The packet scale and physical window are explicit in the theorem. The full
Gaussian source's diffuse coefficients and joint arithmetic weights remain
additional structure that any successful BAG proof must use.

## Source basis and novelty audit

ChiPrimePacketFourthMoment.eventually_exists_dense_prime_packet constructs the
actual dense prime support by source PNT and finite pigeonhole.
ChiPrimePacketCubicMoment.exists_coherentPrimePacketCubicOffDiagonal_positive
proves the signed physical lower bound for EVERY finite subset of a coherent
short interval; all literal chi/window remainders are already paid.
ChiPrimeGaussianGrowingTwists.exists_connected_negligible_error supplies the
preceding full-band quadratic producer. The present theorem tests and refutes
a generic promotion of its quadratic conclusion to cubic control.

Corpus queries for connected/cubic separation and packet thinning found the
prior flat-coefficient obstruction but no simultaneous quadratic/cubic family.
The later Gaussian-identity query was nonpartial over65256 files, with compiler
coverage mostly source-only and semantic coverage unmeasured. Actual source
signatures and proofs were checked in Lean; search status was not treated as
proof. Bernoulli independence and Hoeffding come from the installed mathlib.

## Dependency-closed proof

Set m=K^8 in the source dense packet: H=K^32, N~K^64 and M0>=K^24.
Retain each prime independently with probability1/K. For each positive shift h,
the edge graph {a,a+h} splits into two matchings by parity of floor(a/h).
Indicators inside each matching are independent. Hoeffding bounds each bad
matching event and the bad vertex-count event by exp(-M0/(8K^4)). A finite
union over every1<=h<=H and both matchings has mass below1 for large K.
Thus some deterministic selected S has

    card(S) > M0/(2K),
    card{a in S : a+h in S} < 8card(S)/K for every1<=h<=H.

Negative differences use the opposite projection, so the same bound controls
EVERY nonzero integer difference fibre. The probability argument only selects
S. Its physical cubic is proved by the source theorem valid for every such S;
no random-law statement is substituted for a physical height integral.

For p,q in[N,N+H], put c=(beta-1)N, d=p-q-c and e=p-beta*q. Since H>=1 and
2H^2<=N,

    N|d| <= N|e|+H|c|,
    |c| <= |d|+H,
    hence |d| <= 2|e|+1.

With z=floor(c), (p-q-z)^2<=8e^2+8. The source logarithmic mean-value bound
then dominates the ENTIRE critical Gaussian kernel by
exp(1)*exp(-(p-q-z)^2/256), uniformly for0<beta<=2. Its full integer mass is
at most4(1+4sqrt(pi)). Dividing by card(S) proves the stated connected bound
with C=32exp(1)(1+4sqrt(pi)); no separate far-twist truncation is needed.

The source signed physical cubic lower bound survives every subset. After
unit-energy normalization it is at least(pi*sqrt(N)/16)*card(S)*sqrt(card(S)).
The selected cardinality and N<=128K^64 give the polynomial lower bound
T*K^2/1024. This proves the simultaneous positive survivor, not merely a
negative statement about a proposed estimate.

## Lean and audit record

- Leaf955 lines; capstone at913. Public helper at350 constructs the thin primes;
  exact physical connected decomposition at883.
- Production14031: exit0, no diagnostics, lake --old env lean on the leaf with
  its output olean. Log /tmp/bag-packet-separation-final-01a0.log.
- Axiom13295: exit0. All SIX public declarations depend exactly on propext,
  Classical.choice and Quot.sound. Printed capstone has no outside hypotheses.
  Log /tmp/bag-packet-separation-axioms-01a0.log.
- RHTower umbrella wired; no umbrella or full build.
- Index29684: exit0; generated API/gaps/overview and search index refreshed.
- Lint18740 (--check-generated): exit1,17 unrelated unreachable modules, no
  generated-index error and no finding for this leaf. Existing size warnings
  concern other files. Log /tmp/bag-packet-separation-lint-01a0.log.
- No numerical experiment, added axiom, heartbeat increase or subagent.

## Remaining BAG frontier

Generic quadratic-to-cubic promotion is refuted. The positive actual-prime
family is fully formalized. BAG itself remains OPEN. Next attack must concern
the COMPLETE signed Gaussian cubic/zero aggregate with the literal source
weights and nonzero removed-contraction main, retaining moving Mellin weights,
nearby distinct zeros, all finite exponent pairs and mixed terms. Growing
moments, moving-cofactor transfer, positive self-return and RH remain open.
