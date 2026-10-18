# Horizon radical state and exact defect normal form

- **ID:** thim-horizon-radical-state
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** `R_N(k)=gcd(k,primorial N)` is the complete minimal positive state for all squarefree-supported sieve observers. Multiplication becomes lcm; active sawtooth endpoints factor through this state, while defects acquire an exact nonpositive energy correction.

## Scope and plan

1. Audit corpus for squarefree observation-state duplication and verify arithmetic APIs.
2. Prove completeness, minimality, multiplication, and the defect normal form on paper.
3. Formalize one leaf in the assigned field, audit all declarations, wire umbrella, run lint.
4. Update `logs/thim-radical-sawtooth-knowledge.md` and remove scratch files.

`update_plan` is unavailable; this card tracks work. Period-drift work is now assigned to
another README track, so this contribution focuses on the radical quotient itself.

## Corpus evidence and boundary

- Prior contribution proves invariance under divisor multiplication and common powers,
  plus equal-response defect dissipation for endpoints at least two.
- `FiniteMultiplicativeObservationState` classifies arbitrary weights by the lcm of
  active divisors. The squarefree-only observer class has a strictly different canonical
  state: prime exponents and primes beyond the horizon are invisible.
- Mathlib supplies squarefree primorials, prime divisibility of primorials, and squarefree
  divisibility into primorials. Corpus search found no equivalent squarefree sieve state.
- Initial hybrid search partial at 45 seconds; lexical and exact source checks used for
  local coverage. No global mathematical novelty claim.

## Proved theorem package

- `R_N(k)>0`, squarefree, divides both `k` and `primorial N`.
- For squarefree `d<=N`, `d|R_N(k)` iff `d|k`.
- Equality of `R_N` exactly matches equality of every squarefree-supported sieve response.
- `R_N(kl)=lcm(R_N(k),R_N(l))`; image exactly the divisors of the primorial.
- Both active sawtooth endpoints factor through `R_N`.
- For positive `k`, with `r=R_N(k)`,
  `2(D_N(k-1)-D_N(r-1))=-Σ_{j=r}^{k-1}(s_N(j+1)-s_N(j))²`.
- Equality of defects iff every intermediate step is flat. Canonical representative
  maximizes defect among positive observations in its squarefree observation class.
- Every global upper bound on all prefix defects is equivalent to the finite set of
  tests at predecessors of divisors of `primorial N`.
- For nonnegative damping and `R_N(k)<=2N`, the defect at `k-1` is nonpositive;
  Möbius follows at zero damping. This permits independent prime exponents and rough factors.

## Gates

- [x] Corpus frontier and domain identified.
- [x] Dependency-closed paper proof.
- [x] Original-source Lean and all-declaration axiom audit.
- [x] Umbrella/index/lint, ledger, artifact audit, cleanup (global lint exceptions below).

## Paper proof [PROVED HERE]

Let `P=primorial N`, `R(k)=gcd(k,P)`. Since `P` is a positive product of distinct primes,
`R(k)` is positive and squarefree and divides `k,P`, even at `k=0`. For squarefree
`d<=N`, mathlib's primorial divisibility gives `d|P`; hence `d|R(k)` iff `d|k`.
Every squarefree-supported sieve summand is therefore unchanged by `k -> R(k)`.

Conversely, equality for every such weight can be tested with the indicator weight of
each prime `p<=N`. This detects `p|k`. Thus all prime divisors of the two squarefree
states agree, forcing equality. The state fixes every divisor of `P`, so its image is
exactly that divisor set. Since `R(k)|k`, it is the smallest positive representative.
Prime divisibility of products is disjunction, so
`R(kl)=lcm(R(k),R(l))`: multiplication in this quotient is idempotent.

Harmonic division preserves squarefree support; both active sawtooth endpoint formulas
therefore factor through the same state. For positive `k`, write `r=R(k)<=k`. Extend
the known polarization identity to empty prefixes (both sides vanish), subtract its
instances at `k-1` and `r-1`, and split the energy interval at `r`. The sieve endpoint
responses agree, giving the exact defect normal form above. Every summand is a square,
so the representative maximizes the defect among positive observations in its class, with equality exactly when
each intermediate additive step is flat.

For any real `B`, therefore, `∀M,D_N(M)<=B` iff
`∀r|primorial N,D_N(r-1)<=B`: the forward implication selects those prefixes, and the
reverse applies the canonical upper comparison to `k=M+1`. This is a finite exact
global certificate, including horizon zero and empty prefixes, not just a cofinal bound.

For damped weights with `ε>=0` and `r<=2N`, if `r=1` the canonical defect is `D(0)=0`;
otherwise the previously audited octave checkpoint theorem at exponent one gives
`D(r-1)<=0`. The normal form yields `D(k-1)<=0`. Set `ε=0` for Möbius.
The comparison is valid at every horizon; no upper bound on `k` is introduced.

## Formal verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/HorizonRadicalStateAndDefectNormalForm.lean`.
- Twenty public theorems and one public definition. Actual source compiled with
  `lake --old env lean -o <leaf.olean> <leaf.lean>`: exit 0, no warnings.
- Separate scratch import and `#print axioms` for all 21 public exports: exit 0.
  Every closure is exactly `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA-256: `06d29cef6c6307b1b4785bcedca16e672a84e6decddeb04eb46c0dfc9e56d654`.
- Imported once by the field umbrella, itself imported by `MainTheorems`; all public
  exports present in generated API. No full or umbrella build performed.
- `scripts/formal_tools.py index`: exit 0. `scripts/formal_tools.py lint --check-generated`:
  exit 1, with eight unrelated-area unreachable modules and the existing field-umbrella
  registration error. No finding names this leaf; no generated-file staleness in this run.
- Evidence: `logs/thim-radical-state-{lean,axioms,index,lint}.txt` and
  `logs/thim-radical-state-audit.json`. Artifact audit passed, including source identity,
  all export/axiom entries, fresh object file, API coverage, and import reachability.
- Removed all nine owned scratch files after their jobs exited. README untouched;
  no numerical experiments, proof holes, added axioms, or heartbeat changes.

## Survivor and next boundary

The exact finite criterion is the positive tool: every global prefix upper bound is
equivalent to bounds at canonical radical representatives. For nonnegative damping,
the residual representatives `r|primorial N` with `r>2N` remain unclassified here.
This card completes one contribution; the open-ended research goal remains active.
