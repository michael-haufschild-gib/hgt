# Intertwined challenge prolongation, observer contraction, and false-closure law

- **ID:** ULF-ALG-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / OBSERVER DATA-PROCESSING LAW FOR ADVERSARIAL LAW GENESIS
- **Source:** `../../1-in-progress/universal-law-field/adversarial-law-genesis-and-sequential-stress-mechanics.md`
- **Statement:** A failure-promoter generates a linear challenge-prolongation language.  Every
  intertwining observer maps the source challenge space onto the observed challenge space, cannot
  increase its rank, and can create an apparent finite recurrence only by erasing a definite
  source challenge combination.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CLASSICAL KRYLOV/LINEAR-SYSTEMS PARENT] [LEAN-FORMALIZED] [NOT RH]
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveChallengeProlongation`

## 1. Mechanism

Let (K) be a field, (V,W) vector spaces, and let


[
  D:V\to V,qquad E:W\to W,qquad q:V\to W
	ag{CP.1}
]

be linear maps satisfying the exact transport law

[
  qD=Eq.
	ag{CP.2}
]

Choose a current source response (v\in V).  The next legal challenge is not drawn from a fixed
list.  Failure promotes the current reporter by (D), producing the lineage

[
  v, Dv, D^2v,ldots .
	ag{CP.3}
]

For horizon (n), define source and observed challenge languages

[
  \mathcal C_n(D,v)=\operatorname{span}_K\{D^iv:0\le i<n\},
  qquad
  \mathcal C_n(E,qv)=\operatorname{span}_K\{E^iqv:0\le i<n\}.
	ag{CP.4}
]

For coefficients (a=(a_0,ldots,a_{n-1})), write

[
  P_a(D)v=\sum_{i<n}a_iD^iv.
	ag{CP.5}
]

The operator (D) is the challenge promoter.  It is not claimed to be universal or automatically
source-native; source production of (D) is the next formation gate.

## 2. Exact transport and contraction

### Theorem 2.1 -- challenge data processing

For every (n\ge0):

1. (q(D^iv)=E^iq(v)) for every (i);
2. (q(P_a(D)v)=P_a(E)q(v)) for every coefficient packet (a);
3. (q(\mathcal C_n(D,v))=\mathcal C_n(E,qv));
4. consequently
   
   [
     \dim_K\mathcal C_n(E,qv)\le \dim_K\mathcal C_n(D,v).
   	ag{CP.6}
   ]

### Proof

Clause 1 follows by induction from `(CP.2)`.  Linearity gives clause 2.  Clause 1 sends every source
generator in `(CP.4)` to the corresponding observed generator, so the image of the source span is
exactly the observed span.  Finite-dimensional rank cannot increase under a linear image. `QED`

This is an actual observer data-processing law for promoted challenges.  It is not a slogan that
observation loses information: it identifies the entire lost subspace.

## 3. False closure is a kernel event

### Theorem 3.1 -- recurrence/erasure equivalence

For every coefficient packet (a),

[
  P_a(E)q(v)=0
  quad\Longleftrightarrow\quad
  P_a(D)v\in\ker q.
	ag{CP.7}
]

Hence:

1. if (q) is injective, every observed recurrence already holds in the source;
2. more generally, injectivity of (q) only on (\mathcal C_n(D,v)) suffices for every
   order-(<n) observed recurrence to lift;
3. an observer creates an apparent recurrence absent in the source exactly when it kills one
   nonzero promoted challenge combination.

### Proof

By Theorem 2.1,

[
  q(P_a(D)v)=P_a(E)q(v).
]

Thus the right side of `(CP.7)` is the left side by definition of the kernel.  The three
consequences are immediate. `QED`

### Theorem 3.2 -- exact false-closure witness

Assume the source packet

[
  v,Dv,ldots,D^{n-1}v
]

is linearly independent while the observed packet

[
  qv,Eqv,ldots,E^{n-1}qv
]

is linearly dependent.  Then there is a nonzero coefficient packet (a) such that

[
  0\ne P_a(D)v\in\ker q,qquad P_a(E)qv=0.
	ag{CP.8}
]

### Proof

Observed dependence supplies nonzero (a) with (P_a(E)qv=0).  Source independence makes
(P_a(D)v\ne0), and `(CP.7)` places it in the kernel. `QED`

## 4. Sharp finite laboratory

Take (V=K^{n+1}), (W=K^n), let (D) and (E) be the forward shifts on their standard bases,
let (v=e_0), and let (q) retain the first (n) coordinates.  Then `(CP.2)` holds through the
first (n) challenge stages.  The source packet (e_0,ldots,e_n) is independent, while the
observed stage-(n) challenge vanishes.  The new apparent closure is exactly the killed vector
(e_n\in\ker q).

The abstract theorem is sharper than this truncated cell because it applies whenever the full
intertwining law `(CP.2)` holds.

## 5. Mechanism consequences

1. **Observer contraction is typed.**  The contraction is the quotient of the promoted challenge
   language by its intersection with `ker q`, not an unspecified loss scalar.
2. **Apparent theorem closure has a certificate.**  Every new observed recurrence comes with a
   hidden source residual (P_a(D)v).
3. **Faithful observation reflects closure.**  An observer injective on the current challenge
   language cannot manufacture a finite law.
4. **Hypertranscendence belongs to challenge growth.**  A differential realization may have every
   finite promoted packet algebraically independent.  Noncompactness is a possible realization
   consequence, not the definition of that growth.
5. **Doctrines remain load-bearing.**  Enlarging allowed coefficients from constants to rational,
   algebraic, nonlinear, or topological operations changes which promoted combinations count as
   legal recurrence certificates.

This certifies ALG Law V in a linear prolongation chart and connects it to ALG Law VII: a surviving
nonzero hidden residual is the exact candidate to promote into the next legal reporter.

## 6. Hostile boundaries

1. Generic Krylov spaces, minimal polynomials, observability, and intertwining are classical linear
   systems mathematics.  The field-level role is their reinterpretation as one law of
   challenge-language transport.
2. The theorem does not derive (D) from a source failure.  Choosing (D) after seeing a target
   would be theatre.
3. Linear rank is only one doctrine.  It does not identify algebraic differential,
   computable-strategy, positive, or topological admission ranks.
4. A nonintertwining observer has no reason to preserve challenge lineage; `(CP.6)--(CP.8)` may
   fail.
5. Rank contraction alone does not prove open law genesis.  One needs unbounded promoted rank or a
   source-derived rule that promotes hidden residuals into later challenges.
6. No RH route, endpoint, physical clock, positivity form, or arithmetic source is used.

## 7. No-go closure and positive survivor

The conjecture that observer closure can be treated as an intrinsic closure of the source law is
false.

- **Exact killing mechanism:** an observer may erase a nonzero polynomial-in-the-promoter residual.
- **Strongest positive survivor:** every observed recurrence coefficient packet produces a
  canonical typed kernel certificate, and every intertwining observer contracts the finite
  challenge rank.
- **New insight:** observer-made simplicity is not absence of future challenges; it is a quotient of
  their promoted language.
- **Formal status:** Lean-certified.  Prolongation transport, combination transport, exact image of
  challenge spaces, finite-rank contraction, kernel equivalence, recurrence reflection, and the
  hidden-challenge witness are unconditional declarations in
  `ConstitutiveChallengeProlongation.lean`.

## Log

- 2026-08-10 -- theorem closed after ALG-2 forced adaptivity to become an independent field axis.
  Current RH routes were excluded from construction.
- 2026-08-10 -- Lean gate passed and module wired into the Universal Law Field umbrella.  Axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
