# Specification consistency, polarization independence, and cusp concentration

- **ID:** ULF-INV-5
- **Stage:** 2-fully-proven
- **Type:** METATHEOREM (paper) / CONSISTENCY + INDEPENDENCE FOR THE INVERSE-THEORY AXIOMS
- **Source:** the charter's §5 gate (rigidity/consistency required); executed via the two
  calibration worlds
- **Statement:** The no-go-derived specification N1–N6 is consistent — its clauses are jointly
  modeled by the Weil–Castelnuovo intersection pairing for curves over finite fields, with the
  cusp clause N5 vacuous there — and it is provably insufficient: the graph world satisfies
  N1–N6 (partly vacuously) while its RH-conclusion fails, so no derivation of RH-grade
  positivity from the no-go axioms alone can exist. Sufficiency requires the polarization
  clause N7, whose rigidity half the corpus already owns. Over the rationals the entire open
  content therefore concentrates in jointly modeling {N5 cusp, N7 polarization, N2 geometric
  truncation}: the function-field world models everything but N5; the graph world everything
  but N7; no known world models both.
- **Status:** [PAPER-PROVED AT CITATION LEVEL] [INDEPENDENCE EXACT] [VACUOUS-SATISFACTION
  CAVEAT RECORDED] [NOT RH] [NO LEAN]

## 1. The specification (from ULF-INV-0 §2, §7)

N1 no factoring through multiplicative regularization (proved, ULF-INV-1); N2 operation outside
the moment category M required (exact contrapositive, charter §7.2); N3 upper-bound engine of
trace type (scoped); N4 systole/mass floor log 2 (exact, §7.3); N5 noncompact corner with
geometrically positive relative truncation (exact, §7.4); N6 pole data consumed (proved,
ULF-INV-3). N7 (added here): a polarization — a positivity of the self-pairing on the primitive
part of the arithmetic correspondence, in the sense instantiated by the corpus's Deninger layer.

## 2. Theorem A — consistency by the function-field model

The clauses N1–N4, N6, N7 are jointly satisfied by the classical Weil positivity proof for a
curve \(C/\mathbb F_q\) (Weil; Castelnuovo–Severi inequality; textbook form in Hartshorne
Exercise V.1.9–1.10 / Milne's notes):

| clause | discharging structure in the model |
|---|---|
| N1 | the pairing is the intersection form on the surface \(C\times C\), not a regularized limit of prime moment data; correspondences are cycles, and the pairing sees them integrally |
| N2 | the operation outside M is literal geometry: products, cycle classes, and intersection with **regions** (divisors) — indicators exist; truncation by ample divisors is positive |
| N3 | the upper bound on the count is `count ≤ trace`: the Lefschetz fixed-point count against \(H^1\) with the Castelnuovo bound gives \(|a_C|\le2g\sqrt q\) |
| N4 | the length spectrum of closed points starts at the degree-one places, \(\log q\): the model's systole clause with \(\log q\) in place of \(\log 2\) |
| N6 | the purchase is the pole: the Hodge-index/Castelnuovo argument spends the two trivial classes (the fibers — the pole divisors of the zeta function of \(C\times C\)) to dominate the primitive part |
| N7 | Castelnuovo positivity **is** the polarization: negativity of the self-intersection on the primitive part of \(\mathrm{Num}(C\times C)\) |
| N5 | **vacuous**: no archimedean place, the corner does not exist |

Hence the system is consistent, and the function-field proof is precisely a model in which every
no-go-derived clause is discharged by geometry. QED (by the cited classical proofs; no clause
requires new mathematics — that is the point).

## 3. Theorem B — independence of polarization: N1–N6 cannot suffice

There exist structures satisfying the graph-world analogues of N1–N6 in which the RH-conclusion
fails. Take a connected \(d\)-regular graph \(X\) (\(d\ge3\)) that is not Ramanujan — e.g., two
copies of a \(d\)-regular expander joined by a single matching edge-pair: the two-block structure
forces an eigenvalue \(\lambda\) with \(\lambda>2\sqrt{d-1}\) (standard: poor expansion pushes
\(\lambda_1\) toward \(d\); explicit non-Ramanujan families are elementary). The Ihara zeta of
\(X\) then violates its RH. Meanwhile: the trace is finite (finite-dimensional adjacency), so
N2, N5 are vacuously satisfied and N3's `count ≤ trace` is the spectral theorem; N6's pole is
the Perron eigenvalue \(d\), consumed by every spectral bound; N1, N4 hold in their graph forms
(the pairing is not a regularized moment limit; the length spectrum starts at the girth).

Consequently: **no theorem of the form "N1–N6 ⟹ RH-grade positivity" can exist** in any
formulation that transfers to the graph analogues. The no-go-derived axioms are necessary
(each inverts a proved corpus theorem) but provably not sufficient; sufficiency requires an
additional clause not derivable from any no-go — the polarization N7. QED.

**Caveat, recorded for hostility:** part of the satisfaction in the witness is vacuous (N2, N5
trivialize in finite dimensions). The independence conclusion survives the caveat — vacuous
satisfaction is satisfaction, and the failure of the conclusion in the model is exact
(non-Ramanujan means off-band eigenvalues). What the caveat does limit: the witness says nothing
about whether N1–N6 plus *infinite-dimensionality* forces more; that refinement is open and
recorded, not claimed.

## 4. Theorem C (cited) — rigidity of the polarized system

With N7 added, the corpus's own layer supplies the rigidity half: the Deninger weight-one
polarization axioms are equivalent to \(\operatorname{Re}\rho=\tfrac12\)
(`riemannHypothesis_iff_xiWeilPolarization_nonneg`; the structural producers'
premise computes to \((1-2\operatorname{Re}\rho)\cdot(\text{positive})\)). So:
specification + polarization ⟹ RH-grade positivity, in the corpus's own formalized setting.
Nothing new is claimed here; the point is that the metatheorem the charter demanded does not
need to be invented — it needs to be *reached*, and Theorems A/B locate exactly what reaching
it requires.

## 5. Theorem D — concentration of difficulty

Combining A–C: over \(\mathbb Q\), the open content of the entire specification program is the
joint modeling of

\[
\{\ \text{N5 (cusp)},\ \ \text{N7 (polarization)},\ \ \text{N2 (geometric truncation)}\ \}.
\]

The function-field world models all clauses except N5 (vacuous there, load-bearing over
\(\mathbb Q\)); the graph world models all except N7; no known structure models both
simultaneously. The corpus's one live object — the UV model — is precisely the N5+N2 fragment
(a noncompact corner with a positive relative truncation); the Deninger layer is the N7
fragment. The missing object of the inverse theory is their joint model: a **cusped polarized
structure with geometric truncation**, and every corpus no-go is a theorem that no fragment
assembled inside the moment/majorant/block categories can substitute for it.

## 6. Hostile scope

- Theorem A is a reading of classical proofs against the clause list; its value is the exact
  clause-by-clause discharge table and the observation that N5 alone is unmodeled. If a
  literature source states the function-field proof as a model of a no-go-derived axiom system,
  this demotes to BRIDGE; none was found (the standard sources present the proof, not the
  specification reading).
- Theorem B's witness is elementary; the independence formulation (no-go axioms provably
  insufficient; polarization not derivable from no-gos) is believed new in this exact form and
  is the card's main claim. Its caveat is §3's.
- Theorem D is a synthesis of A–C; it is exact given them, and it is the sharpest current
  answer to "what would the higher theory have to be": not a metaphor — a joint model of three
  named clauses, two of which have separate models and one of which (the pair N5+N7 together)
  has none.

## Log

- 2026-08-09 — created to discharge the charter's consistency/rigidity gate: consistency by the
  Castelnuovo model, independence of polarization by the non-Ramanujan witness, rigidity cited
  from the corpus's Deninger layer, difficulty concentrated in {N5, N7, N2} joint modeling.
