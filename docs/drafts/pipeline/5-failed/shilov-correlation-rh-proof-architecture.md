# Shilov--Weil descent architecture for the RH source boundary

- **ID:** shilov-correlation-rh-proof-architecture
- **Stage:** 5-failed
- **Type:** FALSIFIED CONJECTURE WITH PAPER-PROVED POSITIVE SURVIVOR
- **Source:** ../2-fully-proven/shilov-envelope-correlation-law.md · impact audit requested 2026-08-04
- **Statement:** `[FALSIFIED AS STATED]` No coefficient-faithful ordinary/local-
  \(C^*\) Shilov diagram can both retain the cofinal Gamma Bockstein and prove
  \(dh+hd=1\) on its physical reflection-odd class while preserving the known
  period-one source \(H^1\) detector. Two independent obstructions force failure:
  the Stokes regulator forbids the contraction off the critical line, and
  \(C^*\)-closure erases the trace-class/non-trace-class distinction carried by
  the Gamma defect.

## Requested Shilov--Weil theorem

Before selecting an Xi zero, construct a bifiltered ordinary-prime/Gamma/BV/Stokes
operator-system diagram whose cofaces are complete-order quotients, and construct a
source-defined homotopy \(h\) satisfying

\[
dh+hd=1
\]

on the reflection-odd relative migration class containing the physical Xi defect,
while retaining the source \(H^1\) class detected with Stokes period one.

The following audit treats "containing" coefficient-faithfully: the arithmetic
comparison must carry the already computed Gamma coefficient, not merely attach a
new abstract generator with the same name.

There is also a notation/type fork. The corpus symbol \(\kappa_\Xi\) is a fixed
real first-defect calibration, not a cochain. Therefore a "migration class
containing \(\kappa_\Xi\)" does not yet exist. A valid theorem must construct a
source-defined landing of that scalar into the migration complex and prove its
relation to the physical cofinal defect. An arbitrary rank-one inclusion would
be vacuous. If \(\kappa_\Xi\) instead denotes the already constructed physical
cofinal class, the no-go propositions below apply directly.

## Gates

- [x] 0 → 1 in-progress: exact source complexes, period-one regulator, physical
  class, and proposed Shilov interface extracted
- [x] hostile regulator audit: requested contraction is equivalent to annihilating
  the already RH-equivalent source class
- [x] hostile topology audit: ordinary and local \(C^*\)-closures erase the
  Bockstein's summability wall
- [x] 1 → 5 failed: exact requested theorem retired; strongest positive survivor
  extracted below
- [ ] successor: build a hybrid trace-filtered fracture, not an all-Shilov diagram

## Exact source data

For an ordinary prime \(p\), the resolved rational-adelic relative source has

\[
C^0=\mathrm{Core},\qquad C^1=\mathrm{Core}\oplus\mathbf C,
\qquad C^2=\mathbf C,
\]

with

\[
d^0x=(p\cdot x-x,\operatorname{ev}_0x),\qquad
d^1(y,z)=\operatorname{ev}_0y.
\]

Its retained cocycle is \(\eta_p=(0,1)\). The bilateral prime-orbit Stokes
functional

\[
R_p(y,z)=z-\operatorname{Stokes}_p(y)
\]

satisfies \(R_pd^0=0\) and \(R_p(\eta_p)=1\), hence descends to a nonzero
functional on source \(H^1\). These statements are already unconditional in
`CCMRationalAdelicPrimeIsotropyStokesRegulator.lean`.

The pre-divisor cofinal physical landing is also explicit. On an Xi divisor
\(\rho\), its top-coordinate readout is

\[
\bigl(g_n(\rho)-1\bigr)
\,\Xi^{(m_\rho)}(\rho)\,
\operatorname{Tr}(x),
\qquad
g_n(s)=\exp((2\Re s-1)\log n).
\]

For the ordinary-prime source atom the trace and leading Xi jet are nonzero.
Therefore the physical relative class vanishes exactly when
\(\Re\rho=1/2\), and its global vanishing is equivalent to RH. This is the
unconditional theorem
`ccmMobiusThetaEveryPhysicalDefectSourceNullHomologous_iff_riemannHypothesis`;
it does not assert the vanishing side.

## No-go I: regulator obstruction

**Proposition (detector-preserving contraction obstruction).** Let
\((C^\bullet,d)\) be a cochain complex, let \(\kappa\in C^1\) satisfy
\(d\kappa=0\), and let \(R:C^1\to V\) satisfy \(Rd=0\) on \(C^0\). If a
degree \(-1\) operator \(h\) satisfies

\[
(dh+hd)\kappa=\kappa,
\]

then \(R(\kappa)=0\).

**Proof.** Since \(d\kappa=0\), the identity gives
\(\kappa=d(h\kappa)\). Apply \(R\) and use \(Rd=0\). ∎

For \(\kappa=\eta_p\), this contradicts \(R_p(\eta_p)=1\). For the physical
reflection-odd landing \(\kappa_\Xi(\rho,p)\), the same argument forces its
explicit readout to vanish and hence forces \(\Re\rho=1/2\). Thus a global
source-defined \(h\) of the requested kind is not a construction available
before RH: its asserted action on the actual class is precisely the missing
RH-bearing theorem.

A detector-preserving contraction must instead have Hodge form

\[
\boxed{dh+hd=1-\iota R,\qquad R\iota=1.} \tag{H}
\]

It contracts \(\ker R\) and preserves the detected line. It contracts the
physical class only after independently proving that its regulator coordinate
vanishes.

## No-go II: \(C^*\)-Shilov blindness

Write the two-orientation cofinal Gamma coefficient as

\[
\Delta_t(p)=F_{-t}(p)-F_t(p),\qquad
F_t(p)=p^t\frac{p}{(p+1)^2},\qquad |t|<1,
\]

and let \(D_t=\operatorname{diag}(\Delta_t(p))\) on
\(\ell^2(\mathbb P)\). Existing sharp estimates give, for \(t\ne0\),

\[
|\Delta_t(p)|\asymp p^{|t|-1},\qquad
\sum_p|\Delta_t(p)|^q<\infty
\Longleftrightarrow q(1-|t|)>1. \tag{S}
\]

**Theorem (cofinal Gamma \(C^*\)-blindness).** For every \(|t|<1\),
\(D_t\) is compact. It is trace class exactly when \(t=0\). If \(J\) is a
norm-closed two-sided ideal of \(B(\ell^2(\mathbb P))\) containing the
finite-rank diagonal operators, then \(D_t\in J\) for every \(|t|<1\).
Equivalently, any Shilov quotient that absorbs the finite-stage or trace-class
ambiguity also absorbs every off-line cofinal Gamma defect.

**Proof.** From the upper estimate in `(S)`, \(\Delta_t(p)\to0\), so the
finite-prime diagonal truncations converge to \(D_t\) in operator norm;
therefore \(D_t\) is compact. At \(t=0\), \(D_0=0\). If \(0<|t|<1\),
the criterion `(S)` with \(q=1\) fails, so \(D_t\notin\mathcal S_1\).
Finally, a two-sided ideal containing a nonzero rank-one diagonal projection
contains every matrix unit and hence every finite-rank operator. The compact
operators are their operator-norm closure. Closedness of \(J\) gives
\(\mathcal K\subseteq J\), hence \(D_t\in J\). ∎

The same obstruction survives the local \(C^*\) variant on the diagonal
source algebra. Every \(C^*\)-seminorm on \(c_0(\mathbb P)\) is contractive
for its \(C^*\)-norm. Hence \(c_{00}(\mathbb P)\) remains dense for any
topology generated by such seminorms. A closed local Shilov ideal containing
the finite-stage ambiguity therefore contains every \(\Delta_t\in c_0\).

This does not say that arbitrary operator-system diagrams never exist. It
says that no diagram compatible with the actual diagonal Gamma coefficient,
finite-prime truncation, and Shilov/local-\(C^*\) closure can be the required
faithful RH carrier. Packaging the existing linear BV/Stokes maps into a
universal Paulsen operator system would create complete-positive maps but
would not evade either obstruction; it would be representational theatre.

## Strongest positive survivor: trace-filtered Shilov fracture

The exact replacement is necessarily hybrid:

\[
\begin{array}{ccc}
\text{finite-prime operator systems} &\longrightarrow&
\text{compact/Shilov completion}\\
\downarrow && \downarrow\\
\text{Gamma--BV--Stokes source complex}&\longrightarrow&
\text{trace-filtered comparison cone}.
\end{array} \tag{F}
\]

- Horizontal prime-aperture cofaces may be genuine complete-order quotients.
- Vertical structure must retain the non-\(C^*\) filtration
  \(\{\mathcal S_q:q>1\}\), or its sequence analogue
  \(\{\ell^q:q>1\}\).
- The reflection-odd Bockstein lives in the completion/fracture anomaly, not
  in an ordinary Shilov ideal.
- Chain contraction must have form `(H)`, with the physical Gamma coefficient
  as the residual \(\iota R\) or fracture term.

Because every Schatten ideal contains finite ranks densely in operator norm,
the vertical quotient in `(F)` cannot be a Hausdorff \(C^*\)-quotient. It
must be bornological, projective-limit, filtered-derived, or a corona/Rees
comparison of incompatible completions. This matches the independent
finite-simplex and derived-specialization no-go: one exact realization cannot
both preserve source contractibility and create the nonzero Xi conormal
class; the class must be carried by a fracture between realizations.

The active source theorem remains
`COEFFICIENT_GENERATED_REES_CORONA_SOURCE_ADMISSION`. It asks for a
pre-divisor arithmetic construction placing the explicit physical coordinate
in a source-derived corona kernel. Shilov theory organizes its horizontal
finite-aperture correlations but cannot supply the vertical annihilation.

The explicit coefficient-faithful model in
`PrimeDepthBVWoldReesCoronaQuotient.lean` confirms this separation rather than
closing it. The resolved harmonic lift lies in the corona kernel
unconditionally; the fixed physical lift lies there exactly on the critical
line, and global physical admission is equivalent to RH. Thus replacing the
Shilov quotient by a corona quotient locates the missing theorem but does not
prove the source-to-physical lift identification.

## Hostile-review verdict

- **Correctness:** regulator and closure proofs are dependency-closed.
- **Non-circularity:** requested contraction fails this gate; on the physical
  class it is equivalent to the RH-bearing vanishing already isolated in the
  corpus.
- **Type correctness:** existing BV/Stokes constructions are linear or
  Hilbert/Krein maps, not canonical unital completely positive maps. No
  arithmetic operator system currently exists from which all requested
  cofaces arise. Literal \(\kappa_\Xi\) is a scalar; no source-defined
  migration-class landing for it has been constructed.
- **Novelty:** complete-order quotients, Shilov ideals, local \(C^*\)-envelopes,
  and compact-ideal closure are parent mathematics. New content here is the
  source-specific incompatibility theorem and resulting architecture
  correction. It is a bridge/no-go, not enough by itself for a renowned
  general journal.
- **RH impact:** Shilov correlations remain useful bookkeeping, but they do
  not open a new proof producer. Any viable successor must prove an
  arithmetic comparison-anomaly law in a finer trace-filtered fracture.

## Literature frontier checked

- Kavruk--Paulsen--Todorov--Tomforde, *Quotients, exactness and nuclearity in
  the operator system category*, Adv. Math. 235 (2013), 321--360,
  arXiv:1008.2811.
- Joiţa, *The Shilov boundary for a local operator system*, arXiv:2409.10474.
- Joiţa--Şimon, *The R-Shilov boundary for a local operator space*,
  arXiv:2602.03628.
- Calkin, *Two-sided ideals and congruences in the ring of bounded operators
  in Hilbert space*, Ann. of Math. 42 (1941), 839--873.
- Brodzki--Plymen, *Entire cyclic homology of Schatten ideals*, Homology
  Homotopy Appl. 7 (2005), 87--100, arXiv:math/0409164.

## Log

- 2026-08-04 — created in Stage 1 for exact impact audit; no new RH route accepted yet.
- 2026-08-04 — naive automatic-vanishing interpretation killed by arbitrary-defect realization;
  retained derived-correlation architecture as a Stage-1 bridge with explicit arithmetic open core.
- 2026-08-04 — exact requested Shilov--Weil contraction killed by the period-one regulator and
  cofinal Gamma \(C^*\)-blindness. Retained trace-filtered fracture `(F)` and Hodge identity `(H)`;
  route moved to Stage 5.
- 2026-08-04 — explicit Rees--corona quotient audited: resolved admission is unconditional,
  physical admission is critical-line equivalent, and global admission is RH-equivalent. No
  source-to-physical lift comparison was supplied.
