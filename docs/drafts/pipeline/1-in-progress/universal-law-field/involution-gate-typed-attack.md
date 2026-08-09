# Involution gate (N8) — typed attack

- **ID:** ULF-INV-11
- **Stage:** 1-in-progress
- **Type:** TYPED ATTACK PLAN / THE GROUP-3 BOUNDARY, INSTANTIATED ON THE DECISIVE CLASS
- **Source:** N8 (charter §7.9) + ULF-INV-10's promoted identification
- **Status:** [DEFECT LEMMA DERIVED] [FORK SUB-TARGETS TYPED] [GROUP-3 BY CONSTRUCTION]
  [NOT RH] [NO LEAN]

## 1. The gate, exactly

N8 demands a source-compatible anti-holomorphic involution whose Hermitian extension is
identified with the prime source. On the divisor side the involution exists (line conjugation,
`xiWeilLineConjLp`, isometric, unconditional); ULF-INV-10 identifies the Hermitian pairing with
prime sums on the decisive class. What is missing is exactly: a SOURCE-side realization making
the prime-sum quadratic form manifestly a sum of squares — the wall, as the trichotomy requires.

## 2. Eigen-class defect lemma (derived)

On the eigen class the N8 defect functional becomes explicit. By the antidiagonal Gram: an
on-line simple zero contributes a 1×1 block (|value|² ≥ 0); an off-line pair (α, its line
partner ᾱ*) contributes a 2×2 block of the form [[0, g],[ḡ, 0]] with eigenvalues ±|g| —
indefiniteness exactly −|g|. Hence the decisive-class defect (the distance of the eigen Gram
from the PSD cone, in the natural blockwise sense) is

    Defect = Σ_{off-line pairs} |g_pair| ,   with g_pair the antidiagonal Gram entry,

which by ULF-INV-10 is a prime+Gamma-expressible quantity per pair. Defect = 0 ⟺ RH (with
simplicity handling degeneracies as in the promoted card). This ties the two boundary gates:
the involution's failure on the decisive class is measured by explicit, now prime-sum-expressible
block norms — the eigen-class shadow of the corpus's imaginary-energy functional.

## 3. Fork sub-targets (typed, falsifiable)

- **(a-target)** Native: exhibit a source-side operation J on the time domain (measurable,
  involutive, k-compatible) whose induced action on transforms is the sharp operation. The
  polarization theorem and the no-gos constrain J: it cannot be a pointwise phase (unimodular
  gauge — modulus budget), cannot act through moduli (caps), cannot be divisor-side only
  (conjugation no-sign). First falsifiable sub-target: prove J cannot be a composition operator
  f ↦ conj(f ∘ σ) for any measurable σ (or construct the σ — either outcome is knowledge; the
  candidate σ(x) = −x is killed by evenness bookkeeping unless the source pairing degenerates —
  check first).
- **(b-target)** Import: a correspondence transporting a positive structure onto the eigen
  class from a world with native polarization; must transport more than Mertens-normal data
  (ULF-INV-1) and infinite rank (charter §7.8). First falsifiable sub-target: the function-field
  Castelnuovo positivity transported along any known zeta-correspondence — write down what the
  transport would have to preserve and find the first broken invariant.
- Attacks here are RH-grade by construction; the discipline is proof-or-obstruction on the
  SUB-targets only, never a claim on the gate itself.

## Log

- 2026-08-09 — card created; defect lemma derived from ULF-INV-10 + antidiagonal structure;
  fork sub-targets typed with first falsifiable steps named.

## 4. Sub-target (a), first branch — executed 2026-08-09: the involution EXISTS; N8 re-typed

Computation (one line, e^{−izx} convention pinned in ULF-INV-10): for J f(x) := conj(f(−x)),

    (Jf)^(z) = ∫ conj(f(−x)) e^{−izx} dx = conj( ∫ f(u) e^{−i(conj z)u} du ) = conj( f̂(conj z) )
             = (sharp f̂)(z).

So the composition operator J = conj ∘ reflect REALIZES the sharp/line-conjugation on
transforms: the source-side involution exists trivially. VERDICT on the dichotomy's construct
branch: CONSTRUCTED. And the construction adds no positivity: W(f, Jf) = Σ_ρ f̂(ρ)·conj(f̂(ρ̄))
is a sum of |f̂(ρ)|² exactly when every ρ is line-fixed — positivity of the J-pairing IS RH,
unchanged.

**Consequence — N8 re-typed (charter correction).** The missing primitive was never the
involution's existence (free, one line). N8's honest form is: a source-side FACTORIZATION of
the explicit-formula pairing through a positive structure intertwining this J — the GNS/dilation
shape — which is group 3 verbatim, as the trichotomy demanded all along. The inverse theory's
terminal statement sharpens: every structural ingredient (involution, Hermitian form,
identification on the decisive class, defect functional) now EXISTS unconditionally and is
corpus-formalized or paper-proved; the single remaining content of RH inside this specification
is the positivity of one explicit pairing, with every no-go a proved constraint on where that
positivity cannot come from. Nothing about this is a route; it is the problem, cornered.

Remaining sub-target: (b-target) the import-fork first-broken-invariant test — the only
still-typed attack that could add structure rather than positivity-by-fiat.

## 5. Sub-target (b) — executed 2026-08-09: first broken invariant identified; verdict

What a Castelnuovo transport must preserve, in order: (1) the ambient self-product with its two
projections and diagonal (the Frobenius/correspondence graph lives there); (2) the intersection
pairing with its pole classes (the two fibers) dominating via Hodge index; (3) the reality/
polarization compatibility. Walking the chain against the arithmetic target: local factors
transport trivially (each Euler factor is a degree-1 function-field zeta); one level up,
arithmetic SURFACES over Spec Z have Arakelov intersection theory with genuine positivity
theorems (Faltings-Hriljac); but for zeta itself the target object is Spec Z as a curve, and
the required square — Spec Z x_{F1} Spec Z with an intersection pairing — does not exist in any
known category. **The first broken invariant is the very first requirement: the absolute
self-product.**

VERDICT: REDISCOVERED — this is the literature's own diagnosis (Manin; Connes-Consani; the F1
program's founding motivation). The marginal content the inverse theory adds, recorded here:
any candidate square must ALSO satisfy the corpus's constraint list — N5 (its archimedean fiber
noncompact, no trace-class comparison), N1 (its prime-data comparison transports more than
Mertens-normal moments), N4 (systole log 2 in its length spectrum), and the eigen-class defect
of §2 as its positivity test object. These attach machine-checked design constraints to a known
open program; they do not open it.

## 6. Card status after both sub-targets

Both typed sub-targets executed to verdicts: (a) CONSTRUCTED + N8 re-typed (the involution is
free; the factorization is the problem); (b) REDISCOVERED + constraints attached (the square is
the known wall of the import fork). The typed surface of this card is exhausted. What remains
on the gate is the gate itself — group 3, the problem — now stated with: all structure existing
unconditionally, the decisive-class pairing in prime-sum form (ULF-INV-10), the defect
functional explicit, and every no-go a proved constraint on the positivity's origin. Further
cycles on this card require genuinely new structure (a fresh hunch-formation pass with new
literature or corpus input), not harder pushing.

## 7. Correction from the literature pass — 2026-08-09: the square EXISTS; the break is one layer up

The §5 verdict was too coarse. Connes–Consani's arithmetic site realizes the Frobenius
correspondences on the SQUARE of the site (arXiv:1405.4527; the topos-theoretic self-product
exists), and their announced program (the "Riemann–Roch strategy") is precisely to build the
missing layer: an intersection/Riemann–Roch/index-positivity apparatus on that square. So the
transported invariant chain breaks at link (2) — the Hodge-index layer — not link (1). §5's
verdict corrects to: REDISCOVERED at link (2), with the corpus constraint list still attaching.

More consequential for fork (a): CC's Selecta paper (arXiv:2006.13771) PROVES Weil positivity
semi-locally (the archimedean place, operator-theoretically, via Sonin-space squares) — i.e.,
**the N8 factorization EXISTS LOCALLY**: a GNS-shape positive structure intertwining the
involution is a theorem at the archimedean place. The corpus is already deep in this seam: its
Sonin folder is stage-3 complete, and its sonin-burnol weld attempt is TERMINALLY RETIRED
(`sonin-burnol-weld-terminally-retired`) — a proved failure of one specific globalization shape.

**Updated terminal map of the gate (the sharpest yet):** the group-3 wall has (i) a proved
LOCAL solution (CC semi-local positivity; corpus Sonin layer), (ii) a proved-failed
globalization attempt in-corpus (the weld retirement), and (iii) a named missing global layer
(Riemann–Roch on the site's square) with our machine-checked constraints N1, N4, N5 attached.
The open question is global assembly of a locally-existing positive structure — a descent/
gluing problem for positivity, which is a genuinely different (and sharper) shape than "create
positivity": it now reads as a LOCAL-TO-GLOBAL obstruction problem, the field's oldest shape
(the PRD/RBD charters' compactness-escape laws), returned at the top of the tower.
