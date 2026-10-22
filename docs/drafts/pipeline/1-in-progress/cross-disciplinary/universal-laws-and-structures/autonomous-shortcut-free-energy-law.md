# Autonomous shortcut free-energy law

- **ID:** autonomous-shortcut-free-energy-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / inverse theorem for autonomous quantum complexity
- **Status:** `[FALSIFIED AS AN EXACT CONJECTURE] [POSITIVE SHADOWS RETAINED]`
- **Parent:** `static-local-complexity-law.md`, obligation O4
- **Date:** 2026-08-05

## Exact frontier

The parent problem asks for a selector-aware upper bound on the whole radial
shortcut locus of a fixed-locality Hamiltonian ensemble.  Three exact
obstructions are now known.

1. A `d`-dimensional continuously fast-forwardable carrier forces shortcut
   volume `Omega(R^d)`.
2. A rank-`r` recurrence lattice can create `Theta(R^r)` separated shortcut
   components even when each component is zero-dimensional.
3. For state complexity, the kernel of the projective Hamiltonian action at
   the initial state has dimension `m-v_Phi` and is a zero-gate carrier.  For
   a product input in the full fixed-`q` qubit Pauli space,

   \[
   v_\Phi=2\sum_{k=1}^{q}{n\choose k}.                \tag{1}
   \]

The paper-proved mixed-carrier theorem shows that continuous carrier
dimension and transverse recurrence rank add.  Therefore the prior scalar
conjecture `kappa=m-f_*`, with `f_*` defined only as a continuous synthesis
dimension, is false as a universal representation.

There is a second defect.  At fixed `n` and fixed error, compactness plus
universality gives a finite circuit bound for every state.  A relative budget
growing linearly with `R` therefore makes the complete annulus easy after a
finite radius.  A bare `R->infinity` exponent at fixed `n` is always `m` on
the shortcut-volume side.  Any nontrivial law must be a uniform finite-size
statement in an explicit pre-capacity `(n,R)` window.

## Failed competing representations

### A. Endpoint rate-distortion profile — `CIRCULAR/INSUFFICIENT`

Unrestricted metric entropy of the random endpoint ensemble is at most
`O(m log R)` by the Duhamel parameter cover.  A codebook with exponentially
many centers can cover the whole ensemble, so ordinary rate-distortion throws
away the computational restriction and cannot prove ballistic complexity.
Constraining the codebook to low circuits recovers the shortcut locus itself
and merely renames O4.

### B. Synthesis-speed spectrum — `CIRCULAR`

Defining a carrier's speed by the minimal circuit complexity uses the desired
quantity inside the proposed invariant.  Replacing it by an independently
certified compiler avoids circularity, but a single continuous dimension
still misses recurrence and architecture-component proliferation.

### C. Largest uniform synthesis dimension — `FALSE AS UNIVERSAL LAW`

The mixed-carrier theorem produces exponent `d+r`, not `max(d,r)`.  The
fixed-`n` saturation argument also makes the asymptotic exponent ill-typed
unless the double scaling is specified.  These failures force a finite-scale
energy--entropy representation.

## Certified shortcut formats

Fix a system size `n`, coefficient dimension `m_n`, a radius `R` in the
pre-capacity window, strict/relaxed error margins
`epsilon_-<epsilon_+`, and strict/relaxed relative budgets `a_-<a_+`.

A **certified shortcut format** `F` is finite data, specified independently of
the shortcut locus, with the following content.

1. A uniformly tame family of smooth or algebraic carrier pieces
   `Y_(F,alpha)(R) subset A_R={x:R<=||x||<=2R}` of a common continuous
   dimension `d_F`.  Their reach, distortion, degree/format, and local volume
   constants are controlled by `poly(n,log R)` data.
2. A uniform classical compiler or fixed algebraic gate architecture which,
   from the carrier parameters, outputs a circuit preparing
   `exp(-iH(x))Phi` to error `epsilon_+` within budget `a_+` for every point on
   every carrier piece.  Brute-force minimal-circuit search and an explicit
   list of all shortcut points are forbidden.
3. A component-count law

   \[
   \#\{\alpha:Y_{F,\alpha}(R)\cap A_R\ne\varnothing\}
   =R^{h_F+o(m_n)},                                  \tag{2}
   \]

   where `h_F>=0` is the **component-growth entropy exponent**.  Period
   lattices, semilinear recurrence families, and polynomial-growth circuit
   languages enter here.
4. Pairwise overlap multiplicity `R^{o(m_n)}` after a fixed-radius tube is
   taken.  This prevents artificial entropy from repeatedly naming the same
   carrier.

The **free codimension** of the format is

\[
 g_F=(m_n-d_F-h_F)_+.                                \tag{3}
\]

It is an energy--entropy balance.  Tuning transversely to one component costs
`m_n-d_F` powers of radius; having `R^(h_F)` distinct components refunds
`h_F` powers.

The definition is intentionally stricter than “a subset of shortcuts.”  A
format must expose the algebraic/periodic carrier and its synthesis compiler
before any volume estimate is invoked.  Weakly special matrix-exponential
carriers, commuting period lattices, Cartan compilers, block diagonalization,
and product-state stabilizer carriers are admissible examples.

Let

\[
 g_*(n,R;\epsilon_+,a_+)
 =\inf_F g_F                                           \tag{4}
\]

over all certified formats with controlled complexity at that scale.

## Conjecture — autonomous shortcut free-energy law

For every fixed locality `q>=2`, local dimension, finite universal gate
model, robust margins, and every `eta>0`, there are uniform constants and an
explicit pre-capacity window such that

\[
 N_r\!\left(
  \mathfrak S_{\epsilon_-,a_-}\cap A_R
 \right)
 \leq
 R^{m_n-g_*(n,R;\epsilon_+,a_+)+\eta m_n}             \tag{5}
\]

for every sufficiently large `n` and every admissible `R` in that window.
Conversely, every certified format supplies, after the same robustness
margins,

\[
 N_r\!\left(
  \mathfrak S_{\epsilon_+,a_+}\cap A_R
 \right)
 \geq
 R^{m_n-g_F-o(m_n)}.                                  \tag{6}
\]

Thus the sharp aggregate Gaussian escape exponent is

\[
 \boxed{
 \kappa_*(n,R)=g_*(n,R)+o(m_n)
 =\inf_F\bigl(m_n-d_F-h_F\bigr)_++o(m_n).
 }                                                     \tag{7}
\]

The genuinely new assertion is the inverse inequality (5): exponentially
many allowed circuit architectures cannot create excess shortcut mass in an
arithmetically unorganized way.  If their union beats every known
energy--entropy balance, it must generate a new finite-format compression
carrier with a lower free codimension.

## Shadows already proved

The law specializes correctly to every current exact obstruction.

| Mechanism | `d_F` | `h_F` | Forced escape ceiling |
|---|---:|---:|---:|
| observer-stationary carrier `ker T_Phi` | `m-v_Phi` | `0` | `v_Phi` |
| continuous fast-forwardable subspace | `d` | `0` | `m-d` |
| isolated rank-`r` recurrence lattice | `0` | `r` | `m-r` |
| mixed synthesis carrier plus period lattice | `d` | `r` | `m-d-r` |
| fully easy one-local family | `m` | `0` | `0` |

The first four lower bounds are paper-proved in the parent cards.  The table
is not evidence for the inverse law; it shows that the new representation
absorbs the exact mechanisms that killed its predecessors.

## Concrete Pauli prediction

For the all-to-all fixed-`q` qubit Pauli family and any product input, the
observer-stationary format gives

\[
 g_*\leq v_\Phi
 =2\sum_{k=1}^{q}{n\choose k}
 ={2\over3^q}m_n+O(n^{q-1}).                          \tag{8}
\]

The sharp companion conjecture is that, for `q>=2` and sub-direct budgets,
no certified format has smaller free codimension at leading order:

\[
 \boxed{
 g_*(n,R)=2\sum_{k=1}^{q}{n\choose k}+o(m_n).
 }                                                     \tag{9}

Together, (7) and (9) predict

\[
 \Pr_J\!\left\{
 C_\epsilon(e^{-itH(J)}\Phi)
 \leq {a\Lambda(H(tJ))\over p(n)}
 \right\}
 =t^{-2\sum_{k\leq q}{n\choose k}+o(m_n)}            \tag{10}

uniformly before saturation.  State complexity would then grow at the sharp
rate allowed by the number of real local-Hamiltonian directions the initial
ray can distinguish—not by the full coefficient count.

## Preliminary hostile attack

### Circularity

Survives the current attack only because carrier geometry and compiler are
independent certificates.  If “finite format” is weakened to allow a list of
minimal circuits or arbitrary shortcut components, (4) becomes tautological
and the conjecture is `CIRCULAR`.  A final theorem must use a formal complexity
class for carriers, not prose.

### Fixed-size saturation

Survives: (5) is finite-scale and uniform only inside an explicit
pre-capacity window.  It makes no fixed-`n`, `R->infinity` assertion.

### Discrete recurrence

Survives: recurrence contributes through `h_F`, even when every exact
component is a point.  This is precisely what the old continuous-dimension
law missed.

### Architecture proliferation

Not assumed away.  It is the content of (5): large aggregate component
entropy must organize into a certified format.  Proving this is the hard
inverse theorem, not a consequence of targetwise transversality.

### One-local counterexample

The explicit sharp prediction (9) is restricted to `q>=2`; for `q=1`, the
entire product-state orbit is uniformly easy and the correct format has
`d_F=m`, hence `g_*=0`.  The universal law (7) still gives the right value.

### Other integrable or state-specific families

They are admissible competing formats.  Finding one with
`d_F+h_F>m-v_Phi+o(m)` falsifies (9) and improves the law's predicted
minimizer without falsifying (7).  This is a concrete experimental and
mathematical discriminator.

## External SOTA audit

- Atia--Aharonov and Gu--Somma--Sahinoglu define fast-forwarding, prove its
  relation to precise energy measurement, and supply commuting, quadratic,
  block-diagonal, permutation-invariant, and low-energy examples.  They do
  not classify all fast-forwardable coefficient carriers or count their
  recurrence components.
- Papas's matrix-exponential Ax--Schanuel theorem is qualitative, exact, and
  restricted to components through zero/identity outside weakly special
  loci.  It does not give fixed-radius tube volume, translated recurrence
  components, growing circuit targets, or an architecture union.
- Uniform/effective Pila--Wilkie theory supplies the parent pattern “many
  points force algebraic blocks,” but only for its definable/height-counting
  setting.  Global oscillatory matrix exponential, approximation tubes, and
  circuit-language growth are absent.
- Rigorous Brown--Susskind growth results currently use random circuits,
  Brownian/stochastic Hamiltonians, or completed-time design arguments.
  They do not prove the static quenched inverse law (5).

No audited source gives (7), the observer branch (8) as a circuit-complexity
escape ceiling, or the sharp Pauli claim (9).  This is not a priority claim;
the literature audit remains incomplete enough that all new results retain
`[NOVELTY UNVERIFIED]`.

## Final hostile verdict

The preliminary verdict was too generous.  The proposed law fails Gate 2
before its inverse can be attacked: it is not an exact, well-typed conjecture.

1. “Uniformly tame,” “finite format,” “controlled complexity,” the allowed
   compiler model, tube radius `r`, overlap multiplicity, the pre-capacity
   window, and both occurrences of `o(m_n)` are unspecified.  Different
   legitimate choices change `g_*`, so (5) and (7) have no fixed truth value.
2. If the format class is broad enough to contain an arbitrary circuit
   selector, (5) is circular.  If it is restricted to the listed affine,
   periodic, or weakly special examples, it excludes possible nonlinear
   shortcut organizations by definition and is not universal.
3. Raw circuit-language growth is exponential in the allowed word length,
   not polynomial in `R`.  Re-encoding it as `R^(h_F)` either makes `h_F`
   scale-dependent and potentially larger than `m_n`, trivializing (3), or
   discards the very selector entropy the inverse theorem must control.
4. Positive shortcut mass does not imply an efficiently computable compiler:
   existence of a short circuit and ability to select one from the
   Hamiltonian coefficients are different complexity statements.  The card
   silently moves between them.

Thus (7) is not a conjecture awaiting a hard proof; its central invariant is
not yet defined independently of the desired conclusion.  It is retired as a
universal law.

### Relentless-interrogation replacement

The killing mechanism says the next claim must avoid a prose category of
“organized” shortcuts and must quantify the actual circuit selector directly.
The replacement is the exact flagship-ensemble conjecture in
`observer-rank-autonomous-no-shortcut-law.md`: for the full fixed-`q` Pauli
Gaussian ensemble, the aggregate shortcut probability has power-law exponent
equal, to leading order, to the observer/QFI rank.  This is bolder and more
falsifiable than (7): it names the probability space, gate model, time window,
budget, and exponent, and it can be killed by one explicit larger shortcut
family without debating what counts as a format.

### Positive survivor

The energy--entropy addition `m-d-h` remains valid for every independently
certified mixed continuous/lattice carrier, by the Stage-2 mixed-carrier
theorem.  That is a lower obstruction, not an inverse classification.  Its
paper status remains `[PAPER-PROVED] [NOVELTY UNVERIFIED]`; no Lean theorem is
yet claimed.

## Superseded open cores

**Verdict:** `FALSIFIED AS AN EXACT CONJECTURE`.

`[OPEN CORE A]` Replace the prose “certified shortcut format” by a precise
algebraic/algorithmic category closed under the known commuting, Cartan,
quadratic, block, observer-stabilizer, and mixed-periodic examples but unable
to enumerate an arbitrary shortcut set.

`[OPEN CORE B]` Prove the inverse block estimate (5): the non-format part of
the complete circuit-selector pullback has a uniform power saving after the
full growing architecture union.

`[OPEN CORE C]` Prove or falsify the fixed-`q` Pauli minimizer (9).  A
counterexample must exhibit an independently certified carrier whose
continuous dimension plus component entropy exceeds
`m_n-v_Phi+o(m_n)`.

No Lean work is authorized on (5), (7), or (9) before a complete paper proof.
The paper-proved observer and mixed-carrier lower laws have separate Stage-2
cards and are the only current formalization candidates.
