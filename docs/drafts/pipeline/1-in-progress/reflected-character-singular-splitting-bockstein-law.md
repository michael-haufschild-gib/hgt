# Reflected-character singular-splitting Bockstein law

- **ID:** `reflected-character-singular-splitting-bockstein-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / RH INTERFACE / BOLD CONJECTURE
- **Parents:**
  - `../3-formalized/new_scientific_knowledge/prime-first-trace-essential-normal-bockstein.md`;
  - `../2-fully-proven/new_scientific_knowledge/gamma-copoisson-sonin-full-quotient-flatness-syzygy.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/source-linear-essential-superselection-no-sewing.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/prime-log-action-condensation-normal-cone-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/finite-boolean-hochschild-diagonal-cofinal-fracture.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/wold-boolean-diagonal-renormalization-mismatch.md`;
  - `../5-failed/burnol-copoisson-prime-seam-calkin-lift.md`.
- **Statement:** Distinct characters of a commutative source algebra admit no nonzero internal
  derived morphism in any degree.  Relative Hochschild-one splitting is its degree-one shadow.
  The Gamma factorial conormal is exactly the local co-Poisson divided-difference cell, whose
  confluence is a nonzero logarithmic tangent class.  Therefore a nonzero source-first Xi
  conormal landing on the reflected derived diagonal forces the critical line.

## Goal

Replace the vague instruction “find an essential operator sewing reflected sectors” by one exact
cohomological mechanism and one exact remaining source theorem.  The mechanism must explain at
once:

1. why fixed finite-Rees morphisms erase the reflected irregular sector;
2. why arbitrary infinite rank and arbitrary essential growth do not help;
3. why every closed source-linear off-line relation splits;
4. why the compactly supported co-Poisson divided difference is the correct local source cell;
5. why a divisor conormal is a Bockstein rather than an ordinary boundary vector; and
6. why the critical line is a collision locus, not the sign locus of a scalar inequality.

The algebraic theorem below is unconditional.  RH still requires the explicitly labelled
source-normal landing conjecture in the final section.

## 1. Relative character cohomology

Let \(k\) be a field, let \(A\) be a commutative unital \(k\)-algebra, and let
\(\alpha,\beta:A\to k\) be characters.  Write \(k_{\alpha,\beta}\) for the one-dimensional
\(A\)-bimodule
\[
 a\cdot z=\alpha(a)z,
 \qquad
 z\cdot a=z\beta(a).
\tag{1}
\]
A Hochschild one-cocycle with these coefficients is a \(k\)-linear map \(d:A\to k\) satisfying
\[
 d(ab)=\alpha(a)d(b)+d(a)\beta(b).
\tag{2}
\]
Its inner cocycles are
\[
 d_c(a)=c\bigl(\alpha(a)-\beta(a)\bigr).
\tag{3}
\]

### Theorem 1 — distinct-character splitting

If \(\alpha\ne\beta\), then every cocycle `(2)` is inner.  Equivalently,
\[
 \boxed{\qquad
 HH^1(A,k_{\alpha,\beta})=0
 \quad\text{whenever }\alpha\ne\beta.
 \qquad}
\tag{4}
\]

### Proof

Commutativity and `(2)` give
\[
 \alpha(a)d(b)+d(a)\beta(b)
 =
 \alpha(b)d(a)+d(b)\beta(a),
\]
hence
\[
 d(b)\bigl(\alpha(a)-\beta(a)\bigr)
 =
 d(a)\bigl(\alpha(b)-\beta(b)\bigr).
\tag{5}
\]
Choose \(b\) with \(\alpha(b)\ne\beta(b)\).  Then
\[
 d(a)
 =
 {d(b)\over\alpha(b)-\beta(b)}
 \bigl(\alpha(a)-\beta(a)\bigr)
\tag{6}
\]
for every \(a\), which is `(3)`.  `QED`

This proof is purely algebraic.  Discontinuity, unbounded growth, infinite Hilbert dimension,
essential operator norm, and an infinite number of Rees grades cannot produce a nontrivial
relative one-class while the object remains a cocycle over the same commutative source algebra.

### Theorem 2 — collision creates the tangent class

Let \(M=\mathbb N_{>0}\) under multiplication and \(A=k[M]\).  Over \(k=\mathbb C\), for any
multiplicative character \(\chi:M\to\mathbb C^\times\), the rule
\[
 \partial_{\log}[n]=\chi(n)\log n
\tag{7}
\]
extends linearly to a nonzero \((\chi,\chi)\)-derivation.  Since every inner
\((\chi,\chi)\)-derivation is zero,
\[
 [\partial_{\log}]
 \ne0
 \quad\text{in}\quad
 HH^1(A,\mathbb C_{\chi,\chi}).
\tag{8}
\]

### Proof

For basis elements,
\[
\begin{aligned}
 \partial_{\log}[mn]
 &=\chi(mn)(\log m+\log n)\\
 &=\chi(m)\partial_{\log}[n]
   +\partial_{\log}[m]\chi(n).
\end{aligned}
\]
Linearity gives the Leibniz rule on \(A\).  The value at every prime is nonzero.  Formula `(3)`
vanishes identically when its two characters agree.  `QED`

Thus relative character cohomology has a sharp support law:
\[
\boxed{\quad
 \text{off the character diagonal: every one-extension splits;}
 \qquad
 \text{on the diagonal: logarithmic tangent classes can survive.}
\quad}
\tag{9}
\]

## 2. The co-Poisson divided difference is the singular splitting

For complex parameters \(z,w\), define
\[
 \chi_z(n)=n^{z-1/2}.
\tag{10}
\]
For \(z\ne w\), the divided difference
\[
 \delta_{z,w}[n]
 =
 {\chi_z(n)-\chi_w(n)\over z-w}
\tag{11}
\]
satisfies
\[
 \delta_{z,w}[mn]
 =
 \chi_z(m)\delta_{z,w}[n]
 +
 \delta_{z,w}[m]\chi_w(n).
\tag{12}
\]
It is the inner cocycle with primitive \(c=(z-w)^{-1}\).  On the diagonal it has the confluent
limit
\[
 \delta_{w,w}[n]
 =
 \chi_w(n)\log n,
\tag{13}
\]
which is the nonzero outer class `(7)`.

At one prime \(p\), `(11)` is exactly the compact-log-support Burnol/co-Poisson cell
\[
 {p^{z-1/2}-p^{w-1/2}\over z-w}
 =
 p^{w-1/2}\int_0^{\log p}e^{(z-w)u}\,du.
\tag{14}
\]
The source cell is therefore not merely analogous to a Bockstein.  It is the canonical family
of splittings of two distinct source characters.  Its primitive leaves the category at
confluence, and its residue is the logarithmic point-derivation class.

The local spectral confluence has the following exact form:

```text
arbitrary essential growth:
  no selection;

off-diagonal divided difference:
  an exact/inner relative cocycle;

character collision:
  splitting primitive becomes singular;

confluent residue:
  a nonzero outer logarithmic Bockstein.
```

### Correction — spectral confluence is not Rees essentiality

The scalar pole in `(11)` is only a singularity in the spectral separation \(z-w\).  It is not
the essential singularity in the cofinal Wold cutoff proved by the all-orders-flat theorem.  The
two statements have different variables and neither implies the other:

- for fixed \(z\ne w\), the algebraic divided-difference primitive \((z-w)^{-1}\) is a constant,
  while an exact sewing of the two reflected Wold sectors has norm beyond every finite Rees
  order;
- at \(z=w\), the spectral primitive ceases to exist and leaves the logarithmic tangent class,
  while the two reflected asymptotic sectors coincide and no flat-to-half-normal sewing is
  required.

Thus the earlier wording that `(11)` was “the precise kind of singularity required” was false.
The corpus instead exhibits a **singularity transmutation**:

```text
off the character diagonal:
  derived class vanishes algebraically;
  any analytic sector identification is external and essentially singular;

on the character diagonal:
  external sector mismatch vanishes;
  the internal logarithmic tangent/derived self-intersection survives.
```

The RH-bearing theorem must show that an Xi conormal is the second, internal kind.  Essential
growth alone points toward the first kind and therefore cannot select the critical line.

## 2A. All-degree reflected-diagonal support law

Let \(A\) be a commutative \(k\)-algebra and let \(k_\alpha,k_\beta\) be the one-dimensional
modules defined by two characters.  Then for every \(q\geq0\),
\[
\boxed{\qquad
 \operatorname{Ext}_A^q(k_\alpha,k_\beta)=0
 \quad\text{if }\alpha\ne\beta.
\qquad}
\tag{14a}
\]

Indeed, the two central \(A\)-actions on
\(\operatorname{Ext}_A^q(k_\alpha,k_\beta)\) agree.  For \(a\in A\), the action through the first
endpoint is multiplication by \(\alpha(a)\), while the action through the second endpoint is
multiplication by \(\beta(a)\).  Hence every class \(\xi\) satisfies
\[
 (\alpha(a)-\beta(a))\xi=0.
\tag{14b}
\]
If the characters differ, choose \(a\) for which the scalar in `(14b)` is nonzero; then
\(\xi=0\).

For
\[
 A=\mathbb C[\mathbb N_{>0}]
 \simeq\mathbb C[x_p:p\ {\rm prime}],
\tag{14c}
\]
the diagonal self-extension space is large.  A point derivation is determined freely by its
values on the prime generators, and the distinguished logarithmic tangent has
\[
 \partial_{\log}(x_p)=\chi(p)\log p.
\tag{14d}
\]
Thus the diagonal is not a rank-one truncation.  It carries the complete countable prime
cotangent, while the Xi principal conormal may select one nonzero logarithmic direction in it.

Theorem 1 is exactly the \(q=1\) cocycle calculation behind `(14a)`.  The all-degree statement is
the more natural RH interface because a source-normal exact couple may place the multiplicity
class in a degree or complex not known in advance.

This support law unifies several proved corpus results:

```text
relative Hochschild splitting:
  degree-one algebraic shadow;

closed source-linear relation splitting:
  spatial C*-completion shadow;

finite Boolean separability contractions:
  finite diagonal resolution;

failure of cofinal Boolean diagonals to converge:
  strict infinite diagonal is missing;

Wold thermofield standard form:
  non-scalar diagonal correspondence survives;

finite-Rees flat-radical conservation:
  filtered external transport cannot replace the diagonal;

Gamma/co-Poisson divided difference:
  local contracting homotopy off diagonal and tangent residue on diagonal;

Sonin full-quotient syzygy:
  finite higher coherence of the same local resolution.
```

What remains is not a new sign theorem.  It is the construction of one strict all-prime
**derived diagonal** carrying the Gamma anomaly and the literal Xi conormal boundary.

## 2B. Exact Gamma-factorial/co-Poisson local comparison

Put
\[
 C(\zeta)=\sum_{n\ge0}{\zeta^n\over(n+1)!}.
\tag{14e}
\]
The complete Gamma Taylor conormal has precisely these coefficients, and
\[
 \zeta C(\zeta)=e^\zeta-1.
\tag{14f}
\]
For a logarithmic interval of length \(L\), define
\[
 \Theta_L(z,w)
 =
 e^{(w-1/2)L}L\,C((z-w)L).
\tag{14g}
\]
Then, without excluding the diagonal,
\[
 (z-w)\Theta_L(z,w)
 =
 e^{(z-1/2)L}-e^{(w-1/2)L}.
\tag{14h}
\]
Consequently, off diagonal \(\Theta_L\) is the usual divided difference, while
\[
 \Theta_L(w,w)=e^{(w-1/2)L}L.
\tag{14i}
\]
The same cell obeys exact logarithmic-interval concatenation:
\[
\boxed{\quad
 \Theta_{L_1+L_2}(z,w)
 =
 e^{(z-1/2)L_1}\Theta_{L_2}(z,w)
 +
 \Theta_{L_1}(z,w)e^{(w-1/2)L_2}.
\quad}
\tag{14i+}
\]
Thus \(\Theta\) is a \((\chi_z,\chi_w)\)-derivation for the additive log-action monoid, not
merely a matching scalar formula.  Taking \(L_1=\log m\) and \(L_2=\log n\) gives the
multiplicative source rule at \(mn\).  Associativity and prime-order independence come from
addition of logarithmic actions, so finite Tate/Kummer intervals, Gamma factorial conormals, and
compact co-Poisson interval sources have one strict chain-level character.

At the reflected endpoints
\[
 z=1-\rho,\qquad w=\overline\rho,
\tag{14i++}
\]
the endpoint characters are exactly \(n^{1/2-\rho}\) and
\(n^{\overline\rho-1/2}\).  Off the critical line `(14h)` has the inner primitive divided by
\(1-\rho-\overline\rho\).  On the critical line that primitive ceases to exist and `(14i)` is the
logarithmic tangent character.  This finite-action component is constructed without selecting an
Xi zero.

Taking \(L=\log p\) proves that the complete factorial-tail Gamma conormal and the compact
Burnol/co-Poisson interval cell `(14)` are literally the same local source object.  This is now
formalized in
`formal/GaloisForLFunctions/RHTower/GammaCoPoissonIntervalFactorialBridge.lean`.

The same entire cell retains every finite conormal order:
\[
\boxed{\quad
 \left.\partial_z^k\Theta_L(z,w)\right|_{z=w}
 =
 e^{(w-1/2)L}{L^{k+1}\over k+1}.
\quad}
\tag{14i+++}
\]
For \(L\ne0\), `(14i+++)` never vanishes.  Thus Gamma factorial compression does not collapse a
finite multiplicity jet at spectral confluence.  The proof factors \(\Theta_L\) as the removable
divided slope of \(e^{Lz}\), then applies the exact all-order divided-slope/Taylor-jet law.  This
closes local multiplicity faithfulness; it does not prove that the all-prime Xi Cartier conormal
reaches this receiver.

There is also an unconditional all-action comparison in the absolute-convergence region.  If
\[
 B(s)=\sum_{n\ge1}\mu(n)n^{-s}={1\over\zeta(s)}
 \qquad(\Re s>1),
\tag{14j}
\]
then absolute convergence permits termwise subtraction:
\[
 \sum_{n\ge1}\mu(n)
 {n^{-z}-n^{-w}\over z-w}
 =
 {B(z)-B(w)\over z-w}.
\tag{14k}
\]
At confluence, `(14k)` is \(B'(w)\), the Möbius-log action current.  Hence local factorial
conormals do assemble to the reciprocal-zeta divided difference before continuation.  The exact
failure is now visible: `(14k)` does not by itself continue as a strict all-prime derived
diagonal carrying the Wold standard-form marginal and the Xi top conormal at a pole.

## 2C. Dimension-free flatness forces an irregular nearby-cycle ontology

The arbitrary-dimensional finite-Rees theorem rules out a whole class of proposed “third
completions,” not only finite matrices.  If every transition family has full operator norm of
some fixed finite Rees order, then it preserves the all-orders-flat radical in every dimension.
Countable rank, an inductive Hilbert limit, or a larger ambient vector space changes nothing while
its structure maps remain in that class.

The first-trace essential-normal theorem shows what does survive.  One must first remove the
already attained response face and then rescale at the next exponential action.  For the actual
prime graph this gives the canonical boundary edge
\[
 \bigl((\log p)X_p,\;p\,\Pi_1^\perp Y_p\bigr)
 \longrightarrow (e_1,Se_1)=(e_1,e_2).
\tag{14l}
\]
This is not an operator sewing two completed Hilbert sectors.  It is a nearby-cycle operation on
the source graph before closure.  Essential singularity is therefore a change of base/scale, not
permission to choose an arbitrarily fast unbounded multiplier.

The factorial coefficients in `(14e)` supply the exact analytic receiver of this kind of normal
ladder.  They are Borel-type data: factorial compression converts the raw power-jet ladder into
the entire interval cell, while `(14i+)` converts shift/concatenation into the relative-character
cocycle.  This does **not** assert that Xi has a resurgent presentation or that generic Stokes
data prove RH.  It identifies the precise source-defined fragment that an irregular completion
must extend.

`[BOLD CONJECTURE] [PRIME_IRREGULAR_NEARBY_CYCLE_LAW]`

> The ordinary-prime Euler--Gamma preclosure admits a Hausdorff irregular nearby-cycle functor
> \(\Psi_{\rm irr}\), indexed by the complete squarefree log-action scale, such that:
>
> 1. its finite-Rees shadow kills the all-orders-flat radical, but its essential associated
>    boundary contains every iterated face-removal class extending `(14l)`;
> 2. its factorial analytic realization is exactly \(\Theta_L\) and respects `(14i+)`;
> 3. its non-scalar Wold realization is the thermofield/Boolean diagonal rather than the
>    nonexistent scalar cofinal diagonal;
> 4. its literal boundary realization is the Gamma-completed co-Poisson/Sonin quotient with the
>    proved source-error syzygy; and
> 5. failure of source completion, reflection, and analytic adjunction to commute is a strict
>    internal nearby-cycle class whose Xi Cartier fibre is the nonzero top divisor conormal.

Clause 5 is the RH-bearing source theorem.  The point of the conjecture is not to rename it:
clauses 1--4 prescribe a pre-divisor construction and exclude arbitrary essential sewings,
zero-indexed Stokes symbols, and target-fed logarithms of Xi.  If clause 5 holds, its two central
actions are the reflected characters `(15)`; all-degree diagonal support then forces the critical
line.

This is the proposed universal law behind the corpus:

```text
finite Rees no-go       = perturbative shadow kills irregular nearby cycles
essential normal edge  = first nonzero nearby-cycle chart
Gamma factorial cell   = analytic factorial realization
Tate/Kummer interval   = algebraic action-resolution realization
Wold thermofield       = non-scalar standard-form realization
Sonin source syzygy    = boundary descent/flatness realization
Xi conormal            = completion-curvature fibre
critical line          = reflected-character diagonal support
```

## 2D. Exact construction gap: critical factorial--Sonin synthesis

The preceding ontology still hides one typing problem.  Sonin's strong cofinal transport acts on
Euler/source coordinates, whereas the Gamma factorial coordinate in `(14e)` is jet order.  A
normal-family argument on factorial coherent vectors cannot be applied until these two coordinate
systems are joined by a source-defined synthesis.  The obvious synthesis is already ruled out:
the standard factorial-Fock all-prime incidence has unbounded prime columns.  The even-factorial,
Gamma-damped incidence is Hilbert--Schmidt only in the safe lane
\(\operatorname{Re}s>1/2\); it does not furnish a boundary map at the critical action scale.

`[BOLD CONJECTURE] [XI_CRITICAL_FACTORIAL_SONIN_SYNTHESIS]`

> There is a source-defined family \(\Sigma_x\), initially for \(x>1/2\), from the factorial
> jet/interval preclosure to the ordinary Euler preclosure such that:
>
> 1. every finite-prime restriction is the synthesis of the exact interval cell
>    \(\Theta_{\log n}\) and hence obeys `(14i+)`;
> 2. in the safe lane it agrees with the proved Gamma-damped even-factorial incidence;
> 3. as \(x\downarrow1/2\), after the canonical attained-face removal and essential normal
>    rescaling, \(\Sigma_x\) has a nonzero Hausdorff corona class, although it need not have a
>    bounded Hilbert-space limit;
> 4. one cofinal Sonin schedule transports the factorial coherent germs locally uniformly in
>    this irregular topology; and
> 5. the resulting literal co-Poisson/Sonin boundary class is nondivisible and its strict Xi
>    Cartier base change is the top divisor conormal.

Items 1--2 are constrained by existing corpus theorems; item 3 is the missing third completion;
item 4 is the required upgrade from scalar/countable coordinate transport to an analytic
normal-family transport; item 5 is RH-bearing.  This formulation does not ask for an infinite-rank
multiplier.  It asks for a renormalized source graph whose essential normal class survives after
every fixed finite-Rees shadow has vanished.

## 3. Reflected characters and the critical line

For a strip point \(\rho\), define on \(M\)
\[
 \alpha_\rho(n)=n^{1/2-\rho}
 \quad\text{(source inverse)},\qquad
 \beta_\rho(n)=n^{\overline\rho-1/2}
 \quad\text{(analytic adjoint)}.
\tag{15}
\]
Their ratio is
\[
 {\beta_\rho(n)\over\alpha_\rho(n)}
 =
 n^{\,2\operatorname{Re}\rho-1}.
\tag{16}
\]
Consequently
\[
 \alpha_\rho=\beta_\rho
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.
\tag{17}
\]
It is enough to evaluate `(16)` at \(n=2\).

For \(\operatorname{Re}\rho\ne1/2\), the reflected divided difference
\[
 d_\rho[n]
 =
 {\beta_\rho(n)-\alpha_\rho(n)\over
  2\operatorname{Re}\rho-1}
\tag{18}
\]
is an inner \((\beta_\rho,\alpha_\rho)\)-cocycle.  As
\(\operatorname{Re}\rho\to1/2\) at fixed imaginary part, it tends to the outer logarithmic
derivation
\[
 n^{-i\operatorname{Im}\rho}\log n.
\tag{19}
\]

Thus the horizontal Julia residue, prime-transfer Lyapunov exponent, and relative Sonin torsion
measure distance from the support of the relative cohomology class.  They are not the class
itself.  Off-line systems may realize those nonzero scalar charges while their reflected
one-extension remains split.

## 4. Conditional RH consumer

### Theorem 3 — RH from nonzero reflected Bockstein landing

Assume that for every nontrivial Xi zero \(\rho\), the ordinary-prime
Euler--Gamma/co-Poisson source-normal exact couple supplies a class
\[
 {\mathfrak b}_\rho
 \in
 HH^1\!\left(
   \mathbb C[\mathbb N_{>0}],
   \mathbb C_{\beta_\rho,\alpha_\rho}
 \right)
\tag{20}
\]
whose image on the top multiplicity conormal is nonzero.  Then RH holds.

### Proof

If \(\operatorname{Re}\rho\ne1/2\), `(17)` gives
\(\alpha_\rho\ne\beta_\rho\), so Theorem 1 makes the group in `(20)` zero, contradicting
nonvanishing.  Therefore every nontrivial zero satisfies
\(\operatorname{Re}\rho=1/2\).  `QED`

The theorem uses neither positivity nor a norm estimate.  It does not require two independent
prime directions on the specialized conormal.  The positive HT divisor frame already proves that
such rank need not survive specialization.  Only nontriviality modulo inner splittings matters.

### Theorem 4 — all-degree derived-diagonal RH consumer

Assume instead that every nontrivial Xi zero supplies a nonzero internal class
\[
 0\ne\xi_\rho\in
 \operatorname{Ext}_A^{q_\rho}
   (\mathbb C_{\alpha_\rho},\mathbb C_{\beta_\rho})
\tag{20a}
\]
for some degree \(q_\rho\), with the two central actions induced by the fixed ordinary-prime
source algebra.  Then RH holds.

The proof is immediate from `(14a)` and `(17)`.  This is strictly more flexible than Theorem 3:
it does not prescribe Hochschild degree one, a scalar cocycle model, or simplicity.  Multiplicity
may be retained by a complex, filtration, or confluent jet as long as one top class is nonzero.

The vector-level dependency-closed consumer is formalized by:

- `relativeCharacters_eq_of_nonzero_carrier`;
- `criticalLine_of_nonzero_reflectedCharacterCarrier`;
- `riemannHypothesis_of_nonzero_reflectedCharacterCarrier`.

These theorems expose nonzero carrier landing as a hypothesis; they do not instantiate an
`Ext` group or manufacture the Xi class.

## 5. Exact remaining theorem

`[BOLD CONJECTURE] [XI_DERIVED_REFLECTED_DIAGONAL_LANDING]`

There is a strict all-prime source-normal derived correspondence
\(\mathfrak D_{\Xi}^{\rm src}\), constructed before divisor specialization, such that:

1. every finite-prime restriction is the canonical Tate/Kummer interval resolution and its
   Boolean separability diagonal;
2. its analytic local character is the factorial-conormal/co-Poisson cell `(14g)`, not an
   independently fitted kernel, its finite action gluing is the exact cocycle `(14i+)`, and every
   finite multiplicity jet survives by `(14i+++)`;
3. its all-prime realization is supplied by `XI_CRITICAL_FACTORIAL_SONIN_SYNTHESIS` and retains
   both the non-scalar Wold thermofield diagonal and the Gamma first-trace/anomaly channel,
   without scalarizing either;
4. its boundary functor is the literal Gamma-completed co-Poisson/Sonin quotient and carries the
   proved source-error syzygy;
5. after strict Xi Cartier base change, the top multiplicity conormal at every zero \(\rho\)
   gives a nonzero cohomology class whose two central source actions are
   \(\alpha_\rho\) and \(\beta_\rho\); and
6. construction, strictness, and nonvanishing are independent of a zero list, a fitted
   reflection operator, or an RH-equivalent boundary norm.

Clause 5 and Theorem 4 imply RH.  Clauses 1--4 are not decorative: they specify the source
construction from corpus objects and distinguish the conjecture from simply declaring that
the Xi conormal lies on the character diagonal.

The earlier degree-one label below is a possible realization of this conjecture, not an
independent terminal demand.

`[BOLD CONJECTURE] [XI_REFLECTED_CHARACTER_SINGULAR_SPLITTING_LANDING]`

The strict source-normal exact-couple morphism
\[
 \Phi_{\rm src}:
 {\mathfrak B}_{\rm first\ trace}
 \longrightarrow
 {\mathfrak B}_{\Gamma/{\rm coP}/{\rm Sonin}}
\tag{21}
\]
has a reflected-character Hochschild realization with all of the following properties:

1. the local prime component is the literal divided-difference cell `(14)`;
2. its finite primitive is the nondivisive source-error syzygy already proved for the full
   co-Poisson quotient;
3. squarefree action condensation is performed before divisor specialization and before ordinary
   Hilbert closure;
4. the source inverse and analytic adjoint actions on its target coefficient line are exactly
   \(\alpha_\rho\) and \(\beta_\rho\) from `(15)`;
5. its Bockstein is the full Xi principal conormal, including every top multiplicity jet; and
6. that Bockstein is nonzero modulo inner relative cocycles.

Then Theorem 3 proves RH.

This degree-one formulation weakens the previous metric terminal demand, but it may still be too
specific.  The all-degree conjecture above is the current open core.  One need not first prove
equality of inverse and adjoint scalars by a metric theorem; one must construct a nonzero internal
derived class typed by both actions.  Diagonal support then forces equality.

## 6. Hostile audit

1. **Not RH.**  Items 3--6 of the landing conjecture are open.  Theorem 3 is a conditional
   consumer, not a proof of its premise.
2. **Parent algebra.**  Twisted derivations, Hochschild one-cocycles, inner derivations, and point
   derivations are established mathematics.  Theorem 1 is elementary.  No novelty is claimed for
   it separately.
3. **A self-Bockstein is insufficient.**  Every zero \(\rho\), on or off the line, has a
   logarithmic self-extension in
   \(HH^1(A,\mathbb C_{\chi_\rho,\chi_\rho})\).  The load-bearing datum is the single class typed
   simultaneously by source inverse and analytic adjoint as in `(20)`.
4. **The chain-level syzygy is insufficient.**  The proved Gamma/co-Poisson/Sonin syzygy identifies
   the finite primitive, but it does not yet prove that its completed Bockstein is nonzero in
   `(20)`.
5. **Bulk rank is insufficient.**  The positive hypertranscendental divisor frame has countably
   maximal transverse differential rank and a one-dimensional common divisor mode.  This kills
   the earlier attempted inference from source rank to conormal rank.
6. **Topology cannot rescue the wrong class.**  If a proposed completed object is still an
   honest relative one-cocycle over the same commutative source algebra, Theorem 1 splits it off
   line without any boundedness assumption.  A surviving object must therefore be the Bockstein
   of the singular splitting before ordinary closure, not a closed operator introduced
   afterwards.
7. **Generalized-prime falsifier.**  An off-line generalized-prime Euler system can carry the same
   scalar reflection, completion, orientation, and HT data.  In the present ontology its
   reflected cross-class must either split, fail source-normal nonvanishing, or fail the literal
   ordinary-integer Gamma/co-Poisson landing.  Any proof of the conjecture using only the shared
   scalar data is false.
8. **No renamed dagger theorem.**  The conjecture is useful only if `(21)` is constructed from the
   compact source cells and action condensation.  Declaring the Xi conormal to be a nonzero class
   in `(20)` would assume the conclusion in a new language.
9. **Two singularities must not be conflated.**  A simple pole in spectral separation does not
   supply the beyond-all-Rees cutoff growth, and essential cutoff growth does not create an
   internal derived class.  The source totalization must compare both variables explicitly.
10. **Derived support can be circular.**  Merely assigning the fibre in `(20a)` is already an RH
    selector.  Progress begins only with a pre-divisor construction satisfying clauses 1--4 and
    a proof that Cartier base change gives clause 5.
11. **Infinite Rees rank is not the irregular boundary.**  The proved Fisher--Gamma certificate
    retains arbitrarily large finite-prime symbol rank and preserves prime summability.  The
    dimension-free flat-radical theorem shows that this still does not cross the asymptotic-type
    wall.  It is input to \(\Psi_{\rm irr}\), not its construction.
12. **“Stokes” is not a proof word.**  Generic resurgence of a zeta or Gamma transform supplies
    asymptotic expansions and Stokes coefficients, not the ordinary-prime internal class in
    `(20a)`.  Any Stokes formulation that first takes \(\log\Xi\) or indexes jumps by Xi zeros is
    target-fed and rejected.
13. **A factorial normal-family lemma is not the missing synthesis.**  Once a uniformly bounded
    source synthesis exists, factorial tails can upgrade convergence on a growing finite prefix
    to locally uniform convergence of coherent germs.  Here that premise is exactly unavailable:
    standard factorial synthesis is unbounded, while the proved even-factorial synthesis lives
    only in the safe half-plane.  Treating jet order and Euler coordinate as the same index would
    be a type error, not progress.

## 7. Literature boundary

The parent language of \((\phi,\psi)\)-derivations and their continuity on \(C^*\)-algebras is
explicit in Hejazian--Janfada--Mirzavaziri--Moslehian, *Achievement of continuity of
\((\phi,\psi)\)-derivations without continuity*, arXiv:math/0611016.  Complete and torsion
derived Hochschild functors for adic commutative algebras are treated by Shaul, *Derived
Hochschild functors over commutative adic algebras*, arXiv:1307.5658.  The elementary
distinct-character splitting theorem belongs to that parent algebraic landscape.

Andersen, *Resurgence Analysis of Meromorphic Transforms*, arXiv:2011.01110, gives a general
Borel-resummable/Stokes framework whose examples include Gamma and zeta transforms.  This
confirms that factorial/resurgent language is parent mathematics.  It does not construct the
ordinary-prime action-indexed nearby-cycle functor, the literal co-Poisson/Sonin landing, or an
RH-support theorem.  The candidate-new content is the conjunction in
`PRIME_IRREGULAR_NEARBY_CYCLE_LAW`, not Borel summation itself.

Targeted searches found no source connecting:

- the Burnol compact-log-support divided difference;
- its confluence from an inner reflected-character cocycle to an outer logarithmic point
  derivation;
- the prime first-trace essential normal Bockstein;
- the full Gamma/co-Poisson/Sonin source-error syzygy; and
- the Xi critical-line condition

through `(20)`--`(21)`.  This is only a preliminary noncollision result, not a priority claim.

## Lean decision

Theorems 1--3 are dependency-closed algebra.  Formalization is warranted only as the exact
consumer interface for `(21)`, not as a stand-alone novelty claim.  First search the current
formal corpus for the bimodule/Hochschild vocabulary and choose the smallest representation that
does not import an unnecessary homological library.  Do not formalize the landing conjecture as
an assumption disguised as a structure field.

`[LEAN-PROVED UPDATE]` The dependency-closed part is now formalized without constructing the open
landing:

- `formal/GaloisForLFunctions/HTGeometry/RelativeCharacterDerivation.lean`
  - `relativeCharacterCoboundary_isRelativeCharacterDerivation`;
  - `isInnerRelativeCharacterDerivation_of_ne`;
  - `relativeCharacters_eq_of_not_inner`;
  - `not_inner_of_eq_of_exists_ne_zero`.
- `formal/GaloisForLFunctions/RHTower/ReflectedCharacterBocksteinRH.lean`
  - `criticalLine_of_nonInner_reflectedCharacterDerivation`;
  - `riemannHypothesis_of_nonInner_reflectedCharacterBockstein`;
  - `criticalLine_of_nonzero_reflectedCharacterCarrier`;
  - `riemannHypothesis_of_nonzero_reflectedCharacterCarrier`.
- `formal/GaloisForLFunctions/RHTower/GammaCoPoissonIntervalFactorialBridge.lean`
  - `mul_gammaFactorialComplexCompression`;
  - `spectralBoundary_mul_gammaCoPoissonIntervalCell`;
  - `gammaCoPoissonIntervalCell_eq_dividedDifference`;
  - `gammaCoPoissonIntervalCell_self`;
  - `gammaCoPoissonIntervalCell_add`;
  - `gammaCoPoissonIntervalCell_eq_dslope`;
  - `iteratedDeriv_gammaCoPoissonIntervalCell_self`;
  - `iteratedDeriv_gammaCoPoissonIntervalCell_self_ne_zero`.

The RH theorem exposes cocycle landing, non-innerness, and both reflected norm calibrations as
hypotheses.  It does not package them into an inhabited structure or assert their construction.
Both leaf files pass `lake env lean`; project formal lint passes; the final module audit
`lake build GaloisForLFunctions.RHTower.ReflectedCharacterBocksteinRH` succeeds.  `#print axioms`
reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1: exact cocycle theorem, confluence law, RH consumer, source-pure landing conjecture,
  and hostile falsifiers stated
- [x] separate spectral confluence from cofinal Rees essentiality
- [x] prove the all-degree reflected-character support theorem on paper
- [x] identify and Lean-formalize the exact Gamma-factorial/co-Poisson interval cell
- [x] prove its strict logarithmic-action concatenation/relative-character cocycle law
- [x] prove every finite conormal/multiplicity jet survives the local factorial receiver
- [x] formalize the vector-level all-degree support and conditional RH consumers
- [x] isolate the jet-order/Euler-coordinate type mismatch and critical irregular synthesis core
- [ ] 1 → 2: construct `(21)` and prove items 1--6 without selecting a zero-fitted map
- [ ] 2 → 3: formalize Theorems 1--3 and the proved source-normal landing; audit axioms
- [ ] 3 → 4: external specialist audit and standalone paper

## Log

- 2026-07-31 — Killed the attempted bulk-rank argument: the corpus already proves that maximal
  transverse HT rank may collapse to one common divisor mode.  Replaced rank by relative
  cohomology modulo inner splittings.
- 2026-07-31 — Proved distinct-character splitting and the confluent divided-difference law.
  Reinterpreted required essential singularity as the residue of a canonical splitting that
  leaves the category at reflected-character collision.
- 2026-07-31 — Formalized the unconditional algebraic splitting theorem, critical-line consumer,
  and conditional RH interface.  Kept the source-normal landing explicit and unproved.
- 2026-07-31 — Corrected the conflation of spectral and Rees singularities.  Upgraded the
  degree-one cocycle law to the all-degree reflected-diagonal support theorem.  Proved and
  formalized that Gamma's complete factorial conormal is exactly Burnol's local interval
  divided-difference cell.  Isolated the strict all-prime derived-diagonal Xi landing as the
  remaining theorem.
- 2026-07-31 — Proved the interval cell's exact concatenation law.  This identifies finite
  Tate/Kummer intervals, Gamma factorial conormals, co-Poisson intervals, and reflected-character
  derivations as one source cocycle, including spectral confluence.  Finite-action gluing is now
  closed; essential all-prime completion and nonzero Xi Cartier landing remain open.
- 2026-07-31 — Proved the complete confluence-jet formula `(14i+++)` and unconditional
  nonvanishing for every order at every nonzero log action.  Gamma factorial compression cannot
  erase finite divisor multiplicity locally.  Remaining nonvanishing problem is strictly the
  global source-normal Cartier landing, not local analytic jet loss.
- 2026-07-31 — Applied the dimension-free flat-radical theorem to the completion problem.
  Infinite rank cannot cross the finite-Rees wall.  Isolated
  `XI_CRITICAL_FACTORIAL_SONIN_SYNTHESIS`: a critical renormalized synthesis from factorial jet
  order to ordinary Euler coordinates whose essential normal has a nonzero Hausdorff corona
  class.  Standard factorial synthesis is unbounded; the existing even-factorial synthesis is
  confined to the safe half-plane.  No RH conclusion is claimed.
- 2026-07-31 — Corrected the local/global synthesis boundary.  The Hilbert--Hankel kernel
  \(H_{mn}=1/(m+n+1)\) satisfies \(HS=S^*H\), and the exponential Borel transform of its
  \(m\)-th column is exactly the \(m\)-th derivative of the Gamma factorial cell
  \(C(z)=(e^z-1)/z\).  Thus the first-trace Hardy edge and complete Gamma jet ladder have a
  literal local source-normal comparison.  The multiplicative Hilbert matrix supplies the
  all-prime fixed-source dagger and critical contraction but has purely continuous spectrum, so
  it loses divisor fibres.  The open core is not arbitrary essential synthesis: it is the
  polarized preclosure pullback and conormal-faithful
  `XI_SOURCE_NORMAL_STOKES_BOCKSTEIN_DAGGER_LANDING`.  Accelerated Weyl transport and the positive
  HT divisor frame respectively refute essentiality-only selection and rank-to-conormal
  faithfulness.
- 2026-07-31 — Identified and Lean-formalized the moving-horizon Gram law
  \({\bf H}_c(L)=e^{(c-1/2)L}/L\).  The Gamma/co-Poisson cell is exactly its critical and reflected
  finite displacement:
  \({\bf H}_c-{\bf H}_0=(c/L)\Theta_L(c,0)\) and
  \({\bf H}_c-{\bf H}_{-c}=(2c/L)\Theta_L(c,-c)\), while the reflected entry ratio is
  \(e^{2cL}\).  Therefore Gamma interval transport, Sonin reflection defect, and Weyl modular
  drift are one change-of-source-horizon law.  The all-orders-flat theorem forces the
  corresponding diagonal gauge to be essential, but accelerated Weyl shows that essentiality is
  nonselective.  The exact RH-facing selector is now fixed-source horizon descent: every Xi top
  conormal must land nontrivially through one comparison built over \({\bf H}_0\) before
  specialization, without the zero-dependent retuning
  \({\bf H}_0\rightsquigarrow{\bf H}_c\).  That landing remains unproved.
- 2026-07-31 — Differentiated the moving-horizon family.  Its boundary derivative is the
  factorized rank-one kernel
  \(\partial_c{\bf H}_c(m,n)=v_c(m)v_c(n)\),
  \(v_c(n)=n^{c-1/2}\).  Lean proves its squared coefficient mass is summable exactly for
  \(c<0\); off line exactly one of the reflected boundary amplitudes is a Hilbert vector, while
  the other is a nonclosable distribution.  At \(c=0\) both are the same harmonic
  half-density boundary distribution.  This identifies the essential preclosure carrier and
  yields a regularity-parity form of the RH mechanism, but does not discharge the same missing
  step: every Xi top conormal must land nontrivially and dagger-naturally in this fixed-source
  horizon exact couple.
