# Cofinal conormal Picard-purity law

- **ID:** `cofinal-conormal-picard-purity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / RH-BEARING SOURCE CONJECTURE
- **Scientific status:** `[PAPER-PROVED SECTOR THEOREM] [NEW CORPUS SYNTHESIS]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:**
  - `prime-valuation-kakutani-polar-third-completion.md`;
  - `polarized-irregular-source-purity-law.md`;
  - `adjoint-duality-cauchy-nerve-purity-law.md`;
  - `high-shell-critical-hardy-conormal-uniformization.md`;
  - `xi-entire-high-shell-bipolar-completion-graph.md`.
- **Statement:** Finite Euler stages carry an invertible occupation/conormal line whose vacuum
  and first-trace records satisfy the exact zig-zag scalar identity.  A coherent radial twist
  remains an internal invertible line in the fixed critical all-prime sector exactly on the
  critical line.  Therefore RH follows if source-normal Xi conormal localization preserves this
  finite-stage invertibility under cofinal completion.

## 1. What the earlier interpretations missed

The recurring pairs

```text
vacuum survival             versus raw occupation mass;
Hellinger half-density      versus Gamma first trace;
projective direction        versus determinant/norm torsor;
finite conormal line        versus reflected dual line;
source completion           versus conormal localization
```

are not merely reciprocal numbers.  At every finite prime stage they are the coevaluation and
evaluation data of one invertible line.  The formal identity

```text
vacuum amplitude * raw occupation mass = 1
```

is its scalar zig-zag identity.

This changes the infinite question.  The critical line is not primarily a positivity locus.  It
is the locus where the finite conormal line stays **internal and invertible in the same
source-normal sector** after all primes are added.  Off the line the reflected line still exists,
but only as an external correspondence between mutually singular sectors.

## 2. Finite occupation-line identity

For a finite index set \(P\) and nomes \(|q_p|<1\), put
\[
 {\cal M}_P(q)
 =
 \sum_{\nu\in\mathbb N^P}\prod_{p\in P}q_p^{\nu_p},
 \qquad
 {\cal V}_P(q)
 =
 \prod_{p\in P}(1-q_p).                                   \tag{1}
\]
Then
\[
 {\cal M}_P(q)={\cal V}_P(q)^{-1},
 \qquad
 \boxed{{\cal V}_P(q){\cal M}_P(q)=1}.                    \tag{2}
\]

For positive real nomes, \({\cal V}_P\) is the normalized vacuum probability and
\({\cal M}_P\) is the squared norm of the raw occupation vector.  Equation `(2)` is
Lean-proved as
`HTGeometry.finiteOccupation_vacuum_mul_mass` in
`formal/GaloisForLFunctions/HTGeometry/OccupationVacuumAnomalyReciprocity.lean`.

Categorically, let \(L_P\) be the raw occupation line and \(L_P^\vee\) its reflected dual.
Vacuum normalization gives coevaluation
\[
 {\bf1}\longrightarrow L_P\otimes L_P^\vee,
\]
while the first trace gives evaluation
\[
 L_P^\vee\otimes L_P\longrightarrow{\bf1}.
\]
After choosing the canonical raw/vacuum generators, their composite is exactly `(2)`.  Every
finite stage is therefore invertible even though its condition number diverges cofinally.

## 3. Theorem: cofinal sector-internality wall

`[PROVED FROM THE EXISTING KAKUTANI THEOREM]`

Let
\[
 \mu_{p,0}(k)=(1-p^{-1})p^{-k},\qquad k\geq0,             \tag{3}
\]
and for \(c<1/2\),
\[
 \mu_{p,c}(k)
 =
 (1-p^{-(1-2c)})p^{-(1-2c)k}.                            \tag{4}
\]
For finite \(P\), all product measures
\[
 \mu_{P,c}=\bigotimes_{p\in P}\mu_{p,c}
\]
are mutually equivalent.  Hence the coherent radial line
\[
 r_{P,c}(\nu)=\prod_{p\in P}p^{c\nu_p}                   \tag{5}
\]
and its inverse \(r_{P,-c}\) are internal change-of-density lines at every finite stage.

Put
\[
 \mu_c=\bigotimes_p\mu_{p,c},\qquad \mu_0=\bigotimes_p\mu_{p,0}. \tag{6}
\]
Call the cofinal radial line **sector-internal** when the identity change of density is normal
in the fixed standard representation of \(L^\infty(\Omega,\mu_0)\); equivalently
\(\mu_c\) and \(\mu_0\) have the same measure class.  Then
\[
 \boxed{\quad
 r_c\text{ is sector-internal}
 \quad\Longleftrightarrow\quad
 \mu_c\sim\mu_0
 \quad\Longleftrightarrow\quad
 c=0.
 \quad}                                                   \tag{7}
\]

### Proof

Finite equivalence follows because every local probability in `(3)`--`(4)` is strictly
positive.  In the infinite product, Kakutani's theorem makes equivalence equivalent to nonzero
Hellinger product.  The exact local affinity is
\[
 H_p(c)
 =
 \frac{\sqrt{(1-p^{-1})(1-p^{-(1-2c)})}}
 {1-p^{-(1-c)}}.                                         \tag{8}
\]
The rationalized defect contains
\[
 \left(p^{-1/2}-p^{-(1/2-c)}\right)^2.                   \tag{9}
\]
The existing prime-clock reflection theorem proves that the sum of `(9)` over ordinary primes
is finite exactly when \(c=0\).  Thus the product measures are mutually singular for every
nonzero \(c\), and identical for \(c=0\).

The word “internal” is representation-relative.  No claim is made that the abstract commutative
von Neumann algebras of two singular standard probability spaces cannot be isomorphic.

## 4. The factorized conormal anomaly is failure of invertibility

For a divisor point \(\rho\) of multiplicity \(d_\rho\), put
\[
 c_\rho=\frac12-\operatorname{Re}\rho.                   \tag{10}
\]
The corpus gives five exact readings of \(d_\rho c_\rho\):

```text
Riemann tame-regulator period;
bilateral prime-clock exponential slope;
HT shell reflection rate;
two-infinity Kummer boundary dipole;
Wold--Gamma irregular Stokes slope.
```

Equation `(7)` adds a sixth, categorical reading:
\[
 d_\rho c_\rho
 \ne0
 \quad\Longleftrightarrow\quad
 (L_\rho)^{\otimes d_\rho}
 \text{ leaves the critical source sector}.              \tag{11}
\]
Thus the Beck--Chevalley defect for source completion versus principal-conormal localization is
the obstruction to preserving the finite-stage dual pair.  The two-infinity dipole records where
one triangle map escapes; the Gamma anomaly records the divergent norm of the same map; the
Hellinger product records loss of normal overlap.

This explains simultaneously:

1. every finite truncation is invertible and therefore cannot detect the obstruction;
2. finite-Rees operators cannot repair it because sector loss is exponentially flat;
3. bare all-prime \(L^2\) restores covariance but discards the conormal line;
4. enhanced irregular categories retain the external correspondence and therefore admit
   off-line fibres;
5. a single scalar determinant preserves the divisor but forgets which sector contains its
   conormal;
6. multiplicity causes no simplicity assumption: tensoring an invertible line \(d_\rho\) times
   cannot turn a nonzero sector charge into zero.

## 5. Role of the positive hypertranscendental frame

The high-exponent shells already provide an unconditional faithful conormal reporter:
\[
 S_m^\#=\zeta H_m,
 \qquad
 (S_m^\#)^{(d_\rho)}(\rho)
 =
 \zeta^{(d_\rho)}(\rho)H_m(\rho).                         \tag{12}
\]
Their coefficient supports are pairwise disjoint, their common divisor has exact multiplicity,
and their transverse multipliers are countably differentially independent over the full zeta
differential field.

This does not prove sector-internality.  It prevents a false proof from making the triangle
identity true by killing or finitely identifying the conormal.  Invertibility must survive on a
nonzero line simultaneously detected by all the Kolchin-free shell coordinates.  Hypertranscendence
is therefore a **conservativity witness**, not an orientation inequality.

## 6. RH-bearing universal source law

> **[CONJECTURE — XI COFINAL CONORMAL INVERTIBILITY.]**
> The ordinary-integer Poisson/Wold/BV Euler--Gamma source defines a source-normal principal
> conormal line before divisor specialization.  Its finite-prime evaluation and coevaluation maps
> satisfy `(2)`.  Factorized nearby-cycle localization into the standard prime-valuation sector
> is conservative and symmetric monoidal on this line and its reflection dual: it commutes with
> cofinal completion and preserves one, hence both, triangle identities.  The positive
> hypertranscendental shell graph detects the resulting line faithfully with full multiplicity.

The conjecture is not a declaration that a selected zero has a bounded vector.  It is one global
functorial statement, formulated before the divisor is evaluated: the completion/localization
functor preserves the already-existing finite dual pair.

## 7. Conditional RH theorem

Assume `XI COFINAL CONORMAL INVERTIBILITY`, and let \(\rho\) be any nontrivial zero.  The
source-normal BV character identifies its radial exponent with `(10)`.  Preservation of the
finite triangle identity makes its completed conormal line internal and invertible in the
critical sector.  The sector theorem `(7)` gives \(c_\rho=0\), hence
\[
 \operatorname{Re}\rho=\frac12.
\]
Faithfulness of the shell reporter prevents the line from becoming zero.  Tensor-power
compatibility preserves every multiplicity, so the argument does not assume simple zeros.

## 8. New research reduction

The proof no longer needs to construct a self-adjoint operator with Xi eigenvalues or a positive
metric on the whole Meyer quotient.  It is enough to construct and verify one source-natural
triangle map:
\[
 {\bf1}
 \xrightarrow{\operatorname{coev}}
 N_\Xi\widehat\otimes N_\Xi^\vee
 \xrightarrow{\operatorname{ev}}
 {\bf1},                                                   \tag{13}
\]
after source-normal nearby-cycle completion, and prove that `(13)` remains the identity rather
than escaping to the prime-infinity sector.  Required checks are:

1. identify the finite BV/Wold conormal line with the occupation line in `(1)`;
2. identify Gamma genus change with its evaluation norm;
3. prove the strict cofinal base-change functor is monoidal on this one dual pair;
4. use the HT shell graph to prove the completed coevaluation is nonzero;
5. invoke `(7)`.

This is smaller than full Hodge completion but stronger than scalar properness: properness must
preserve the duality maps, not merely the underlying divisor or weak limit.

## 9. Hostile audit

1. **Not RH yet.**  Monoidal conservative base change in the conjecture is load-bearing.
2. **Not automatic category theory.**  Cofinal completion is singular; finite-stage
   dualizability need not survive an inverse/inductive limit.
3. **Not abstract Morita equivalence.**  The conclusion concerns internality in the fixed
   ordinary-prime critical representation.
4. **Not scalar reciprocity alone.**  Equation `(2)` holds for every finite nome family and does
   not constrain zeros.
5. **Not bare hypertranscendence.**  HT supplies faithfulness, not sector preservation.
6. **Not functional equation alone.**  Reflection constructs the dual external correspondence;
   it does not make that correspondence internal.
7. **Generalized-prime falsifiers are explained.**  They may preserve positivity, FE, entire
   completion, HT, and finite-stage duality while their cofinal conormal line changes sector.
8. **No zero-fitted norm.**  The standard sector, valuation law, source-normal scaling, and
   triangle maps must all be defined before divisor specialization.

## 10. Literature boundary

Kakutani product-measure equivalence, correspondences of von Neumann algebras, Picard/Morita
groupoids, dualizable objects, conormal line bundles, and proper nearby-cycle base change are
parent mathematics.  Preliminary searches found these subjects separately, but no theorem
combining the ordinary-prime valuation sector, Wold/BV conormal normalization, Gamma first-trace
anomaly, positive hypertranscendental shell reporter, and preservation of the Xi conormal dual
pair.  Novelty is claimed only provisionally for this arithmetic conjunction and reduction, not
for Kakutani or Morita theory.

Relevant parents include:

- S. Kakutani, *On equivalence of infinite product measures*, Annals of Mathematics 49 (1948);
- R. M. Brouwer, *A bicategorical approach to Morita equivalence for rings and von Neumann
  algebras*, arXiv:math/0301353;
- O. Gabber, *Transitivity and cohomological properness of nearby cycles*;
- the wild/enhanced Riemann--Hilbert references recorded in
  `polarized-irregular-source-purity-law.md`.

## Gates

- [x] finite vacuum--anomaly zig-zag scalar formalized in Lean
- [x] finite occupation/conormal invertibility identified
- [x] cofinal sector-internality wall paper-proved
- [x] Kakutani scalar wall already formalized in Lean
- [x] HT shell conormal reporter and multiplicity faithfulness already formalized
- [x] factorized conormal anomaly reinterpreted as loss of internal invertibility
- [x] preliminary corpus and literature collision audit
- [ ] construct finite BV/Wold occupation-line equivalence
- [ ] construct source-normal monoidal nearby-cycle functor
- [ ] prove conservative cofinal triangle identity
- [ ] compose to unconditional RH
- [ ] formalize RH

## Log

- 2026-07-30 — Identified vacuum probability and first-trace mass as the coevaluation/evaluation
  records of one finite occupation line.  Reinterpreted the all-prime Kakutani wall as failure of
  that line to remain internal in the fixed critical sector.  Formulated
  `XI COFINAL CONORMAL INVERTIBILITY`, reducing RH to preservation of one source-defined dual pair
  under strict cofinal conormal base change.
- 2026-07-30 — Closed the finite BV/Wold occupation-line identification.  Existing source
  identities give, for every finite prime packet \(P\),
  \[
   J(E_Pp_a)=a_PJ(p_a),\qquad
   {\cal M}_P=a_P^{-1}.
  \]
  Therefore
  \[
   \boxed{{\cal M}_P\,J(E_Pp_a)=J(p_a).}
  \]
  This is the evaluation--coevaluation triangle identity on the literal pole-cancelled BV
  principal conormal.  Its scalar factors are Lean-proved by
  `finitePrimeOccupationFirstMoment_eq_inv_woldBoundaryVolume` and
  `HTGeometry.finiteOccupation_vacuum_mul_mass`; the BV conormal equation is the paper-proved
  source law `(18)` in `prime-sieve-wold-gamma-bv-relative-character.md`.  Remaining obstruction
  is no longer finite identification, but preservation of this identity by singular cofinal
  completion.
