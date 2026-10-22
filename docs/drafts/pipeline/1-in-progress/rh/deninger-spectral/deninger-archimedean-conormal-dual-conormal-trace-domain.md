# Archimedean conormal/dual-conormal trace domain

- **ID:** `deninger-archimedean-conormal-dual-conormal-trace-domain`
- **Stage:** 1-in-progress
- **Type:** SOURCE COMPACTIFICATION/TRACE-DOMAIN CONJECTURE
- **Label:** `DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** A compactified Deninger arithmetic flow should use paired
  conormal/dual-conormal leafwise-current complexes only at the
  archimedean stationary component. Finite-prime packets remain periodic
  orbits in the open dynamical source. The supported archimedean normal-jet
  tower, not an order-zero residue line, must produce the
  \(\Gamma_{\mathbb R}\) contribution. This is a Lefschetz trace domain,
  not the missing positive Hodge polarization on \(M_\zeta\).

## 1. Arithmetic/dynamical separation forced by primary sources

Deninger's dictionary has two different localization structures.

1. In the arithmetic coefficient, finite primes occur as closed strata and
   enter the generic-to-residue complex.
2. In the dynamical trace, finite primes occur as periodic-orbit packets,
   while infinite primes occur as stationary points or preserved
   components.

For a finite prime \(p\), the primitive period is \(\log p\). Deninger's
2018 rational-Witt suspension has compact packets of periodic orbits of
that period and explicitly has no fixed points. In the conjectural
compactification from his 2002 paper, the real infinite prime is a
stationary point \(x_\infty\) with transverse normal flow
\[
 r\longmapsto e^{-2t}r, \qquad \kappa_\infty=-2.                \tag{1}
\]
The transverse germ is the real orbifold
\(\mathbb R_{\ge 0}\cong\mathbb R/\{\pm1\}\), and the expected coefficient
is the smooth real Rees sheaf \(\xi^\infty_{\mathbb R}\), including the
infinite Frobenius involution.

Thus prime pro-log collars remain part of the source coefficient and its
Hodge gluing, but they are not conormal support for the dynamical trace.

## 2. Analytic theorem being adapted

Álvarez López--Kordyukov--Leichtnam prove for a closed
codimension-one foliated manifold with simple closed orbits and
transversely simple compact preserved leaves \(M^0\) that ordinary
smooth leafwise forms and unrestricted leafwise currents are not the
correct trace complexes.

They use
\[
\begin{aligned}
 I(\mathcal F)&=I(M,M^0;\Lambda\mathcal F),\\
 I'(\mathcal F)&=I(M,M^0;\Lambda\mathcal F;\Omega_M)' ,
\end{aligned}                                                   \tag{2}
\]
with strict exact sequences
\[
\begin{aligned}
 0&\longrightarrow K(\mathcal F)
   \longrightarrow I(\mathcal F)
   \longrightarrow J(\mathcal F)\longrightarrow0,\\
 0&\longleftarrow K'(\mathcal F)
   \longleftarrow I'(\mathcal F)
   \longleftarrow J'(\mathcal F)\longleftarrow0.               \tag{3}
\end{aligned}
\]
Here \(K,K'\) are supported at \(M^0\), while \(J,J'\) are the
extendable/dual-extendable complexes on the cut-open manifold.

The supported terms do not collapse to an order-zero boundary value.
For each preserved leaf \(L\),
\[
\begin{aligned}
 K(\mathcal F)
   &\cong\bigoplus_{k\ge0}C^\infty(L;\Lambda),&
 d_{\mathcal F}
   &\cong\bigoplus_{k\ge0}d_{-k-1},\\
 K'(\mathcal F)
   &\cong\prod_{k\ge0}C^{-\infty}(L;\Lambda),&
 d_{\mathcal F}
   &\cong\prod_{k\ge0}d_k .                                    \tag{4}
\end{aligned}
\]
The \(k\)-th summand is the \(k\)-th normal derivative of a Dirac-type
current. If the transverse exponent is \(\kappa_L\), the flow weights on
the two towers are respectively
\[
 e^{-(k+1)\kappa_Lt}
 \quad\text{and}\quad
 e^{k\kappa_Lt}.                                                \tag{5}
\]
Their renormalized combined character is the distribution extending
\[
 \frac{\chi(L)}{|e^{\kappa_Lt}-1|}
 \quad (t\ne0).                                                 \tag{6}
\]
Both current complexes are therefore load-bearing.

## 3. Arithmetic compactification candidate

Fix a finite character lattice \(L\). Let \(X_L^\circ\) be the finite
source stage carrying Deninger's finite-prime periodic packets. Adjoin a
real stationary component \(Y_{L,\infty}\) with:

1. stationary point \(x_\infty\);
2. transverse orbifold ray \(\mathbb R_{\ge0}\);
3. transverse flow `(1)`;
4. orientation-sign/infinite-Frobenius coefficient from
   `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`;
5. a leafwise coefficient whose transverse restriction is
   \(\xi^\infty_{\mathbb R}\).

Write the resulting candidate compactification as
\[
 \overline X_L=X_L^\circ\cup Y_{L,\infty},\qquad
 M_L^0=Y_{L,\infty}.                                           \tag{7}
\]
Define
\[
\begin{aligned}
 I_{L,\infty}^\bullet
 &=I(\overline X_L,M_L^0;
     \Lambda^\bullet\mathcal F\otimes\mathscr A_{\rm arith}),\\
 I_{L,\infty}^{\prime\,\bullet}
 &=I_{L,\infty}^\bullet(\Omega_{\overline X_L})'.              \tag{8}
\end{aligned}
\]

The notation `(8)` is provisional: Deninger's source is a generalized
lamination and its archimedean component may be singular, so the local
spaces must be constructed rather than imported from the compact smooth
theorem.

## 4. Conjecture

`[CONJECTURE] [DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN]`

There is a functorial compactification `(7)` and paired complexes `(8)`
such that:

1. **Strict conormal sequences.** Versions of `(3)` are strict
   topological exact sequences.
2. **Full Rees/jet identification.** Their supported terms identify
   with the full real Rees normal-jet tower, with
   \(K\)-cohomology \(\bigoplus_{k\ge0}H^\bullet_{-k-1}(Y_{L,\infty})\)
   and \(K'\)-cohomology
   \(\prod_{k\ge0}H^\bullet_k(Y_{L,\infty})\). No normal jet is
   discarded.
3. **Real normal law.** The induced flow has
   \(\kappa_\infty=-2\), and Hodge star exchanges the conormal and
   dual-conormal domains with the orientation-sign twist.
4. **Open-source identification.** The \(J,J'\) terms are the
   extendable and dual-extendable completions of the already-constructed
   open Deninger relevant complex. Their closed orbits are exactly the
   finite-prime packets.
5. **Trace regularization.** Witten deformation and the \(b\)-calculus
   define the paired distributional trace on the nuclear test-operator
   domain, including its renormalization at \(t=0\).
6. **Filtered passage.** Character-lattice refinement commutes strictly
   with current duality, the jet filtration, trace regularization, and
   the Deninger flow.
7. **Separated trace comparison.**
   - the \(K/K'\) normal-jet character is the
     \(\Gamma_{\mathbb R}\) distribution;
   - the \(J/J'\) periodic-orbit character is Meyer's finite-prime
     distribution;
   - their sum is Meyer's full Weil distribution.

Clause 7 must be proved before Mellin divisor evaluation. None of these
clauses proves cup-isometry, generalized-jet faithfulness, or positive
Hodge theory on \(M_\zeta\); those remain in
`DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION`.

## 5. What is already closed

- Finite-prime packets in Deninger's 2018 space are periodic orbits of
  primitive length \(\log p\); they are not fixed strata.
- The real transverse exponent \(-2\) and orbifold normal ray are
  Deninger's source prescriptions.
- `DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER` constructs the
  complete local even-jet product, proves weights \(e^{-2kt}\), and
  derives the exact positive-time character
  \((1-e^{-2t})^{-1}\). The corresponding arbitrary-test identity is
  already unconditional in `DeningerArithmeticArchimedean.lean`.
- `DAC_REAL_STATIONARY_KAHLER_CONORMAL_PRODUCT_GERM` constructs an
  explicit three-dimensional local quotient with independent leaf and
  normal weights. It simultaneously realizes leafwise Kähler weight
  one, the orientation-sign Hodge star, Deninger's transverse exponent
  \(-2\), and the real even-jet character.
- `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` constructs the local
  orientation-sign Hodge atom.
- The open relevant complex is strictly the Poisson--zeta three-term
  complex by `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION`.
- The finite-prime pro-log Hodge atoms and their affine overlap remain
  valid coefficient geometry; they are not reinterpreted as preserved
  leaves.

## 6. Unclosed hypotheses

The compact foliated-flow theorem does not apply directly:

1. Deninger's 2018 space is infinite-dimensional and has no fixed
   points; `(7)` is a new arithmetic compactification.
2. Its foliation is generalized, not a finite-dimensional classical
   foliation.
3. The archimedean stationary component may be a singular leaf rather
   than a compact smooth preserved leaf.
4. The correct twisted Euler characteristic of
   \(Y_{L,\infty}\) must be derived from the real Rees coefficient; it
   cannot be assigned to force the gamma factor.
5. Deninger's finite-prime packets are compact families of periodic
   orbits, not automatically simple isolated orbits.
6. Full \(b\)-trace and Witten estimates must be uniform under lattice
   refinement.

## 7. Immediate proof tasks

1. Embed the proved three-dimensional stationary product germ into a
   functorial global compactification of the rational-Witt suspension.
2. Compute its conormal and strong-transpose dual-conormal exact
   sequences, including the \(\mu_2\) orientation-sign action and the
   full Witten twists.
3. Determine the leafwise stationary coefficient
   \(Y_{L,\infty}\) and prove its twisted Euler characteristic from
   source data.
4. Extend the proved positive-time jet character through \(t=0\) by
   the source \(b\)-trace and identify its renormalization anomaly.
5. Separately realize finite-prime packets as the closed-orbit sector
   of \(J,J'\) and prove the coefficient \(\log p\) for every iterate.
6. Only then pass to the lattice limit and construct the global paired
   \(b\)-trace.

## 8. Falsifiers

The route fails if:

- no source compactification adjoins the real stationary component
  functorially;
- the real Rees coefficient is not the full supported-current jet
  tower;
- the twisted stationary Euler characteristic gives the wrong
  \(\Gamma_{\mathbb R}\) multiplicity;
- finite-prime packets cannot be isolated in the \(J/J'\) trace;
- Hodge star does not exchange the two current domains;
- the all-lattice completion destroys strict exactness;

## Hostile audit

- Conormal support is archimedean only.
- Prime arithmetic residues and prime dynamical orbits are related
  comparison data, not the same geometric stratum.
- Higher normal Dirac derivatives are retained.
- The compact smooth theorem is evidence and an analytic template, not
  an existence proof for `(7)`.
- The paired trace complex is not advertised as the source Hodge
  polarization or RH proof.
- No zeta zero, RH premise, CCM object, or numerical computation defines
  the source.

## References

- Christopher Deninger, *A note on arithmetic topology and dynamical
  systems*, arXiv:math/0204274.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Jesús A. Álvarez López, Yuri A. Kordyukov, and Eric Leichtnam,
  *A trace formula for foliated flows*, arXiv:2402.06671.
- Richard Melrose, *The Atiyah--Patodi--Singer Index Theorem*.

## Log

- 2026-07-27 — Replaced the incorrect finite-prime preserved-stratum
  candidate by an archimedean compactification conjecture. Retained the
  full supported normal-jet towers and separated their gamma character
  from the finite-prime closed-orbit character.
- 2026-07-27 — Restricted the conjecture to its justified role:
  paired Lefschetz trace regularization. Removed the unsupported claim
  that conormal trace cohomology itself supplies positive Hodge
  polarization on \(M_\zeta\).
