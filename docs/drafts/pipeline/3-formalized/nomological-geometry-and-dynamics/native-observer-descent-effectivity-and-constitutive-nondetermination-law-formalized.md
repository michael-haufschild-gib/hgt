# Native observer descent, effectivity, and constitutive non-determination law

- **ID:** `native-observer-descent-effectivity-and-constitutive-nondetermination-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / UNIVERSAL KINEMATICS / NO-GO
- **Status:** `[LEAN-COMPLETE] [UNCONDITIONAL] [AXIOM-AUDITED] [NO SORRY]`
  `[FIVE-ORGAN CALIBRATION] [ROUTE-INDEPENDENT] [NOT A FIELD EQUATION] [NOT RH]`

## 1. Native observer geometry

Let `C` be an infinity-category with finite products, pullbacks, and geometric realizations of Cech
nerves, and let

\[
 q:X\longrightarrow O
\tag{1}
\]

be an observer in `C`.  Its Cech nerve and native coimage are

\[
 N_n(q)=\underbrace{X\times_O\cdots\times_OX}_{n+1},
 \qquad
 \operatorname{Coim}(q)=|N_\bullet(q)|.
\tag{2}
\]

The augmentation factors `q` canonically as

\[
 X\xrightarrow{e_q}\operatorname{Coim}(q)
 \xrightarrow{\varepsilon_q}O.
\tag{3}
\]

This construction must be made in the observer's native category.  Algebraic, topological,
Banach, derived, and stacky effectivity are different statements.

## 2. Universal descent--effectivity theorem

### Theorem 2.1

For any charge `chi:X->Z`:

1. maps `b:Coim(q)->Z` are equivalent to coherent descent data on the full Cech nerve:

   \[
    \operatorname{Map}(\operatorname{Coim}(q),Z)
    \simeq
    \operatorname*{Tot}_{[n]\in\Delta}\operatorname{Map}(N_n(q),Z);
   \tag{4}
   \]

   the datum descends the fixed `chi` precisely when its degree-zero component is `chi`, equivalently
   `chi=b e_q`;
2. `chi` factors through the declared target `O` iff it first descends to such a `b` and this map
   extends across `epsilon_q`, so `b=d epsilon_q` for some `d:O->Z`;
3. if `q` is an effective epimorphism, `epsilon_q` is an equivalence and a full coherent Cech
   descent datum is sufficient for factorization;
4. for postprocessing `f:O->O'`, there is a natural map

   \[
    N_\bullet(q)\longrightarrow N_\bullet(fq),
    \qquad
    \operatorname{Coim}(q)\longrightarrow\operatorname{Coim}(fq);
   \tag{5}
   \]

   serial observation may add identifications but cannot remove existing ones;
5. for a finite parallel observer `q=(q_i):X->product_i O_i`, its kernel relation is the pullback
   intersection

   \[
    X\times_{\prod_iO_i}X
    \simeq
    \prod_{X\times X,i}(X\times_{O_i}X),
   \]

   so parallel channels can repair losses that serial postprocessing cannot;
6. for pointed spaces and a pointed observer `(X,x)->(O,o)`, if `F_o=hofib_o(q)` is based at the
   lift `x` and a chosen path `q(x)\simeq o`, the exact sequence

   \[
    \cdots\to\pi_{n+1}(O,o)\to\pi_n(F_o)\to
    \pi_n(X)\to\pi_n(O)\to\cdots
   \tag{6}
   \]

   places relative isotropy and vertical history in different homotopy degrees of one observer
   fibre.  At `pi_0`, exactness is in pointed sets.

#### Proof

Equation `(4)` is the universal property of geometric realization.  Factorization `(3)` gives
Part 2 in both directions.  Part 3 is the definition of effective epimorphism.  A tuple equal over
`O` remains equal after `f`, producing the simplicial map `(5)`.  Equality in a product is the
intersection of equality in each factor, proving Part 5.  Part 6 is the homotopy-fibre long exact
sequence. ∎

For sets, Part 2 reduces to the exact kernel-pair criterion

\[
 \ker(q)\subseteq\ker(\chi)
 \iff
 \chi\text{ factors through }q(X).
\tag{7}
\]

For stacks, equality on the strict kernel pair is not enough; higher Cech coherence is part of the
datum.

## 3. Five-organ calibration

| Corpus organ | Native observer | Exact Cech/fibre consequence | Constitutive datum not supplied |
|---|---|---|---|
| multiple Gamma | marked action stack to coarse quotient, then Hausdorff reflection | isotropy, dense-coset loss, and closure quotient are distinct | DA-depth equality; normalized reflection |
| Hurwitz | marked branch-history action to affine/local observers | local characters and vertical branch histories are separated | robust analytic atlas realization; differential rank |
| framed GHZ recurrence | phase fibre to fixed boundary pair | winding and phase action are vertical and cannot descend to boundary data | Fubini--Study scale; Berry connection |
| Stokes positivity/inertia | rank port `M:V->R^r` | kernel relation identifies the vertical sector `ker M` and rank of the coarse port | positivity on that sector; quadratic form; coarea coefficient; polarization |
| singular completion | dense injective map in its native topology | native topological Cech data detect failed effectivity; forgotten set/algebraic data do not determine it | compatible Banach/norm enrichment after forgetting; closed-range/lower-bound theorem |

The Stokes row has an independent exact consequence.  Let `V` be a finite-dimensional real vector
space, `M:V->R^r` linear, and `Q` a symmetric bilinear form positive definite on `ker M`.  Then

\[
 \operatorname{ind}_-(Q)+\dim\operatorname{Rad}(Q)
 \le\operatorname{rank}M\le r.
\tag{8}
\]

Indeed, every subspace of dimension greater than `rank M` meets `ker M` nontrivially.  A
nonpositive subspace of that dimension would contradict positivity on `ker M`.  For `r=1`, this is
the exact one-port inertia bound.

## 4. Constitutive non-determination theorem

The observer `q`, its full native Cech nerve, and its homotopy fibres do **not** determine a
constitutive metric, inertia phase, hypertranscendence, or normalization.  Native effectivity
itself **is** determined by `q`: it is the statement that `epsilon_q` in `(3)` is an equivalence.
What a coarser or forgotten-category observer does not determine is effectivity after choosing an
additional topology, norm, or other enrichment.

### Proof by same-observer countermodels

1. **Cost.**  Fix `q:S^1->*` and `lambda>0`.  Metrics
   `g_lambda=lambda^2 dtheta^2` have identical observer and homotopy data.  For the kinetic action
   `A(gamma)=(1/2) integral_0^T norm(gamma_dot)^2 dt`, the minimum in the unit-winding class is

   \[
    \mathcal A_\lambda=\frac{2\pi^2\lambda^2}{T}.
   \tag{9}
   \]

2. **Inertia.**  Fix `q:R^2->R`, `q(x,y)=x`.  The forms

   \[
    Q_\sigma(x,y)=y^2+\sigma x^2,
    \qquad \sigma\in\{1,0,-1\},
   \tag{10}
   \]

   share the observer and are positive on `ker q`, but are positive definite, corank one, and
   Lorentzian respectively.
3. **Hypertranscendence.**  Fix non-torsion `q_0=e^(-2 pi i s)`.  The function `a^(-s)` has that
   monodromy and satisfies `a f'(a)+s f(a)=0`, while the Hurwitz function with the same exponent
   character is hypertranscendental.  They share only this scalar exponent-character label, not the
   full branch-history action.  Thus the character observer does not determine DA depth.
4. **Forgotten-category data do not determine enriched effectivity.**  The identity of underlying
   sets admits the continuous bijection

   \[
   \mathbb R_{\rm discrete}\longrightarrow\mathbb R_{\rm usual}
   \tag{11}
   \]

   Its Set-level observer and Set Cech nerve agree with the ordinary identity on `R`, but this Top
   lift is not a homeomorphism whereas the usual-to-usual lift is.  These are different native Top
   observers; the counterexample concerns loss of enrichment, not non-determination from a fixed
   native `q`.
5. **Normalization.**  For `C in C^times`, replacing normalized `Gamma_m` by `C Gamma_m` preserves
   period action and DA depth but breaks `F(c-z)=F(z)^(-1)` unless `C^2=1`.

These examples prove non-determination. ∎

## 5. Field consequence

Bare observer geometry has a universal coordinate-free content:

\[
 \boxed{\text{Cech descent} + \text{native effectivity} + \text{relative homotopy}.}
\tag{12}
\]

It does not supply the field dynamics.  The theorem proves only that richer input or a canonical
construction is necessary.  The following **source-normalized constitutive structure on the Cech
nerve** is a field-design conjecture, not a consequence of Theorem 2.1; it should control, in typed
target categories:

1. vertical coercivity or action;
2. source choice of topology/norm and comparison of effectivity under completion or forgetting;
3. analytic/differential realization;
4. polarization and inertia;
5. normalization and orientation;
6. functoriality under serial and parallel observer composition.

The source-normalization requirement is load-bearing.  If constitutive data may be chosen after the
desired observer behaviour is known, Countermodels 1--5 refute any law assigning the listed
constitutive outputs from bare `q` alone.

## 6. Scope

1. The theorem is internal to each native category; no single ambient category containing all five
   organs has been constructed.
2. Correspondence-valued observers require lax descent and are outside Theorem 2.1.
3. Nonproperness belongs to topology of Cech projections; isotropy belongs to higher fibre
   homotopy.  Neither determines the other: an irrational free `Z`-action on `S^1` has trivial
   isotropy and is nonproper, whereas a finite group acting on a point has nontrivial isotropy and
   is proper.
4. No numerical conservation law among DA rank, inertia, winding, and completion defect follows.
5. This is exact kinematics, not a constitutive field equation and not an RH theorem.

## Lean formalization

The dependency-closed formalization uses four modules:

- `NomologicalHomotopyGeometry/ObserverDescent.lean`: universal effective sieves, Yoneda descent
  after every base change, derived isomorphism/base-change/composition laws, and resulting observer
  pretopology and Grothendieck topology.
- `NativeObserverDescentEffectivityLaw.lean`: native Set coimage, canonical factorization,
  kernel-pair/Cech descent with uniqueness, target extension, effective-surjection theorem, serial
  coimage map, and exact finite-parallel kernel intersection.
- `NativeObserverUniversalDescentInertiaLaw.lean`: effectivity comparison is bijective iff observer
  is surjective; one exact descent/effectivity/serial/parallel package; full pointed-fibre
  long-exact-sequence interface in every degree with literal pointed-set exactness at `pi₀`; and
  the sharp finite-dimensional law
  `ind₋(Q) + dim Rad(Q) ≤ rank(M) ≤ r`, where `ind₋` is constructed as the attained maximum
  dimension of negative-definite subspaces and `Rad(Q)` is the full bilinear radical.
- `NativeObserverConstitutiveCountermodels.lean`: all five explicit witnesses: exact scaled
  unit-winding minima `2π²λ²/T`; the common projection with positive-definite, corank-one, and
  Lorentzian forms; a first-order exponential and differentially independent Hurwitz function with
  identical monodromy character `2`; continuous bijective discrete-to-usual identity that is not a
  homeomorphism beside the usual identity homeomorphism; and actual finite multiple-Gamma constant
  rescaling preserving period ratios and DA depth while breaking reciprocal reflection.

Both new modules are imported by `GaloisForLFunctions.HTGeometry`.  They passed direct
`lake env lean <file>` checks and targeted `lake build <module>` audits; umbrella was not built.
Batched `#print axioms` checks for every new theorem reported only `propext`, `Classical.choice`,
and `Quot.sound`, with no project axiom and no `sorryAx`.

## Log

- 2026-09-02 — exact Lean formalization completed, targeted modules built, axioms audited, and
  card advanced to Stage 3.
