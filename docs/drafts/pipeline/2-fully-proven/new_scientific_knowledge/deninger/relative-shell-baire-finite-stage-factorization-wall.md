# Relative-shell Baire finite-stage factorization wall

- **ID:** `relative-shell-baire-finite-stage-factorization-wall`
- **Stage:** 2-fully-proven
- **Type:** AUXILIARY LITERATURE-DERIVED TOPOLOGY OBSTRUCTION
- **Labels:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Frontier status:** `[AUXILIARY ONLY — NO ROUTE-L GATE CLOSED]`

## 2026-08-02 frontier correction

Full Deninger-corpus audit shows this theorem is not on Route L's active frontier.  Its Baire
factorization mechanism is known Grothendieck theory, its Baire topology is only hypothesized, and
the relative-shell source has not been identified with Deninger's rational-Witt relevant
coefficient.  It may constrain a future comparison after that identification exists, but it does
not construct the arithmetic coefficient, source-to-packet restriction, secondary Cauchy map,
closed-boundary topology, cup/Hodge structure, or Xi transport.  Do not cite this card as Route L
progress.

## 1. Exact statement

Let \(\mathcal F_\Lambda\) be the complete relative-shell differential
field and let
\[
 \mathcal F_\varnothing
 =
 \mathbb C\langle \zeta\rangle
\]
be its common zeta differential field.  Give
\(\mathcal F_\Lambda\) any Baire complex topological-vector-space
structure.

Let \(V\) be a complex topological vector space and let
\((V_n)_{n\geq 0}\) be closed complex-linear subspaces.  Suppose a
continuous complex-linear map
\[
 T:\mathcal F_\Lambda\longrightarrow V
\]
has stage-covered range:
\[
 \forall x\in\mathcal F_\Lambda\quad
 \exists n\quad T(x)\in V_n.                                   \tag{1}
\]

`[PAPER-PROVED]` There is one \(N\) such that
\[
 T(\mathcal F_\Lambda)\subseteq V_N.                            \tag{2}
\]

`[PAPER-PROVED]` If
\[
 \ker T=\mathcal F_\varnothing,                                \tag{3}
\]
then \(V_N\) contains a complex-linearly independent copy of the
entire private jet family
\[
 \bigl(H_m^{(k)}\bigr)_{m\in\Lambda,\ k\geq0}.                  \tag{4}
\]
In particular \(V_N\) is infinite-dimensional.  Consequently no
continuous complex-linear map satisfying `(1)` and `(3)` exists
when every \(V_n\) is finite-dimensional.

For a strict countable inductive limit of finite-dimensional
rational-Witt detector stages, every stage is closed and `(1)` is
automatic.  Such a target therefore cannot be the final
label-faithful Route-L coefficient target of a Baire shell source.

## 2. Proof

### 2.1 Full private differential rank over the common field

Let \(K\) be the rational-coordinate field.  The complete-shell
differential-independence theorem says that the family consisting of
all zeta jets and all private-shell jets is algebraically independent
over \(K\):
\[
 \operatorname{AlgInd}_K
 \left(
   (\zeta^{(j)})_{j\geq0}
   \sqcup
   (H_m^{(k)})_{m\in\Lambda,\ k\geq0}
 \right).                                                       \tag{5}
\]
The standard change-of-base law for an algebraically independent
disjoint union gives
\[
 \operatorname{AlgInd}_{
   K((\zeta^{(j)})_{j\geq0})
 }
 \left(
   (H_m^{(k)})_{m,k}
 \right).                                                       \tag{6}
\]
The coefficient field in `(6)` is exactly the differential field
\(\mathcal F_\varnothing\).  Hence the complete private jet family is
algebraically independent over the common zeta field.

Suppose `(3)` holds and a finite complex linear combination of the
images in `(4)` vanishes:
\[
 \sum_{m,k}c_{m,k}T(H_m^{(k)})=0.                               \tag{7}
\]
Then
\[
 y:=\sum_{m,k}c_{m,k}H_m^{(k)}
 \in\ker T=\mathcal F_\varnothing.                              \tag{8}
\]
Equation `(8)` gives the polynomial relation
\[
 \sum_{m,k}c_{m,k}X_{m,k}-y=0
\]
over \(\mathcal F_\varnothing\) on the family in `(6)`.
Algebraic independence forces every \(c_{m,k}=0\).  Thus the image
family `(4)` is complex-linearly independent.

### 2.2 Baire stage factorization

For each \(n\), set
\[
 E_n=T^{-1}(V_n).
\]
Continuity of \(T\) and closedness of \(V_n\) make \(E_n\) a closed
complex-linear subspace of \(\mathcal F_\Lambda\).  Condition `(1)`
gives
\[
 \mathcal F_\Lambda=\bigcup_{n\geq0}E_n.                        \tag{9}
\]
By the Baire category theorem, one \(E_N\) has nonempty interior.
A linear subspace of a complex topological vector space with
nonempty interior is the whole space: translating an interior
neighborhood to zero and absorbing by nonzero scalars puts every
vector in the subspace.  Therefore \(E_N=\mathcal F_\Lambda\),
which is `(2)`.

Under `(3)`, the independent family `(4)` lies inside \(V_N\), so
\(V_N\) is infinite-dimensional.  If all stages are
finite-dimensional this is impossible.

## 3. Hostile audit

- **Abstract mechanism is known.**  Section 2.2 is Grothendieck's
  factorization theorem in the special case needed here.  It is
  `[LITERATURE]`, not a novelty claim.
- **The shell consequence is stronger than dimension rhetoric.**
  The forced family is the actual full private differential-jet
  family, algebraically independent over the actual common zeta
  field.
- **Closed stages are essential.**  An arbitrary non-strict
  inductive topology may have nonclosed stages, so the Baire proof
  need not apply.
- **Baire source is essential.**  A strict LF source need not be a
  Baire space.
- **Finite-stage means finite-dimensional here.**  The theorem does
  not exclude a stage already made infinite-dimensional by tensoring
  with Meyer's radial nuclear space.
- **No arithmetic comparison is fabricated.**  The theorem rules
  out one target category and identifies a necessary replacement; it
  does not build the relevant complex, cup/trace map, Hodge form, or
  Xi-spectrum comparison.

## 4. Positive survivor

A viable Baire-source comparison with exact common-field kernel must
land in a target having at least one closed stage of infinite
differential capacity.  The canonical quotient
\[
 \mathcal F_\Lambda/\mathcal F_\varnothing
\]
is the minimal algebraic source of that capacity.  On the
rational-Witt/Meyer side, the finite detector union must therefore be
replaced or enlarged by an actual completed coefficient stage which
contains all private jet directions.  Tensoring with an unrelated
infinite radial factor is insufficient unless the comparison is
proved faithful on those jet directions.

This changes Route L's topology requirement: “strict pro-Ind limit of
finite stages” cannot by itself be the final source-faithful target.
The missing arithmetic theorem must exhibit the completed
infinite-stage coefficient direction and identify its kernel with
closed middle boundaries.

## 5. External frontier

- Grothendieck's factorization theorem supplies the Baire-to-countable
  inductive-limit mechanism.
- Deninger's rational-Witt dynamical space supplies the arithmetic
  finite-stage source, but not the relevant coefficient complex.
- Meyer's Poisson realization supplies a nuclear Fréchet radial
  target and zeta-zero cokernel, but no relative-shell comparison.

No checked source combines these with the complete positive
relative-shell differential frame.  Priority of the exact Route-L
application remains `[NOVELTY UNVERIFIED]`.

## 6. Lean target

Formalize unconditionally:

1. algebraic independence of all private jets over
   \(\mathcal F_\varnothing\);
2. linear independence of their images under every complex-linear
   map with kernel exactly \(\mathcal F_\varnothing\);
3. Baire factorization through one closed stage;
4. nonexistence for a closed finite-dimensional stage cover.

No RH, relevant-complex, positivity, or numerical hypothesis enters.

## References

- A. Grothendieck, *Sur les espaces (F) et (DF)*, Summa Brasil.
  Math. 3 (1954), 57--123.
- C. Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- R. Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.

## Lean status

### All four Lean targets landed

`formal/GaloisForLFunctions/RHTower/RelativeShellBaireWall.lean`; axiom audit for all four
declarations: `propext, Classical.choice, Quot.sound`.  The card's §6 asked for exactly four things
and all four are proved unconditionally, in the generality in which they are true — no shell, zeta,
RH, positivity or numerical hypothesis appears anywhere in the statements.

- `shellPrivate_algebraicIndependent_over_common` — **target 1**: if the common jets `Z` and the
  private jets `H` are together algebraically independent over the coordinate ring, the private jets
  are algebraically independent over the ring generated by the common jets.  This is the change-of-
  base law `(5) ⟹ (6)`; the mechanism is mathlib's `AlgebraicIndependent.sumElim_iff`, so the card's
  `[LITERATURE]` classification of this step is confirmed rather than re-derived.
- `shellImage_linearIndependent` — **target 2**: for a linear map whose kernel is exactly the
  subalgebra the family is independent over, the images of the family are linearly independent.
  This is `(7)`–`(8)`: a vanishing combination of images puts the combination in the kernel, hence
  in the subfield, and `∑ c_{m,k} X_{m,k} − y` is then a polynomial relation over that subfield, so
  algebraic independence forces every coefficient to vanish.  Formally: the multivariate polynomial
  maps to zero under `aeval`, hence is zero, and reading its coefficient at `X_i` gives `c_i = 0`.
- `shellBaire_exists_stage` — **target 3**: a continuous linear map out of a Baire topological
  vector space whose range is covered by countably many closed subspaces already lands in a single
  one.  This is `(9) ⟹ (2)`: the preimages are closed subspaces covering the source, Baire gives one
  with interior, and a submodule with interior is everything.
- `shellBaire_no_finiteDimensional_stages` — **target 4**: with the kernel hypothesis `(3)` and an
  infinite private family, no such map exists when every stage is finite dimensional.  This is the
  wall itself, stated as the impossibility it is.

### Scope, unchanged

This is the auxiliary topology obstruction only.  Nothing here identifies the relative shell with
Deninger's rational-Witt coefficient, constructs the arithmetic coefficient or the comparison map,
or verifies that the shell field carries a Baire vector topology — the card's own §"frontier
correction" and hostile audit state that those are hypotheses, and the Lean statements carry them as
hypotheses too.  The theorem proved is exactly the conditional one the card claims.

### Log

- 2026-08-02 — All four Lean targets of §6 formalized unconditionally.
