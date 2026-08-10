# Arbitrarily weak local interaction singularly expands quantum time

- **ID:** `weak-interaction-singular-quantum-time-expansion`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER THEOREM / ONE-KNOB ACTIVATION /
  NONCOMMUTING LONG-TIME LIMIT
- **Master:**
  `../1-in-progress/universal-replica-collision-law-of-quantum-return.md`
- **Scientific status:** `[PAPER-PROVED] [PRIORITY PROVISIONALLY CLEARED
  THROUGH LOCAL GENERATOR] [ONE-KNOB POLYNOMIAL LAYER LEAN-PROVED]`
  `[FINITE-HORIZON CSTAR CORE LEAN-PROVED]`
  `[FINITE-FAMILY HAUSDORFF ASSEMBLY LEAN-PROVED]`
  `[PHYSICAL LOCAL GENERATOR FORMALIZATION OPEN]`

## Discovery

> **Local interaction opens exponentially many dimensions of quantum time.**

The statement is not that a weak interaction has an immediate macroscopic
effect. It is an exact singular-limit law: finite-time histories vary
continuously with interaction strength, while completed long-time temporal
dimension jumps from at most linear to exponential at arbitrarily weak
generic coupling.

## Setting

Let \(n,q\geq2\), \(D=q^n\), and let
\(\mathcal L_{P_n,q}\) be the real vector space of traceless Hermitian
Hamiltonians containing arbitrary one-site and nearest-neighbour two-site
terms on the open \(q\)-level path. Use the unique Hilbert--Schmidt
orthogonal decomposition
\[
 \mathcal L_{P_n,q}
 =
 \mathcal A_{n,q}\oplus\mathcal V_{n,q},              \tag{1}
\]
where \(\mathcal A_{n,q}\) contains onsite terms and
\(\mathcal V_{n,q}\) contains pure edge correlations with zero partial
trace on each endpoint. Fix
\[
 H_g=A+gV.                                            \tag{2}
\]

For a finite Hilbert--Schmidt reporter family
\(\mathcal O=(B_a,\lambda_a)_{a=1}^{N}\), put
\[
 \mathcal B_{\mathcal O}
 =
 \left(\sum_a\lambda_a\|B_a\|_{\mathrm{HS}}^2\right)^{1/2}
                                                               \tag{3}
\]
and let \(X_{H_g}^{\mathcal O}(T)\) be its Heisenberg orbit during
\([-T,T]\). The reporter family is **spectrally complete** when its visible
gaps span the full projective gap module.

## Theorem — singular expansion law

For Lebesgue-almost every pair
\((A,V)\in\mathcal A_{n,q}\times\mathcal V_{n,q}\), there is a countable set
\(C_{A,V}\subset\mathbb R\), containing zero, such that every
\(g\notin C_{A,V}\) satisfies all of the following.

### 1. Exponential temporal-rank activation

\[
 \rho(H_g)=D-1=q^n-1,                                 \tag{4}
\]
whereas
\[
 \rho(H_0)=\rho(A)\leq n(q-1)<q^n-1.                 \tag{5}
\]
Thus every punctured interval around zero contains all but countably many
strengths that activate the full projective Hilbert dimension.

### 2. Simultaneous deletion of every excess return collision

For every initial-state spectral weight vector \(p\) and every replica order
\(m\geq1\),
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
 \left|\sum_{j=1}^{D}p_je^{-itE_j(H_g)}\right|^{2m}dt
 =
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}\prod_{j=1}^{D}p_j^{2k_j}.        \tag{6}
\]
The right side is the absolute fixed-weight collision floor. One scalar
coupling therefore removes every nontrivial equal-cardinality energy-sum
resonance at every finite order simultaneously.

### 3. Finite observation remains continuous

For every reporter family, every \(T\geq0\), and every \(g\in\mathbb R\),
\[
 d_{\mathrm H}\!\left(
 X_{H_g}^{\mathcal O}(T),X_{H_0}^{\mathcal O}(T)
 \right)
 \leq
 2T|g|\,\|V\|_{\mathrm{op}}\mathcal B_{\mathcal O}. \tag{7}
\]
Thus no resolution-\(\varepsilon\) observer can see an order-one profile
change before a time of order
\(\varepsilon/(|g|\|V\|_{\mathrm{op}}\mathcal B_{\mathcal O})\).

### 4. Completed observation is discontinuous

For every spectrally complete reporter family,
\[
 \dim_{\mathrm M}X_{H_0}^{\mathcal O}(\infty)
 \leq n(q-1),
 \qquad
 \dim_{\mathrm M}X_{H_g}^{\mathcal O}(\infty)
 =q^n-1.                                             \tag{8}
\]
Consequently
\[
 \lim_{\substack{g\to0\\g\notin C_{A,V}}}
 \dim_{\mathrm M}X_{H_g}^{\mathcal O}(\infty)
 =
 q^n-1
 >
 \dim_{\mathrm M}X_{H_0}^{\mathcal O}(\infty),       \tag{9}
\]
even though `(7)` tends to zero at every fixed \(T\). This is the precise
noncommutation of weak-coupling and completed-time limits.

## Proof

The one-knob theorem in
`local-interaction-replica-collision-extremality.md` proves `(4)`--`(5)`.
Its argument restricts the countable nonzero discriminant and rational
relation polynomials from the full local space to the affine line
\(A+gV\). For almost every \((A,V)\), none of those restrictions is the
zero polynomial. Each has finitely many real roots, so their union is
countable. At \(g=0\), onsite energy differences lie in the rational span of
at most \(n(q-1)\) local gaps.

Maximal projective rank is equivalent to absence of every nontrivial
equal-cardinality energy-sum collision. The universal replica-collision
expansion then gives `(6)` at all orders.

The Duhamel perturbation bound and reporter-orbit covering theorem in
`finite-horizon-observer-temporal-profile-stability.md` give `(7)`. The same
paper proves that the Minkowski dimension of the completed reporter orbit is
the rational rank of its visible gap module. Spectral completeness, `(4)`
and `(5)` give `(8)`--`(9)`. \(\square\)

## Formal proof status

`formal/GaloisForLFunctions/HTGeometry/AffineLinePolynomialAvoidance.lean`
now proves unconditionally:

1. nonzero real multivariate polynomials have Lebesgue-null zero sets;
2. restriction to almost every affine line is a nonzero univariate
   polynomial;
3. for almost every affine line, a countable family of nonzero polynomial
   obstructions has a countable exceptional parameter set.

This closes the algebraic-measure upgrade from a full-parameter generic
theorem to the countable-exception one-knob theorem. It does not yet
instantiate the obstruction polynomials with eigenvalue relations of the
local qudit chain. That tensor-local spectral witness is the remaining
formal core.

`formal/GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean`
now also proves unconditionally, for arbitrary unital \(C^*\)-algebras:

1. the dimension-free Duhamel bound
   \(\|e^{-itH}-e^{-itK}\|\leq |t|\|H-K\|\);
2. operator-normalized Heisenberg stability
   \[
   \|e^{-itH}Oe^{itH}-e^{-itK}Oe^{itK}\|
   \leq2|t|\|H-K\|\|O\|;
   \]
3. the inverse-coupling distinguishability-time lower bound.

Thus the finite-horizon continuity mechanism is no longer restricted to
finite matrices or Hilbert--Schmidt probes. The finite-family Hausdorff
assembly in `(7)` remains to be formalized.

## What one law now explains

The same arithmetic transition simultaneously explains:

1. why free/commuting systems retain only \(O(n)\) independent time
   directions;
2. why generic bounded-range interaction generates \(q^n-1\) directions;
3. why every higher return moment drops to its fixed-weight minimum;
4. why exact global return occupies a doubly exponentially small fraction
   of asymptotic time as a function of maximum entropy;
5. why a bounded-time observer cannot detect the rank jump immediately;
6. why observer dependence is unavoidable: every reporter sees a quotient
   of the activated global gap module.

These are consequences of one generator event—destruction of all
nontrivial additive energy collisions—not separate mechanisms.

## Hostile boundary

1. “Almost every background/profile” is essential. The theorem does not
   cover a prescribed integrable or symmetry-constrained device.
2. Countable exceptional strengths are not located or uniformly separated.
3. `(7)` is a universal lower obstruction on observability, not an upper
   equidistribution time. Near resonances can delay activation arbitrarily.
4. Translation-invariant fixed-parameter chains remain outside the proved
   generator theorem.
5. The theorem concerns finite-dimensional stationary unitary dynamics.
   It is not a theorem about real black holes, quantum gravity or
   thermodynamic irreversibility.
6. Every equation must be formally closed before manuscript use. Current
   status is paper proof only.

## Promotion gates

- [x] dependency-closed paper proof
- [x] no numerical computation
- [x] countable exceptional-set sharpening
- [x] finite-horizon continuity included
- [x] exact observer qualification
- [x] exact-object priority provisionally cleared
- [ ] independent specialist proof audit
- [x] formalization of local generator
- [x] formalization of generic one-knob polynomial restriction
- [x] formal instantiation with local-chain relation polynomials
- [x] formalization of dimension-free operator-norm finite-horizon stability
- [x] formalization of finite-family Hausdorff assembly
- [ ] hostile Nature editorial pass

## Formal status update — finite-family Hausdorff assembly `[LEAN-PROVED]`

`formal/GaloisForLFunctions/HTGeometry/FiniteHorizonReporterHausdorff.lean` closes equation `(7)`
unconditionally for an arbitrary unital C*-algebra and an arbitrary finite weighted reporter
family:

- `reporterFamily` is the weighted family as a vector of the `ell^2` product of the algebra, and
  `norm_reporterFamily` identifies its norm with the card's scale
  `B_O = (sum_a lambda_a ||B_a||^2)^(1/2)`;
- `reporterOrbit` is the Heisenberg orbit of the whole family, and
  `norm_reporterOrbit_sub_le` lifts the single-observable C* stability bound to the family with the
  same factor `2|t| ||H-K||` and the family scale;
- `hausdorffDist_reporterOrbit_le` bounds the Hausdorff distance of the two orbits over `[-T,T]`;
- `hausdorffDist_coupledReporterOrbit_le` is `(7)` itself, for `H_g = H + gV`:
  `d_H <= 2 T |g| ||V|| B_O`.

`#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` only.

Remaining Lean gates are unchanged: formalization of the local generator, and the instantiation of
the obstruction polynomials with local-chain relation polynomials (the tensor-local spectral
witness).

## Formal status update — one-knob instantiation `[LEAN-PROVED]`

The generic one-knob layer is now instantiated with the actual spectral relation polynomials, so
the countable-exception mechanism of `(4)`-`(5)` is closed in Lean:

- `HTGeometry/ComplexAffineLinePolynomialAvoidance.lean` extends the real affine-line avoidance
  layer to complex-coefficient obstruction polynomials evaluated at real parameters, by splitting a
  complex polynomial into its coefficientwise real and imaginary parts
  (`mvPolynomialRealShadow`); the capstone is
  `countable_complexMvPolynomialAffineLineAvoidance_ae_pair`.
- `HTGeometry/OneKnobSpectralActivationLaw.lean` applies it to the corpus obstruction family
  `complexSpectralCoefficientObstructionPullback` of a polynomial Hermitian matrix family, i.e. to
  the actual balanced-character spectral relation polynomials of the characteristic-polynomial
  coefficients.  `countable_exceptional_coupling_of_maximallyProjective_witness` is the result: one
  maximally projective member of the family forces, along almost every affine line `A + gV` of
  parameters, maximal projective rank at all but countably many coupling strengths `g`.
  `mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective` supplies the witness transfer.

The hypothesis consumed is exactly the one the already-formalized parent card
`3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md` discharges for the uniform
qudit path at every `n, q >= 2`
(`exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`), so the
local-chain case is an instance of the theorem above rather than a separate argument.

`#print axioms` on the five capstones: `propext`, `Classical.choice`, `Quot.sound` only.

## Formal status update — local generator `[LEAN-PROVED]`

`HTGeometry/OneKnobLocalChainActivationLaw.lean` binds the physical path witness of the parent card
`3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md` into the one-knob law:

- `countable_exceptional_coupling_realAffineHermitianMaximalSet` and
  `countable_exceptional_coupling_realHermitianSubmoduleMaximalSet` state the countable-exception
  law for an arbitrary real-affine Hermitian family and for a Hermitian matrix submodule;
- `exists_uniformQuditPath_countable_exceptional_coupling` is the local-chain instance: for every
  `n, q >= 2` there is a physically realized path system of Hilbert dimension `q^n` such that along
  almost every affine coupling line inside its trace-zero local Hamiltonian space, all but
  countably many coupling strengths have maximal projective rational rank.

All Lean gates of this card are now closed; see the companion card
`../3-formalized/weak-interaction-singular-quantum-time-expansion-formalized.md`.  The two
remaining gates are the specialist proof audit and the editorial pass, neither of which is a
formalization gate.
