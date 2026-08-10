# Route U off-critical capacity and negative-index amplification law

- **ID:** `route-u-offcritical-capacity-negative-index-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ROUTE-U POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [NEW SCIENTIFIC KNOWLEDGE CANDIDATE] [NOT RH]`
- **Parent:** `../1-in-progress/universal-law-field/route-u-crossing-attack-typing.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/FiniteWeightedMonomialFrame.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ScheffeCounting.lean`,
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelRedundantSamplingCapacity.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryPadeContactParity.lean`,
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelCassiniSourceJet.lean`
- **Statement:** Critical-line Xi atoms are a summable positive sector and can always be absorbed
  into a finite prefix without changing a fixed canonical reconstruction frame. Thus Route U's
  capacity obstruction is purely off-critical. More strongly, odd contact `2m+1` forces the
  off-critical divisor form to be strictly negative on the full `(m+1)`-dimensional space
  `P · Poly_{≤m}`. This negative sector localizes to a finite FE--Schwarz-complete packet and
  requires more than `m` distinct conjugation-folded shifted nodes. Folded-node equivalence and
  count are independent of mass shift. More strongly, the complete positive-mass moment tower,
  every Hankel block and defect, and the crossing-conditioned negative functional are exact jets
  of one fixed Cassini source at the moving center `1-y`. If a finite packet covers every
  off-critical copy, its folded-node support has cardinality greater than `m`.

## Goal

Replace the scalar target `L_y(X(PX^m)^2) >= 0` by exact geometry retaining every lower contact
constraint. Determine which part of the Xi divisor must carry a hypothetical crossing and how its
required complexity grows with stationary contact order.

## Gates

- [x] 0 → 1 in-progress: Route-U contact obstruction and positive/off-critical split identified
- [x] 1 → 2 fully-proven: dependency-closed finite-frame, absorption, and negative-index proofs
- [x] 2 → 3 formalized: exact theorems compile with `lake env lean`
- [ ] 3 → 4 publication-ready: external novelty audit and standalone exposition

## 1. Canonical redundant-frame law

For positive real nodes `x_r` and monomial feature vector

```text
v_n(t) = (1,t,...,t^(n-1)),
```

define

```text
G_x = sum_r x_r v_n(x_r) v_n(x_r)^T.
```

Enough distinct nodes make `G_x` positive definite. Its inverse gives the minimum-energy canonical
reconstruction vector for every complex target `z`. The resulting capacity is

```text
C_x(z) = |z| v_n(z)^* G_x^(-1) v_n(z).
```

For the sample nodes themselves, capacity is leverage and obeys the exact conservation law

```text
sum_r C_x(x_r) = n.                                    (U-CAP.1)
```

For any finite complex target packet `z_q`, total capacity is the relative moment trace

```text
sum_q C_x(z_q)
 = Re Tr(G_x^(-1) M_z),                                (U-CAP.2)
```

where `M_z` is the Hermitian absolute target moment matrix. Positive real targets reduce `(U-CAP.2)`
to an ordinary relative Hankel trace.

Lean anchors include:

- `HTGeometry.weightedMonomialGram_posDef`;
- `HTGeometry.sum_weightedMonomialLeverage_eq_dimension`;
- `HTGeometry.canonicalMonomialReconstruction_reproduces_monomial`;
- `RHTower.ofReal_sum_canonicalRedundantSamplingCapacity_eq_trace`.

## 2. Critical-line absorption `[PROVED HERE]`

At a positive mass shift, every critical-line copy has a positive real coordinate

```text
lambda_q = xiShiftedReciprocalSquare y q > 0.
```

For a fixed frame, canonical capacity is bounded by a finite sum of positive powers of `lambda_q`.
Unconditional shifted reciprocal-power summability therefore gives summability of canonical
capacity over every critical-line subtype.

Let `P` denote the critical-line predicate and `f(q)>=0` canonical capacity. If

```text
sum_(q notin P) f(q) < 1,                               (U-CAP.3)
```

finite-tail convergence selects a finite critical-line packet `F` so that

```text
sum_(q outside F) f(q) < 1.                             (U-CAP.4)
```

Adding `F` to the positive prefix does not change the fixed inverse Gram matrix. Hence the full
Route-U square is strictly positive whenever off-critical canonical capacity is subunit.

Lean anchors:

- `summable_canonicalCapacity_xiCriticalLineSubtype`;
- `GaloisForLFunctions.HTGeometry.exists_finset_absorber_of_compl_tsum_lt_one`;
- `full_xiShiftedHankelPair_tsum_pos_of_canonicalBaseFrame_positiveAbsorber`;
- `full_xiShiftedHankelPair_tsum_pos_of_offCriticalCanonicalCapacity_lt_one`;
- `no_genuine_crossing_of_offCriticalCanonicalCapacity_lt_one`.

This proves that critical-line capacity is not an open Route-U burden. Any surviving capacity
estimate must control only off-critical copies.

## 3. Capacity no-go and pivot

Atomwise capacity uses an absolute evaluation norm. It discards conjugate/quartet cancellation.
The corpus's sharp sector law

```text
Im(lambda)^2 <= Re(lambda)^2 / 84
```

does not repair this at arbitrary degree: polynomial evaluation amplifies phase with degree, and
the existing affine atomwise no-go already shows every nonreal atom admits a negative real
polynomial test. A degree-uniform proof cannot follow from sector width alone.

**Positive survivor:** keep the signed off-critical sum and every lower flat-defect identity.

## 4. Off-critical carrier law `[PROVED HERE]`

At odd contact `2m+1`, write `P` for the degree-`n` flat null polynomial. The new arbitrary
multiplier identity proves

```text
L_y((P Q)^2) = 0                 for every deg Q <= m.  (U-IDX.1)
```

This strengthens the former terminal statement `L_y((PX^m)^2)=0` to the complete lifted null
subspace.

Fix a finite critical-line prefix with more than `n+m` distinct shifted nodes. For nonzero
`Q`, `deg Q<=m`, the positive-real critical-line restriction is strict:

```text
L_y^line((P Q)^2) > 0.                                (U-IDX.2)
```

Splitting the absolutely summable full divisor into critical and off-critical subtypes and using
`(U-IDX.1)` gives

```text
L_y^off((P Q)^2) = -L_y^line((P Q)^2) < 0.             (U-IDX.3)
```

Thus the off-critical restriction is negative definite on

```text
P · Poly_{≤m},
```

an `(m+1)`-dimensional space. The earlier final two-vector determinant `-delta^2` is only one
visible corner of this larger forced negative sector.

Lean anchors:

- `momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul`;
- `momentFunctional_liftedNullSubspace_eq_zero_of_odd_contact`;
- `offCritical_energy_doubleNegative_of_null_and_marked_negative`;
- `offCritical_liftedNullSubspace_neg_of_odd_contact`;
- `exists_degreeEscape_or_offCritical_doubleNegative_of_genuine_crossing`;
- `exists_degreeEscape_or_offCritical_liftedSubspace_neg_of_genuine_crossing`.

## 5. Folded-node index law `[PROVED HERE]`

For one shifted atom `z`, choose `r^2=z`. Its quadratic block is

```text
Re(z A(z)^2)=Re(r A(z))^2-Im(r A(z))^2.
```

Hence one detectable node supplies at most one negative coordinate. Raw Xi copies are not the
detectable nodes: functional-equation reflection fixes `z`, Schwarz conjugation replaces `z` by
`conj z`, and the real block is unchanged. Define the upper-half-plane fold

```text
z^up = (Re z, |Im z|).
```

The negative-coordinate map therefore lands in functions on the finite set of distinct folded
nodes. Strict negativity on `Poly_{≤m}` makes this map injective, so

```text
m+1 <= # { z_q^up : q in packet }.                     (U-IDX.4)
```

This removes analytic multiplicity, FE--Schwarz quartet duplication, and accidental collisions
between different zero copies. Equality of two folded shifted nodes holds exactly when the
centered spectral points differ by sign and/or complex conjugation. Thus folded nodes are the
geometric quartet orbits seen by the trace-Hankel form.

Lean anchors:

- `finite_xiFamily_negative_degreeLT_foldedNode_card`;
- `xiSpectralPoint_mem_quartet_of_conjugationFold_eq`;
- `oddContact_order_lt_offCriticalCover_foldedNode_card`.

The former annihilator argument remains valid but weaker:
`oddContact_order_lt_twice_offCriticalCover_card`. The sharp finite-cover statement is now
`m < #(folded nodes in T) <= |T|`.

## 6. Symmetry-complete finite localization `[PROVED HERE]`

Strict negativity of the full summable off-critical family has a uniform coercive margin on the
finite-dimensional lifted sector. Openness of positive definiteness localizes that margin to a
finite packet. The compactness theorem is strengthened to converge along any extensive finite-set
completion. Applying explicit FE--Schwarz quartet completion gives a finite symmetry-complete
packet that remains negative on every nonzero `P Q`, `deg Q<=m`, and still has more than `m`
distinct folded nodes. Infinite support cannot hide the index in a diffuse tail or in an
asymmetric truncation.

Lean anchors:

- `exists_finsetCompletion_xiFamily_negative_degreeLT_of_tsum_negative`;
- `exists_offCritical_quartetCompletion_foldedNodes_neg_of_odd_contact`.

## 7. Fixed-source Cassini jet bridge `[PROVED HERE]`

For every nonnegative shifts `y,v`, equality of folded shifted nodes is the same equivalence
relation:

```text
fold(lambda_y(q)) = fold(lambda_y(r))
  iff
fold(lambda_v(q)) = fold(lambda_v(r)).                  (U-IDX.5)
```

The Möbius mass translation creates no collisions. Consequently every finite folded-node count is
mass invariant. A crossing at adaptive `y` therefore forces the same `m+1` orbit-rank burden at
shift one, where `lambda_1(q)` is the fixed `xiSquaredSeamOneCoordinate` and the complete moment
germ is the logarithmic derivative of `xiSquaredSeamCassiniSource`.

The count transport is only the shadow of a stronger identity. Put

```text
Psi(U) = xiSquaredSeamCassiniSource(U).
```

For every `y>0` and every `n>=0`, the complete adaptive tower is the normalized jet of this one
fixed entire function at the moving zero-free real center `U=1-y`:

```text
-2 D^n(logDeriv Psi)(1-y) = n! xiShiftedReciprocalMoment(y,n).       (U-JET.1)
```

Indeed a Cassini zero has coordinate `U_q=1+alpha_q^2`, while its adaptive reciprocal-square atom
is `1/(alpha_q^2+y)=1/(U_q-(1-y))`. Mass shift is therefore translation of source basepoint, not a
congruence transport of quadratic forms. Equality (U-JET.1) retains every Hankel entry, flat Padé
defect, polynomial moment functional, and crossing-induced negative sector. It is valid for every
positive mass; only the optional prime--Gamma identification retains the `y<41/2` window.

Lean anchors:

- `conjugationFold_xiShiftedReciprocalSquare_eq_iff_shift`;
- `card_image_conjugationFold_xiShiftedReciprocalSquare_eq_shift`;
- `exists_offCritical_cassiniCoordinateFoldedNodes_of_odd_contact`;
- `neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment`;
- `xiShiftedHankelBoundaryPadeDefect_eq_cassiniSource`;
- `momentFunctional_xiShifted_eq_cassiniSource`;
- `exists_negative_cassiniSource_liftedShiftedSquare_of_genuine_crossing`.

## 8. New open core

Route U no longer asks for a generic sign of one polynomial. A hypothetical genuine crossing
forces all of the following simultaneously:

1. an off-critical-only negative carrier;
2. strict negativity on the self-selected space `P · Poly_{≤m}`;
3. negative-index growth at least `m+1`;
4. a finite symmetry-complete witness with at least `m+1` distinct folded quartet orbits;
5. the original first odd marked defect remains negative.

The next admissible source theorem must exclude this whole signed off-critical negative sector.
No transport estimate remains: at every adaptive `y`, the complete crossing flag is already the
jet-Hankel geometry of the same fixed source `-2 Psi'/Psi` at `1-y`. The exact open statement is
therefore a zero-free-real-center rigidity law: jets of this source cannot have a genuine odd
flat-Padé contact with negative terminal shifted square. It must use the lower vanished defects
and self-selected null polynomial essentially. An unrestricted Stieltjes positivity theorem for
all polynomials is RH-equivalent; a global Cassini orbit cap of zero is RH itself. Atomwise norms,
fixed polynomial classes, generic Weil budget inequalities, and critical-line tail estimates
cannot close it.

## No-go closure

- **Exact killing mechanism:** square Lagrange interpolation is saturated by reflection-duplicate
  sample copies; unsaturated capacity is at least one. Canonical atomwise capacity also discards
  signed quartet cancellation and has no degree-uniform consequence from the `1/84` sector alone.
- **Strongest positive survivor:** canonical redundant frames remove all dual-vector hypotheses;
  critical-line capacity is finitely absorbable; odd contact forces an off-critical negative
  subspace of dimension `m+1`; finite localization can be quartet complete; distinct folded-node
  rank is at least `m+1` and is mass invariant.
- **New insight:** Route U is a fixed-source zero-free-center jet-rigidity problem, not a scalar
  tail-capacity problem. Stationary contact order measures geometric quartet-orbit rank, not copy
  multiplicity. Adaptive mass flow is exactly basepoint translation on one Cassini resolvent;
  it changes neither orbit relation nor the full moment/defect data.
- **Status:** dependency-closed Lean proofs in modules listed above; RH remains open.

## Log

- 2026-08-10 — canonical redundant frame, leverage conservation, complex relative trace, and
  positive-target summability formalized.
- 2026-08-10 — critical-line finite absorption and off-critical-only no-crossing criterion
  formalized.
- 2026-08-10 — arbitrary lifted null-subspace identity and off-critical negative-index
  amplification formalized.
- 2026-08-10 — finite off-critical support contact ceiling `m < 2|T|` formalized.
- 2026-08-10 — sharp folded-node rank `m+1`, quartet-complete finite localization, and intrinsic
  finite-cover ceiling formalized.
- 2026-08-10 — folded-node equivalence/count proved mass invariant and transported to fixed
  Cassini source coordinate.
- 2026-08-10 — full adaptive moment tower, every Hankel block, Padé defect, and polynomial
  functional proved equal to jets of one fixed Cassini source at `1-y`; genuine crossing transport
  made window-free and sign-faithful.
