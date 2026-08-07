# First-order nonautonomous rational tails are eventually parabolic-orbifold currents

- **ID:** nonautonomous-rational-first-order-tail-orbifold-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** nonautonomous projective-time law + first-order tensor-symbol defect law
- **Statement:** A degree-expanding sequence of rational maps of projective lines has a nonconstant persistent observable of differential order at most one exactly when, after a finite transient prefix, it is a tower of coverings of parabolic orbifolds; the complete tail is the transported finite-holonomy Maurer--Cartan current field.

## Setup

Let `C` be algebraically closed of characteristic zero with trivial derivation.  For each phase
`i>=0`, let `F_i=C<y_i>`.  A rational map

```text
R_i:P1_i->P1_(i+1),  degree(R_i)>=2,
```

induces an injective differential pullback `phi_i:F_(i+1)->F_i`.  With

```text
P_(i,n)=R_(i+n-1) composed ... composed R_i,
T_i=intersection_(n>=0) P_(i,n)^*F_(i+n),
```

the phase tails satisfy `phi_i(T_(i+1))=T_i`.

## Classification theorem

**[PROVED HERE]** The following are equivalent.

1. Some, hence every, `T_i` contains a nonconstant element of differential order at most one.
2. There are a nonzero integer `k` and nonzero rational `k`-differentials

   ```text
   omega_i=q_i(z)(dz)^k
   ```

   at every phase, with

   ```text
   R_i^*omega_(i+1)=omega_i.                              (1)
   ```

3. There is a phase `N` such that for every `i>=N`:

   - `P1_i` carries a parabolic orbifold `O_i`;
   - `R_i:O_i->O_(i+1)` is an orbifold covering;
   - on the affine universal cover, `omega_i` is a nonzero scalar multiple of a power of the
     translation-invariant Maurer--Cartan form.

In these cases the complete phase tail is

```text
T_i=C<Q_i>,
Q_i=q_i(y_i)(delta y_i)^k,                                (2)
```

and `Q_i` is hypertranscendental.  The finite prefix before `N` may be arbitrary; its only effect
is to pull the late orbifold current back to a tensor with a finite transient divisor.

## Proof

### 1. Persistent first-order information forces a tensor chain

The first-order symbol theorem proves `1 iff 2`.  Briefly, there is no nonconstant order-zero tail
because a compatible rational family would satisfy

```text
degree(a_i)=degree(P_(i,n)) degree(a_(i+n))
```

at every depth.  For an order-one family

```text
H_i(z,v)=H_(i+1)(R_i(z),R_i'(z)v),                        (3)
```

the first nonzero Laurent term at vertical infinity is `q_i(z)v^k` for one
phase-independent `k!=0`.  Comparing symbols in (3) gives (1).  Conversely (1) and the chain rule
give a compatible family (2), which is hypertranscendental by differential-algebraic transitivity.

Replace `omega_i` by its inverse if `k<0`; henceforth its order is a positive integer `ell`.

### 2. Finite transient zeros disappear

Let `Z_i` be the total zero multiplicity of `omega_i`.  The pullback order law at a point of
ramification index `e_x` is

```text
ord_x(R_i^*omega_(i+1))
  =e_x ord_(R_i(x))(omega_(i+1))+ell(e_x-1).               (4)
```

Summing over fibers of terminal zeros gives

```text
Z_i>=degree(P_(i,n)) Z_(i+n).                              (5)
```

Since every map has degree at least two, (5) makes `Z_j=0` for every sufficiently late phase.

### 3. Expansion quantizes every late cone weight

Fix an initial phase `i`.  At any point `x`, define its shifted tensor order

```text
a_i(x)=ell+ord_x(omega_i).                                 (6)
```

At regular points `a_i(x)=ell`; only the finite divisor support is exceptional.  For a prefix
`P=P_(i,n)`, equation (4) becomes the exact multiplicative law

```text
a_i(x)=e_x(P) a_(i+n)(P(x)).                              (7)
```

Let

```text
B_i^+ = sum_(x in supp div omega_i, a_i(x)>0) a_i(x),
B_i^- = sum_(x in supp div omega_i, a_i(x)<0) |a_i(x)|.
```

These are finite integers.

Take a singular point `y` of a deep terminal tensor and put `a=a_(i+n)(y)`.

- If `a<0`, every point of `P^(-1)(y)` belongs to the finite negative exceptional support at phase
  `i`.  Taking absolute values in (7) and summing the ramification indices gives

  ```text
  degree(P)|a|<=B_i^-.
  ```

- If `a>0` but `a` does not divide `ell`, no preimage can be regular: a regular preimage would
  give `ell=e_x a`.  Hence the whole fiber lies in the finite positive exceptional support, and

  ```text
  degree(P)a<=B_i^+.
  ```

For prefix degree larger than `max(B_i^+,B_i^-)`, both alternatives are impossible.  Therefore
every sufficiently late singular point has

```text
a=0  or  a is a positive divisor of ell.                  (8)
```

The zero case corresponds to an infinite orbifold weight.  Otherwise define

```text
nu_y=ell/a in {2,3,...}.                                   (9)
```

Because late tensors are zero-free, every singularity is a pole of order

```text
p_y=ell-a=ell(1-1/nu_y).                                  (10)
```

The divisor degree of an `ell`-differential on `P1` is `-2ell`, so

```text
sum_y p_y=2ell,
2-sum_y(1-1/nu_y)=0.                                      (11)
```

Thus the weights define a parabolic orbifold.  Equation (7) is exactly the orbifold-covering law

```text
nu_(R_i(x))=e_x(R_i) nu_x.                                (12)
```

This proves that every sufficiently late map is a covering between parabolic orbifolds.

### 4. Uniformization and completeness of the tail

The parabolic signatures are the Euclidean signatures

```text
(infinity,infinity), (2,2,infinity), (2,2,2,2),
(2,3,6), (2,4,4), (3,3,3).
```

Their universal orbifold cover is the affine line, and every covering lifts to an affine map.
Equivalently the protocol lifts phasewise to isogenies of `G_m` in the cusp cases or elliptic
curves in the compact cases, modulo finite holonomy.  Pullback of `omega_i` to the cover is a
constant multiple of the translation-invariant form to the `ell`-th power.

Prefix degrees tend to infinity, so the union of iterated deck kernels is infinite and hence
Zariski dense in the one-dimensional connected algebraic cover group.  The nonautonomous
isogeny-tail theorem therefore identifies the full late tail with the finite-holonomy invariant
Maurer--Cartan field `C<Q_i>`.  Exact phase-tail transport carries this equality backward through
the arbitrary finite prefix.  This proves (2) and `2 implies 3`.

Conversely a late parabolic-orbifold tower supplies its descended Maurer--Cartan tensor chain.
Pull it through the finite prefix and evaluate on the free jet to obtain a nonconstant order-one
tail element.  This proves `3 implies 1` and completes the classification.

## Physical/topological meaning

This is a converse holography theorem.  It does not assume a hidden group, flat space, or orbifold.
The mere survival of one first-order observable through every rational constraint depth forces:

1. an integer tensor charge at vertical jet infinity;
2. a finite budget for transient curvature defects;
3. quantization of every late cone angle by divisibility of that tensor charge;
4. a Euclidean orbifold and affine universal cover;
5. the complete tail as a finite-holonomy Maurer--Cartan current field.

The finite prefix is genuine transient geometry, not a flaw: a one-sided constraint protocol can
begin arbitrarily, but it cannot keep creating defects at unbounded depth because every deep defect
must be replicated across all inverse sheets.  No propagated physical state, Hamiltonian,
probability, numerical experiment, or continuous time is used.

## Novelty and significance gate

Classical parents are explicitly separated:

- pullback orders of meromorphic tensors and parabolic-orbifold uniformization;
- autonomous parallel-tensor classification, especially Garofali,
  [Dynamical systems with a parallel tensor](https://arxiv.org/abs/1806.10056);
- differential Luroth and scalar projective tail coordinates;
- constant algebraic-group logarithmic derivatives.

Targeted searches found no nonautonomous converse deriving an eventual parabolic orbifold from a
persistent first-order differential-substitution tail, no tensor-charge divisibility argument
(7)--(9), and no finite-transient defect classification.  The theorem is more than a transported
version of the autonomous result: every individual early map may be nonexceptional, and the
orbifold structure is forced only by infinite compatibility.

The result is both novel and significant within the proposed HT geometry: it classifies the
complete first-order persistent sector of every degree-expanding scalar rational protocol.  It is
not yet the full medal-level theorem because a nontrivial tail might a priori have minimal
differential order greater than one.  Eliminating or classifying that sector is the remaining
global converse.

## RH impact audit

Any future source-pure rational protocol on a completed zeta or `L`-function field with an
RH-sensitive first-order tail is now forced into a finite-transient parabolic-orbifold current.
This sharply restricts possible constructions and makes the required topology explicit.  No such
zeta protocol or RH-sensitive current is presently known, so the theorem has no direct RH
consequence.

## Lean status

`FirstOrderRationalTailSymbol.lean` formalizes the differential-Laurent step that this card
previously listed as missing.  For arbitrary rational first-order observables it constructs the
injective vertical-transport map and proves:

- `verticalRatFuncLaurentWeight_eq_of_transport`, invariance of the integer vertical weight;
- `verticalRatFuncLaurentCoefficient_eq_zpow_of_transport`, the exact leading tensor law;
- `verticalRatFuncLaurentWeight_eq_zeroPhase`, one common weight along an arbitrary phase chain;
- `verticalRatFuncLaurentCoefficient_phaseChain`, the phasewise transported coefficient chain.

`NonautonomousFirstOrderTailSymbol.lean` formalizes tensor evaluation and composition, fiberwise
degree-times-multiplicity amplification, the exact logarithmic defect cutoff, eventual zero
collapse, confinement of a nondividing terminal angle to the exceptional divisor, the resulting
degree budget, and the divisibility/angle-quantization theorem.  The cached
`NonautonomousFirstOrderTailSymbolLaw.lean` additionally proves that every compatible tensor chain
lies in every phase tail, and that a transcendental chain makes those tails nontrivial.

The remaining formal gap is the analytic parabolic-orbifold uniformization and its identification
of the complete tail with the finite-holonomy Maurer--Cartan field.  It is not introduced as an
axiom.  No build was run for this audit because all three exact modules already have cached
`.olean` files.

## Gates

- [x] 0 -> 1: exact source-pure converse and tensor-symbol attack
- [x] 1 -> 2: complete proof through integral holonomy and exact tail reconstruction
- [ ] 2 -> 3: Laurent-symbol extraction, tensor quantization, and phase-tail membership are
      formalized; parabolic-orbifold uniformization and complete-tail identification remain
- [ ] 3 -> 4: standalone manuscript and independent specialist audit

## Lean progress — the Euclidean signature classification is closed

`GaloisForLFunctions/HTGeometry/EuclideanConeSignature.lean` (wired, axiom-clean):

    euclidean_cone_triple            the only weakly increasing integer triples ≥ 2 with
                                     reciprocal sum 1 are (2,3,6), (2,4,4), (3,3,3)
    cone_pair_eq_two, cone_quad_eq_two
    sum_one_sub_inv, sum_inv_le_half_length, sum_inv_pos
    parabolic_signature_classification :
      c + ∑ (1 - 1/ν_i) = 2 with every ν_i ≥ 2 and the list weakly increasing forces
      (c, list) ∈ {(2, []), (1, [2,2]), (0, [2,2,2,2]), (0, [2,3,6]), (0, [2,4,4]), (0, [3,3,3])}

`GaloisForLFunctions/HTGeometry/ParabolicSignatureClassification.lean` (wired, axiom-clean):

    ParabolicSphereSignature.euclidean          each recorded signature solves the equation
    ParabolicSphereSignature.coneOrders_spec    its cone list is sorted with entries ≥ 2
    exists_parabolicSphereSignature             every solution is one of the six
    parabolicSphereSignature_iff                **the six signatures are exactly the solutions**

The enumerated datatype `ParabolicSphereSignature` was previously a convention; it is now proved to
be the complete solution set of the parabolic (zero orbifold Euler characteristic) equation.  This
is the step the card's proof calls "the weights define a parabolic orbifold" together with the list
of Euclidean signatures.

## Lean progress — the Hurwitz gap for arbitrary sphere signatures

`GaloisForLFunctions/HTGeometry/HyperbolicSignatureGap.lean` (wired, axiom-clean):

    half_le_cone_defect, two_thirds_le_cone_defect, cone_defect_lt_one
    half_length_le_sum_defect, sum_defect_lt_length
    hyperbolic_signature_gap :
      if `2 < c + ∑ (1 - 1/ν)` with every `ν ≥ 2`, then `2 + 1/42 ≤ c + ∑ (1 - 1/ν)`

This is `(21)` of the complete-tail card, generalized from triples to arbitrary signatures with
cusps: the corpus already owned the delicate three-cone case (`hurwitz_triple_sum_le`), and every
other case is a counting bound (five cones, or four with one order at least three, already overshoot
`2` by more than `1/42`).

Together with `parabolic_signature_classification` this closes the Euler-characteristic trichotomy
input of the classification: hyperbolic signatures are bounded away from parabolic by `1/42`, and
the parabolic ones are exactly the six recorded signatures.

Added to `ParabolicSignatureClassification.lean` (wired, axiom-clean):

    sum_map_const_mul                           pulling the tensor weight out of a pole-order sum
    parabolic_of_pole_orders                    `(11)`: total pole order `2ℓ` gives `∑(1-1/ν) = 2`
    parabolicSphereSignature_of_pole_orders     hence one of the six signatures

This is the passage from the divisor-degree budget of an `ℓ`-differential on the sphere to the
parabolic equation and its classification — steps `(10)`, `(11)` and the signature list of the
proof, now formal end to end.
