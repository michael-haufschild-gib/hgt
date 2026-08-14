# First-order nonautonomous rational tails are eventually parabolic-orbifold currents

- **ID:** nonautonomous-rational-first-order-tail-orbifold-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Formalized companion:** `nonautonomous-rational-first-order-tail-orbifold-law-formalized.md`
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
- [x] 2 -> 3: Laurent-symbol extraction, tensor quantization, phase-tail membership,
      parabolic-orbifold uniformization (discharged uniformization-free in the differential-deck
      model) and complete-tail identification (on the generic reparametrisation of the meromorphic
      plane field) are all formalized
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

## Lean plan — the cusp case needs no uniformization

The `b = 2` branch of the classification, signature `(∞,∞)`, does not need orbifold uniformization
at all: the card itself says the maps are monomials after projective coordinates and that `dz/z`
is transported up to a scalar.  That is exactly the `G_m` position--velocity theorem already proved
for the isogeny card:

    HTGeometry/LogarithmicDerivativeFixedField.lean
      fixedField_scaling_eq_logDerivField : {x | ∀ a ≠ 0, σ_a x = x} = F⟨y′/y⟩

What is missing to apply it to a power protocol `R_i(z) = z^{d_i}` is one generalization: the deck
group of a power map is the group of `d`-th roots of unity, not a single scalar with pairwise
distinct powers.  So `ScalingInvariantRationalFunction.lean`'s
`natDegree_eq_zero_of_scaling_invariant` should be restated for a *family* of scalars with the
property that for every pair of indices `i ≠ j` some member `a` of the family has `a^i ≠ a^j` —
which a sequence of roots of unity of unbounded order satisfies.  With that, the tail of a
degree-expanding power protocol is `C⟨y′/y⟩`, the cusp case is closed, and uniformization is needed
only for the compact signatures.

Added (wired, axiom-clean):

    ScalingInvariantRationalFunction.lean
      eq_monomial_of_comp_scaling_family
      natDegree_eq_zero_of_scaling_invariant_family
    LogarithmicDerivativeFixedField.lean
      mem_logDerivField_of_scaling_invariant_family

The deck group no longer has to contain a single scalar with pairwise distinct powers: a family
that separates every pair of exponents suffices, and roots of unity of unbounded order do that
although no single root of unity does.  This is exactly the deck group of a degree-expanding power
protocol, so the cusp signature `(∞,∞)` is now reachable without any uniformization input.

## The cusp branch is closed, with no uniformization

Added to `LogarithmicDerivativeFixedField.lean` (wired, axiom-clean):

    scalingAutomorphism_fixes_differentialAdjoin   the deck automorphism fixes the differential
                                                   field generated by anything it fixes
    scalingAutomorphism_pow                        it acts on `y ^ d` by `a ^ d`
    scalingAutomorphism_fixes_powAdjoin            so a `d`-th root of unity fixes `F⟨y^d⟩`
    logDeriv_mem_powAdjoin                         `y′/y = (1/d)·((y^d)′/(y^d)) ∈ F⟨y^d⟩`
    mem_logDerivField_of_mem_powAdjoin             the hard inclusion
    iInter_powAdjoin_eq_logDerivField :
      {x | ∀ n, x ∈ F⟨y ^ D n⟩} = F⟨y′/y⟩

whenever the degree sequence `D` carries roots of unity of unbounded order.  This is the `(∞,∞)`
signature branch: the tail of a degree-expanding power protocol is exactly the Maurer--Cartan field
of the logarithmic derivative.  The deck group here is the roots of unity, no single one of which
separates two exponents, which is why the family form of the scaling-invariance theorem was needed.

Uniformization is therefore required only for the compact signatures `(2,2,2,2)`, `(2,3,6)`,
`(2,4,4)`, `(3,3,3)` and the mixed `(2,2,∞)`.

## The `(2,2,∞)` current, exactly

`GaloisForLFunctions/HTGeometry/ChebyshevQuadraticCurrent.lean` (wired, axiom-clean):

    deriv_add_inv                        `(w + w⁻¹)′ = w′(w² - 1)/w²`
    add_inv_sq_sub_four                  `(w + w⁻¹)² - 4 = (w² - 1)²/w²`
    logDeriv_sq_eq_chebyshev_current     **`(w′/w)² = y′²/(y² - 4)` for `y = w + w⁻¹`**
    logDeriv_inv                         the deck involution negates `w′/w`
    add_inv_involutive                   and fixes the Chebyshev coordinate

This is the card's "rational quadratic differential with simple poles at the two order-two points
and a double pole at the cusp, transported up to scalar", written as an exact identity: the square
of the Maurer--Cartan current upstairs *is* the quadratic differential `y′²/(y² - 4)` downstairs,
whose denominator vanishes exactly at the two cone points `y = ±2`.  The square is the right object
because the involution negates the current, so only its square descends.

## Correction — the additive deck group is already corpus-owned

The compact signatures have the additive group as universal cover and translations as deck
transformations.  That rigidity is **already in the tree** and must not be rebuilt:

    HTGeometry/RatFuncTranslationFixedField.lean
      ratFuncTranslation_fixed_eq_constant          a translation-invariant rational function is a
                                                    constant, for one nonzero shift in char 0
      fixedField_zpowers_ratFuncTranslationAction   its fixed-field form
    HTGeometry/ScalarAdditiveDifferentialTorsor.lean
      scalarDerivativeField, scalarAdditiveTorsorRatFuncEquiv
      scalarDifferentialTranslationEquivDerivative  the translation automorphisms
      scalarDifferentialTranslationEquiv_fixed_on_derivativeField
      fixedField_zpowers_scalarDifferentialTranslation_one
                                                    **unit translation fixes exactly `F⟨q′⟩`**
      DifferentialAlgEquiv.fixed_on_scalarDerivativeField_of_fixed_deriv

So for the compact signatures the deck-group algebra is done; what those four signatures still need
is only the uniformizing coordinate — a doubly periodic meromorphic function with prescribed
lattice.  The multiplicative analogue (`LogarithmicDerivativeFixedField.lean`) had no counterpart in
the tree, which is why it had to be built.

## The four compact Euclidean currents, exactly

`GaloisForLFunctions/HTGeometry/EuclideanOrbifoldCurrents.lean` (wired, axiom-clean):

    weierstrass_square_current      `(2,2,2,2)`, coordinate `y = ℘`:
                                      `(y′)² = (4y³ - g₂y - g₃)(u′)²`
    weierstrass_square_current_div  its quotient form `(u′)² = (y′)²/(4y³ - g₂y - g₃)`
    weierstrass_cubic_current       `(3,3,3)`, hexagonal lattice `g₂ = 0`, coordinate `y = ℘′`:
                                      `2(y′)³ = 27(y² + g₃)²(u′)³`
    weierstrass_quartic_current     `(2,4,4)`, square lattice `g₃ = 0`, coordinate `y = ℘²`:
                                      `(y′)⁴ = 16y³(4y - g₂)²(u′)⁴`
    weierstrass_sextic_current      `(2,3,6)`, hexagonal lattice `g₂ = 0`, coordinate `y = ℘³`:
                                      `(y′)⁶ = 729y⁴(4y - g₃)³(u′)⁶`

Each is the card's "on the affine universal cover, `ω_i` is a nonzero scalar multiple of a power of
the translation-invariant Maurer–Cartan form" made explicit for one compact signature, in the same
style as the `(2,2,∞)` Chebyshev identity.  The invariant coordinate of each signature is the
indicated function of `℘`, whose degree matches the order of the rotation in the deck group: `℘` has
degree `2`, `℘′` degree `3`, `℘²` degree `4`, `℘³` degree `6`.

No uniformization theorem and no analysis is used.  The hypotheses are the Weierstrass relation
`q² = 4p³ - g₂p - g₃` and the chain rules `p′ = q·u′`, `q′ = (6p² - g₂/2)·u′`, so each statement is
an identity in an arbitrary differential field; the exponent pattern of the right-hand side is the
cone-point divisor of the signature.

With this, every parabolic signature of the classification has its transported current formalized:
`(∞,∞)` by `iInter_powAdjoin_eq_logDerivField`, `(2,2,∞)` by `logDeriv_sq_eq_chebyshev_current`, and
the four compact ones here.

## Lean progress — the two expansion steps of the proof

`GaloisForLFunctions/HTGeometry/ExpandingProtocolVanishing.lean` (wired, axiom-clean):

    eq_zero_of_expanding_degree_law     §1: there is no nonconstant order-zero tail — a degree
                                        obeying `deg a₀ = deg P_n · deg a_n` with `deg P_n ≥ 2^n`
                                        at every depth is zero
    eventually_eq_zero_of_expanding_bound
                                        §2: transient zeros disappear — multiplicities obeying
                                        `2^n · Z_n ≤ Z_0` vanish from some depth on

Both are the arithmetic core of their sections: a fixed natural number cannot dominate `2^n` for
every `n`.  Every map of the protocol has degree at least two, so the composite degree is at least
`2^n`, and that is the only property used.

## Lean progress — the symbol comparison of §1

`GaloisForLFunctions/HTGeometry/VerticalSymbolTransformation.lean` (wired, axiom-clean):

    leadingCoeff_comp_scaling      the leading coefficient after `v ↦ a v` is `a^{deg}` times the
                                   original
    symbolDegree, symbolCoeff      the vertical symbol of a coprime pair: an integer degree and a
                                   leading coefficient
    symbolDegree_comp_scaling      the degree is invariant under the fibrewise scaling
    symbolCoeff_comp_scaling       **`q ↦ a^k q`**: the leading coefficient transforms as a
                                   `k`-differential, with `k` its own symbol degree
    symbol_comparison              the two conclusions together
    symbolDegree_const_of_protocol **`k` is phase-independent** along the whole protocol

This is the mechanism of "comparing symbols in `(3)` gives `(1)`": the exponent of the fibre
coordinate at vertical infinity is preserved by every phase map, so a single `k` serves all phases,
and the leading coefficients then satisfy exactly the pullback law `R_i^* ω_{i+1} = ω_i` of a
`k`-differential.  Only the two properties of the substitution are used — that it is a scaling of
the fibre coordinate by a nonzero factor.

## Lean progress — §3's quantization step `(8)`

Added to `ExpandingProtocolVanishing.lean` (wired, axiom-clean):

    weight_quantization    once the prefix degree exceeds the finite exceptional bound `B`, a
                           shifted tensor order is `0` or a positive divisor of `ℓ`

Both alternatives of the card's argument reduce to the same inequality `deg(P)·|a| ≤ B` with
`|a| ≥ 1`, which contradicts `B < deg(P)`.  With `(8)` formal, and the bridge from pole orders to
the parabolic condition already formal (`parabolicSphereSignature_of_pole_orders`, together with
`parabolic_triple_classification` and `hyperbolic_signature_gap`), §3 of the proof is complete:
late weights quantize, the pole orders sum to `2ℓ`, and the resulting signature is one of the six
Euclidean ones.

## Lean progress — every deck fixed field is identified, uniformization-free

The "parabolic-orbifold uniformization" half of the open gate is now discharged for every
signature, in the same uniformization-free differential-deck model that closed the cusp branch.
Three new modules (wired into `GaloisForLFunctions.HTGeometry`, all
`[propext, Classical.choice, Quot.sound]`):

    RootOfUnityScalingFixedField.lean
      mem_differentialAdjoin_pow_of_rootOfUnity_invariant
      setOf_rootOfUnityScaling_invariant… :
        **the invariant field of a scaling by a root of unity of exact order n on the free
        rank-one differential field is C⟨vⁿ⟩** — the rotation layer of every parabolic deck
        group, by the rank-1 torus invariant theorem plus v′/v = (vⁿ)′/(n·vⁿ)

    TranslationRotationDeckFixedField.lean
      mem_derivativeField_of_translation_invariant     unit translation ⟹ membership in C⟨u′⟩
      setOf_translation_rotation_invariant_eq_differentialAdjoin_derivPow :
        **the deck fixed field of a compact signature is exactly C⟨(u′)ⁿ⟩**, n ∈ {2,3,4,6} the
        rotation order — translations collapse to the velocity field by the additive torsor
        theorem, the rotation then scales the free velocity generator
      setOf_forall_fixed_eq_differentialAdjoin_derivPow :
        the same for ANY family of deck maps containing the two generators — the complete tail
        of an affine deck tower of any depth profile

    DihedralInversionFixedField.lean
      inversionAutomorphism, inversionAutomorphism_logDeriv    w ↦ w⁻¹ negates the current
      setOf_scaling_inversion_invariant_eq_differentialAdjoin_sqCurrent :
        **the dihedral (2,2,∞) deck fixed field is exactly C⟨(w′/w)²⟩**
      setOf_forall_fixed_eq_differentialAdjoin_sqCurrent       the tower form

With `iInter_powAdjoin_eq_logDerivField` (the cusp) and the six transported-current identities
(`ChebyshevQuadraticCurrent`, `EuclideanOrbifoldCurrents`), the "finite-holonomy invariant
Maurer–Cartan field" of every parabolic signature is now a computed object: `C⟨(u′)ⁿ⟩` on the
cover, equal to the rational current downstairs by the proved identities.  No uniformization
theorem enters: translations use the scalar additive torsor, rotations the rank-one torus
invariant theory, and the inversion the free palette equivalence.

What remains of the gate is the complete-tail identification *in the protocol presentation* for
the compact signatures: exhibiting the elliptic phase fields concretely (the elliptic-curve
column of the nonautonomous isogeny-tail card) so that the phase-tail equals these deck fixed
fields through the depthwise deck identity, as already done for the `G_m` and torus columns.
Mathlib now carries the analytic Weierstrass `℘` (`Mathlib.Analysis.SpecialFunctions.Elliptic.
Weierstrass`), which supplies the uniformizing witness for that presentation.

## Lean progress — the elliptic function field theorem is proved

The uniformizing witness the previous section names is now a theorem of this tree, not a plan.  Four
new modules (wired into `GaloisForLFunctions.HTGeometry`, all `[propext, Classical.choice,
Quot.sound]`):

    EllipticMeromorphicOrderTools.lean
      meromorphicOrderAt_lt_sub_of_trailingCoeff_eq   equal order and equal trailing coefficient
                                                      make the difference vanish to higher order
      even_meromorphicOrderAt_of_neg_eq               an even meromorphic function has even order
      exists_const_eventuallyEq_of_lattice_periodic   elliptic Liouville in meromorphic form, via
                                                      the canonical normal form

    EllipticEvenPolynomialWeierstrass.lean
      meromorphicOrderAt_weierstrassP_pow_zero        `℘ ^ k` has pole order exactly `2k`
      exists_polynomial_eval_weierstrassP_of_even :
        **an even lattice-periodic meromorphic function analytic off the lattice is a polynomial
        in `℘`** — descending induction on the even pole order, cancelling the leading Laurent term
        by a multiple of `℘ ^ k`

    EllipticEvenRationalWeierstrass.lean
      exists_pole_representative_weierstrassP         every pole is congruent to a pole of the
                                                      fundamental parallelogram, with the same
                                                      order and the same value of `℘`
      exists_rational_eval_weierstrassP_of_even :
        **every even elliptic function is rational in `℘`** — multiply by the monic product of the
        `(℘ - ℘(a))` over the poles `a` of the parallelogram, raised to the pole orders

    EllipticFunctionFieldWeierstrass.lean
      meromorphicOrderAt_derivWeierstrassP_zero       `℘'` has a triple pole at the origin
      eventually_derivWeierstrassP_ne_zero            hence `℘'` is nowhere locally zero
      exists_rational_weierstrass_representation :
        **every elliptic function lies in `ℂ(℘, ℘')`**:
          `C(℘)·f = A(℘) + ℘'·B(℘)` with `C` monic, as germs at every point

No divisor-degree theorem, no residue theorem and no Jensen formula is used: the even part and the
`℘'`-quotient of the odd part are both even, and the pole-clearing product plus elliptic Liouville
finish the induction.  This is the classical generation theorem for elliptic function fields, which
mathlib does not carry, and it is the concrete presentation of the compact-signature phase fields
that this card's gate calls for.

## Lean progress — the compact-signature current on a differential-generic carrier

The `(2,2,2,2)` transported current now exists on a carrier where the orbifold coordinate is a
*differential-generic* point, not a fixed function, so its current is nonconstant.

`GaloisForLFunctions/HTGeometry/EllipticReparamCurrent.lean` (wired, axiom-clean):

    eventually_notMem_lattice        the lattice is eventually avoided off any point
    weierstrass_relation_plane       `(℘')² = 4℘³ - g₂℘ - g₃` as an identity of meromorphic germs
    deriv_weierstrassPElement        the derivative of `℘` in the plane field is `℘'`
    reparamWeierstrassP, reparamDerivWeierstrassP
    deriv_reparamWeierstrassP        **`P′ = Q·u′`** — the chain rule with the free velocity
    weierstrass_relation_reparam     the Weierstrass relation upstairs
    weierstrass_square_current_reparam :
      **`(P′)² = (4P³ - g₂P - g₃)·(u′)²`** — the `(2,2,2,2)` current, on the generic
      reparametrisation

The carrier is `ReparamField MeromorphicPlane`: the meromorphic functions of the plane composed with
a completely free reparametrisation of the variable, with the chain-rule derivation
`(a)′ = (δa)·u′` (`HTGeometry/GenericReparametrization.lean`).  There the deck translations of the
lattice still act, by `ReparamField.fieldEquiv`, and fix every jet — so the deck theory of the
compact signatures runs with no `℘` addition theorem.  Its translation layer is already closed:

    HTGeometry/EllipticVelocityTail.lean
      deckInvariantField_eq_velocityField :
        the invariants of every deck translation of every depth of a degree-expanding elliptic
        protocol are exactly `C⟨u′⟩`

What remains for the compact signatures is the rotation layer on this carrier: the order-`n`
rotation acts by `ReparamField.twistFieldEquiv` with factor `ζ`
(`HTGeometry/TwistedReparametrizationAutomorphism.lean`), and the invariant field of that scaling on
the free rank-one field `C⟨u′⟩` is `C⟨(u′)ⁿ⟩` by the corpus's
`RootOfUnityScalingFixedField.setOf_rootOfUnity_invariant_eq_differentialAdjoin_pow`, once the
subfield `C⟨u′⟩` is equipped with its restricted differential structure.

## Lean progress — the compact-signature deck fixed field, in the protocol presentation

The gate's remaining item — the complete-tail identification *in the protocol presentation* for the
compact signatures — is now a theorem.

`GaloisForLFunctions/HTGeometry/PlaneScaleSimilarity.lean` (wired, axiom-clean):

    planeScaleEquiv                  scaling the variable, as a field automorphism
    planeScale_constPlane            it fixes the constants
    planeScale_deriv                 **`(f(m·))′ = m·f′(m·)`** — scaling is a *similarity*

`GaloisForLFunctions/HTGeometry/EllipticRotationTail.lean` (wired, axiom-clean):

    rotationEquiv, rotationAlgEquiv  the orbifold rotation on the generic reparametrisation,
                                     acting on every jet by the same root of unity
    rotationEquiv_jet, rotationEquiv_deriv
    rotation_fixes_jetPow            the rotation fixes `C⟨(u′)ⁿ⟩`
    differentialAdjoin_jetPow_le_velocityField
    mem_differentialAdjoin_jetPow_of_rotation_invariant :
      an element of the velocity field fixed by a rotation of exact order `n` is a differential
      rational function of `(u′)ⁿ`
    setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow :
      **the deck fixed field of a compact parabolic signature is exactly `C⟨(u′)ⁿ⟩`** — the
      elements fixed by every deck translation of every depth of a degree-expanding elliptic
      protocol and by the rotation of exact order `n`

Combined with `weierstrass_square_current_reparam` — `(P′)² = (4P³ - g₂P - g₃)(u′)²` on the same
carrier — this is the card's assertion `(2)` for the compact signatures: the complete tail is the
finite-holonomy Maurer–Cartan current field, and the current is the rational differential of the
orbifold coordinate.

The presentation is uniformisation-free in the sense the card requires: the deck transformations are
the analytic translations and scalings of the plane, transported to a carrier on which the orbifold
coordinate is a differential-generic point; no `℘` addition theorem and no uniformisation theorem is
used anywhere.

## Lean progress — the phase tail on the reparametrised carrier, and the closed gate

`GaloisForLFunctions/HTGeometry/EllipticPhaseTailReparam.lean` (wired, axiom-clean):

    baseAdjoinJets                   the phase field: the elliptic functions of a phase together
                                     with the reparametrisation jets
    jet_mem_baseAdjoinJets, velocityField_le_baseAdjoinJets
    translationFixedField            the elements fixed by one deck translation
    baseAdjoinJets_le_translationFixedField
                                     a deck translation of a phase fixes the whole phase field
    iInter_baseAdjoinJets_eq_velocityField :
      **the phase tail of a degree-expanding elliptic protocol is the velocity field**
    iInter_baseAdjoinJets_rotation_eq_differentialAdjoin_jetPow :
      **with the rotation of exact order `n`, the phase tail is `C⟨(u′)ⁿ⟩`**

This is the last clause of the `2 → 3` gate: the phase tail — an intersection of the phase fields of
all depths — equals the deck fixed field, computed on a carrier where the orbifold coordinate is a
differential-generic point.  With `weierstrass_square_current_reparam` the current is the rational
differential of that coordinate, so the tail is the finite-holonomy Maurer–Cartan current field
`C⟨Q_i⟩` of the card's `(2)`.

Every declaration this card names was re-audited with `#print axioms` and reports
`[propext, Classical.choice, Quot.sound]` (several report only `[propext, Quot.sound]`).
