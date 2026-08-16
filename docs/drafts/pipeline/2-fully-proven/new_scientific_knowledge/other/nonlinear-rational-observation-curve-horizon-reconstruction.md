# Nonlinear rational observation curves are visible through every HT derivative horizon

- **ID:** `nonlinear-rational-observation-curve-horizon-reconstruction`
- **Stage:** 2-fully-proven
- **Type:** GENERAL HT THEOREM / DIFFERENTIAL-RATIONAL OBSERVABILITY CLASSIFICATION
- **Scientific status:** `[PROVED ON PAPER] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `projective-horizon-building-schwarzian-complementarity`
- **Statement:** At every positive derivative depth, finitely many rational views of a free HT
  scalar reconstruct exactly the differential function field of their normalized observation
  curve if and only if that curve is not an affine line.

## Goal

Classify which finite static rational observation systems remain globally observable after deleting
every jet below an arbitrary positive depth. The result concerns simultaneous constraint fields.
Derivative depth is a filtration index, not a flow or time variable.

## Main theorem: normalization of the observation curve `[PROVED]`

Let `C` be an algebraically closed constant field of characteristic zero and let `x` be
hypertranscendental over `C`. Choose nonconstant rational functions

```text
R_1,...,R_m in C(z),   m>=1,
```

and let `T in C(x)` be an ordinary Luroth generator of their joint function field:

```text
C(R_1(x),...,R_m(x))=C(T).                                (1)
```

For `n>=1`, put

```text
L_n=C<(R_1(x))^(n),...,(R_m(x))^(n)>.
```

Then exactly one of the following holds.

1. The normalized observation curve is an affine line. Equivalently, for a generator `V` of
   `C(T)`, every `R_i` has the form `a_i V+b_i`. Then

   ```text
   L_n=C<V^(n)> < C<V>                                    (2)
   ```

   for every `n>=1`.

2. The normalized observation curve is not an affine line. Then

   ```text
   L_n=C<T>                                                (3)
   ```

   for every `n>=1`.

Thus the arbitrarily deep derivative horizons reconstruct the normalization of their joint
algebraic image and no larger finite cover above it. Affine linearity of that image, not derivative
depth, is the exact failure condition.

### Proof

Replace `x` by the differentially transcendental Luroth coordinate `T`. Differential Luroth gives
`L_n=C<u>` for some differential rational `u(T)`. Choose `R_1` nonconstant. Highest-jet coefficient
comparison, exactly as in Lemma 1 below, puts every slope ratio

```text
q_i(T)=R_i'(T)/R_1'(T)                                    (4)
```

in `L_n`.

If every `q_i` is constant, integration gives `R_i=a_iR_1+b_i`; the observation curve is a line,
`R_1` is a rational coordinate on its normalization, and `(2)` follows. Positive differential
order makes the inclusion strict.

Otherwise some `q_i` is nonconstant, so `T` is algebraic over `L_n`. Let `Z` be an `L_n`-conjugate
of `T`. Unique extension of the derivation and equality of the observed `n`-th jets give, by their
highest free jet coefficients,

```text
R_i'(Z) dZ/dT = R_i'(T)                                   (5)
```

for every `i`. Hence

```text
R_i(Z)=R_i(T)+c_i,   c_i in C.                            (6)
```

The translation vector `c=(c_i)` stabilizes the irreducible observation curve. A nonlinear
algebraic curve in affine space has trivial translation stabilizer in characteristic zero: if
`c!=0`, all integer multiples of `c` stabilize it, the Zariski closure is a one-dimensional
additive subgroup, and the curve is its affine-line coset. Therefore `c=0`. The functions `R_i`
generate `C(T)`, so `(6)` forces `Z=T`. Every conjugate is trivial and separability gives
`T in L_n`, proving `(3)`.

## Identity-view corollary: exact affine/non-affine dichotomy `[PROVED]`

Let `C` be an algebraically closed constant field of characteristic zero, let `x` be
hypertranscendental over `C`, and put `F=C<x>`. Let `R in C(z)` be nonconstant. For `n>=1`, define

```text
L_n(R)=C<x^(n),(R(x))^(n)>.
```

Then

```text
L_n(R)=F for every n>=1   iff   R is not affine.            (7)
```

If `R(z)=az+b`, then `L_n(R)=C<x^(n)>`, a proper depth-`n` jet tail. Every rational nonlinearity,
including every genuine projective denominator, has complete reconstruction power when paired
with the original horizon.

## Lemma 1: principal symbols recover the ordinary derivative

Assume `R` is non-affine and fix `n>=1`. Put `L=L_n(R)`. Differential Luroth gives `u in F` such
that `L=C<u>`. Let `m=ord_x(u)`. Both observed generators have exact differential order `n` in
`x`, and the coefficient of `x_n` in `delta^n R(x)` is `R'(x)`. Differential-order additivity
therefore gives rational differential expressions

```text
A(u,...,u_r)=x_n,
B(u,...,u_r)=delta^n R(x),
r=n-m.
```

Taking the formal partial derivative with respect to the highest jet `x_n` gives

```text
1     = A_(u_r) u_(x_m),
R'(x) = B_(u_r) u_(x_m).                                  (2)
```

The first line is nonzero, so division in `(2)` yields

```text
R'(x)=B_(u_r)/A_(u_r) in L.                                (3)
```

This is the nonlinear information injected by the second horizon. For an affine `R`, `(3)` is
only a constant and no missing jet is recovered.

## Lemma 2: one rational shadow plus one positive jet separates every branch

Let `r in C(z)` be any nonconstant rational function. Then, for every `n>=1`,

```text
C<r(x),x_n>=C<x>.                                          (4)
```

Write `K=C<r(x),x_n>`. Since `r(x) in K`, the element `x` is algebraic over `K`. Let `z` be a
`K`-conjugate of `x` in an algebraic differential closure. Derivations extend uniquely across
separable algebraic extensions, so the conjugacy commutes with `delta` and gives

```text
r(z)=r(x),
delta^n z=x_n.                                             (5)
```

The first equation makes `z` algebraic over `C(x)`. In the algebraic function field `C(x,z)`,
the coefficient of the free highest jet `x_n` in `delta^n z` is the algebraic derivative
`dz/dx`; all remaining terms use only `x_1,...,x_(n-1)`. Algebraic independence of the HT jets
and the second equation in `(5)` force

```text
dz/dx=1.                                                   (6)
```

Hence `z-x` is a constant of the algebraic function field. Algebraic closedness of `C` gives
`z=x+c` for some `c in C`. Now `(5)` says

```text
r(x+c)=r(x).                                               (7)
```

A nonconstant rational function in characteristic zero has no nonzero additive period: a
nonconstant polynomial cannot be periodic by its leading term, while a rational function with a
pole would acquire the infinite pole orbit `a+Zc`. Thus `c=0`, every conjugate equals `x`, and the
separable minimal polynomial of `x` over `K` has degree one. This proves `(4)`.

## Proof of the classification

If `R` is non-affine, `R'` is nonconstant. Lemma 1 puts `R'(x)` in `L_n(R)`, and Lemma 2 with
`r=R'` puts `x` in `L_n(R)`. Differential closure then gives `F<=L_n(R)`; the reverse inclusion
is immediate.

If `R(z)=az+b`, positive derivatives satisfy

```text
delta^k R(x)=a x_k,   k>=1.
```

Hence `L_n(R)=C<x_n>`. The strict HT jet flag proves this is proper in `F`. This proves `(7)`.

## Projective all-depth corollary

For `p in P^1(C)`, choose `M_p in PGL_2(C)` carrying `p` to infinity and put

```text
H_(p,n)=C((M_p x)^(n),(M_p x)^(n+1),...).                 (8)
```

The field is choice-independent by constant-affine jet-tail invariance. If `p!=q`, the transition
`M_q M_p^(-1)` has a genuine denominator and is therefore non-affine. Applying `(7)` gives

```text
H_(p,n) H_(q,n)=F                                         (9)
```

for every `n>=1`. Each individual horizon omits `n` independent jets; any two distinct projective
ends reconstruct all of them at every finite depth.

## Novelty and significance attack

- Differential Luroth, differential-order additivity, unique extension of derivations across
  separable algebraic fields, and ordinary no-periodicity of rational functions are classical.
- Exact-statement searches found nonlinear-system observability theory and differential-Luroth
  algorithms, but no theorem reconstructing the normalization of a rational observation curve
  from arbitrary common-order derivative horizons, or identifying affine-line images as the exact
  failures uniformly in `n`.
- The theorem is not a rank condition, a local inverse-function statement, or a renamed Schwarzian
  invariant. It is a global equality of differential function fields at arbitrary derivative
  depth, with the residual finite cover identified exactly by ordinary Luroth normalization.
- The principal-symbol step alone is insufficient: `(3)` generally makes `x` only algebraic.
  Lemma 2 is the branch-separation mechanism that upgrades algebraic observability to exact
  rational reconstruction.
- The theorem would fail for a merely differentially algebraic source because highest jets need
  not be free. Hypertranscendence is the load-bearing hypothesis, not decoration.

## Physical interpretation

`[CONJECTURAL INTERPRETATION]` Affine curvature of the joint observation image is the exact static
information threshold. A nonlinear observation curve is reconstructed together with its complete
differential function field at every depth, while an affine-line image remains one proper horizon.
The invisible information is not vague: it is precisely any finite algebraic cover above the
normalized observation curve. This is an exact algebraic analogue of depth-independent holographic
normalization, not a quantum or black-hole assertion.

## RH impact audit

`[FORMULATION CONSTRAINT; NOT RH PROGRESS]` An RH construction based on an HT source cannot claim
that deep derivative erasure is intrinsic when its rational observations trace a nonlinear curve:
their horizons reconstruct that curve's full differential function field. Any residual ambiguity
must be a genuine common algebraic cover. No canonical nonlinear source-pure zeta observation curve
is known, and the theorem does not constrain zeros or imply a critical-line statement.

## Lean realization and exact boundary

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonComplementarity.lean` formalizes:

```text
projectiveInversion_twoJet_reconstruction
hypertranscendentalOver_differentialJet_ne_zero
hypertranscendentalOver_sup_firstJetTail_inv_eq_top
mem_of_pow_mem_and_nonzero_differentialJet_mem_of_cast_ne_zero
mem_of_pow_mem_and_nonzero_differentialJet_mem
mem_of_sq_mem_and_nonzero_differentialJet_mem
```

`formal/GaloisForLFunctions/HTGeometry/JetFieldAlgebraicBranchRigidity.lean`,
`formal/GaloisForLFunctions/HTGeometry/RatFuncPositiveJetBranchSeparation.lean`, and
`formal/GaloisForLFunctions/HTGeometry/RatFuncPositiveJetFieldReconstruction.lean` formalize the
exact algebraic-branch and field-equality content of Lemma 2:

```text
differentialJet_eq_base_of_isAlgebraic
algebraic_branch_eq_of_ratFunc_and_positive_jet
isAlgebraic_freeGenerator_over_rational_positiveJet_observation
adjoin_freeGenerator_over_rational_positiveJet_observation_eq_top
rational_positiveJet_observation_eq_top
```

The inversion and horizon declarations certify the full depth-one inversion case. The jet theorem
certifies, uniformly at every order, that every differential jet of an HT scalar is nonzero; the
horizon proofs reuse it instead of duplicating the order-zero and order-one arguments. The latter
two declarations certify the power branch-collapse mechanism at arbitrary depth: in any
derivation-closed intermediate field, visibility of any positive power `x^k` and one nonzero jet
forces visibility of `x`.  The formal core is stronger and characteristic-free: it requires only
that the image of `k` in the coefficient field be nonzero; the original characteristic-zero API
is retained as a corollary.

The exact Lemma 2 proof is unconditional: it constructs the finite simple extension generated by
the free coordinate, transports the unique derivation to a finite normal closure, proves every
embedding fixes the coordinate by positive-jet branch separation, and deduces degree one from the
embedding cardinality. Direct source checks and targeted module builds pass. Axiom reports for all
new capstones contain only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The uniform principal-symbol/Luroth theorem `(2)--(3)` and resulting affine/non-affine main
classification remain to be formalized. No axiom or opaque placeholder is added.

## Gates

- [x] 0 -> 1 in-progress: exact classification, source-pure proof, parent collision, and formal
  boundary identified
- [x] 1 -> 2 fully-proven: highest-jet coefficient and algebraic-branch arguments audited
- [x] all-order nonvanishing of every HT differential jet formalized and reused
- [ ] 2 -> 3 formalized: depth-one inversion, arbitrary-depth rational branch separation, and
  exact Lemma 2 field reconstruction formalized; general Luroth principal symbol and main
  affine/non-affine classification remain
- [ ] 3 -> 4 publication-ready: independent specialist priority audit and standalone exposition

## Log

- 2026-07-15 — inversion all-depth complementarity discovered from the first-horizon projective
  building, then strengthened to the exact affine/non-affine rational classification.

## Primary references checked

- L. D'Alfonso, G. Jeronimo, P. Solerno, *Effective Differential Luroth's Theorem*, Journal of
  Algebra 406 (2014), for differential Luroth and exact-order generator control.
- Classical Hermann--Krener and modern algebraic observability literature, for the adjacent but
  flow-based local/global observability setting; no matching free-HT field classification found.

## 2026-08-14 — the parabolic half of the translation-stabilizer step

`formal/GaloisForLFunctions/HTGeometry/TranslationShiftAffineRigidity.lean`, unconditional and
axiom-clean, wired into the `HTGeometry` umbrella.

The proof's step `(6)` says the translation vector `c` stabilizes the observation curve, and the
card argues that a nonlinear curve has trivial translation stabilizer through a one-dimensional
additive subgroup.  On the normalization that argument becomes a statement about a Möbius
reparametrization `M` of the coordinate with `Rᵢ ∘ M = Rᵢ + cᵢ`, and only two cases occur: `M` is
parabolic, or `M` has two fixed points.  The parabolic case is now closed:

**`HTGeometry.shift_const_quotient_affine`** — for a coprime representation `p/q`, the relation
`p(X+1)·q = (p + c·q)·q(X+1)` forces `q` to be a nonzero constant `b` and `p = c·b·X + a`.  That
is: the only rational solutions of `R(z+1) = R(z) + c` are the affine `R(z) = cz + d`, so every
`Rᵢ` is affine in the parabolic coordinate and the observation curve is a line.

The mechanism is a one-line reduction rather than a new estimate: subtracting `c·z` turns the
constant shift defect into shift periodicity, and the corpus already owned
`shift_periodic_quotient_constant` — a shift-periodic rational function is constant.  What remains
of the translation-stabilizer step is the two-fixed-point case, where `M(z) = λz` and the same
relation forces `c = 0`.

### The two-fixed-point half, and the dichotomy closed

`formal/GaloisForLFunctions/HTGeometry/ScalingShiftRigidity.lean`, unconditional and axiom-clean.

**`HTGeometry.scale_const_quotient_eq_zero`** — for a coprime representation `p/q` and `λ ≠ 0`,
the relation `p(λX)·q = (p + c·q)·q(λX)` forces `c = 0`.  So a Möbius reparametrization with two
fixed points cannot produce a nonzero constant shift at all.

The proof is entirely algebraic.  The scaling substitution is a ring automorphism, so it preserves
coprimality; hence the scaled denominator divides the denominator, they have equal degree, and they
differ by a unit `u`.  Cancelling leaves `u·p(λX) = p + c·q`, and evaluating at the fixed point `0`
gives `u·p(0) = p(0) + c·q(0)` together with `q(0) = u·q(0)`.  If `q(0) ≠ 0` then `u = 1` and
`c·q(0) = 0`.  If `q(0) = 0` then coprimality gives `p(0) ≠ 0`, again `u = 1`, and now `q` is
scaling invariant — so `λ^{deg q} = 1` by comparing leading coefficients.  Iterating
`p(λX) = p + c·q` through that period returns `p.comp X = p` while accumulating `deg q · c · q`,
which forces `c = 0` in characteristic zero.

**The translation-stabilizer step `(6)` is therefore complete**: with
`shift_const_quotient_affine` for the parabolic case, a nonzero translation of the observation
curve realized on its normalization forces every `Rᵢ` to be affine, i.e. the curve is a line — and
in the non-affine branch the translation vector is zero, which is exactly what the card's `(6)`
needs to conclude `Rᵢ(Z) = Rᵢ(T)` and hence `Z = T`.

## 2026-08-16 — Lemma 1 in full generality, and the identity-view dichotomy

`formal/GaloisForLFunctions/HTGeometry/JetPrincipalSymbolExtraction.lean`, unconditional and
axiom-clean, wired into the `HTGeometry` umbrella.

**`HTGeometry.exists_mem_pd_ratio`** is the general Lüroth principal-symbol theorem the card asked
for.  Let `K` be a derivation-closed intermediate field of the free scalar differential rational
field, strictly above the constants, and let `v, w ∈ K` have the same exact scalar differential
order `n` with `∂_{x_n} v ≠ 0`.  Then `∂_{x_n} w / ∂_{x_n} v ∈ K`.

The mechanism is exactly the card's `(2)–(3)`, but organized so that no formal partial derivative
with respect to a Lüroth generator has to be constructed.  Differential Lüroth writes `K = C⟨u⟩`;
if `u` has exact order `r`, order additivity forces `v` and `w` to have order `s = n − r` over `u`,
so both lie in `C(u, …, u^{(s)})`.  Every jet `u^{(i)}` with `i < s` has `x`-order below `n` and is
therefore killed by `∂_{x_n}`.  A single adjoin induction then shows that `∂_{x_n}` maps that whole
subfield into `C(u, …, u^{(s)}) · t` for the one element `t = ∂_{x_n} u^{(s)}`, and the two
multipliers divide.

Supporting theorems in the same module:

```text
pd_differentialJet_top          -- principal symbols are unchanged by differentiation
exists_mem_mul_of_mem_adjoin    -- one free direction propagates through an adjoined field
pd_eq_zero_of_mem_jetObservableField
```

**The identity-view corollary `(7)` is closed.**

```text
differentialAdjoin_jets_eq_top_of_pd_notMem_bot
exists_affine_of_pd_zero_ratFuncEval_mem_bot
differentialAdjoin_jets_ne_top_of_affine
differentialAdjoin_jets_eq_top_iff
```

`differentialAdjoin_jets_eq_top_iff` is the exact dichotomy: for a rational view `r` of the free
generator and every `n ≥ 1`,

```text
C⟨x^{(n)}, (r(x))^{(n)}⟩ = C⟨x⟩   iff   r is not affine.
```

The forward half combines the extraction theorem with the already-formalized Lemma 2
(`rational_positiveJet_observation_eq_top`): extraction puts `r'(x)` in the field, and Lemma 2 then
puts `x` in it.  Nonaffineness enters through the constant-kernel theorem: if `∂_{x_0}(r(x))` were
constant then `r(x) − a x` would have every partial derivative zero, hence be constant, so `r`
would be affine.  The affine half is the jet-flag strictness.

`#print axioms` on every capstone returns only `propext`, `Classical.choice`, `Quot.sound`.

### What remains

The general `m`-view Main theorem — the normalization of the observation curve — is not yet
formalized.  Its route is now short, because the extraction theorem applies to each pair
`(δ^n R_1(y), δ^n R_i(y))` and produces the slope ratios `q_i = R_i'(y)/R_1'(y)` inside `L_n`, and
because differential order additivity forces the Lüroth generator of `L_n` to have order zero as
soon as one nonconstant order-zero observable lies in `L_n`.  Writing `L_n = C⟨u⟩` with `u ∈ C(y)`,
extraction gives `R_i'(y)/u'(y) ∈ C(u)`.  Then every `C(u)`-embedding `σ` of `C(y)` commutes with
the unique extension of the derivation and fixes `R_i'(y)/u'(y)`, so `σ(R_i(y)) − R_i(y)` is an
algebraic differential constant, hence a base constant `c_i`; iterating `σ` to its order forces
`c_i = 0` in characteristic zero.  Every embedding therefore fixes each `R_i(y)`, so
`C(y) = C(R_1(y), …, R_m(y)) ⊆ C(u)` and `L_n = C⟨y⟩`.  The translation-stabilizer modules
`TranslationShiftAffineRigidity.lean` and `ScalingShiftRigidity.lean` are no longer needed for this
route; the finite-order argument replaces them.
