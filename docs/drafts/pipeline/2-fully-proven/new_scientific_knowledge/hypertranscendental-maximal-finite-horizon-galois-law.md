# Every hypertranscendental source realizes maximal finite-horizon Galois ambiguity

- **ID:** `hypertranscendental-maximal-finite-horizon-galois-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / DIFFERENTIAL-FUNCTION-FIELD GALOIS LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY PROVISIONAL] [SIGNIFICANT] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-full-symmetric-monodromy`,
  `projective-horizon-finite-jet-page-transition`, `ProjectiveJetHorizon.lean`
- **Lane:** source-pure hypertranscendental geometry; actual-source realization

## Theorem

Let `F` be a characteristic-zero differential field, let `E/F` be a differential field extension,
and let `f in E` be hypertranscendental over `F`.  Fix `m,n>=1`, put `L=m+n`, and use divided jets

```text
x_i=D^i f/i!,       0<=i<L,
X(t)=sum_(i=0)^(L-1)x_i t^i,
Y(t)=X(t)^(-1) mod t^L=sum_(i=0)^(L-1)y_i t^i.             (1)
```

Define the full finite-jet field and the complementary raw/reciprocal horizon field by

```text
K_L=F(x_0,...,x_(L-1)),
H_(m,n)=F(x_m,...,x_(L-1),y_n,...,y_(L-1)).                (2)
```

Then

```text
[K_L:H_(m,n)]=D=choose(m+n,m),                             (3)
Gal(normalClosure(K_L/H_(m,n)))=S_D.                       (4)
```

The extension in `(3)` has no proper intermediate field.  It is solvable by radicals exactly for

```text
(m,n)=(1,1),(1,2),(2,1),(1,3),(3,1).                      (5)
```

In contrast, before adding the reciprocal packet, every omitted low jet is transcendental over
the strict raw tail.  Thus complementary observation produces an exact field-theoretic transition:

```text
raw derivative horizon       : positive transcendence dimension,
critical raw/reciprocal join : finite degree D with full S_D ambiguity.       (6)
```

This is not a generic-specialization statement.  It holds for the actual differential function
field of every hypertranscendental element.

## Proof

### 1. A hypertranscendental finite jet is the universal generic point

Hypertranscendence is precisely algebraic independence of the infinite derivative family over
`F`.  Hence

```text
x_0,...,x_(L-1)                                            (7)
```

are algebraically independent.  Division by the nonzero constants `i!` preserves independence in
characteristic zero.  Evaluation therefore extends from the polynomial algebra to a labelled
field isomorphism

```text
ev_f : F(X_0,...,X_(L-1))  ~=  K_L,
       X_i |-> x_i.                                        (8)
```

Let `Y_i(X)` be the universal rational reciprocal coordinates determined by

```text
(sum X_i t^i)(sum Y_i t^i)=1 mod t^L.                      (9)
```

Because inversion is rational and triangular, `(8)` sends `Y_i(X)` to the actual `y_i` in `(1)`.
It consequently restricts to an isomorphism from the universal critical horizon subfield

```text
F(X_m,...,X_(L-1),Y_n,...,Y_(L-1))                        (10)
```

onto `H_(m,n)`.  No discriminant or denominator degenerates under this transfer: a nonzero
universal rational function cannot vanish at an algebraically independent tuple.  In particular
`x_0 x_m y_n` is nonzero, so the actual function-field point lies on the chart used by the
universal theorem.

### 2. Transport of degree and monodromy

The all-rank projective-horizon monodromy theorem says that the extension of the universal rational
jet field over `(10)` has degree

```text
D=choose(L,m)                                              (11)
```

and geometric normal-closure group `S_D`.  Transport through `(8)` immediately proves `(3)`.

For completeness, there is no constant-field descent gap in `(4)`.  After base change to an
algebraic closure of `F`, the geometric Galois group is already the full permutation group `S_D`.
The arithmetic normal-closure group over `F` contains that geometric group and acts faithfully on
the same `D` embeddings, so it is simultaneously a subgroup and a supergroup of `S_D`.  It is
therefore `S_D`.  Field isomorphism `(8)` transports the normal closure and proves `(4)`.

### 3. Atomicity and radical threshold

Inside the normal closure, `K_L` is the fixed field of a point stabilizer `S_(D-1)`.  This is a
maximal subgroup of `S_D` for every `D>=2`.  Galois correspondence therefore leaves no proper field
strictly between `H_(m,n)` and `K_L`.

The extension is solvable by radicals exactly when `S_D` is solvable, namely `D<=4`.  The positive
pairs with `choose(m+n,m)<=4` are precisely `(5)`; every `m,n>=2` already has `D>=6`.  `QED`

## Algebraic Page transition for an actual source

The finite-jet Page theorem gives the complete transcendence-rank law before and after the critical
join.  For a fixed truncation `N` and

```text
O_(a,b;N)=F(x_a,...,x_N,y_b,...,y_N),                      (12)
```

hypertranscendence makes the formula exact in the actual source field:

```text
trdeg_F O_(a,b;N)
 =min(N+1,(N+1-a)+(N+1-b)).                                (13)
```

At `N=a+b-1`, this card refines the zero hidden transcendence degree in `(13)` to the exact finite
degree and full Galois group `(3)--(4)`.  In the raw tail alone, the previously formalized strict
jet-horizon theorem says each omitted jet is transcendental over all of its strict successors.  The
reciprocal packet therefore does not merely add coordinates: at the critical count it changes the
extension from transcendental to finite, maximally non-normal, and algebraically indecomposable.

## Physical and topological meaning

This gives a source-specific meaning to hypertranscendence without introducing a flow.  A finite
observer who sees complementary raw and reciprocal tails faces `D` locally valid low-jet states.
Continuation through observation-parameter space braids them by every permutation in `S_D`, and
there is no invariant intermediate packet that partially reconstructs the missing state.  The
actual HT source is a marking of one sheet, but that marking is invisible to the universal finite
horizon data.

The appropriate physical description is therefore

```text
hypertranscendental source
  = a generic-point worldline through every finite jet space
  = an actual realization of maximal finite-horizon state scrambling
  = a source marking that cannot be replaced by a universal finite algebraic selector.           (14)
```

Here "worldline" is only a geometric image of the derivation parameter.  The theorem establishes
no time evolution, quantum dynamics, entropy law, black-hole model, or holographic duality.

## Novelty and significance audit

Algebraic independence of finite jets is the defining field-theoretic consequence of
hypertranscendence, and transport of an extension through a generic-point isomorphism is classical.
The new content inherited from the parent theorem is the exact all-rank horizon extension and its
full symmetric normal closure.  The present theorem is the first source-level synthesis: it proves
that this maximal Galois ambiguity is not merely generic ambient geometry but occurs unchanged in
the differential function field of every HT source.

A targeted search found literature on differential transcendence and differential Galois theory,
jet/prolongation spaces, and generic monodromy of sparse systems, but no raw/reciprocal horizon
subfield, binomial extension law, or full-symmetric reconstruction theorem for hypertranscendental
functions.  Relevant adjacent boundaries include Huang--Ng on perturbations of HT functions
([arXiv:2007.10037](https://arxiv.org/abs/2007.10037)), Moosa--Scanlon on jet and prolongation
spaces ([arXiv:0806.4196](https://arxiv.org/abs/0806.4196)), and Esterov on generic monodromy of
sparse systems ([arXiv:1801.08260](https://arxiv.org/abs/1801.08260)).  Novelty remains provisional
pending expert review.

The theorem is significant inside the proposed field because it supplies an exact, all-depth,
actual-source classification law with sharp degree, Galois group, intermediate-field obstruction,
and radical threshold.  It does not by itself meet the user-set Fields-Medal completion bar: its
external consequences and independent expert novelty validation remain open.

The child theorem `projective-horizon-one-step-postcritical-rigidity` uses the maximal-subgroup
statement here to prove an all-or-nothing response law: the first reciprocal coefficient beyond
the critical truncation is a primitive generator of this entire extension, and every later finite
horizon is birational.

## RH impact

The zeta jet-freeness theorem makes `(3)--(6)` unconditional for the differential function field of
Riemann zeta.  Thus no finite algebraic or radical rule can reconstruct its missing low jets from a
critical complementary raw/reciprocal tail once `D>=5`, and there is no intermediate
reconstruction field at any critical depth.

This is a genuine obstruction for finite-jet RH strategies, but not a proof of RH.  The horizon
extension is universal and target-translation blind; it neither identifies Xi zeros nor orients
the critical line.  Any positive RH route must add Euler data, functional-equation reality,
positivity, infinite-depth compatibility, or another source marking not present in the finite
horizon field.

## Lean verification

`HypertranscendentalHorizonFunctionField.lean` formalizes the exact generic-point core:

- every finite jet packet of an HT element is algebraically independent;
- multivariate polynomial evaluation at that packet is injective;
- evaluation extends to an algebra equivalence from the universal rational function field to the
  actual finite-jet field;
- each universal coordinate maps to the corresponding actual derivative.

The critical degree, Schur ramification, and monodromy inputs live in the adjacent projective
horizon modules and paper cards.  A targeted leaf check passes; no full build was run.
