# The source-rigged clock domain

- **ID:** `source-rigged-clock-domain`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT DOMAIN/TOPOLOGY CONJECTURE
- **Scientific status:** `[CONJECTURE] [GAMMA RAW-DOMAIN NO-GO LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `hypertranscendental-mackey-corona-field.md`
  - `gamma-periodic-constraint-corona.md`
- **Statement:** A genuine infinite-support source conormal is generally not defined on every raw
  clock sequence. A constrained HT object must therefore contain a source-selected summability
  domain between finite clocks and the raw product, together with its conormal dual and topology.

## 1. Topology-only no-go

Let

```text
J_raw=K^N                                                   (1)
```

be the unrestricted raw clock. A formal infinite conormal with coefficients `lambda_n` suggests

```text
lambda(a)=sum_n lambda_n a_n.                               (2)
```

But `(2)` is not a linear functional on all of `J_raw` unless a summation convention or a
noncanonical algebraic-dual extension is imposed. Refining the topology on `J_raw` cannot make an
undefined series defined.

For Gamma, `lambda_n=1/(n+1)!`. The Lean-formalized raw clock `a_n=(n+1)!` gives

```text
lambda_n a_n=1                                             (3)
```

for every `n`, so the series is not summable. Thus the actual Gamma conormal is not defined on all
raw sequences.

## 2. Positive object: a rigged clock

The source must select a domain

```text
J_fin subset E_x subset J_raw,                              (4)
```

where:

- `J_fin` contains the finite observable packets;
- `E_x` contains the analytic source tangent and framed section;
- every generator of the source conormal module is defined and continuous on `E_x`;
- the clock truncations, source algebra, reflection, and boundary colligation preserve the
  appropriate domain structure.

The actual dual pair is

```text
(E_x, E_x^natural=J_fin^vee+Lambda_x),                      (5)
```

and the Mackey interval belongs to `(5)`, not to all of `J_raw`.

Call `(J_fin,E_x,J_raw,Lambda_x)` the **source-rigged clock**.

## 3. Domain arbitrariness no-go and positive minimality conjecture

Any infinite series has many possible convergence domains. Choosing a weighted sequence space by
hand merely moves the noncanonical-boundary-condition problem into the definition of `E_x`.

There is nevertheless a canonical maximal first domain attached to a conormal module:

```text
E_max(Lambda_x)=intersection_(lambda in Lambda_x) Dom(sum lambda_n a_n).  (5a)
```

For Gamma, Lean now constructs this domain for the cyclic family `D^k(exp(D)-1)` as the submodule

```text
E_Gamma={b | for every k,
  sum_(n>=0) b_(n+k)/(n+1)! is summable}.                  (5b)
```

It is stable under the derivative-tail shift and contains every finite periodic Fourier packet.
Thus `E_Gamma` is the first literal source-rigged clock domain. What remains open is whether the
source-framed analytic object selects all of `E_Gamma` or a canonical complete subdomain and which
topology is minimal.

Lean also constructs the actual cyclic family of conormal functionals

```text
lambda_k(b)=sum_(n>=0) b_(n+k)/(n+1)!                     (5c)
```

on `E_Gamma`, proves `lambda_k(Tb)=lambda_(k+1)(b)`, and proves that every `lambda_k` annihilates
every finite periodic Fourier packet. Thus domain, cyclic source action, and source tangent are now
one formal object; only topology, completion, minimality, and parameterized-Galois identification
remain open.

The finite boundary currents retain this infinite object jointly. Lean proves

```text
lambda_(N-i-1)=v_N(i),                                    (5d)
```

and an extensionality theorem: any coefficient sequence having all restrictions `(5d)` is
`lambda`. Hence no single finite observable detects the conormal, but the oriented inverse family
of finite seams reconstructs it exactly. This is tail-faithful boundary tomography, not a
finite-rank surrogate for the source.

**[CONJECTURE -- SOURCE DOMAIN MINIMALITY]** For every regular source-minimal constrained HT object,
there is a canonical bornological/locally convex domain `E_x` characterized as the smallest
complete source-algebra- and reflection-stable domain which:

1. contains every source-admissible analytic jet;
2. makes the minimal source conormal module `Lambda_x` continuous;
3. supports the global framed constraint section;
4. makes the opposite-variance seam current continuous;
5. is functorial under source equivalence.

**Falsifier.** Two incomparable minimal domains satisfy all five conditions for one source, or the
intersection of all admissible domains fails to support the source section or conormal action.

## 4. Domain/topology complementarity

The earlier strict-refinement theorem remains exact when a nonzero conormal is already defined on
the ambient clock. The Gamma no-go shows that the analytic source problem has two independent
pieces:

```text
domain:   where the conormal pairing exists,
topology: where that pairing is continuous and separated.  (6)
```

Neither determines the other. The unified field must retain both.

## 5. Five obstruction faces sharpened

On a source-rigged clock, the obstruction dictionary becomes:

1. **continuation failure:** `E_x(D)` or `Lambda_x(D)` does not extend to a larger analytic domain;
2. **noncanonical boundary conditions:** multiple incomparable minimal admissible riggings exist;
3. **monodromy:** local riggings glue with nontrivial automorphism;
4. **spectral incompleteness:** the framed realization is incomplete in an admissible topology on
   `E_x`;
5. **positivity failure:** no reflection-stable rigging admits a positive polarization.

This makes continuation and completeness genuinely properties of the same object as the boundary
current, rather than analogies attached afterwards.

## 6. Capacity and thinness

Finite algebraic capacity lives in the projections of `J_raw`. Thin constraint geometry lives in
the finitely generated conormal module on `E_x`. Hypertranscendence can therefore have all finite
projections algebraically free while the source section is globally constrained in `E_x`.

**[CONJECTURE -- RIGGED-CLOCK HT CRITERION]** Within the regular source-minimal constrained class,
hypertranscendence is equivalent to:

- algebraic independence of every finite clock packet;
- no nonzero source conormal extending to a finite-coordinate functional;
- a nonzero finitely generated corona conormal on the canonical proper domain `E_x`;
- tail-faithful boundary transgression on `E_x`.

## 7. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta unified object would require a prime--archimedean rigged
clock domain constructed before its zero divisor. Different RH proof chains could be using
different completions or local riggings of that one source domain. Critical zeros could only be
self-dual degeneracies after the common domain, conormal module, current, and framing are built.

## Gates

- [x] topology-only raw-clock model rejected
- [x] Gamma factorial raw-clock divergence Lean-formalized
- [x] positive source-rigged clock object stated
- [x] maximal cyclic Gamma conormal domain constructed in Lean
- [x] derivative-tail stability Lean-formalized
- [x] containment of every finite periodic Fourier packet Lean-formalized
- [x] cyclic Gamma conormal functionals constructed on the maximal domain
- [x] tail covariance and annihilation of the Fourier source tangent Lean-formalized
- [x] oriented finite boundary family reconstructs the full Gamma conormal Lean-formalized
- [ ] canonical complete source-framed Gamma subdomain identified
- [ ] Gamma conormal continuity on that domain proved
- [ ] source-domain minimality proved for Gamma
- [ ] one non-affine coefficient domain constructed
- [ ] domain functoriality under gauge proved
- [ ] two obstruction categories compared on one rigged clock
