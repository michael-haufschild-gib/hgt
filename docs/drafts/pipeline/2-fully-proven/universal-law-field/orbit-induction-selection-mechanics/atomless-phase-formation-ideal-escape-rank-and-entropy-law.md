# Atomless phase formation, ideal escape, rank growth, and entropy law

- **ID:** ULF-OISM-5
- **Stage:** 2-fully-proven
- **Type:** CONTINUOUS-PHASE / OPERATOR-IDEAL / INFORMATION-FORMATION THEOREM
- **Parent:** ULF-OISM-4
- **Statement:** For an atomless phase representation, conjugation transgression on the
  Hilbert--Schmidt ideal has dense nonclosed range and no resonant Hilbert--Schmidt survivor.
  Cesaro-formed positive trace-class packets converge to zero in Hilbert--Schmidt norm while
  retaining their full trace norm.  In the Haar model a rank-one packet forms an exact normalized
  rank-`N` projection, with operator norm `1/N`, Hilbert--Schmidt norm `1/sqrt(N)`, trace norm one,
  and entropy `log N`.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [ATOMLESS RESONANCE GEOMETRY] [DENSE NONCLOSED TRANSGRESSION]
  [IDEAL-DEPENDENT FORMATION ESCAPE] [EXACT RANK-ENTROPY LAW]
  [FUNCTIONAL-EQUATION NEUTRAL] [LEAN-PENDING] [NOT RH]

## 1. Higher pivot

ULF-OISM-4 shows that finite and countable pure-point phase packets retain a commutant survivor.
That is not the only possible global geometry.  In an atomless phase representation the diagonal
resonance relation has product measure zero.  The Hilbert--Schmidt ideal therefore sees no fixed
survivor at all.

Positivity still conserves trace.  The resulting packet can disappear in the `S_2` topology while
remaining a unit positive state in `S_1`.  This is not a contradiction: trace is not continuous in
Hilbert--Schmidt norm on an infinite-dimensional space.

The theorem below identifies this as an exact formation law rather than a convergence pathology.

## 2. Atomless phase representation

Let `(X,mu)` be a probability space, let

```text
zeta : X -> S^1
```

be measurable, and assume its pushforward

```text
nu = zeta_* mu
```

is atomless.  Put

```text
H = L2(X,mu),
(U f)(x)=zeta(x)f(x).
```

Then `U` is unitary.  On the Hilbert space `S_2(H)` of Hilbert--Schmidt operators define

```text
alpha(T)=U* T U,
delta(T)=T-alpha(T).
```

Use the standard kernel identification

```text
S_2(H) = L2(X x X, mu x mu).
```

If `T_K` has kernel `K(x,y)`, then

\[
 \boxed{
 \alpha(T_K)=T_{\bar\zeta(x)\zeta(y)K(x,y)},
 \qquad
 \delta(T_K)=T_{(1-\bar\zeta(x)\zeta(y))K(x,y)}.}
\tag{AIE.1}
\]

### Lemma 2.1 -- resonance relation has zero product measure

Let

```text
R={(x,y):zeta(x)=zeta(y)}.
```

Then

\[
 \boxed{(\mu\times\mu)(R)=0.}
\tag{AIE.2}
\]

#### Proof

By Tonelli and the definition of pushforward,

\[
 (\mu\times\mu)(R)
 =\int_X\mu\{y:\zeta(y)=\zeta(x)\}\,d\mu(x)
 =\int_{S^1}\nu\{w\}\,d\nu(w)=0,
\]

because every singleton has `nu`-measure zero. QED.

### Theorem 2.2 -- no Hilbert--Schmidt resonant survivor

\[
 \boxed{\ker\delta=\{0\}.}
\tag{AIE.3}
\]

#### Proof

By `(AIE.1)`, a fixed kernel must vanish outside `R`.  Lemma 2.1 says `R` is null, so the kernel is
zero in `L2(X x X)`. QED.

This is the atomless counterpart of the pure-point commutant projection in ULF-OISM-4.  The full
operator commutant is not zero; the statement is that it contains no nonzero Hilbert--Schmidt
operator.

## 3. Dense nonclosed transgression

### Theorem 3.1 -- exact topology of `1-Ad_U`

The range of

```text
delta = 1-Ad_U : S_2(H) -> S_2(H)
```

is dense and not closed.

#### Proof: density

Conjugation by `U` is unitary on `S_2(H)`, so

```text
delta* = 1-alpha^(-1).
```

The fixed spaces of `alpha` and `alpha^(-1)` agree.  Theorem 2.2 therefore gives

```text
ker(delta*)=0.
```

For bounded operators between Hilbert spaces,

```text
closure(ran delta)=(ker delta*)^perp.
```

Hence `ran(delta)` is dense.

#### Proof: nonclosedness

Choose `w` in the support of the nonzero probability measure `nu`.  There are arcs `I_n` about
`w`, of diameter tending to zero, with `nu(I_n)>0`.  Put

```text
E_n=zeta^(-1)(I_n),
K_n=1_(E_n x E_n) / mu(E_n).
```

Then `||K_n||_2=1`.  On `E_n x E_n`,

```text
|1-conj(zeta(x))zeta(y)| <= diam(I_n),
```

so `(AIE.1)` gives

```text
||delta(T_(K_n))||_2 <= diam(I_n) -> 0.
```

Thus the injective operator `delta` is not bounded below.  An injective bounded Hilbert-space
operator with closed range is bounded below.  Therefore the range is not closed. QED.

### Corollary 3.2 -- finite exactness, global failure

Every kernel supported where

```text
|1-conj(zeta(x))zeta(y)| >= epsilon > 0
```

has a Hilbert--Schmidt primitive obtained by division by the multiplier in `(AIE.1)`.  Exhausting
the complement of the resonance relation by such regions gives finite/local exactness and dense
global exactness, but the inverse norms diverge as `epsilon->0`.

This is the continuous-spectrum version of the small-divisor wall in ULF-OISM-4.

## 4. Positive formation escapes the Hilbert--Schmidt ideal topology

For `T in S_2(H)`, define the Cesaro packet

\[
 M_N(T)=\frac1N\sum_{n=0}^{N-1}\alpha^n(T).
\tag{AIE.4}
\]

### Theorem 4.1 -- Hilbert--Schmidt disappearance

For every `T in S_2(H)`,

\[
 \boxed{\|M_N(T)\|_2\longrightarrow0.}
\tag{AIE.5}
\]

#### Proof

The von Neumann mean ergodic theorem says that Cesaro averages of the unitary `alpha` converge in
the Hilbert-space norm to the orthogonal projection onto `ker(1-alpha)`.  Theorem 2.2 identifies
that fixed space with zero. QED.

### Theorem 4.2 -- trace conservation and ideal escape

If `T>=0` is nonzero and trace class, then every `M_N(T)` is positive trace class and

\[
 \boxed{
 \operatorname{tr}M_N(T)=\operatorname{tr}T,
 \qquad
 \|M_N(T)\|_1=\|T\|_1>0,}
\tag{AIE.6}
\]

while `(AIE.5)` still holds.  Consequently `(M_N(T))` has no trace-norm limit.

#### Proof

Unitary conjugation preserves positivity, trace class, trace, and trace norm.  Convex averaging
preserves positivity and trace, and a positive trace-class operator has trace norm equal to its
trace.  This proves `(AIE.6)`.  If `M_N(T)` converged in trace norm, it would converge to the same
limit in Hilbert--Schmidt norm because `||A||_2<=||A||_1`.  Theorem 4.1 forces that limit to be zero,
contradicting the constant positive trace norm. QED.

Thus the same formed packet has two exact observer outcomes:

```text
S_2 observer:  packet -> 0,
S_1 observer:  full positive mass retained, no norm limit.
```

This is a topology/ideal law, not observer error.

## 5. Exact Haar model

Take

```text
X=S^1,       mu=normalized Haar measure,
zeta(z)=z,   H=L2(S^1),
(Uf)(z)=z f(z).
```

Let `v=1` and let

```text
rho=|v><v|
```

be the rank-one pure state.  Put

```text
e_n(z)=z^(-n).
```

The family `(e_n)_(n>=0)` is orthonormal and

```text
alpha^n(rho)=|e_n><e_n|.
```

Let `P_N` be the orthogonal projection onto

```text
span{e_0,...,e_(N-1)}.
```

### Theorem 5.1 -- exact rank/norm/entropy formation

\[
 \boxed{M_N(\rho)=\frac1N P_N.}
\tag{AIE.7}
\]

Consequently

\[
 \boxed{
 \operatorname{rank}M_N(\rho)=N,
 \quad
 \|M_N(\rho)\|=N^{-1},
 \quad
 \|M_N(\rho)\|_2=N^{-1/2},
 \quad
 \|M_N(\rho)\|_1=1.}
\tag{AIE.8}
\]

Its von Neumann entropy is

\[
 \boxed{S(M_N(\rho))=\log N.}
\tag{AIE.9}
\]

#### Proof

The formula for `alpha^n(rho)` and orthonormality give `(AIE.7)`.  The nonzero eigenvalues of
`P_N/N` are exactly `1/N` with multiplicity `N`.  Rank and all three Schatten norms follow
immediately.  Finally,

\[
 S(P_N/N)=-N(1/N)\log(1/N)=\log N.
\]

QED.

### Corollary 5.2 -- one formation, four incompatible compactness readings

The same positive state sequence has:

1. rank tending to infinity;
2. operator norm tending to zero;
3. Hilbert--Schmidt norm tending to zero;
4. trace norm fixed at one;
5. entropy tending to infinity.

No scalar “size of the defect” can encode all five.  The operator ideal and formation chronology
are constitutive data.

## 6. Functional-equation action is neutral

Define the anti-orientation unitary

```text
(Jf)(z)=f(conj(z)).
```

Then

```text
J U J^(-1)=U*,
```

and `J` sends `e_n(z)=z^(-n)` to `z^n`.  Therefore reflection conjugates `P_N` to the positive
frequency projection and preserves all quantities in `(AIE.8)`--`(AIE.9)`.

More generally, replacing `zeta` by `conj(zeta)` preserves atomlessness of the pushed-forward
measure, the zero-measure resonance relation, density/nonclosedness of transgression, and all
Schatten conclusions.  The functional equation again acts as an information-neutral symmetry of
formation.

If the formed packet is encoded through a common exact-recovery channel, the established recovery
isometry preserves its information separation.  No common encoding repairs the ideal mismatch in
Theorem 4.2.

## 7. Fusion and fourth-organ predictions

The theorem fuses five organs with one mechanism.

| organ | exact output |
|---|---|
| phase dynamics | atomless unitary orbit |
| transgression | dense nonclosed range of `1-Ad_U` |
| positivity | trace-one Cesaro packet |
| topology | `S_2` convergence but `S_1` nonconvergence |
| reconstruction/information | rank `N`, entropy `log N` |

It yields three route-independent predictions.

1. **Ideal-split prediction.** Any literal atomless phase realization with a positive trace-class
   seed must display Hilbert--Schmidt disappearance and trace-class nonconvergence simultaneously.
2. **Rank/entropy prediction.** If the source orbit vectors are orthogonal through aperture `N`,
   the normalized formed state has rank `N` and entropy `log N`.
3. **Topology prediction.** Atomless phase transport forces dense nonclosed transgression before
   any RH specialization; no bounded global primitive can exist in `S_2`.

These are falsifiable.  A proposed source realization that violates one of them is not an
instantiation of this mechanism.

## 8. Hostile boundaries

1. **Classical ingredients.** Kernel models for Hilbert--Schmidt operators, von Neumann mean
   ergodicity, Schatten norms, and entropy of a normalized projection are classical.
2. **Not every continuous spectrum is atomless in the required representation.** The pushforward
   phase measure must be atomless.
3. **Not every positive formation has orthogonal orbit states.** Exact `log N` entropy is the Haar
   calibration.  The general theorem gives ideal escape, not this exact rate.
4. **No RH selector follows.** The theorem supplies a global admission obstruction only after a
   literal source phase representation is constructed.
5. **Trace does not vanish.** `S_2` convergence to zero must never be interpreted as physical
   annihilation without specifying the observer ideal.
6. **The full commutant is not zero.** Only its intersection with `S_2` vanishes.
7. **No isolated novelty claim.** The programme contribution is the coupled mechanism and its exact
   rank/entropy calibration, not the classical components.

The corpus contains finite Lüders pinching, trace-norm dephasing for pure-point number spectra, and
prime-diagonal dephasing laws.  None found in the audit states the atomless dense-nonclosed
transgression together with the `S_2/S_1` escape and exact Haar rank--entropy law.

## 9. Lean status

Paper proof is dependency-closed.  Under the active read-only formal audit, no Lean file is added
or built.  Existing reusable infrastructure includes:

1. `HTGeometry.HilbertSchmidtMatrix` for kernel/operator conversion;
2. `HTGeometry.HilbertClosedRange` for the bounded-below/closed-range criterion;
3. project trace-class and Hilbert--Schmidt ideal bridges;
4. finite pinching and unitary-conjugation laws;
5. the common-recovery functional-equation packet lift.

Missing formal infrastructure is the measurable `L2(X x X)` conjugation multiplier, its atomless
fixed-space proof, and the trace/entropy package for the Haar calibration.  Status is
`[LEAN-PENDING]`.
