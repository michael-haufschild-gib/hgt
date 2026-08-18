# Closed-range transgression and global formation properness law

- **ID:** ULF-LHSM-4
- **Stage:** 2-fully-proven
- **Type:** FOURTH-ORGAN PREDICTION / TOPOLOGICAL FORMATION THEOREM
- **Statement:** For composable closed-range Hilbert laws, the composite has closed range exactly
  when the law-history transgression has closed range.  A finite history is globally proper at
  every prefix exactly when every prefix transgression is strict.  Terminal closedness alone can
  hide an earlier loss of properness.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [HILBERT CLOSED RANGE]
  [TRANSGRESSION STRICTNESS] [GLOBAL PREFIX PROPERNESS] [SHARP COUNTERMODEL]
  [LEAN REQUIRED] [NOT RH]

## 1. Setup

Let `X,Y,Z` be Hilbert spaces and let

\[
 X\xrightarrow fY\xrightarrow gZ
 \tag{CRP.1}
\]

be bounded linear maps.  Assume

\[
 M:=\operatorname{ran}f
 \quad\text{and}\quad
 \operatorname{ran}g
 \quad\text{are closed}.
 \tag{CRP.2}
\]

Put `N=ker g`.  Because `M` is closed, the cokernel `Y/M` is a Hilbert quotient.  The local
law-history differential is the bounded map

\[
 \delta_{f,g}:N\longrightarrow Y/M,
 \qquad n\longmapsto[n].
 \tag{CRP.3}
\]

Its range is

\[
 \operatorname{ran}\delta_{f,g}=(M+N)/M.
 \tag{CRP.4}
\]

## 2. Quotient strictness lemma

### Lemma 2.1

Let `H` be a Hilbert space and let `M,N` be closed subspaces.  For the quotient map
`pi_M:H->H/M`,

\[
 \boxed{
 \pi_M(N)\text{ is closed in }H/M
 \Longleftrightarrow
 M+N\text{ is closed in }H.}
 \tag{CRP.5}
\]

### Proof

The preimage of `pi_M(N)` is exactly `M+N`.  If `pi_M(N)` is closed, continuity of `pi_M` makes
its preimage closed.

Conversely, suppose `M+N` is closed.  The quotient `(M+N)/M` is then a Banach space.  Its canonical
inclusion into `H/M` is an isometry for the quotient norm and therefore has closed range.  That
range is `pi_M(N)`. `square`

Equivalently, the quotient map is a closed map on every saturated closed subspace containing `M`.

## 3. Product strictness lemma

### Lemma 3.1

Under `(CRP.2)`,

\[
 \boxed{
 \operatorname{ran}(gf)\text{ is closed}
 \Longleftrightarrow
 M+N\text{ is closed}.}
 \tag{CRP.6}
\]

### Proof

Because `ran g` is closed, the induced map

\[
 \bar g:Y/N\longrightarrow\operatorname{ran}g,
 \qquad [y]\longmapsto gy
 \tag{CRP.7}
\]

is a continuous linear bijection between Banach spaces.  The open mapping theorem makes it a
topological isomorphism.

The image of `M` in `Y/N` is `(M+N)/N`, and `bar g` sends it exactly to `g(M)=ran(gf)`.  Therefore
`ran(gf)` is closed in `ran g` exactly when `(M+N)/N` is closed in `Y/N`.  Since `ran g` is closed
in `Z`, closedness in `ran g` is the same as closedness in `Z`.  Lemma 2.1 with `M,N` interchanged
identifies the remaining condition with closedness of `M+N` in `Y`. `square`

## 4. Closed-range transgression theorem

### Theorem 4.1

Under `(CRP.2)`, the following are equivalent:

\[
 \boxed{
 \begin{aligned}
 &(1)\quad \operatorname{ran}(gf)\text{ is closed};\\
 &(2)\quad \operatorname{ran}f+\ker g\text{ is closed};\\
 &(3)\quad \operatorname{ran}\delta_{f,g}\text{ is closed}.
 \end{aligned}}
 \tag{CRP.8}
\]

### Proof

Lemma 3.1 proves `(1) iff (2)`.  Equation `(CRP.4)` and Lemma 2.1 prove `(2) iff (3)`. `square`

This is the promised fourth-organ prediction from ULF-LHSM-3.  A completion failure in a composite
law is not an untyped global pathology.  It is exactly non-strictness of the transgression that
mediates later erasure against earlier nonattainment.

## 5. Angle and reduced-minimum-modulus form

Let

\[
 L=M\cap N.
\]

On `N`, the kernel of `delta_(f,g)` is `L`.  Its reduced minimum modulus is

\[
 \gamma(\delta_{f,g})
 :=\inf\{\operatorname{dist}(n,M):
 n\in N\cap L^\perp,\ \|n\|=1\}.
 \tag{CRP.9}
\]

This is the sine of the Friedrichs angle between `M` and `N`.  The closed-range theorem gives

\[
 \boxed{
 \operatorname{ran}(gf)\text{ closed}
 \Longleftrightarrow
 \gamma(\delta_{f,g})>0.}
 \tag{CRP.10}
\]

Thus the first properness scalar is not determinant or index.  It is the transgression gap between
attained directions and later-invisible directions.

## 6. Finite-history global properness

Let

\[
 V_0\xrightarrow{a_1}V_1\xrightarrow{a_2}\cdots
 \xrightarrow{a_m}V_m
 \tag{CRP.11}
\]

be bounded maps of Hilbert spaces.  Put

\[
 A_j:=a_j\cdots a_1:V_0\longrightarrow V_j,
 \qquad A_0=\operatorname{id}_{V_0}.
 \tag{CRP.12}
\]

Assume every local `a_j` has closed range.

### Definition 6.1 -- global formation properness

The history is **globally formation-proper** when every prefix `A_j` has closed range.

For `j>=2`, whenever `A_(j-1)` has closed range, define the prefix transgression

\[
 \Delta_j:ker a_j\longrightarrow
 V_{j-1}/\operatorname{ran}A_{j-1},
 \qquad y\longmapsto[y].
 \tag{CRP.13}
\]

### Theorem 6.2 -- global properness criterion

The history `(CRP.11)` is globally formation-proper if and only if every prefix transgression
`Delta_j` has closed range.

### Proof

The first prefix `A_1=a_1` has closed range by hypothesis.  Suppose inductively that `A_(j-1)` has
closed range.  Apply Theorem 4.1 to

\[
 V_0\xrightarrow{A_{j-1}}V_{j-1}\xrightarrow{a_j}V_j.
\]

It gives

\[
 \operatorname{ran}A_j\text{ closed}
 \Longleftrightarrow
 \operatorname{ran}\Delta_j\text{ closed}.
\]

Induction proves both directions. `square`

### Corollary 6.3 -- properness energy

The history is globally formation-proper exactly when every prefix transgression has positive
reduced minimum modulus after removing its kernel:

\[
 \boxed{
 \gamma(\Delta_j)>0
 \qquad(2\le j\le m).}
 \tag{CRP.14}
\]

For a cofinal family of finite histories, the uniform strengthening

\[
 \inf_j\gamma(\Delta_j)>0
 \tag{CRP.15}
\]

is the natural global properness gate.  The pointwise theorem does not assert the uniform bound.

## 7. Terminal closedness is not global properness

### Theorem 7.1 -- later erasure countermodel

There exist bounded closed-range maps `f,g` for which `gf` has nonclosed range.  Appending the zero
map produces a three-law history whose total composite has closed range while its middle prefix is
nonclosed.

### Construction and proof

Let `K=ell^2(N)` and let

\[
 T(x_1,x_2,\ldots)=(x_1,x_2/2,x_3/3,\ldots).
 \tag{CRP.16}
\]

Then `T` is bounded, injective, and has dense nonclosed range.  In `H=K direct-sum K`, put

\[
 M=K\oplus0,
 \qquad
 N=\operatorname{graph}T.
 \tag{CRP.17}
\]

Both are closed, but

\[
 M+N=K\oplus\operatorname{ran}T
 \tag{CRP.18}
\]

is nonclosed.  Let `f:K->H` be inclusion onto `M`, and let `g:H->H` be orthogonal projection onto
`N^perp`.  Then `ran f=M`, `ker g=N`, and `ran g=N^perp` are closed.  Theorem 4.1 implies that
`ran(gf)` is nonclosed.

Now append the zero map `h:H->0`.  The total composite `hgf=0` has range `{0}`, hence closed.  The
middle prefix remains nonclosed. `square`

Consequently

\[
 \boxed{
 \text{terminal closedness}\not\Rightarrow
 \text{global formation properness}.}
 \tag{CRP.19}
\]

This is the exact reason a final RH endpoint cannot certify the legitimacy of the history that
produced it.  Properness must be checked through the whole formation process.

## 8. Relation to the obstruction spectral machine

ULF-LHSM-3 derives algebraic pages by taking kernels and cokernels of higher transgressions.
Theorem 4.1 supplies the missing topological law:

```text
algebraic page survives       = nonzero kernel/cokernel
topological page is strict    = transgression range closed
uniform formation is proper   = transgression gap bounded below
```

These are three different conditions.  A class can cancel algebraically while the cancellation
operator has nonclosed range and arbitrarily bad recovery conditioning.

## 9. Hostile boundaries

1. **Closed local ranges are load-bearing.** Without closed `ran f`, `Y/ran f` is non-Hausdorff;
   without closed `ran g`, the induced map `Y/ker g -> ran g` need not be a Banach isomorphism.
2. **Hilbert structure is used for the angle form.** Equivalence `(CRP.8)` has Banach analogues
   under appropriate quotient hypotheses, but `(CRP.9)` uses orthogonality.
3. **No uniform bound follows.** Every finite prefix may be strict while the gaps tend to zero.
4. **Final exactness can hide damage.** The zero-map countermodel proves terminal tests are too
   weak.
5. **No RH premise is produced.** A literal arithmetic history and a source-derived lower bound on
   all transgression gaps remain open.
6. **Classical operator parent.** Closed range of products and Friedrichs-angle criteria are
   established operator theory.  The field contribution is their role as strictness law for the
   law-history differential.

## 10. Literature boundary

- Kamran Sharifi, *The product of operators with closed range in Hilbert C*-modules*,
  <https://arxiv.org/abs/1010.4574>, proves the broader adjointable-module product/sum criterion.
- Standard closed-range and open-mapping theorems supply the Hilbert-space proof above.

No external theorem is used as an unproved premise; the proof is included.

## 11. Lean requirements

Formalization must certify:

1. quotient-image closedness iff the saturated sum is closed;
2. product closedness iff `ran f + ker g` is closed under `(CRP.2)`;
3. transgression closedness equivalence `(CRP.8)`;
4. finite-history induction `(CRP.13)`--`(CRP.14)`;
5. explicit graph/projection countermodel `(CRP.16)`--`(CRP.19)`;
6. no full umbrella build.

No `sorry`, `admit`, new axiom, opaque placeholder, or computation proof is permitted.

