# Finite law-history obstruction spectral machine and joint reconstruction law

- **ID:** ULF-LHSM-3
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM / FUSION THEOREM
- **Statement:** Every finite composable history of linear laws carries canonical higher
  transgressions.  Page `r` transports a defect surviving `r-1` intermediate laws from a later
  kernel to an earlier cokernel.  Kernel and cokernel of that transgression are exactly the next
  page.  The stable page is the associated graded of the total kernel and total cokernel.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [GENERAL FINITE HISTORY]
  [HIGHER TRANSGRESSION] [EXACT PAGE DERIVATION] [JOINT RECONSTRUCTION]
  [INDEX CONSERVATION] [CORE LEAN-CERTIFIED] [GENERAL PAGE PACKAGING LEAN REQUIRED]
  [UMBRELLA-WIRED] [UMBRELLA-NOT-BUILT BY POLICY] [NOT RH]

## 1. Why another mechanism is required

ULF-LHSM-1 constructs the future-tail survival filtration.  ULF-LHSM-2 constructs the local
transgression

\[
 \ker g\longrightarrow\operatorname{coker}f,
 \qquad y\longmapsto[y].
\]

Those results do not yet explain how a failure invisible at one adjacent pair can reappear after
several later laws.  That missing operation is a higher differential, not another carrier.

For three laws

\[
 X\xrightarrow fY\xrightarrow gZ\xrightarrow hW,
\]

take `z in ker h` whose class vanishes under the adjacent transgression.  Then `z=g y` for some
`y`.  The next obstruction is

\[
 [y]\in Y/(\operatorname{im}f+\ker g).
\]

Changing the lift `y` changes it by `ker g`, so this class is canonical.  This is the first
genuinely higher law-history operation.

## 2. Interval notation

Let `k` be a field and let

\[
 V_0\xrightarrow{a_1}V_1\xrightarrow{a_2}\cdots
 \xrightarrow{a_m}V_m
 \tag{LHS.1}
\]

be a finite history of linear maps.  For `0<=i<=j<=m`, define the interval transport

\[
 A_{i,j}:=a_j a_{j-1}\cdots a_{i+1}:V_i\longrightarrow V_j,
 \qquad A_{i,i}=\operatorname{id}_{V_i}.
 \tag{LHS.2}
\]

Composition is strict:

\[
 A_{j,\ell}A_{i,j}=A_{i,\ell}.
 \tag{LHS.3}
\]

## 3. The two rows on page `r`

For `1<=j<=m` and `1<=r<=j`, define the kernel survivor

\[
 K_j^{(r)}
 :=\ker a_j\cap\operatorname{im}A_{j-r,j-1}
 \subseteq V_{j-1}.
 \tag{LHS.4}
\]

For `1<=i<=m` and `1<=r<=m-i+1`, define the cokernel survivor

\[
 C_i^{(r)}
 :=V_i/\bigl(\operatorname{im}a_i+\ker A_{i,i+r-1}\bigr).
 \tag{LHS.5}
\]

At page one,

\[
 K_j^{(1)}=\ker a_j,
 \qquad
 C_i^{(1)}=\operatorname{coker}a_i.
 \tag{LHS.6}
\]

Thus the initial page contains every local erasure and every local nonattainment, without deciding
in advance which ones survive the full history.

## 4. Higher law-history differential

Fix `r>=1` and `i` with `i+r<=m`.  Put

\[
 P=A_{i,i+r-1}:V_i\longrightarrow V_{i+r-1}.
\]

An element `z in K_(i+r)^(r)` belongs to `im P`.  Choose `y in V_i` with `Py=z` and define

\[
 \boxed{
 d_i^{(r)}(z)
 :=[y]\in C_i^{(r)}.}
 \tag{LHS.7}
\]

### Theorem 4.1 -- well-defined higher transgression

The value in `(LHS.7)` is independent of the lift `y`, is linear in `z`, and is canonical from the
history `(LHS.1)`.

### Proof

If `Py=Py'`, then `y-y' in ker P`.  The denominator of `C_i^(r)` contains `ker P`, so `[y]=[y']`.
Additivity and scalar compatibility follow by choosing sums and scalar multiples of lifts.  No
section of `P` is selected.  Equivalently, the first isomorphism theorem gives the canonical
equivalence

\[
 V_i/\ker P\simeq\operatorname{im}P,
\]

and `(LHS.7)` is its inverse restricted to `K_(i+r)^(r)`, followed by the quotient by
`im a_i`. `square`

For `r=1`, `P=id`, and `(LHS.7)` is exactly ULF-LHSM-2:

\[
 d_i^{(1)}:\ker a_{i+1}\to\operatorname{coker}a_i,
 \qquad z\mapsto[z].
 \tag{LHS.8}
\]

For three maps, the new page-two differential is

\[
 d_1^{(2)}:
 \ker h\cap\operatorname{im}g
 \longrightarrow
 Y/(\operatorname{im}f+\ker g),
 \qquad
 g y\longmapsto[y].
 \tag{LHS.9}
\]

## 5. Exact page derivation

### Theorem 5.1 -- kernel is the next kernel survivor

For every admissible `i,r`,

\[
 \boxed{\ker d_i^{(r)}=K_{i+r}^{(r+1)}.}
 \tag{LHS.10}
\]

Here the right side is viewed as a subspace of `K_(i+r)^(r)`.

### Proof

Take `z=Py` in the domain.  Its image is zero exactly when

\[
 y\in\operatorname{im}a_i+\ker P.
\]

Applying `P`, this is equivalent to

\[
 z\in\operatorname{im}(Pa_i)
 =\operatorname{im}A_{i-1,i+r-1}.
\]

The domain already imposes `z in ker a_(i+r)`.  Hence

\[
 z\in\ker a_{i+r}\cap\operatorname{im}A_{i-1,i+r-1}
 =K_{i+r}^{(r+1)}.
\]

The converse is the same calculation in reverse. `square`

### Theorem 5.2 -- cokernel is the next cokernel survivor

For every admissible `i,r`, there is a canonical equivalence

\[
 \boxed{\operatorname{coker}d_i^{(r)}\simeq C_i^{(r+1)}.}
 \tag{LHS.11}
\]

### Proof

A lift `y in V_i` represents an element in the image of `d_i^(r)` exactly when

\[
 Py\in\ker a_{i+r},
\]

or equivalently

\[
 y\in\ker(a_{i+r}P)=\ker A_{i,i+r}.
\]

Therefore quotienting `C_i^(r)` by the image of `d_i^(r)` gives

\[
 \frac{V_i}
 {\operatorname{im}a_i+\ker P+\ker A_{i,i+r}}.
\]

Because `ker P` is contained in `ker A_(i,i+r)`, this is

\[
 V_i/(\operatorname{im}a_i+\ker A_{i,i+r})=C_i^{(r+1)}.
\]

The equivalence is induced by the identity on `V_i`, so it is canonical. `square`

Equations `(LHS.10)` and `(LHS.11)` are the formation law:

\[
 \boxed{
 \text{next page}=
 \bigl(\ker(\text{current transgression}),
       \operatorname{coker}(\text{current transgression})\bigr).}
 \tag{LHS.12}
\]

No new obstruction is declared.  The next one is forced by failure to cancel on the current page.

## 6. Spectral-machine packaging

On page `r`, take the direct sum of all current kernel and cokernel survivors.  Terms that have
already reached a boundary remain unchanged.  Define `d_r` as the direct sum of the maps
`d_i^(r)` from the kernel row to the cokernel row and zero on the cokernel row.

Then

\[
 d_r^2=0
 \tag{LHS.13}
\]

because the differential vanishes on its entire target row.  Theorems 5.1 and 5.2 give a canonical
page equivalence

\[
 \boxed{E_{r+1}\simeq H(E_r,d_r).}
 \tag{LHS.14}
\]

The machine terminates after at most `m` pages.  This is a bounded two-row spectral machine.  It
may be realized as the homology spectral sequence of the octahedral filtration of the two-term
mapping cone of `A_(0,m)`, but the construction and proof above require no derived category.

## 7. Stable page reconstructs the total kernel

Let

\[
 H_j:=\ker A_{0,j}\subseteq V_0,
 \qquad H_0=0.
 \tag{LHS.15}
\]

Then

\[
 0=H_0\subseteq H_1\subseteq\cdots\subseteq H_m
 =\ker A_{0,m}.
 \tag{LHS.16}
\]

### Theorem 7.1 -- kernel reconstruction

For `1<=j<=m`, interval transport induces a canonical equivalence

\[
 \boxed{H_j/H_{j-1}\simeq K_j^{(j)}.}
 \tag{LHS.17}
\]

### Proof

Restrict `A_(0,j-1)` to `H_j`.  Its image is

\[
 \ker a_j\cap\operatorname{im}A_{0,j-1}=K_j^{(j)}.
\]

Its kernel is exactly `H_(j-1)`.  Apply the first isomorphism theorem. `square`

Thus the stable kernel row is not merely dimension data.  It is the associated graded of the
canonical total-kernel filtration.

## 8. Stable page reconstructs the total cokernel

Let

\[
 Q:=V_m/\operatorname{im}A_{0,m}
\]

and let `pi:V_m->Q` be the quotient.  Put

\[
 F_i:=\pi(\operatorname{im}A_{i,m}),
 \qquad 0\le i\le m.
 \tag{LHS.18}
\]

Then

\[
 0=F_0\subseteq F_1\subseteq\cdots\subseteq F_m=Q.
 \tag{LHS.19}
\]

### Theorem 8.1 -- cokernel reconstruction

For `1<=i<=m`, future-tail transport induces a canonical equivalence

\[
 \boxed{F_i/F_{i-1}\simeq C_i^{(m-i+1)}.}
 \tag{LHS.20}
\]

### Proof

This is the survival-grade theorem of ULF-LHSM-1.  Directly, the map

\[
 V_i\longrightarrow F_i/F_{i-1},
 \qquad y\longmapsto[\pi(A_{i,m}y)]
\]

is surjective.  It vanishes exactly when

\[
 A_{i,m}y\in A_{i,m}(\operatorname{im}a_i),
\]

equivalently when `y in im a_i + ker A_(i,m)`.  This is precisely the denominator of
`C_i^(m-i+1)`. `square`

Combining Theorems 7.1 and 8.1 gives joint reconstruction:

\[
 \boxed{
 \operatorname{gr}\ker A_{0,m}
 \simeq\bigoplus_{j=1}^mK_j^{(j)},
 \qquad
 \operatorname{gr}\operatorname{coker}A_{0,m}
 \simeq\bigoplus_{i=1}^mC_i^{(m-i+1)}.}
 \tag{LHS.21}
\]

The direct sums describe associated graded objects.  No canonical splitting of either filtration is
asserted.

## 9. Exact three-law fusion

For `f,g,h`, the page-one differentials are

\[
 \ker g\to\operatorname{coker}f,
 \qquad
 \ker h\to\operatorname{coker}g.
\]

The sole page-two differential is `(LHS.9)`.  Its exact defects are

\[
 \boxed{
 \ker d_1^{(2)}
 =\ker h\cap\operatorname{im}(gf),}
 \tag{LHS.22}
\]

\[
 \boxed{
 \operatorname{coker}d_1^{(2)}
 \simeq Y/(\operatorname{im}f+\ker(hg)).}
 \tag{LHS.23}
\]

Hence one operation simultaneously recovers:

1. the last graded piece of `ker(hgf)`;
2. the first graded piece of `coker(hgf)`;
3. the exact refinement inserted by the middle law;
4. the obstruction missed by every adjacent-pair analysis.

This is the requested genuine fusion law across local transgression, global survival filtration,
and refactorization mechanics.

## 10. Finite index conservation on every page

Assume all spaces are finite-dimensional.  Give kernel-row terms sign `+1` and cokernel-row terms
sign `-1`.  Define

\[
 \chi(E_r)=
 \sum\dim K^{(r)}-\sum\dim C^{(r)},
\]

including stable boundary terms.

### Theorem 10.1 -- pagewise conservation

For every page,

\[
 \boxed{
 \chi(E_{r+1})=\chi(E_r)
 =\dim\ker A_{0,m}-\dim\operatorname{coker}A_{0,m}.}
 \tag{LHS.24}
\]

### Proof

For any finite-dimensional map `d:K->C`, rank-nullity gives

\[
 \dim\ker d-\dim\operatorname{coker}d
 =\dim K-\dim C.
\]

Apply this to every page differential and sum.  At the stable page, `(LHS.21)` turns the signed sum
into the total kernel dimension minus total cokernel dimension. `square`

The invariant is conserved while its carrier migrates.  This is stronger than saying that the
indices of composable maps add: it identifies every intermediate exchange responsible for the
conservation.

## 11. Composite rigidity

### Corollary 11.1

The total law `A_(0,m)` is bijective if and only if every stable survivor vanishes:

\[
 \boxed{
 A_{0,m}\text{ bijective}
 \Longleftrightarrow
 K_j^{(j)}=0\ \forall j
 \text{ and }
 C_i^{(m-i+1)}=0\ \forall i.}
 \tag{LHS.25}
\]

Equivalently, every local kernel/cokernel class must be killed on some finite page and no stable
extension grade may remain.

This changes the selection question.  One need not make every local route obstruction zero.  One
must construct a common history whose higher transgressions cancel every stable survivor.

## 12. Fourth-organ prediction: topology enters at page strictness

The algebraic theorem predicts where a completion or properness obstruction must occur.  For
bounded maps of Hilbert spaces with closed local ranges, the two-law differential

\[
 \ker g\longrightarrow Y/\operatorname{im}f
\]

has closed range exactly when `im f + ker g` is closed.  Under closed range of `g`, this is exactly
the condition that `im(gf)` be closed.  Therefore failure of global formation strictness cannot be
an untyped completion event: it must first appear as nonclosed range of a law-history
transgression.  The higher-page analogue is the next required theorem.

This is a falsifiable prediction in the completion/properness organ and is not used in the algebraic
proof above.

## 13. What this mechanism explains

The field grammar is now:

```text
local kernel/cokernel inventory
        |
        v
adjacent transgression d1
        |
        v
surviving lift obstruction d2
        |
       ...
        |
        v
stable survivors = associated graded total defect
```

- Local no-gos are `E_1` classes, not final verdicts.
- Cancellation is a nonzero differential, not disappearance by rhetoric.
- A route that repeatedly escapes finite observers is a class surviving to later pages.
- Refactorization changes page presentation but not the reconstructed total defect.
- Positivity and topology are additional structures on the same page differentials, not substitute
  geometries.
- A valid RH architecture must supply one pre-zero history and prove that its stable page vanishes
  by source-derived formation/properness.

## 14. Hostile boundaries

1. **Not an RH proof.** No literal arithmetic history with vanishing stable page is constructed.
2. **Not automatic positivity.** The higher differentials are linear and need not be contractions,
   adjointable, or positive.
3. **Not automatically topological.** Algebraic quotients can be non-Hausdorff after completion;
   closed-range hypotheses are separate.
4. **Not a canonical splitting.** Stable terms reconstruct associated graded objects.  Extension
   data remain part of the total law.
5. **Not hypertranscendence.** An unbounded sequence of nonzero pages is a possible realization of
   unbounded prolongation, not an equivalence without a literal comparison functor.
6. **Not recurrence.** A recurrent observer requires an action and a marked lift; neither is
   contained in a bare linear history.
7. **Classical parent machinery.** Exact couples, filtered mapping cones, and the octahedral axiom
   are established homological algebra.  The contribution here is the explicit law-history page
   formula and its fusion of corpus mechanisms, not a priority claim for spectral sequences.

## 15. Literature boundary

- Rui Xiong, *Kernel-Cokernel Sequence for Composition and its Applications*,
  <https://arxiv.org/abs/2001.07528>, contains the two-map parent sequence.
- George Peschke, *Exact couples and their spectral sequences*,
  <https://arxiv.org/abs/2205.10705>, develops stable and unstable `E-infinity` extension laws for
  exact couples.
- Stacks Project, *Spectral sequences: exact couples*,
  <https://stacks.math.columbia.edu/tag/011P>, gives the standard exact-couple derivation.

None is used as a premise in the elementary proof.

## 16. Lean requirements

Formalization must certify:

1. interval transports and strict interval composition;
2. page kernel and cokernel subquotients;
3. well-defined `d_i^(r)` without a selected section;
4. kernel identification `(LHS.10)`;
5. cokernel equivalence `(LHS.11)`;
6. three-law page-two specialization `(LHS.22)`--`(LHS.23)`;
7. stable kernel and cokernel filtrations `(LHS.17)` and `(LHS.20)`;
8. finite pagewise index conservation `(LHS.24)`;
9. composite rigidity `(LHS.25)`.

No `sorry`, `admit`, new axiom, opaque placeholder, or computation proof is permitted.
