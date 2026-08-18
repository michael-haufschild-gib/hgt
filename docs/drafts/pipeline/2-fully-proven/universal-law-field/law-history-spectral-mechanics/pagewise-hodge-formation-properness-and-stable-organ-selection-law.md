# Pagewise Hodge formation, global properness, and stable-organ selection law

- **ID:** ULF-LHSM-5
- **Stage:** 2 — fully proven on paper
- **Type:** UNIVERSAL LAW-FIELD THEOREM / GLOBAL FORMATION AND SELECTION MECHANISM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [PAGEWISE FORMATION]`
  `[EXACT JOINT RECONSTRUCTION] [GLOBAL PROPERNESS CLASSIFICATION]`
  `[STABLE-ORGAN SELECTION] [FUNCTIONAL-EQUATION NEUTRAL] [NOT RH]`
- **Formal status:** finite diagonal normal form Lean-certified in
  `GaloisForLFunctions.HTGeometry.ConstitutivePagewiseFormationSelection`; abstract orthogonal-flag
  and countable closed-range clauses remain paper-proven.

## 0. Result

The law-history spectral machine identifies how local failures migrate.  This card supplies the
missing global formation law.

Every finite Hilbert realization of the machine splits orthogonally into:

1. a positive and a negative layer dying on each transgression page;
2. one stable harmonic sector surviving every old page.

The page responses jointly reconstruct every dying layer and are blind exactly on the stable
sector.  Their global formation operator has closed range exactly when the page gaps have a
uniform positive lower bound.  Adding another response that factors through the old formation is
information-neutral and cannot improve selection.  A new organ unlocks selection exactly when its
response is bounded below on the stable sector.

Thus the fourth organ is not “another route.”  It has an exact job:

\[
 \boxed{\text{detect the stable history that every earlier page necessarily misses}.}
 \tag{PHF.1}
\]

This is the global formation/properness theorem required by the law-history programme.  It does
not assert that the arithmetic source supplies the terminal response.

## 1. Hodge realization of a law-history machine

Let `K_1` and `C_1` be complex Hilbert spaces.  Fix either a finite page set
`r=1,...,m` or the countable page set `r>=1`.  Suppose there are closed nested subspaces

\[
 K_1\supseteq K_2\supseteq\cdots,
 \qquad
 C_1\supseteq C_2\supseteq\cdots
 \tag{PHF.2}
\]

and bounded maps

\[
 d_r:K_r\longrightarrow C_r
 \tag{PHF.3}
\]

such that

\[
 K_{r+1}=\ker d_r,
 \qquad
 C_{r+1}=C_r\cap(\operatorname{ran}d_r)^\perp,
 \qquad
 \operatorname{ran}d_r\text{ is closed}.
 \tag{PHF.4}
\]

For a finite history put `K_infty=K_(m+1)` and `C_infty=C_(m+1)`.  For a countable history put

\[
 K_\infty=\bigcap_{r\ge1}K_r,
 \qquad
 C_\infty=\bigcap_{r\ge1}C_r.
 \tag{PHF.5}
\]

Define the death layers

\[
 L_r^+=K_r\cap K_{r+1}^\perp,
 \qquad
 L_r^-=\operatorname{ran}d_r
       =C_r\cap C_{r+1}^\perp.
 \tag{PHF.6}
\]

The restriction

\[
 \widehat d_r=d_r|_{L_r^+}:L_r^+\longrightarrow L_r^-
 \tag{PHF.7}
\]

is a bounded bijection.  Its reduced minimum modulus is

\[
 \gamma_r=inf_{0\ne x\in L_r^+}{\|d_rx\|\over\|x\|}>0.
 \tag{PHF.8}
\]

For finite pages the positivity follows from the bounded inverse theorem.  In the countable case
each `gamma_r` is positive separately, but their infimum may vanish.

The hypotheses are exactly the Hilbert realization of the page identities proved in
`finite-law-history-obstruction-spectral-machine-and-joint-reconstruction-law.md`: kernel gives
the next positive survivor, while the orthogonal complement of the image realizes the next
cokernel survivor.

## 2. Exact reconstruction and conservation

### Theorem 2.1 — orthogonal death-page reconstruction

For a finite history,

\[
 \boxed{
 K_1=\left(\bigoplus_{r=1}^m L_r^+\right)\oplus K_\infty,
 \qquad
 C_1=\left(\bigoplus_{r=1}^m L_r^-\right)\oplus C_\infty.}
 \tag{PHF.9}
\]

For a countable history the same statement holds with Hilbert direct sums and closures:

\[
 \boxed{
 K_1=\overline{\bigoplus_{r\ge1}L_r^+}\oplus K_\infty,
 \qquad
 C_1=\overline{\bigoplus_{r\ge1}L_r^-}\oplus C_\infty.}
 \tag{PHF.10}
\]

Consequently, writing `P_r^+`, `P_r^-`, and `P_infty` for the orthogonal projections onto the
displayed layers, every `x=(k,c) in K_1 direct-sum C_1` obeys the exact conservation identity

\[
 \boxed{
 \|x\|^2
 =\|P_\infty x\|^2
  +\sum_r\bigl(\|P_r^+k\|^2+\|P_r^-c\|^2\bigr).}
 \tag{PHF.11}
\]

#### Proof

Because `K_(r+1)` is closed in `K_r`,

\[
 K_r=L_r^+\oplus K_{r+1}.
\]

Because `ran d_r` is closed and `C_(r+1)` is its orthogonal complement in `C_r`,

\[
 C_r=L_r^-\oplus C_{r+1}.
\]

Finite iteration proves `(PHF.9)`.  Countable iteration and the Hilbert projection theorem give
`(PHF.10)`: the orthogonal complement of the closed sum of all death layers is precisely the
intersection of the survivor flag.  Pythagoras gives `(PHF.11)`. `square`

### Corollary 2.2 — information-neutral cancellation

For every page,

\[
 K_r/K_{r+1}\cong L_r^+\xrightarrow[\cong]{\widehat d_r}L_r^-
 \cong C_r/C_{r+1}.
 \tag{PHF.12}
\]

Hence a killed positive class and the negative class it fills carry isomorphic information.  Page
formation transports that information; it does not create or destroy it.  The only information
not paired by an old page is `K_infty direct-sum C_infty`.

This is the linear law-history form of common-recovery information neutrality.  It is stronger
than dimension conservation and does not require choosing bases.

## 3. Pagewise formation operator

Let `U_r:L_r^+->L_r^-` be the partial isometry in the polar decomposition

\[
 \widehat d_r=U_r|\widehat d_r|.
 \tag{PHF.13}
\]

Define the symmetric page response on `L_r^+ direct-sum L_r^-` by

\[
 A_r(x,y)=\bigl(|\widehat d_r|x,
                 |\widehat d_r^*|y\bigr).
 \tag{PHF.14}
\]

It has the same nonzero singular values on the two sides.  Assemble

\[
 \mathcal A=\bigoplus_r A_r
 \tag{PHF.15}
\]

on the orthogonal sum of all death layers and extend it by zero on
`E_infty=K_infty direct-sum C_infty`.

Equivalently, after identifying paired layers by `U_r`, `mathcal A` is the positive diagonal
operator whose page blocks are `|dhat_r|` repeated twice and whose stable block is zero.  This
normal form is intrinsic up to block-unitary conjugacy.

### Theorem 3.1 — exact global kernel and energy

\[
 \boxed{\ker\mathcal A=E_\infty.}
 \tag{PHF.16}
\]

Moreover

\[
 \boxed{
 \|\mathcal A x\|^2
 =\sum_r\left(
   \||\widehat d_r|P_r^+k\|^2
  +\||\widehat d_r^*|P_r^-c\|^2\right).}
 \tag{PHF.17}
\]

Thus every nonstable class has a unique first death page and contributes positive formation work.
Every stable class has zero old-page work.

#### Proof

The block operator on each death layer is injective because `dhat_r` is a bounded bijection.  The
blocks have orthogonal domains and targets.  Therefore the kernel is exactly the omitted stable
block, and Pythagoras gives `(PHF.17)`. `square`

## 4. Global properness classification

### Theorem 4.1 — finite and cofinal page-gap criterion

For a finite history, `mathcal A` has closed range and is bounded below on `E_infty^perp`.  Its
optimal lower bound is

\[
 \gamma_{\rm page}=\min_{1\le r\le m}\gamma_r>0.
 \tag{PHF.18}
\]

For a countable history,

\[
 \boxed{
 \operatorname{ran}\mathcal A\text{ is closed}
 \Longleftrightarrow
 \inf_{r\ge1}\gamma_r>0.}
 \tag{PHF.19}
\]

If `gamma_r_j -> 0`, there are unit vectors supported on successively later death layers whose
formation work tends to zero.  Thus every finite prefix may be strict while global formation is
nonproper.

#### Proof

On `E_infty^perp`, the orthogonal block operator `mathcal A` is bounded below by
`inf_r gamma_r`.  A bounded operator is bounded below on its kernel complement exactly when its
range is closed.  Conversely, if the infimum is zero, choose unit `x_j in L_(r_j)^+` with

\[
 \|d_{r_j}x_j\|\le 2\gamma_{r_j}.
\]

The vectors lie in orthogonal blocks and satisfy `||mathcal A x_j|| -> 0`, so no positive lower
bound and hence no closed range exists. `square`

This theorem is not the earlier one-operator formation theorem repeated.  It identifies the
operator's source-generated blocks as the death pages of a common law history and proves that the
first topological failure is a collapsing transgression gap.

## 5. Stable-organ selection

Let `W` be another Hilbert space and let

\[
 B:E_\infty\longrightarrow W
 \tag{PHF.20}
\]

be a bounded terminal response.  Define the completed formation

\[
 \mathcal A_Bx=\bigl(\mathcal Ax,BP_\infty x\bigr).
 \tag{PHF.21}
\]

### Theorem 5.1 — exact selection and properness gate

\[
 \boxed{\ker\mathcal A_B=\ker B\subseteq E_\infty.}
 \tag{PHF.22}
\]

Therefore:

1. `mathcal A_B` is injective exactly when `B` is injective;
2. in finite dimension, injectivity is equivalent to a positive global formation gap;
3. in the countable Hilbert case, `mathcal A_B` is bounded below exactly when

   \[
   \inf_r\gamma_r>0
   \quad\text{and}\quad
   \beta_B:=\inf_{0\ne s\in E_\infty}{\|Bs\|\over\|s\|}>0;
   \tag{PHF.23}
   \]

4. in that chamber,

   \[
   \boxed{
   \|\mathcal A_Bx\|\ge
   \min\{\inf_r\gamma_r,\beta_B\}\,\|x\|.}
   \tag{PHF.24}
   \]

#### Proof

The two components of `(PHF.21)` live on the orthogonal decomposition
`E_infty^perp direct-sum E_infty`.  The first has kernel `E_infty`; the second acts only on
`E_infty`.  This proves `(PHF.22)`.  Applying the block lower bounds to `(PHF.11)` gives
`(PHF.24)`.  Failure of either lower bound supplies a unit adaptive escape sequence in the
corresponding orthogonal block. `square`

### Theorem 5.2 — redundancy no-go

Let `R:E_1->Z` be another bounded response.  If

\[
 R=S\mathcal A
 \tag{PHF.25}
\]

for some bounded `S`, then

\[
 \boxed{
 R|_{E_\infty}=0,
 \qquad
 \ker(\mathcal A,R)=E_\infty.}
 \tag{PHF.26}
\]

Thus no response reconstructed from old page data can select a stable survivor.  An unlocking
fourth organ must fail to factor through `mathcal A` and must be bounded below on `E_infty`.

#### Proof

`mathcal A` vanishes on `E_infty`, hence so does `R`.  Also `R` vanishes wherever `mathcal A`
does, so adjoining `R` does not change the common kernel. `square`

This is the exact higher-level prediction.  It does not name which route supplies `B`; it says what
any successful organ must mathematically do.

## 6. Scale selection

For `a>1` define the source formation orbit `x_n=a^n x`.  Since `mathcal A_B` is linear,

\[
 \|\mathcal A_Bx_n\|^2=a^{2n}\|\mathcal A_Bx\|^2.
 \tag{PHF.27}
\]

### Corollary 6.1 — bounded-work selector

\[
 \boxed{
 \sup_n\|\mathcal A_B(a^nx)\|<\infty
 \Longleftrightarrow
 x\in\ker B\subseteq E_\infty.}
 \tag{PHF.28}
\]

If the terminal organ is separating, bounded global formation work forces `x=0`.

This isolates the remaining RH obligation without disguising it:

1. construct one literal pre-zero arithmetic history;
2. identify its off-critical defect with a vector `x_rho` in the initial page;
3. prove source normalization gives bounded completed formation work;
4. construct a terminal response `B` from the source and prove `(PHF.23)`;
5. conclude `x_rho=0`, then identify that equation with `Re rho=1/2`.

Only items 1--4 contain new arithmetic work.  No route-local endpoint may be inserted as `B` by
definition.

## 7. Functional-equation neutrality

Suppose a functional-equation action consists of unitaries

\[
 J_r^+:K_r\to K_r',
 \qquad
 J_r^-:C_r\to C_r'
 \tag{PHF.29}
\]

preserving survivor flags and intertwining differentials:

\[
 J_r^-d_r=d_r'J_r^+.
 \tag{PHF.30}
\]

Then it transports every death layer and stable sector unitarily, conjugates `mathcal A` to
`mathcal A'`, and preserves all `gamma_r`.  If `B'J_infty=VB` for a unitary `V`, it also conjugates
`mathcal A_B` to `mathcal A_(B')` and preserves the global gap.

Hence functional equation is information-neutral after common recovery at every page.  It may
exchange positive and negative packets, but it cannot create a terminal detector or improve a
collapsing page gap.

## 8. Three-organ fusion and fourth-organ prediction

The theorem fuses, without identifying, three structurally different universal-law organs.

1. **Law-history transgression:** `d_r` determines which local failures die and which survive.
2. **Formation Laplacian/properness:** the polar blocks of `d_r` generate exact work and the global
   lower-frame condition.
3. **Common recovery / functional equation:** the paired death layers are isomorphic and unitary
   transport is information-neutral.

It then predicts a theorem in a fourth organ:

> A genuinely new observer, topology, positivity, recurrence, or source-normalization organ can
> unlock selection only by producing a response bounded below on the stable law-history sector.
> Any response boundedly reconstructed from prior transgressions is provably redundant.

This is stronger than demanding “another nonzero invariant.”  The required invariant must act on
the correct quotient and satisfy a uniform properness estimate.

## 9. Sharp boundaries

1. **Closed local ranges are load-bearing.** Without them, `C_(r+1)` is the orthogonal complement
   of the closure of the image and algebraic cokernel information can enter a non-Hausdorff
   radical.  ULF-LHSM-4 locates that failure.
2. **Finite strictness does not imply cofinal strictness.** Taking one-dimensional page blocks with
   `d_r=1/r` gives `gamma_r>0` for every page but `inf gamma_r=0`.
3. **Injective terminal response is insufficient in infinite dimension.** It must be bounded
   below.  A diagonal terminal response with weights tending to zero is injective and nonproper.
4. **Nonzero terminal response is insufficient.** It must detect every stable direction.
5. **Old-page factorization is fatal.** Equation `(PHF.26)` is exact, not heuristic.
6. **No canonical terminal organ is supplied.** Declaring `B=id_(E_infty)` would make the theorem
   tautological.  `B` must be generated before target specialization from the same source grammar
   that generated the history.
7. **No RH claim.** This card proves the universal selector architecture, not the arithmetic
   hypotheses needed to activate it.

## 10. Lean requirements

Formalization must certify at minimum:

1. the diagonal Hodge normal form of the assembled page response;
2. exact kernel = zero-gain/stable coordinates;
3. the least page/terminal gain lower bound;
4. vanishing of every factored response on the stable block;
5. adjoining a separating terminal block makes the global response injective;
6. unit-modulus phase conjugacy preserves gains and selection.

The abstract orthogonal-flag construction and countable closed-range equivalence may be formalized
after the finite diagonal normal form.  No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
computation proof is permitted.

## 11. Promotion record

- 2026-08-18 — constructed from the exact ULF-LHSM higher differential after auditing existing
  one-operator formation/properness theorems.  New content is the pagewise Hodge assembly, exact
  stable-sector kernel, cofinal page-gap criterion, and terminal-organ redundancy/selection law.
- 2026-08-18 — finite diagonal Hodge normal form Lean-certified: exact stable kernel, factored-
  response blindness, terminal injectivity, positive least gain, and unit-phase neutrality.  Target
  leaf built and import wired into `HTGeometry.UniversalLawField`; umbrella deliberately not built.
