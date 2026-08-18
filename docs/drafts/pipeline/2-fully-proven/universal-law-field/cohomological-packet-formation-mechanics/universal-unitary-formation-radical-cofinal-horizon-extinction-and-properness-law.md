# Universal unitary formation radical, cofinal horizon extinction, and properness law

- **ID:** ULF-CPFM-4
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL FORMATION REFLECTION / COFINAL EXTINCTION / GLOBAL PROPERNESS
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN FORMALIZED]`
  `[ROUTE-INDEPENDENT] [POSITIVE SURVIVOR] [SELECTION ARCHITECTURE] [NOT RH]`
- **Date:** 2026-08-18

## 1. Higher mechanism

The previous theorem proves that a positive unitary action cannot retain a nontrivial finite Jordan
history.  The positive survivor is not another norm.  It is a universal formation quotient forced
by every positive-unitary observer.

Let `V` be a real vector space, let `T in GL(V)` be a formation automorphism, and put

\[
 \Delta=T-I.
 \tag{UFR.1}
\]

Define the finite-unipotent formation sector

\[
 \mathcal F_T=\bigcup_{n\ge0}\ker \Delta^n
 \tag{UFR.2}
\]

and its displacement radical

\[
 \boxed{\mathcal R_T=\Delta(\mathcal F_T).}
 \tag{UFR.3}
\]

The kernels in `(UFR.2)` are increasing, so their union is a linear subspace.  Hence `(UFR.3)` is
a linear subspace.  It is defined before a topology, norm, completion, or divisor is chosen.

## 2. Universal positive-unitary reflection

Let `H` be a real Hilbert space, let `U` be a surjective linear isometry of `H`, and let

\[
 r:V\longrightarrow H
 \tag{UFR.4}
\]

be linear and equivariant:

\[
 r(Tv)=U r(v).
 \tag{UFR.5}
\]

### Theorem 2.1 -- radical annihilation

Every equivariant positive-unitary reporter kills the unitary formation radical:

\[
 \boxed{\mathcal R_T\subseteq\ker r.}
 \tag{UFR.6}
\]

### Proof

Take `v in F_T`, so `Delta^n v=0` for some `n`.  Equivariance gives, by induction,

\[
 r(\Delta^n v)=(U-I)^n r(v).
 \tag{UFR.7}
\]

The unitary finite-Jordan collapse theorem ULF-CPFM-3 implies

\[
 (U-I)^n r(v)=0\Longrightarrow (U-I)r(v)=0.
\]

Using `(UFR.5)` once more,

\[
 r(\Delta v)=(U-I)r(v)=0.
\]

Every element of `R_T` has this form.  QED.

### Theorem 2.2 -- unique factorization

There is a unique linear map

\[
 \bar r:V/\mathcal R_T\longrightarrow H
 \tag{UFR.8}
\]

such that

\[
 \boxed{r=\bar r\circ\pi_T,}
 \tag{UFR.9}
\]

where `pi_T:V->V/R_T` is the quotient map.

### Proof

Existence follows from `(UFR.6)` by the universal property of the linear quotient.  Surjectivity of
`pi_T` gives uniqueness.  QED.

The quotient in `(UFR.8)` is therefore not an optional semisimplification.  It is the common exit
through which **every** equivariant positive-unitary reporter must pass.  It may still contain
additional nonunitary or nonnormal directions; `(UFR.3)` is the universal forced kernel, not a
claim that every remaining action is unitarizable.

### Theorem 2.3 -- off-unit spectral erasure and full algebraic quotient

Suppose a real source mode is semisimple:

\[
 Tv=\lambda v.
 \tag{UFR.9a}
\]

If `|lambda|!=1`, every equivariant positive-unitary reporter kills it:

\[
 \boxed{r(v)=0.}
 \tag{UFR.9b}
\]

Indeed, equivariance and norm conservation give

\[
 \|r(v)\|=\|Ur(v)\|=\|r(Tv)\|
 =|\lambda|\,\|r(v)\|,
\]

so the norm vanishes.  Define

\[
 \mathcal R_T^{\rm alg}
 =\mathcal R_T+
 \operatorname{span}\{v:Tv=\lambda v,\ |\lambda|\ne1\}.
 \tag{UFR.9c}
\]

Then every equivariant positive-unitary reporter kills `R_T^alg` and factors uniquely through

\[
 \boxed{V/\mathcal R_T^{\rm alg}.}
 \tag{UFR.9d}
\]

Thus positivity erases both nilpotent lineage attached to the unit spectrum and semisimple radial
modes away from the unit spectrum.  Only unit-modulus semisimple algebraic history can survive this
forced quotient.  This does not assert that every remaining mode admits a Hilbert realization.

## 3. Cofinal primitive extinction

Let `b_n,p_n in V` be boundary and primitive histories satisfying

\[
 \Delta p_n=b_n,
 \qquad p_n\in\mathcal F_T.
 \tag{UFR.10}
\]

### Theorem 3.1 -- every finite-depth boundary is invisible

For every reporter `(UFR.4)--(UFR.5)`,

\[
 \boxed{r(b_n)=0\qquad(n\ge0).}
 \tag{UFR.11}
\]

If the boundaries span `V`, then

\[
 \boxed{r=0.}
 \tag{UFR.12}
\]

### Proof

Equation `(UFR.10)` places every `b_n` in `R_T`; apply Theorem 2.1.  If their span is all of `V`,
linearity gives `(UFR.12)`.  QED.

This is the global formation theorem hidden by finite cutoff calculations.  At a finite cutoff, a
top formation class can survive because its next primitive is absent.  Adjoining the next stage
makes that former horizon an interior boundary.  A compatible cofinal tower therefore extinguishes
every finite horizon class unless a genuinely nonexact boundary remains at infinity.

### Canonical chain model

Let `e_0,e_1,...` be a formation chain with

\[
 \Delta e_{n+1}=e_n,
 \qquad \Delta^{n+2}e_{n+1}=0.
 \tag{UFR.13}
\]

At cutoff `N`, the class of `e_N` can survive in the cokernel of the truncated lowering map.
At cutoff `N+1`, `(UFR.13)` makes it a boundary.  Thus the apparent finite horizon migrates rather
than stabilizes.  If the `e_n` span the cofinal source, Theorem 3.1 says that no nonzero faithful
positive-unitary reporter exists on that cofinal exact history.

## 4. Global formation properness

Extinction in the positive quotient does not mean source history is absent.  It means source
history must be retained by a different doctrine.  The corpus already constructs the canonical
depth graph on countable histories:

\[
 c(x)=\sum_{j\ge0}x_j,
 \qquad (Nx)_j=jx_j,
 \qquad
 \Phi(x)=|c(x)|+2\sum_{j\ge0}j|x_j|.
 \tag{UFR.14}
\]

Its sublevels are compact in the ambient `ell^1` source, and

\[
 \|x\|_1\le\Phi(x).
 \tag{UFR.15}
\]

For the normalized horizon at depth `N`,

\[
 h_N(j)=\mathbf 1_{j=N},
 \tag{UFR.16}
\]

one has the exact source ledger

\[
 c(h_N)=1,
 \qquad \|Nh_N\|_1=N,
 \qquad
 \boxed{\Phi(h_N)=1+2N.}
 \tag{UFR.17}
\]

### Theorem 4.1 -- horizon extinction/properness dichotomy

A migrating finite horizon has exactly two possible fates:

1. at the next exact formation stage it becomes a finite-depth boundary and every positive-unitary
   reporter kills it by `(UFR.11)`;
2. if it is retained as a marked source horizon and sent cofinally to infinity, its source action
   diverges by `(UFR.17)` and it leaves every compact `Phi`-sublevel.

Hence no sequence of normalized migrating horizons is simultaneously

\[
 \boxed{
 \text{nonzero in an equivariant positive-unitary reporter}
 \quad\text{and}\quad
 \text{bounded in source formation action}.}
 \tag{UFR.18}
\]

### Proof

The first alternative is Theorem 3.1.  The second is the equality
`Phi(h_N)=1+2N->infinity`.  Compactness of `Phi`-sublevels rules out every adaptive bounded-action
escape, not only a fixed ray.  QED.

This is the requested global formation/properness theorem.  It is generated by the formation
filtration and its codiagonal; no receiver norm is fitted.

## 5. Fusion across structurally different organs

One mechanism now controls four distinct organs:

| Organ | Exact law |
|---|---|
| cohomological exactification | `Delta` turns a primitive into a boundary and lowers formation degree |
| positive/unitary observation | every reporter factors through `V/R_T^alg` |
| cofinal topology | every finite horizon is exactified at a later stage |
| source action/properness | retaining the migrating horizon costs `1+2N` |

The conservation identity is not a shared scalar.  It is the exact alternative

\[
 \boxed{
 \text{later primitive}\Rightarrow\text{unitary erasure},
 \qquad
 \text{marked horizon escape}\Rightarrow\text{unbounded source action}.}
 \tag{UFR.19}
\]

The fourth-organ prediction is sharp:

> Any finite-aperture spectral, recurrence, trace, or positive-Gram calculation which finds a
> nonzero top class must lose that class under the next exact formation extension, unless it also
> records a marked cofinal boundary whose formation action diverges.

This prediction is falsifiable before RH specialization.

## 6. What this changes about the field programme

The new field cannot identify exact formation with unitary time evolution.  They are different
laws:

1. exact formation is unipotent/degree-lowering and creates boundaries;
2. positive recurrence is semisimple and sees only the algebraic unitary quotient `(UFR.9d)`;
3. global source geometry retains erased history through a grading action with compact sublevels;
4. selection must prove that a physical nonneutral class is forced into the dichotomy `(UFR.19)`.

This gives a precise interpretation of several corpus shadows:

- finite quotients repeatedly manufacture top classes which disappear after cofinal exactification;
- positive observers see phase or semisimple support but erase finite polynomial lineage;
- hypertranscendence belongs to unbounded formation-channel rank, not a finite Jordan block;
- recurrent observer projection can stay compact while its marked formation horizon escapes with
  unbounded source action;
- completion no-gos are failures to retain both the semisimple quotient and the graded radical.

These are consequences of one law mechanism rather than renamed route outputs.

## 7. Selection gate toward RH

The abstract selector is now exact:

> **Physical algebraic-formation bridge.** Before zero specialization, every physical defect lands
> in one jointly recoverable packet whose unitary leg intertwines its source multiplier and whose
> exact-history leg carries the source-depth proper action.  A defect erased by the unitary leg must
> remain as a finite boundary, a migrating horizon, or an expanding off-unit orbit in the proper
> exact-history leg.

For the prime-radial receiver, an off-centre defect has positive real multiplier
`lambda=p^(2 Re rho-1)!=1`.  Theorem 2.3 erases its unitary leg.  Finite boundaries are erased by
Theorem 3.1, migrating horizons violate `(UFR.18)`, and a reflected off-unit scale orbit violates the
already Lean-proved expanding-orbit properness law.  Hence the bridge would exclude every
off-centre defect.  The bridge is not yet proved for the literal Xi source, so this card claims no
RH theorem.

The next research problem is no longer “find another source-native scalar.”  It is:

\[
 \boxed{
 \text{construct the literal Xi formation filtration and place its physical defect in the jointly
 recoverable algebraic-unitary formation packet}.}
 \tag{UFR.20}
\]

## 8. Sharp boundaries

1. Indefinite/Krein reporters can retain unipotent directions; Theorem 2.1 is positive-Hilbert.
2. `R_T^alg` is only the algebraically forced kernel.  Further directions may be erased by a
   particular reporter.
3. A finite cutoff can retain a top cokernel class.  The theorem concerns compatibility under later
   exact formation.
4. Properness uses the source-generated depth grading and codiagonal.  Arbitrary unweighted Hilbert
   completions need not retain either.
5. The theorem does not construct the jointly recoverable Xi formation packet.
6. No claim is made that hypertranscendence alone supplies the bridge `(UFR.20)`.

## 9. Lean certification

The new dependency-closed core is formalized in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveUnitaryFormationRadical.lean`.

Lean proves:

1. the finite-unipotent formation submodule and radical `(UFR.2)--(UFR.3)`;
2. exact intertwining of every displacement power `(UFR.7)`;
3. radical annihilation `(UFR.6)`;
4. off-unit eigenmode erasure `(UFR.9b)` and full algebraic radical `(UFR.9c)`;
5. existence and uniqueness of both forced quotient factors `(UFR.8)--(UFR.9)` and `(UFR.9d)`;
6. cofinal primitive extinction `(UFR.11)`;
7. reporter vanishing when cofinal boundaries span `(UFR.12)`;
8. the exact migrating-horizon work formula `(UFR.17)`.

The imported formation-depth modules already Lean-certify compact graph sublevels, coercivity, and
adaptive-escape exclusion.  No `sorry`, `admit`, project axiom, `opaque`, `unsafe`, or computation
is used.

## Log

- 2026-08-18 -- unitary formation radical and universal quotient derived from finite-Jordan
  conservation.
- 2026-08-18 -- cofinal primitive extinction and horizon-cost properness fused into one selection
  architecture.
- 2026-08-18 -- paper proof closed and scratch Lean elaboration passed.
