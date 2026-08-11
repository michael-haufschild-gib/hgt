# Jointly conservative admission descent and migrating-obstruction law

- **ID:** `ulf-grm-joint-admission-descent`
- **Stage:** 2 — fully proven on paper
- **Type:** ROUTE-INDEPENDENT FUSION / CONSERVATION LAW
- **Status:** `[PAPER-PROVED] [LEAN-CERTIFIED] [JOINT RECONSTRUCTION] [FOUR-ORGAN PREDICTION] [NOT RH]`

## 1. Mechanism, not container

Let `V` be an ordered real vector space with positive cone `K`. A source state is `w in K`; an
intervention is `h in V`. For `epsilon>0`, write

\[
\operatorname{Adm}_K(w,h;\epsilon)
\quad\Longleftrightarrow\quad
w+\epsilon h\in K.
\tag{JAD.1}
\]

Let `A_j:V->W_j` be positive linear observers with target cones `L_j`. Positivity alone gives only
lax transport:

\[
\operatorname{Adm}_K(w,h;\epsilon)
\Longrightarrow
\operatorname{Adm}_{L_j}(A_jw,A_jh;\epsilon).
\tag{JAD.2}
\]

This explains why one route can erase an obstruction. Exact fusion needs a law on the *family*.

## 2. Joint conservativity

Call `(A_j)` jointly conservative when

\[
x\in K
\quad\Longleftrightarrow\quad
A_jx\in L_j\text{ for every }j.
\tag{JAD.3}
\]

The forward implication is positivity; the reverse implication is joint order reflection. No
single observer is required to reflect positivity.

### Theorem A — exact admission fusion

For every jointly conservative positive family and every `epsilon>0`,

\[
\boxed{
\operatorname{Adm}_K(w,h;\epsilon)
\Longleftrightarrow
\forall j\;\operatorname{Adm}_{L_j}(A_jw,A_jh;\epsilon).}
\tag{JAD.4}
\]

Likewise, for every `c>=0`,

\[
\boxed{
h+cw\in K
\Longleftrightarrow
\forall j\;(A_jh+cA_jw\in L_j).}
\tag{JAD.5}
\]

**Proof.** Apply linearity to `w+epsilon h` or `h+cw`, then use `(JAD.3)`. QED.

## 3. Exact conservation identity

Let `rho_j` and `kappa_j` be the observer admission radii and negative-density gauges. The feasible
source-scale set is the intersection of all observer feasible-scale sets. Each is a lower interval;
the domination set is an upper interval. Therefore

\[
\boxed{
\rho_K(w,h)=\inf_j\rho_{L_j}(A_jw,A_jh),\qquad
\kappa_K(w,h)=\sup_j\kappa_{L_j}(A_jw,A_jh).}
\tag{JAD.6}
\]

This is the sought route-independent conservation law. It is not scalar averaging. It preserves
the extremal obstruction under fusion.

### Corollary — uniformity is load-bearing

The source is straight-admitted iff the observer family has one common positive lower radius:

\[
\rho_K(w,h)>0
\quad\Longleftrightarrow\quad
\inf_j\rho_{L_j}(A_jw,A_jh)>0.
\tag{JAD.7}
\]

Separate statements `rho_j>0` for every fixed `j` are insufficient.

## 4. Migrating obstruction theorem

If the source fails at scale `epsilon`, `(JAD.4)` gives

\[
\boxed{
\neg\operatorname{Adm}_K(w,h;\epsilon)
\Longrightarrow
\exists j(\epsilon)\;
\neg\operatorname{Adm}_{L_j}(A_jw,A_jh;\epsilon).}
\tag{JAD.8}
\]

The witness may migrate with `epsilon`. Hence no fixed route need carry the whole obstruction. This
is not failure of the fusion law; it is its predicted infinite behavior.

## 5. Exact countable model

Take the conserved probability system from `CofinalGenerativeAdmission`:

\[
w_n=2^{-n-1},\qquad
h_0=1,\qquad h_n=-n2^{-n-1}\;(n\ge1).
\tag{JAD.9}
\]

Let `A_n` be coordinate evaluation. The family is positive and jointly order-reflecting. Every
fixed scalar observer admits the intervention at some positive scale, but

\[
\inf_n\rho_n=0,
\qquad
\rho_K(w,h)=0.
\tag{JAD.10}
\]

At any proposed scale `epsilon`, a sufficiently far coordinate rejects it. Thus the obstruction is
literally cofinal and migrating.

## 6. Fusion grammar across four organs

The preceding finite fusion theorem and `(JAD.4)` now form one mechanism:

1. **source/normalization organ:** centering creates a mass-zero intervention;
2. **phase/moment organ:** a faithful oscillatory reporter reconstructs the intervention;
3. **positive Gram/Hankel organ:** null response determines contingent inward legality and newborn
   rank;
4. **cofinal spectral/admission organ:** the uniform lower envelope of finite radii decides whether
   the reconstructed intervention is executable.

These are not four names for one object. They are four laws linked in a fixed order:

\[
\boxed{
\text{center}\to\text{reconstruct}\to\text{test inwardness}
\to\text{take uniform cofinal radius}\to\text{execute}.}
\tag{JAD.11}
\]

The exact conserved quantities are total mass, the full reconstructed tangent, positive-null
response, and the extremal admission gauge. Information may decrease under one observer, but a
jointly conservative atlas reconstructs it exactly.

## 7. Use for the RH frontier

This theorem changes the next RH question. It is not “find another source-native annihilator.” It
is:

1. construct literal pre-divisor positive comparison maps from one arithmetic intervention space
   into a family of existing route organs;
2. prove the family jointly reflects the source cone;
3. derive a route-uniform positive lower bound for all observer admission radii;
4. identify failure of that uniform bound with the off-critical divisor orientation.

Only step 4 is an RH selection theorem. The current result proves why fixed-route coercivity,
positivity, recurrence, or reconstruction can all succeed without selection: none alone supplies
the infimum in `(JAD.6)`.

## 8. Hostile boundaries

1. **Positive but not jointly reflecting.** Only inequalities survive; the observer family may
   erase a source obstruction.
2. **Jointly reflecting but no uniformity.** Every fixed observer may admit while the source does
   not, as `(JAD.9)` shows.
3. **Faithful phase reconstruction alone.** It recovers `h` but supplies no lower admission radius.
4. **Finite Gram legality alone.** It detects the contingent cone, not straight execution.
5. **Arbitrary nonlinear comparison.** Linearity in `(JAD.4)` is load-bearing unless replaced by an
   independently proved affine intervention law.
6. **RH.** No literal all-route arithmetic comparison family or off-line gauge divergence theorem
   is claimed here.

## 9. Lean certification

`GaloisForLFunctions.HTGeometry.CofinalGenerativeAdmission` certifies:

- `admittedAt_iff_forall_map`;
- `dominatedAt_iff_forall_map`;
- `exists_map_not_admittedAt`;
- `coordinateAdmissionObserver_jointlyReflects`;
- `probabilityAdmission_migrating_obstruction`.

The theorem is wired through `GaloisForLFunctions.HTGeometry.UniversalLawField`.
