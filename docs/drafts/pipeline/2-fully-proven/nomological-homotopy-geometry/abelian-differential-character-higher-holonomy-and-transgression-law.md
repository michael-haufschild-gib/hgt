# Abelian differential-character higher-holonomy and transgression law

- **ID:** `nhg-abelian-higher-holonomy-transgression`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [ABELIAN HIGHER-ARITY SECTOR]`
  `[NO ROUTE INPUT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. Differential-character field

Let `M` be a smooth manifold, `V` a finite-dimensional real vector space, and `Lambda subset V` a
discrete lattice. Fix `n>=2`. A degree-`n` `V/Lambda` differential character is a homomorphism

\[
 h:Z_{n-1}^{\mathrm{sm}}(M)\longrightarrow V/\Lambda
\tag{DH.1}
\]

for which there is a differential form `Omega in Omega^n(M;V)` satisfying

\[
 \boxed{h(\partial c)=\int_c\Omega\pmod\Lambda}
\tag{DH.2}
\]

for every smooth singular `n`-chain `c`. Call `Omega` the curvature of `h`.

This is the abelian strict chart of higher NHG transport.

## 2. Curvature and flat ambiguity

### Theorem 2.1 — curvature integrality and global ambiguity

The curvature in `(DH.2)` is closed and has lattice periods:

\[
 d\Omega=0,
 \qquad
 \int_z\Omega\in\Lambda
 \quad(z\in Z_n^{\mathrm{sm}}(M)).
\tag{DH.3}
\]

If `h` and `h'` have the same curvature, their difference descends to a flat character

\[
 h-h'\in\operatorname{Hom}(H_{n-1}(M;\mathbb Z),V/\Lambda).
\tag{DH.4}
\]

Conversely adding any such flat character preserves curvature. Hence local curvature does not
determine full higher holonomy whenever the group in `(DH.4)` is nonzero.

#### Proof

For any smooth `(n+1)`-chain `b`, apply `(DH.2)` to `partial b`:

\[
 0=h(\partial^2b)=\int_{\partial b}\Omega
 =\int_b d\Omega\pmod\Lambda.
\]

Take `b` inside arbitrarily small coordinate balls. The integral tends continuously to zero, while
`Lambda` is discrete, so the integral is zero for every sufficiently small `b`; therefore
`dOmega=0`. If `z` is an `n`-cycle, `(DH.2)` gives

\[
 0=h(\partial z)=\int_z\Omega\pmod\Lambda,
\]

which is the period claim. If `h,h'` have the same curvature, their difference vanishes on every
boundary and hence descends to homology. The converse is immediate. QED.

## 3. Transgression theorem

Let `Sigma` be a closed oriented smooth manifold of dimension `n-2`, and let

\[
 \mathcal M=C^\infty(\Sigma,M),
 \qquad
 \operatorname{ev}:\Sigma\times\mathcal M\longrightarrow M
\]

be the evaluation map. Define the fibre-integrated two-form

\[
 \tau_\Sigma\Omega:=\int_\Sigma\operatorname{ev}^*\Omega
 \in\Omega^2(\mathcal M;V).
\tag{DH.5}
\]

For a smooth one-cycle `z` in `mathcal M`, define

\[
 (\tau_\Sigma h)(z)
 :=(-1)^{n-2}h\bigl(\operatorname{ev}_*([\Sigma]\times z)\bigr).
\tag{DH.6}
\]

### Theorem 3.1 — higher curvature becomes ordinary loop holonomy after transgression

`tau_Sigma h` is a degree-two differential character on `mathcal M` with curvature
`tau_Sigma Omega`. Explicitly, for every smooth two-chain `C` in `mathcal M`,

\[
 \boxed{
 (\tau_\Sigma h)(\partial C)
 =\int_C\tau_\Sigma\Omega\pmod\Lambda.}
\tag{DH.7}
\]

For a loop `gamma:S^1->mathcal M`, its holonomy is the original higher holonomy on the swept
`(n-1)`-cycle:

\[
 \boxed{
 (\tau_\Sigma h)(\gamma)
 =(-1)^{n-2}h\bigl(\operatorname{ev}_*[
 \Sigma\times S^1\xrightarrow{\operatorname{id}\times\gamma}
 \Sigma\times\mathcal M]igr).}
\tag{DH.8}
\]

#### Proof

Because `Sigma` is closed,

\[
 \partial([\Sigma]\times C)=(-1)^{n-2}[\Sigma]\times\partial C
\]

with the product orientation convention. The sign in `(DH.6)` cancels this boundary sign, so
`(DH.2)` gives

\[
 (\tau_\Sigma h)(\partial C)
 =h\bigl(\partial\operatorname{ev}_*([\Sigma]\times C)\bigr)
 =\int_{\Sigma\times C}\operatorname{ev}^*\Omega\pmod\Lambda.
\]

Fibre integration identifies the last expression with the right side of `(DH.7)`. Equation
`(DH.8)` is Definition `(DH.6)` applied to a loop. QED.

### Corollary 3.2 — arity law

An `n`-form curvature naturally controls holonomy on `(n-1)`-dimensional histories. It becomes
ordinary loop holonomy only after transgression by an `(n-2)`-dimensional probe. For `n=2`, take
`Sigma` to be a positively oriented point and recover ordinary line-bundle-type loop holonomy.

This is the exact abelian base case for the graded Ambrose--Singer--Spencer programme.

## 4. Local versus global separation

1. `Omega=0` does not force `h=0`: any nonzero character of `H_{n-1}(M)` gives flat higher
   monodromy.
2. If two characters have the same `Omega`, every curvature jet agrees but their transgressed loop
   holonomies can differ by the transgression of a flat character.
3. On contractible `M`, the flat ambiguity vanishes for `n>=2`, so curvature determines the
   character whenever a character with that curvature exists.
4. Closedness of `Omega` is insufficient for existence; lattice periods are necessary. Existence is
   the differential-cohomology lifting problem.

## 5. Field consequence

The theorem proves that higher curvature, higher holonomy, transgression, and global flat ambiguity
are one typed geometry. It also forbids two regressions:

- contracting an `n`-ary curvature to a two-form without a declared probe or soldering;
- claiming local curvature jets determine full holonomy on a topologically nontrivial base.

The nonabelian field problem is to replace addition in `V/Lambda` by nilpotent higher-groupoid
composition and prove the corresponding restricted-holonomy generation theorem.
