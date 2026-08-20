# Quantized proximity, approximate formation, and winding selection law

- **ID:** ULF-DFPM-6
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveApproximateFormationSelection`
- **Type:** THEOREM / APPROXIMATE FORMATION / ADMISSION-GAP SELECTION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [EXACT ROOTS NOT REQUIRED] [SOURCE APPROXIMATION OPEN] [NOT RH]

## 1. Mechanism

Exact formation roots are unnecessarily rigid.  Selection only needs three laws:

1. **power formation:** a discrete charge scales by formation depth;
2. **admission stability:** sufficiently close admitted carriers have equal charge;
3. **cofinal approximation:** one carrier is approximated, inside that stability neighborhood, by
   powers of unbounded depth.

The admission gap turns analytic approximation into exact integer divisibility.  Unbounded
divisibility then annihilates charge.

This is a mechanism, not a new route object.  It fuses formation, topology/admission, and discrete
charge before specializing to winding or divisors.

## 2. Abstract quantized-proximity theorem

Let `M` be a monoid, let

\[
 q:M\longrightarrow\mathbb Z
\]

satisfy

\[
 q(x^n)=nq(x),
 \tag{QPA.1}
\]

and let `near(y,x)` be a declared admission relation satisfying

\[
 \operatorname{near}(y,x)\Longrightarrow q(y)=q(x).
 \tag{QPA.2}
\]

### Theorem 2.1 — approximate formation selection

If for every `N` there exist `n >= N` and `y in M` such that

\[
 \operatorname{near}(y^n,x),
 \tag{QPA.3}
\]

then

\[
 \boxed{q(x)=0.}
 \tag{QPA.4}
\]

### Proof

By (QPA.2) and (QPA.1),

\[
 q(x)=q(y^n)=nq(y).
\]

Thus `n` divides `q(x)` for integers `n` of unbounded size.  A nonzero integer has no divisor
larger than its absolute value.  Hence `q(x)=0`. ∎

The conclusion uses neither convergence of the approximating powers nor existence of an exact root.
Each depth may use a different approximant.

### Theorem 2.2 — global sequential formation/properness

Let `M` be a pseudometric monoid.  Suppose depths `n_k` tend to infinity and

\[
 y_k^{n_k}\longrightarrow x.
 \tag{QPA.5}
\]

If there is one `epsilon > 0` such that

\[
 d(z,x)<\epsilon\Longrightarrow q(z)=q(x),
 \tag{QPA.6}
\]

then `q(x)=0`.

### Proof

For every requested lower depth `N`, convergence of `n_k` and of the formed powers supplies one
index `k` with `n_k >= N` and `d(y_k^{n_k},x)<epsilon`.  Theorem 2.1 applies. ∎

This is the global formation/properness theorem in its minimal coordinate-free form: cofinal
formation converges in the native admission topology, and one stable gap converts that return into
exact selection.

### Theorem 2.3 — formation/recovery interchange selection

Let `S` be a source packet type, `M` a pseudometric monoid, and

\[
 \operatorname{rec}:S\longrightarrow M
\]

a recovery map.  At stage `k`, let `p_k` be an unformed packet, `F_k` its source-formed packet, and
`n_k` its formation depth.  Assume

\[
 n_k\longrightarrow\infty,
 \qquad
 \operatorname{rec}(F_k)\longrightarrow x,
 \tag{QPA.7}
\]

and the formation/recovery interchange defect vanishes:

\[
 d\!\left(\operatorname{rec}(p_k)^{n_k},\operatorname{rec}(F_k)\right)
 \longrightarrow0.
 \tag{QPA.8}
\]

If `q` is power-additive and constant on one metric neighborhood of `x`, then

\[
 \boxed{q(x)=0.}
 \tag{QPA.9}
\]

### Proof

The triangle inequality and (QPA.7)--(QPA.8) give

\[
 \operatorname{rec}(p_k)^{n_k}\longrightarrow x.
\]

Apply Theorem 2.2. ∎

This is the exact fusion law joining source formation, recovery, observer admission, and discrete
selection.  Recovery need not be a monoid homomorphism; asymptotic vanishing of its typed
formation-interchange defect is sufficient.

## 3. Native winding-gap realization

Let `gamma, eta : R -> C` be nonvanishing loops on `[a,b]`.  Suppose a real number `m` satisfies

\[
 m\le |\gamma(t)|
 \quad\text{and}\quad
 |\eta(t)^n-\gamma(t)|<m
 \qquad(t\in\mathbb R).
 \tag{QPA.10}
\]

The straight-line homotopy from `gamma` to `eta^n` stays nonzero.  Therefore

\[
 \operatorname{wind}(\gamma)
 =\operatorname{wind}(\eta^n)
 =n\operatorname{wind}(\eta).
 \tag{QPA.11}
\]

### Theorem 3.1 — cofinal approximate-power winding selection

Fix one nonvanishing loop `gamma` and one native floor `m <= |gamma(t)|`.  If for every `N` there
exist `n >= N` and a nonvanishing loop `eta_n` with

\[
 \sup_t|\eta_n(t)^n-\gamma(t)|<m,
 \tag{QPA.12}
\]

then

\[
 \boxed{\operatorname{wind}(\gamma)=0.}
 \tag{QPA.13}
\]

### Proof

Dominated straight-line deformation gives (QPA.11).  Hence unbounded `n` divide the integer winding
of `gamma`.  Apply Theorem 2.1. ∎

For a meromorphic carrier, apply the theorem to every sufficiently small nonvanishing boundary
loop.  Cofinal approximate powers below the local boundary floor force every local divisor order to
vanish.  This is strictly weaker input than global meromorphic roots.

### Corollary 3.2 — quantitative formation-gap obstruction

Suppose `wind(gamma) != 0` and `n > |wind(gamma)|`.  Then every nonvanishing loop `eta` satisfies

\[
 \boxed{
 \exists t:\quad
 |\eta(t)^n-\gamma(t)|\ge m.}
 \tag{QPA.14}
\]

Indeed, strict inequality below `m` at every point would give
`wind(gamma)=n wind(eta)`, contradicting `n>|wind(gamma)|`.  Thus nonzero charge is not merely a
qualitative obstruction: it enforces the native admission margin as a hard approximation floor.

## 4. Fusion and fourth-organ prediction

The mechanism has four exact faces:

1. **formation:** `y -> y^n`;
2. **admission/properness:** the neighborhood that cannot cross the noninvertible locus;
3. **quantized charge:** a locally constant integer reporter;
4. **winding/divisor:** dominated complex loops instantiate the reporter and stability law.

The fourth face was not used to prove the abstract theorem; it is predicted by the first three and
proved independently using the corpus's dominated-homotopy and winding-power laws.

The same grammar predicts an operator face: in any admitted operator quotient, an approximate
`n`-th power lying inside the connected invertible neighborhood has `K_1`/Fredholm charge divisible
by `n`.  That operator realization is not claimed in this card or its Lean module.

## 5. Source consequence

The DFPM source gate is weakened from

> construct exact global roots of the Euler-shell transfer

to

> construct source-native powers of unbounded depth that approximate the transfer on each
> nonvanishing contour more accurately than its native distance to the noninvertible locus.

No choice of branch is required.  Topological charge stability supplies the missing exactness.

This does not prove RH: no such critical-half-plane source approximation is currently constructed.
It changes the required producer from exact root descent to a quantitative formation theorem.

## 6. Hostile boundaries

1. **Arbitrary approximation is enough.** False.  Approximation must remain in one charge-stable
   admission neighborhood.
2. **Pointwise real-axis approximation is enough.** False.  It does not control contour winding.
3. **One depth is enough.** False.  It proves only divisibility by that depth.
4. **Bounded depths are enough.** False.  A nonzero charge may be divisible by every depth in a
   bounded family.
5. **Exact roots are secretly assumed.** False.  Approximants may vary with depth and need satisfy
   only (QPA.3).
6. **Functional equation supplies the approximation.** Not proved.  Information-neutral reflection
   preserves charge and the admission gap; it does not generate powers.
7. **The abstract relation can be chosen after seeing charge.** That would be theatre.  In the loop
   realization it is fixed beforehand by the norm floor and straight-line admission.

## 7. Lean certificate and scope

Module `GaloisForLFunctions.HTGeometry.ConstitutiveApproximateFormationSelection` certifies Theorems
2.1--2.3, 3.1, and Corollary 3.2.  It reuses the already formalized integer-divisibility selector,
`RHTower.windingNumber_eq_of_close`, and `RHTower.windingNumber_pow`.

No RH premise, source approximation, exact root, `sorry`, added axiom, unsafe declaration, full
build, or umbrella build is used.
