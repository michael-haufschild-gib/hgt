# Full formation reflection, polar decomposition, boundary Möbius, and joint reconstruction law

- **ID:** ULF-TAFM-22
- **Stage:** 2-fully-proven
- **Type:** COORDINATE-FREE FORMATION LAW / EXACT REFLECTION LIFT / POLAR BOUNDARY
  RECONSTRUCTION
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [PRE-ZERO] [UNCONDITIONAL] [NOT RH]`
- **Parents:** shifted-Euler full-germ filtration; shifted-Euler Möbius synthesis; positive phase
  quotient; observer-clock information-neutral lift; valuation--interaction superselection
- **Statement:** A finite free-commutative formation profile has a canonical full reflected packet.
  Radial reflection acts on that packet by a multiplier whose polar factors are support parity and
  multiplicity excess. The action is involutive before observation. Its positive norm remembers
  exactly multiplicity excess; its normalized phase remembers exactly support parity; and its
  unitary boundary is exactly the exterior/squarefree locus. Boundary projection followed by
  normalized reflection reconstructs the Möbius law without inserting Möbius as source data. For
  the prime-logarithm representation this becomes an exact reflection law for the shifted-Euler
  coefficients and predicts that squarefree projection of the reflected coefficient is Möbius
  multiplication of the positive coefficient.

## 1. Mechanism, not another route object

The corpus repeatedly reaches the same wall:

1. an Euler or formation receiver is positive;
2. the source cancellation requires an oriented sign, often Möbius;
3. finite jets see only bounded prime breadth;
4. functional reflection is information-neutral at completed level; and
5. inserting the missing sign externally merely renames the source problem.

The missing object is a reflection action on the **full formation profile**, before positivity and
before finite-jet truncation. Its polar decomposition must itself create orientation. This card
constructs that action on the free-commutative formation monoid and proves that its unitary-boundary
phase is Möbius.

This is route-independent. Prime factorization is one representation. The laws require only a
finite multiset of generators with positive weights.

## 2. Weighted free-commutative formation space

Let `P` be any set of generators. A formation state is a finitely supported multiplicity profile

\[
 x:P\longrightarrow\mathbb N.
\tag{22.1}
\]

Write

\[
 S(x)=\{p:x(p)>0\},\qquad b(x)=|S(x)|.
\tag{22.2}
\]

Fix a weight `ell:P -> R`. Define total and support weights

\[
 T_\ell(x)=\sum_{p\in S(x)}x(p)\ell(p),
 \qquad
 R_\ell(x)=\sum_{p\in S(x)}\ell(p),
\tag{22.3}
\]

and multiplicity defect

\[
 D_\ell(x)=T_\ell(x)-R_\ell(x)
 =\sum_{p\in S(x)}(x(p)-1)\ell(p).
\tag{22.4}
\]

Call `x` exterior or squarefree when

\[
 x(p)=1\quad\text{for every }p\in S(x).
\tag{22.5}
\]

Assume only that `ell(p)>0` on `S(x)` when positivity is invoked.

### Theorem 2.1 -- support/depth fracture

\[
 \boxed{D_\ell(x)\ge 0,}
\tag{22.6}
\]

and

\[
 \boxed{D_\ell(x)=0\iff x\text{ is exterior}.}
\tag{22.7}
\]

#### Proof

Every occupied multiplicity satisfies `x(p)>=1`; every summand in (22.4) is therefore
nonnegative. Their sum vanishes exactly when every summand vanishes. Strict positivity of the
occupied weights then gives `x(p)-1=0` for every occupied generator. This is (22.5). QED.

## 3. Full packet and exact reflection lift

For `omega in C`, define the full formation coefficient

\[
 C_{\ell,x}(\omega)
 =\exp\!\bigl(\omega T_\ell(x)\bigr)
  \prod_{p\in S(x)}
   \left(1-\exp\!\bigl(-2\omega\ell(p)\bigr)\right).
\tag{22.8}
\]

Define its reflection multiplier

\[
 M_{\ell,x}(\omega)
 =(-1)^{b(x)}\exp\!\bigl(-2\omega D_\ell(x)\bigr).
\tag{22.9}
\]

### Theorem 3.1 -- full-packet reflection law

For every finite formation profile and every complex `omega`,

\[
 \boxed{
 C_{\ell,x}(-\omega)
 =M_{\ell,x}(\omega)C_{\ell,x}(\omega).}
\tag{22.10}
\]

#### Proof

Each occupied local factor obeys

\[
 1-e^{2\omega\ell(p)}
 =-e^{2\omega\ell(p)}
   \left(1-e^{-2\omega\ell(p)}\right).
\tag{22.11}
\]

Multiplying (22.11) over the support contributes `(-1)^{b(x)}` and
`exp(2 omega R_ell(x))`. Combining this with the reflected outer factor
`exp(-omega T_ell(x))` gives

\[
 -\omega T_\ell(x)+2\omega R_\ell(x)
 =-2\omega\bigl(T_\ell(x)-R_\ell(x)\bigr)+\omega T_\ell(x).
\]

The right side is precisely the exponent in (22.9) followed by the outer factor of
`C_{ell,x}(omega)`. QED.

This is nonperturbative. No fixed transverse jet can replace the product in (22.8) across
unbounded support breadth.

## 4. Information-neutral lift and polar decomposition

### Theorem 4.1 -- involutive conservation

\[
 \boxed{M_{\ell,x}(-\omega)M_{\ell,x}(\omega)=1.}
\tag{22.12}
\]

#### Proof

The two parity factors multiply to `(-1)^{2b(x)}=1`. The two exponential exponents are
opposites. QED.

Thus reflection is information-neutral on the lifted full packet. Any loss occurs only after a
quotient or observer forgets one polar coordinate.

For a real radial parameter `a`, (22.9) is already its polar decomposition:

\[
 M_{\ell,x}(a)
 =\underbrace{(-1)^{b(x)}}_{\text{orientation}}
  \underbrace{e^{-2aD_\ell(x)}}_{\text{positive depth}}.
\tag{22.13}
\]

Consequently,

\[
 \boxed{|M_{\ell,x}(a)|=e^{-2aD_\ell(x)},}
\tag{22.14}
\]

\[
 \boxed{
 \frac{M_{\ell,x}(a)}{|M_{\ell,x}(a)|}=(-1)^{b(x)},}
\tag{22.15}
\]

and, for `a != 0`,

\[
 \boxed{
 D_\ell(x)=-\frac{\log|M_{\ell,x}(a)|}{2a}.}
\tag{22.16}
\]

Equations (22.15)--(22.16) are exact joint reconstruction: full reflection recovers both hidden
coordinates, whereas the positive observer (22.14) discards orientation.

### Corollary 4.2 -- unitary boundary selection

For `a>0` and positive occupied weights,

\[
 \boxed{|M_{\ell,x}(a)|=1\iff x\text{ is exterior}.}
\tag{22.17}
\]

#### Proof

By injectivity of the real exponential, (22.14) equals one exactly when
`D_ell(x)=0`. Apply Theorem 2.1. QED.

The positive norm does not reveal parity, but it canonically reveals where parity is lossless.
This is the first selection law: exterior states are not stipulated; they are the unitary boundary
of full reflection.

## 5. Boundary phase generates Möbius

Define the free-commutative Möbius law

\[
 \mu_F(x)=
 \begin{cases}
 (-1)^{b(x)},&x\text{ exterior},\\
 0,&x\text{ not exterior}.
 \end{cases}
\tag{22.18}
\]

Define the unitary-boundary phase of reflection by

\[
 U_{\partial,\ell,a}(x)=
 \begin{cases}
 M_{\ell,x}(a)/|M_{\ell,x}(a)|,&|M_{\ell,x}(a)|=1,\\
 0,&|M_{\ell,x}(a)|\ne1.
 \end{cases}
\tag{22.19}
\]

### Theorem 5.1 -- universal boundary-Möbius law

For every `a>0`,

\[
 \boxed{U_{\partial,\ell,a}(x)=\mu_F(x).}
\tag{22.20}
\]

#### Proof

If `x` is exterior, (22.17) places it on the unitary boundary and (22.15) gives
`(-1)^{b(x)}`. If `x` is not exterior, (22.17) removes it from the boundary and both sides of
(22.20) are zero. QED.

This is the key source-law advance. Möbius orientation is no longer inserted into a positive Euler
receiver. It is reconstructed as the partial boundary phase of full reflection:

\[
 \boxed{
 \text{Möbius}
 =\text{unitary-boundary projector}
  \times\text{normalized reflection phase}.}
\tag{22.21}
\]

The role of positivity is now precise. Positivity supplies modulus and boundary projection;
orientation lives in the lifted phase which the positive quotient forgets.

## 6. Prime-logarithm representation

Take generators to be rational primes. A positive integer `n` gives the multiplicity profile
`x_n(p)=v_p(n)` and weight `ell(p)=log p`. Then

\[
 T_\ell(x_n)=\log n,
 \qquad
 R_\ell(x_n)=\sum_{p\mid n}\log p,
\tag{22.22}
\]

and

\[
 D(n)=\log n-\sum_{p\mid n}\log p
 =\log\frac{n}{\operatorname{rad}(n)}.
\tag{22.23}
\]

The general packet (22.8) becomes the shifted-Euler coefficient

\[
 c_\omega(n)
 =n^\omega\prod_{p\mid n}(1-p^{-2\omega}).
\tag{22.24}
\]

Theorem 3.1 specializes to

\[
 \boxed{
 c_{-\omega}(n)
 =(-1)^{\omega_0(n)}e^{-2\omega D(n)}c_\omega(n),}
\tag{22.25}
\]

where `omega_0(n)` is the number of distinct prime factors.

The radical is positive, divides `n`, and is squarefree. Hence `D(n)>=0`, with equality exactly
for squarefree `n`. On that unitary locus,

\[
 \boxed{c_{-\omega}(n)=\mu(n)c_\omega(n).}
\tag{22.26}
\]

No Möbius coefficient was used to derive (22.25). It enters (22.26) only as the standard name for
the boundary parity already produced by reflection.

### Corollary 6.1 -- predicted fourth-organ identity

For every positive integer `n`,

\[
 \boxed{
 \mathbf 1_{\mathrm{sqfree}}(n)c_{-\omega}(n)
 =\mu(n)c_\omega(n).}
\tag{22.27}
\]

#### Proof

For squarefree `n`, use (22.26). For nonsquarefree `n`, the indicator and Möbius coefficient both
vanish. QED.

This predicts a theorem in the Möbius organ from a law constructed in the formation/reflection
organ. It is not a relabeling of signed Möbius synthesis: synthesis starts with `mu` and constructs
the positive shifted-Euler source, whereas (22.20) and (22.27) reconstruct `mu` from reflection
polar data.

## 7. Functional-equation interpretation

For a completed function satisfying `F(s)=F(1-s)`, let

\[
 R_\omega(s)=F(s-\omega)/F(s+\omega).
\]

Then

\[
 R_\omega(1-s)=R_{-\omega}(s)=R_\omega(s)^{-1}.
\tag{22.28}
\]

Thus the functional equation acts on a centered two-branch packet by base reflection together with
radial branch exchange `omega -> -omega`. Equation (22.10) is the coefficient-level lift of that
branch exchange on the Euler formation side. Equation (22.12) proves information neutrality before
observation; equations (22.14)--(22.21) describe exactly what the positive quotient retains and
forgets.

This statement is deliberately narrower than claiming that raw Euler coefficients satisfy the
completed functional equation. Gamma completion and boundary continuation remain separate
transport layers.

## 8. Relation to existing no-gos

The law explains, rather than contradicts, several corpus obstructions.

1. **Finite-jet breadth wall.** The order-`k` jet of (22.8) sees only profiles with at most `k`
   occupied generators. The boundary phase (22.20) uses the full exponential product and therefore
   cannot be reconstructed uniformly from any fixed jet.
2. **Positive phase loss.** Norm (22.14) sees multiplicity depth but erases `(-1)^{b(x)}` exactly.
3. **Closed observer/open lift.** Two reflected transports cancel by (22.12), while the intermediate
   normalized lift carries parity invisible to the modulus observer.
4. **Möbius insertion wall.** Signed synthesis remains a valid inverse construction, but Möbius is
   now also characterized intrinsically as reflection boundary phase.
5. **Valuation--breadth fracture.** Breadth is the unitary sign coordinate; valuation excess is the
   positive radial coordinate. Their separation is exact, not heuristic.

## 9. Hostile audit and hard limitation

The following claims are **not** consequences of this card.

1. Equation (22.20) does not prove cancellation of Möbius partial sums.
2. Selecting `omega=0` would degenerate the shifted packet; it is not an RH argument.
3. The law holds for arbitrary weighted free-commutative monoids, so by itself it cannot distinguish
   the ordinary primes from Beurling or other generalized-prime systems.
4. It contains no Gamma factor, zero distribution, Hardy estimate, or critical-line bound.
5. It does not identify hypertranscendence with valuation noncompactness. That requires a separate
   completion theorem.

These are not defects hidden by terminology. They locate the next load-bearing theorem.

## 10. New RH architecture opened by the law

Before this card, the missing sign was external source data. After this card, it is a boundary phase
of a canonical reflection action. The next producer can therefore be asked in geometric form:

> Does the completed prime--Gamma recovery kernel transport the unitary-boundary partial phase
> (22.20) to a globally proper oriented history whose positive projection is the established
> recurrent/energy receiver?

A successful theorem must prove all three clauses at once:

1. **completion compatibility:** the prime-log formation reflection and completed functional
   reflection have the same boundary partial phase after Gamma sewing;
2. **properness:** noncritical completed histories cannot remain in the unitary boundary under
   cofinal formation; and
3. **source cancellation:** the transported boundary phase yields the required signed source law,
   rather than merely another equivalent RH endpoint.

This card supplies the previously absent source-native orientation mechanism. It does not supply
those global analytic clauses.

## 11. Gates

- [x] 0 -> 1: mechanism frozen before implementation.
- [x] 1 -> 2: coordinate-free reflection, involution, polar reconstruction, unitary selection,
  universal boundary-Möbius law, arithmetic specialization, and fourth-organ prediction proved.
- [x] 2 -> 3: coordinate-free formation law and prime-logarithm specialization formalized in Lean;
  modules wired into `HTGeometry.UniversalLawField`.
- [ ] 3 -> 4: no publication claim before completed prime--Gamma compatibility and hostile-model
  separation.

## 12. Lean certification

The dependency-closed theorem family is formalized in:

- `formal/GaloisForLFunctions/HTGeometry/FormationReflectionPolarMechanics.lean`;
- `formal/GaloisForLFunctions/HTGeometry/ShiftedEulerFormationReflectionPolarMechanics.lean`.

Both pass direct foreground elaboration and targeted leaf builds. Eleven audited capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declaration occurs. Both
modules are wired into `HTGeometry.UniversalLawField`; no umbrella or full-project build was run.
