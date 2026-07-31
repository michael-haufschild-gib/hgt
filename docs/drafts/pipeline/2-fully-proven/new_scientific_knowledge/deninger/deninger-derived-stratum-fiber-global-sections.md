# Derived shifted stratum-fibre global sections

- **ID:** `deninger-derived-stratum-fiber-global-sections`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Labels:** `DAC_DERIVED_STRATUM_FIBER_GLOBAL_SECTIONS`,
  `DAC_SHIFTED_STRATUM_RESIDUE_FIBER`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** a Deninger coefficient glued by codimension-one
  generic-to-boundary residues has global sections equal to the
  shifted residue fibre and therefore occupies arithmetic degrees
  \(0,1,2\).

## Setup

Let \(X\) be Deninger's actual coarse rational-Witt suspension for
\(\operatorname{Spec}\mathbb Z\), with arithmetic projection
\[
 a:X\longrightarrow S=\operatorname{Spec}\mathbb Z.
\]
Write
\[
 j:X_\eta=a^{-1}(\eta)\hookrightarrow X,\qquad
 i_p:X_p=a^{-1}(p)\hookrightarrow X.                              \tag{1}
\]

Let \(\mathcal D(S)\) be a stable derived category of sheaves of real
modules, or a stable complete locally convex enhancement in which the
chosen strict boundary object exists.  Let
\[
 \mathscr A_\eta\in\mathcal D(X_\eta),\qquad
 \mathscr A_p\in\mathcal D(X_p)
\]
be the degreewise coarse invariant Tate--Milnor coefficients on the
actual strata.  After arithmetic derived direct image, let
\[
 \mathscr G_\eta=Ra_{\eta,*}\mathscr A_\eta,\qquad
 \mathscr B_{\mathrm{fin}}^S
\]
be respectively the generic object and the already-formed strict
all-prime packet object on \(S\).

Tame residue lowers Milnor degree by one.  Therefore the correctly
typed finite-plus-real target is
\[
 \mathscr D_{\mathrm{ar}}^S
 =
 \left(
   \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus\mathscr B_\infty^S
 \right)[-1],                                                     \tag{2}
\]
where both boundary objects already contain their Tate-normal
\((-1)\) twists.
and a source residue is a cochain map
\[
 \partial_{\mathrm{ar}}^S:
 \mathscr G_\eta\longrightarrow\mathscr D_{\mathrm{ar}}^S.        \tag{3}
\]
Define
\[
 \boxed{
 \mathscr E_{\mathrm{arith}}^S
 =
 \operatorname{Fib}(\partial_{\mathrm{ar}}^S).
 }                                                               \tag{4}
\]

## Global-section theorem

`[PROVED HERE] [DAC_DERIVED_STRATUM_FIBER_GLOBAL_SECTIONS]`

There is a canonical equivalence
\[
 R\Gamma(S,\mathscr E_{\mathrm{arith}}^S)
 \simeq
 \operatorname{Fib}\!\left(
   R\Gamma(S,\mathscr G_\eta)
   \xrightarrow{R\Gamma(\partial_{\mathrm{ar}}^S)}
   R\Gamma(S,\mathscr D_{\mathrm{ar}}^S)
 \right).                                                        \tag{5}
\]
If
\[
 R\Gamma(S,\mathscr B_{\mathrm{fin}}^S)
 \simeq
 \widehat{\bigoplus}_{p}^{\,\prime}
 R\Gamma(X_p,\mathscr A_p),                                      \tag{6}
\]
then `(5)` becomes the fibre of the completed family of actual
finite stratum residues together with the real residue.

### Proof

In a stable category, a homotopy fibre is a finite limit.  Derived
global sections are a right adjoint and preserve limits.  Applying
\(R\Gamma(S,-)\) to `(4)` proves `(5)`.  Equation `(6)` is then a
separate strict comparison for the already-constructed boundary
object; no interchange of an arbitrary infinite sum with a derived
functor is used.

The identities
\[
 R\Gamma(S,Ra_{\eta,*}\mathscr A_\eta)
 \simeq R\Gamma(X_\eta,\mathscr A_\eta)
\]
and its finite-stratum analogues follow from composition of derived
right adjoints.

## Shifted totalization theorem

`[PROVED HERE] [DAC_SHIFTED_STRATUM_RESIDUE_FIBER]`

Assume
\[
 R\Gamma(S,\mathscr G_\eta)
 \simeq[A^0\xrightarrow{d_A}A^1]
\]
in cohomological degrees \(0,1\), and assume the unshifted boundary
object
\[
 D=B_{\mathrm{fin}}\widehat\oplus B_\infty
\]
is concentrated in degree zero.  A map to \(D[-1]\) has only the
component
\[
 \partial^1:A^1\longrightarrow D=(D[-1])^1,                      \tag{7}
\]
and the cochain-map identity is
\[
 \partial^1d_A=0.                                                \tag{8}
\]
Then the fibre in `(5)` is represented, up to the standard cone sign,
by
\[
 L^0=A^0,\qquad L^1=A^1,\qquad L^2=D,                            \tag{9}
\]
\[
 d^0=d_A,\qquad d^1=\partial^1.                                  \tag{10}
\]
Consequently
\[
 H^0=\ker d_A,\qquad
 H^1=\ker\partial^1/\operatorname{im}d_A,\qquad
 H^2=D/\operatorname{im}\partial^1,                              \tag{11}
\]
and cohomology vanishes outside degrees \(0,1,2\).

### Proof

For cochain complexes use
\[
 \operatorname{Fib}(f)=\operatorname{Cone}(f)[-1].
\]
Since `(5)` has target \(D[-1]\), its cone fibre has terms
\[
 \operatorname{Fib}(f)^n
 =
 A^n\oplus(D[-1])^{n-1}.
\]
The second summand is nonzero only when \(n=2\), where it is \(D\).
This gives `(9)`--`(10)`.  Equation `(8)` says
\(d^1d^0=0\), and the ordinary cohomology calculation gives `(11)`.

## Arithmetic consequence

For the source construction:

1. \(D_{\mathrm{fin}}\) is the full strict packet residue space, not
   only its Haar-scalar line;
2. local log-toric Poincaré residue is surjective onto finite-stage
   divisor functions, so packet mean-zero modes belong to the
   degree-two target and have source analytic lifts;
3. the Kummer generator maps to the constant valuation line;
4. the real component is the archimedean logarithmic/signature
   residue.

Thus the endpoint theorem required by Deninger's program is precisely
\[
 \overline{\operatorname{im}\partial_{\mathrm{ar}}}
 =
 \ker\!\left(
   \operatorname{tr}_{\mathrm{Ar}}:
   D_{\mathrm{fin}}\widehat\oplus D_\infty
   \longrightarrow\mathbb R(-1)
 \right),                                                        \tag{12}
\]
with strict closed image.  Equation `(12)` implies
\[
 H^2\simeq\mathbb R(-1).
\]
The source of infinite-dimensional \(H^1\) is then the nonproper
generic coarse-coherence kernel in `(11)`, not an uncoupled direct
sum of local packet modes.

## Hostile audit

- The unshifted fibre
  \(\operatorname{Fib}(A^\bullet\to B^\bullet)\) has a different
  totalization and cannot type tame residue; it is retired in
  `deninger-unshifted-prime-residue-fiber`.
- Prime-packet amplitude \([0,0]\) is compatible with `(9)` because
  the Tate-normal shift places its residue target in degree two.
- The theorem does not prove `(12)`, construct the real residue, or
  identify the middle spectrum.
- No coarse/derived quotient comparison, zeta zero, explicit formula,
  CCM object, or RH statement enters `(4)`--`(11)`.

## Gates

- [x] 0 → 1 in-progress: shifted source coefficient typed
- [x] 1 → 2 fully-proven: stable-category and cone proofs complete
- [ ] 2 → 3 formalized: shifted-fibre totalization
- [ ] 3 → 4 publication-ready: integrate strict trace-kernel theorem

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Introduction pp. 4--5 and Definition 10.1:
  https://arxiv.org/abs/1807.06400
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`
- `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`

## Log

- 2026-07-27 — isolated the categorical global-section identity.
- 2026-07-27 — corrected the residue grading: the Tate-normal
  `[-1]` shift puts finite and real boundary cochains in arithmetic
  degree two.
