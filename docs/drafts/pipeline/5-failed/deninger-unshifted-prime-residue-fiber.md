# Unshifted prime-residue fibre

- **ID:** `deninger-unshifted-prime-residue-fiber`
- **Stage:** 5-failed
- **Type:** GRADING NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Failed label:** `DAC_UNSHIFTED_PRIME_RESIDUE_FIBER`
- **Positive survivor:** `DAC_SHIFTED_STRATUM_RESIDUE_FIBER`

## Failed proposal

Let \(A^\bullet\) be the generic derived-section complex and let
\(B^\bullet\) be the direct sum of prime-packet derived-section
complexes.  The failed proposal was
\[
 E_{\mathrm{bad}}
 =
 \operatorname{Fib}(A^\bullet\longrightarrow B^\bullet).          \tag{1}
\]
For two-term representatives this has underlying total complex
\[
 A^0\longrightarrow A^1\oplus B^0\longrightarrow B^1.             \tag{2}
\]
The proposal treated the \(B^0\) term in `(2)` as the target of the
finite Kummer residue.

## No-go theorem

`[PROVED HERE] [DAC_UNSHIFTED_PRIME_RESIDUE_FIBER_NO_GO]`

The tame Milnor residue has degree
\[
 \partial_p:
 K_n^M(F)\longrightarrow K_{n-1}^M(k(p)).                          \tag{3}
\]
After realification, the analytic construction has the same degree:
\[
 \widetilde{\partial}_p:
 \widetilde{\mathscr A}_\eta^M
 \longrightarrow
 \widetilde{\mathscr A}_p^M(-1)[-1].                              \tag{4}
\]
In particular, a Kummer class in cohomological degree one maps to the
degree-zero scalar residue of the prime coefficient.  Therefore it is
a degree-zero cochain map only after the target is shifted by
\([-1]\).  There is no degree-zero cochain map
\(A^\bullet\to B^\bullet\) whose degree-zero component is `(3)` on
Kummer classes.

Consequently `(1)` cannot be the source residue fibre.  Formula `(2)`
puts \(B^0\) in arithmetic degree one, whereas codimension-one
localization puts the residue of \(A^1\) in arithmetic degree two.
The failed proposal conflates Milnor weight with cohomological degree.

### Proof

Use the convention already fixed by the coefficient cards:
\[
 H\mathscr V[-1]
\]
has \(\mathscr V\) in cohomological degree one.  Thus
\[
 (B[-1])^1=B^0.                                                    \tag{5}
\]
Equation `(3)` is consequently a degree-zero component
\[
 A^1\longrightarrow(B[-1])^1,
\]
but it would be a degree-minus-one component
\(A^1\to B^0\) without the shift.  A cochain map is degree preserving,
so the latter cannot define `(1)`.

For completeness, with
\(\operatorname{Fib}(f)=\operatorname{Cone}(f)[-1]\), a map
\[
 f:A^\bullet\longrightarrow B^\bullet[-1]
\]
with \(A^\bullet=[A^0\to A^1]\) and \(B^\bullet=B^0[0]\) has fibre
\[
 A^0\longrightarrow A^1\longrightarrow B^0,                      \tag{6}
\]
in degrees \(0,1,2\).  Its last differential is \(f^1\), up to the
standard harmless cone sign.  This is exactly the placement in the
finite Milnor endpoint complex.

## Positive survivor

`[PROVED HERE] [DAC_SHIFTED_STRATUM_RESIDUE_FIBER]`

Let
\[
 \mathscr G_\eta=Ra_{\eta,*}\mathscr A_\eta
\]
and let \(\mathscr B_{\mathrm{fin}}^S\) be the strict arithmetic direct
image of the genuine prime-packet coefficients.  The correctly typed
finite residue is
\[
 \partial_{\mathrm{fin}}^S:
 \mathscr G_\eta
 \longrightarrow
 \mathscr B_{\mathrm{fin}}^S(-1)[-1].                             \tag{7}
\]
After adjoining the real Milnor--Witt boundary in the same
codimension-one degree, put
\[
 \mathscr D_{\mathrm{ar}}^S
 =
 \bigl(
   \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus
   \mathscr B_\infty^S
 \bigr)[-1],                                                       \tag{8}
\]
where the two \(\mathscr B\)-objects already carry their Tate-normal
\((-1)\) twists.
\[
 \boxed{
 \mathscr E_{\mathrm{arith}}^S
 =
 \operatorname{Fib}
 \left(
   \mathscr G_\eta
   \xrightarrow{\partial_{\mathrm{ar}}^S}
   \mathscr D_{\mathrm{ar}}^S
 \right).
 }                                                                \tag{9}
\]

If \(R\Gamma(S,\mathscr G_\eta)\) has a two-term representative
\([A^0\to A^1]\) and the boundary direct image is concentrated in
degree zero with value \(D\), then `(9)` is represented by
\[
 L^0=A^0,\qquad
 L^1=A^1,\qquad
 L^2=D_{\mathrm{fin}}\widehat\oplus D_\infty,                     \tag{10}
\]
\[
 d^0=d_A,\qquad
 d^1=\partial_{\mathrm{ar}}.                                      \tag{11}
\]
Hence
\[
 H^0=\ker d_A,\qquad
 H^1=\ker\partial_{\mathrm{ar}}/\operatorname{im}d_A,\qquad
 H^2=\operatorname{coker}\partial_{\mathrm{ar}}.                  \tag{12}
\]

This identifies the actual next source theorem: prove the completed
finite-plus-real residue has closed range equal to the kernel of the
Arakelov trace.  Then \(H^2=\mathbb R(-1)\), while the nonproper
generic coarse-coherence kernel in `(12)` is the only legitimate
source of infinite-dimensional \(H^1\).

## No-go closure

The prime-packet mean-zero functions are not discarded.  They occur
in the degree-two residue target and must be hit by nonconstant
Poincaré residues from the generic pro-log analytic coefficient.
Local Poincaré-residue surjectivity is the positive mechanism; the
remaining all-prime statement is a strict global surjectivity and
closed-range theorem.

Putting packet functions directly in degree one would leave an
uncoupled direct sum of local periodic spectra.  Such a direct sum is
not the global middle cohomology required by Deninger's determinant
program.

## Dependencies and status

- `(4)` is `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.
- strict formation of \(\mathscr B_{\mathrm{fin}}^S\) is
  `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`.
- `(6)` is elementary cone totalization and is already represented
  algebraically by `DeningerArithmeticFiniteResidueEndpoint.lean`.
- the real component and completed trace-kernel exactness in `(12)`
  remain the open construction gate.

**Verdict:** `UNSHIFTED FIBRE RETIRED; SHIFTED RESIDUE FIBRE IS THE
DEPENDENCY-CLOSED POSITIVE SURVIVOR`.
