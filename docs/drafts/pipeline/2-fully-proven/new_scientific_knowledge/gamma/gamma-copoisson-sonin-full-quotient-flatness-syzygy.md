# Gamma--co-Poisson--Sonin full-quotient flatness and source-error syzygy

- **ID:** `gamma-copoisson-sonin-full-quotient-flatness-syzygy`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / RH INTERFACE
- **Scientific status:** `[CORPUS-NEW] [PAPER-PROVED] [PRELIMINARY EXTERNAL NONCOLLISION] [NOT RH]`
- **Parent:** `gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`
- **Primary external input:** Burnol's theorem identifying the closed span of all confluent
  nontrivial-zero evaluators with the orthogonal complement of the closed co-Poisson source space.

## Result

The parent card constructs the literal quotient maps
\[
 T_j^+=E_jU_r^*|_{Y_{j+1}},
 \qquad
 T_j^-=E_jU_r|_{Y_{j+1}},
\tag{1}
\]
and proves that the two paths around a quadrant square agree on each zeroth zero-evaluation
section.  The agreement is in fact an operator identity on the entire source-defined quotient:
\[
\boxed{\qquad
 T_j^+T_{j+1}^-=T_j^-T_{j+1}^+
 \quad:Y_{j+2}\longrightarrow Y_j .
\qquad}
\tag{2}
\]

Consequently every finite word in the forward and inverse quotient maps depends only on its two
endpoint counts, not on the order of the letters.  All finite three-cube and higher coherence
conditions follow from adjacent transpositions.

This is stronger than boundary-section path independence.  It is also not an RH proof.  The
result makes the surviving obstruction exact: the Gamma--co-Poisson--Sonin quotient connection is
flat, while its Hilbert metric is not compatible with the connection off the critical line.
Horizontal Xi charge is the conserved nonmetricity, not a connection curvature.

## Notation

For a regular \(w\), put
\[
 L(w)=\overline{\lambda_r(w)},\qquad
 M_j(w)=\overline{\Lambda_j(w)}
\tag{3}
\]
and use the parent factorization
\[
\begin{aligned}
 T_j^+y_{w,j+1}&=L(w)y_{w,j}-M_{j+1}(w)e_j^+(w),\\
 T_j^-y_{w,j+1}&=L(w)^{-1}y_{w,j}-M_{j+1}(w)e_j^-(w).
\end{aligned}
\tag{4}
\]
Here
\[
 e_j^+(w)=E_jU_r^*c_{w,j+1},
 \qquad
 e_j^-(w)=E_jU_rc_{w,j+1}.
\tag{5}
\]

Define the two-path commutator
\[
 K_j=T_j^+T_{j+1}^- -T_j^-T_{j+1}^+
 :Y_{j+2}\longrightarrow Y_j .
\tag{6}
\]
It is bounded.

## Exact off-divisor source-error syzygy

Substitution of `(4)` twice gives, for every regular \(w\),
\[
\begin{aligned}
K_jy_{w,j+2}
={}&M_{j+1}(w)
 \left(
 L(w)e_j^-(w)-L(w)^{-1}e_j^+(w)
 \right)\\
&+M_{j+2}(w)
 \left(
 T_j^-e_{j+1}^+(w)-T_j^+e_{j+1}^-(w)
 \right).
\end{aligned}
\tag{7}
\]

After `(2)`, this becomes the vector-valued first syzygy
\[
\boxed{\begin{aligned}
0={}&\overline{\Lambda_{j+1}(w)}
 \left(
 \overline{\lambda_r(w)}e_j^-(w)
 -\overline{\lambda_r(w)}^{-1}e_j^+(w)
 \right)\\
&+\overline{\Lambda_{j+2}(w)}
 \left(
 T_j^-e_{j+1}^+(w)-T_j^+e_{j+1}^-(w)
 \right).
\end{aligned}}
\tag{8}
\]

Locally write the common nontrivial divisor as \(D\) and
\(\Lambda_k=u_kD\), where each \(u_k\) is a holomorphic unit.  Cancelling the common
anti-holomorphic factor in `(8)` before specializing to a divisor point yields
\[
\begin{aligned}
0={}&\overline{u_{j+1}(w)}
 \left(
 \overline{\lambda_r(w)}e_j^-(w)
 -\overline{\lambda_r(w)}^{-1}e_j^+(w)
 \right)\\
&+\overline{u_{j+2}(w)}
 \left(
 T_j^-e_{j+1}^+(w)-T_j^+e_{j+1}^-(w)
 \right).
\end{aligned}
\tag{9}
\]
This cancellation is source-local and occurs on an open neighborhood.  It does not divide a
scalar identity by the value of \(\Xi\) at a chosen zero.

Equation `(9)` is the first literal co-Poisson reporter syzygy.  It transports the one-step
forward/inverse source-error mismatch to the next aperture cell.

## Proof of full-quotient flatness

Let \(\rho\) be a nontrivial zeta zero of multiplicity \(m_\rho\).  Each multiplier
\(\Lambda_k\) has the same zero there with the same multiplicity.  Therefore `(7)` and all its
anti-holomorphic parameter derivatives of order \(<m_\rho\) vanish at \(\rho\):
\[
 K_j\,
 \overline\partial_w^\ell y_{w,j+2}|_{w=\rho}=0,
 \qquad 0\leq\ell<m_\rho .
\tag{10}
\]

The quotient-kernel factorization
\[
 y_{w,j+2}
 =k_{w,j+2}
  -\overline{\Lambda_{j+2}(w)}c_{w,j+2}
\tag{11}
\]
shows that the same derivatives agree at \(\rho\) with the ambient confluent evaluation vectors:
\[
 \overline\partial_w^\ell y_{w,j+2}|_{w=\rho}
 =
 \overline\partial_w^\ell k_{w,j+2}|_{w=\rho},
 \qquad 0\leq\ell<m_\rho .
\tag{12}
\]
Thus \(K_j\) kills every confluent nontrivial-zero evaluator in \(Y_{j+2}\).

Burnol's co-Poisson orthogonal-complement theorem identifies the closed span of all those
confluent evaluators with \(Y_{j+2}=C_{j+2}^{\perp}\).  Since \(K_j\) is bounded, `(10)`--`(12)`
force \(K_j=0\).  This proves `(2)`.  Substitution back into `(7)` proves `(8)`, and local analytic
cancellation proves `(9)`.  `QED`

## Higher coherence

For a word \(\epsilon=(\epsilon_0,\ldots,\epsilon_{N-1})\in\{+,-\}^N\), let
\[
 T_\epsilon
 =T_0^{\epsilon_0}T_1^{\epsilon_1}\cdots T_{N-1}^{\epsilon_{N-1}}
 :Y_N\longrightarrow Y_0,
\tag{13}
\]
with the rightmost map applied first.  If two adjacent letters are interchanged, `(2)` says the
composite is unchanged.  Any two binary words with the same numbers \(p\) of \(+\) letters and
\(q\) of \(-\) letters are connected by adjacent interchanges.  Hence there is a well-defined
endpoint operator
\[
 T_{p,q}:Y_{p+q}\longrightarrow Y_0,
\qquad
 \|T_{p,q}\|\leq1,
\tag{14}
\]
independent of path.

On a zero evaluator,
\[
 T_{p,q}y_{\rho,p+q}
 =
 \overline{\lambda_r(\rho)}^{\,p-q}y_{\rho,0}.
\tag{15}
\]
Equation `(15)` recovers the parent quadrant escape bounds, but now from a flat operator
connection on the full quotient.

## Anti-diagonal relative torsion

The flat system has a canonical determinant-line invariant which does not depend on the unknown
evaluation-kernel norms.  Put
\[
 L_{\rho,j}=\mathbb C y_{\rho,j}
\tag{16}
\]
with the Hilbert norm inherited from \(Y_j\), and use the unit vector
\(u_{\rho,j}=y_{\rho,j}/\|y_{\rho,j}\|\).  The two restricted edge maps have orthonormal-basis
coefficients
\[
\begin{aligned}
 a_{\rho,j}^+
 &=\overline{\lambda_r(\rho)}
   {\|y_{\rho,j}\|\over\|y_{\rho,j+1}\|},\\
 a_{\rho,j}^-
 &=\overline{\lambda_r(\rho)}^{-1}
   {\|y_{\rho,j}\|\over\|y_{\rho,j+1}\|}.
\end{aligned}
\tag{17}
\]
Their positive relative torsion is therefore
\[
\boxed{\qquad
 \tau_r(\rho)
 :=
 {|a_{\rho,j}^+|\over|a_{\rho,j}^-|}
 =
 |\lambda_r(\rho)|^2
 =
 r^{\,2\operatorname{Re}\rho-1}.
\qquad}
\tag{18}
\]
It is independent of \(j\) and of every aperture-kernel norm.

For the endpoint maps in `(14)`, comparison with the reflected endpoint gives
\[
 {|\det(T_{p,q}|L_{\rho,p+q})|
  \over
  |\det(T_{q,p}|L_{\rho,p+q})|}
 =
 \tau_r(\rho)^{\,p-q}.
\tag{19}
\]
Thus the determinant character factors through the anti-diagonal quotient
\[
 \mathbb Z^2/\langle(1,1)\rangle\simeq\mathbb Z.
\tag{20}
\]
Restricting to \(p=q\) kills it identically.  This is the determinant-line reason that every
diagonal quadrant completion loses horizontal orientation.

This character is the complete common-gauge invariant of a rank-one reciprocal flat connection.
Indeed, let nonzero scalar edge coefficients \(a_j,b_j\) satisfy
\[
 a_jb_{j+1}=b_ja_{j+1}.
\tag{21}
\]
Then \(a_j/b_j\) is independent of \(j\).  A change of vertex frame multiplies \(a_j\) and \(b_j\)
by the same coboundary, so the ratio is unchanged.  Conversely, two such systems with the same
ratio are related by a recursively defined common vertex gauge.  Thus finite flatness leaves
exactly one oriented invariant: the anti-diagonal determinant character.  Hermitian
scalarization retains only its positive modulus \(\tau\).

Let
\[
 Q_\rho
 =
 \operatorname{ReRes}_{s=\rho}
 \left(-(s-\tfrac12){\Xi'(s)\over\Xi(s)}\right)
 =
 m_\rho(\tfrac12-\operatorname{Re}\rho).
\tag{22}
\]
Then
\[
\boxed{\qquad
 \log\tau_r(\rho)
 =
 -{2Q_\rho\over m_\rho}\log r.
\qquad}
\tag{23}
\]
The normalized Julia residue, shell-transfer entropy, independent-quadrant Lyapunov exponent,
and relative determinant torsion are four charts of the same charge.

The finite adjoint-mate curvature is the hyperbolic sine of this torsion:
\[
 |\lambda_r(\rho)|^2-|\lambda_r(\rho)|^{-2}
 =
 \tau_r(\rho)-\tau_r(\rho)^{-1}
 =
 2\sinh(\log\tau_r(\rho)).
\tag{24}
\]
Hence mate curvature is not an additional obstruction.  It is the Hermitian linearization of the
anti-diagonal relative torsion.

## The surviving metric obstruction

Flatness does not make the connection metric.  Define
\[
 {\cal N}_j
 =(T_j^+)^*T_j^+-(T_j^-)^*T_j^-
 \quad\text{on }Y_{j+1}.
\tag{25}
\]
For every nontrivial zero,
\[
\left\langle y_{\rho,j+1},{\cal N}_jy_{\rho,j+1}\right\rangle
=
\left(
 |\lambda_r(\rho)|^2-|\lambda_r(\rho)|^{-2}
\right)
\|y_{\rho,j}\|^2 .
\tag{26}
\]
The normalized right side is independent of \(j\), has the sign of
\(\Re\rho-\tfrac12\), and vanishes exactly on the critical line.

Thus the exact geometry is:

```text
connection curvature:
  zero on the full co-Poisson quotient;

Hermitian nonmetricity:
  nonzero and aperture-conserved on every off-line Xi fibre;

ordinary Hilbert closure:
  erases the essential input--output correlation;

all-orders-flat/essential boundary:
  only place where the conserved nonmetric flux can terminate.
```

This explains why more finite commutation, higher cubes, infinite rank, or a stronger ordinary
closure cannot prove RH.  Those structures are already flat.

## Revised RH-bearing open core

`[OPEN CORE — XI_SOURCE_NORMAL_STOKES_BOCKSTEIN_DAGGER_LANDING]`

Construct, before ordinary Hilbert closure, the source-normal exponential completion of the
literal Gamma/co-Poisson/Sonin system and prove a Stokes formula with these exact terms:

1. its finite connection is the operator-flat system `(2)`;
2. its finite source-error primitive is the nondivisive syzygy `(9)`;
3. its determinant boundary character is the relative torsion `(18)`--`(23)`;
4. its Hermitian boundary current is the explicit nonmetricity `(25)`;
5. the computed first-trace essential normal edge maps to `(9)` through one strict morphism of
   source-normal exact couples; and
6. the resulting Bockstein is the full Xi principal conormal and intertwines Riemann inverse
   duality with Hilbert adjunction on every nonzero top multiplicity jet.

Then `(18)` or `(26)` forces
\[
 |\lambda_r(\rho)|=1,
 \qquad
 \Re\rho=\frac12,
\tag{27}
\]
for every nontrivial zero.

The load-bearing theorem is items 5--6.  Naming a completion, declaring the connection pure, or
assuming subexponential evaluator growth would merely restate the missing RH estimate.

## Hostile audit

1. **No RH from flatness.**  Reciprocal characters give flat rank-one systems for arbitrary
   \(\lambda\neq0\).  Equation `(2)` alone cannot force \(|\lambda|=1\).
2. **No RH from torsion language.**  Equation `(18)` computes the missing character; it does not
   prove its unimodularity.  A self-duality which merely pairs \(\rho\) with
   \(1-\overline\rho\) sends \(\tau\) to \(\tau^{-1}\) and permits every off-line pair.
3. **No positivity.**  No sign or order is asserted for `(25)`.
4. **No bounded-lift claim.**  The endpoint maps are contractions, but their inverse-limit lifts
   may grow exponentially.  The parent sharp aperture-type theorem realizes that growth.
5. **Multiplicity is load-bearing.**  Zeroth evaluators need not be complete at multiple zeros.
   The proof uses every confluent jet through order \(m_\rho-1\).
6. **No illicit zero division.**  Equation `(9)` follows by cancelling a common analytic divisor
   in an identity valid on a neighborhood.  It is not obtained by evaluating
   \({\mathfrak K}/\Xi\) at a zero.
7. **Not the mate-curvature factorization.**  The syzygy controls connection-error curvature.
   The Hermitian nonmetricity `(26)` survives.  A claim that `(9)` already proves the
   co-Poisson mate-curvature ideal factorization is false.
8. **Generalized-prime falsifier.**  A generalized-prime model may carry an analogous flat
   reciprocal connection and an external essential reflection correspondence.  The remaining
   theorem must construct the same literal ordinary-integer first-trace/co-Poisson Bockstein and
   its dagger landing; an independently fitted correspondence does not qualify.
9. **No integral-torsion quantization.**  An integral Laurent determinant class may specialize
   to an arbitrary positive real regulator.  Explicitly, multiplication by \(t\) on the integral
   rank-one module over \(\mathbb Z[t,t^{-1}]\) specializes under
   \(t\mapsto p^\alpha\) to determinant modulus \(p^\alpha\) for every real \(\alpha\).
   Integrality quantizes the Laurent exponent, not
   \(\alpha=2\operatorname{Re}\rho-1\).  The terminal audit is
   `../../5-failed/xi-relative-torsion-integral-degree-quantization.md`.

## Categorical sharpening after the essential no-sewing theorem

The all-orders-flat radical theorem proves that fixed finite-Rees morphisms cannot sew the
reflected irregular and vacuum sectors.  This does **not** make an essentially singular operator
the missing object.  The stronger theorem
`../not_new_scientific_knowledge/source-linear-essential-superselection-no-sewing.md` proves that
every closed source-linear operator is zero off the critical line, regardless of essential
growth, and every closed source-linear relation splits.

The only live site is therefore before ordinary closure.  The first-trace corpus computes its
first local chart:
\[
 \bigl((\log p)X_p,\;p\Pi_1^\perp Y_p\bigr)
 \longrightarrow(e_1,Se_1).
\tag{28}
\]
This is a source-normal Bockstein edge, not a bounded boundary operator.  Equation `(9)` is the
literal Gamma/co-Poisson/Sonin target syzygy into which that edge must land.

Consequently the exact construction problem is a morphism of source-normal exact couples
\[
 \Phi_{\rm src}:
 {\mathfrak B}_{\rm first\ trace}
 \longrightarrow
 {\mathfrak B}_{\Gamma/{\rm coP}/{\rm Sonin}}
\tag{29}
\]
defined before divisor specialization, satisfying all four conditions:

1. it sends the computed edge \(e_1\mapsto Se_1\) in `(28)` to the nondivisive source-error
   syzygy `(9)`;
2. action condensation identifies its Bockstein with the full Xi principal conormal, including
   every top multiplicity jet;
3. it intertwines Riemann inverse duality with the source Hilbert dagger on the same relative
   class; and
4. the map remains strict and conormal-faithful through the source-normal exponential completion.

Full-quotient flatness `(2)` means no independent higher-cube curvature remains to be constructed:
all finite higher coherence follows automatically once `(29)` is compatible with the generating
edges.  On a nonzero conormal line, condition 3 identifies the inverse scalar
\(\lambda_r(\rho)^{-1}\) with the adjoint scalar
\(\overline{\lambda_r(\rho)}\), hence
\[
 |\lambda_r(\rho)|=1
 \quad\Longrightarrow\quad
 \operatorname{Re}\rho=\frac12.
\tag{30}
\]

This is the literal specialization of the corpus's
`SOURCE_EFFECTIVE_DAGGER_BECK_CHEVALLEY_LAW`.  The mathematical delta from `(2)` is that the
finite target connection and all of its higher coherence are now closed; only the essential
source-normal Bockstein landing `(29)` remains.  Calling `(29)` an “essential operator,”
“integral torsion,” or “horizon flux” without constructing the exact-couple morphism would hide
the same open theorem.

## Literature boundary

Burnol proves the completeness/minimality and co-Poisson orthogonal-complement input.  Normalized
Mellin covariance and the fact that commuting elementary squares imply path independence are
standard.  Searches of the primary Sonine/co-Poisson literature and arXiv did not locate the
specific operator identity `(2)`, source-error syzygy `(8)`--`(9)`, or their interpretation as
flat connection versus conserved metric defect.  This is preliminary noncollision evidence, not
a priority certificate.

## Lean status

Three of the four interfaces the earlier decision listed as absent are corpus-owned and
unconditional: the extended Sonine space `soninExtendedSpace`, the closed co-Poisson source space
`burnolCoPoissonSourceSpace` with its orthogonal quotient `burnolCoPoissonQuotientSpace`, and the
continuous completed-Mellin evaluation vector `burnolExtendedSoninEvaluationVector` with its Riesz
and reproducing identities.  Only Burnol's **completeness** theorem — the statement that the closed
span of the confluent nontrivial-zero evaluators is the whole quotient — is missing.

What is now unconditional Lean, in
`formal/GaloisForLFunctions/RHTower/GammaCoPoissonSoninQuadrantSection.lean` and
`formal/GaloisForLFunctions/RHTower/GammaCoPoissonSoninQuadrantSyzygy.lean`:

| eq. | statement | Lean |
|---|---|---|
| `(1)` | the two literal quotient maps | `coPoissonQuotientForward`, `coPoissonQuotientInverse` |
| `(3)`--`(5)` | characters, source defect, error vectors | `soninLadderCharacter`, `coPoissonLadderDefect`, `soninLadderKernel_eq_add_defect` |
| `(4)` | the exact off-divisor factorization | `coPoissonQuotientForward_ladderKernel_offDivisor`, `coPoissonQuotientInverse_ladderKernel_offDivisor` |
| `(6)` | the two-path commutator `K_j` | `coPoissonQuotientCommutator` |
| `(7)` | the exact off-divisor source-error syzygy | `coPoissonQuotientCommutator_ladderKernel_offDivisor` |
| `(10)`--`(12)` | `K_j` kills every zeroth zero evaluator | `coPoissonQuotientCommutator_ladderKernel_eq_zero` |
| `(17)`--`(18)` | the anti-diagonal relative torsion `tau_r(rho) = abs(lambda)^2` | `norm_coPoissonQuotientForward_div_inverse_ladderKernel` |
| `(21)` | the complete gauge invariant of a rank-one reciprocal flat system | `ratio_eq_of_flat_reciprocal_edges`, `ratio_const_of_flat_reciprocal_edges` |

`(7)` is proved without any hypothesis on `w`, and is strictly sharper than the card's version: the
error terms are the literal source projections `P_k k_{w,k}`, with the two reciprocal characters
cancelling identically, so no multiplier `Lambda_k` and no local anti-holomorphic factorization is
used.  On the annihilator boundary those projections vanish
(`coPoissonLadderDefect_eq_zero_of_annihilator`), which is `(10)`--`(12)` at `ell = 0`.

### The exact remaining Lean input for `(2)`

The boxed operator identity `(2)` needs exactly one further theorem:

```text
closure (span {confluent evaluators at co-Poisson annihilator points}) = burnolCoPoissonQuotientSpace b
```

that is, Burnol's completeness/minimality theorem for the two systems attached to the zeros.  The
corpus's cyclicity theorem `isCyclicFamily_burnolCoPoissonQuotientEvaluationFamily` is *not* a
substitute: it uses the evaluators at **all** regular points, where `(7)` shows `K_j` is exactly the
nonzero source-error expression.  Indeed `(2)` and the syzygy `(8)` are equivalent given `(7)`, so
no rearrangement of the finite-level algebra can prove either.

Once that theorem exists, `(2)` follows from `coPoissonQuotientCommutator_ladderKernel_eq_zero`
together with its confluent jets and boundedness of `K_j`; `(8)` is then a substitution back into
`(7)`, `(9)` is local cancellation, and `(13)`--`(15)` follow from `(2)` by adjacent transpositions.

## Gates

- [x] operator square and source-error syzygy stated on literal quotient maps
- [x] confluent-jet multiplicity audit
- [x] full-quotient flatness paper-proved from Burnol completeness
- [x] all finite higher coherence derived
- [x] anti-diagonal relative torsion and its exact charge calibration proved
- [x] connection flatness separated from Hermitian nonmetricity
- [x] preliminary primary-literature noncollision search
- [ ] construct the strict source-normal exact-couple morphism `(29)`
- [ ] identify its Bockstein with the full Xi conormal and prove dagger naturality
- [x] Burnol Sonine/co-Poisson/evaluation interfaces available in Lean (corpus-owned)
- [x] formalize `(1)`, `(3)`--`(7)`, `(10)`--`(12)`, `(17)`--`(18)`, `(21)` unconditionally
- [ ] formalize Burnol completeness (closed span of confluent zero evaluators = quotient) and hence `(2)`, `(8)`, `(9)`, `(13)`--`(15)`
- [ ] RH

## Bilateral source-covariance reduction

The pre-divisor source layer now gives an unconditional stronger simplification. Both normalized
dilation orientations send the literal closed co-Poisson source at aperture `a` into the source at
`a/r`. Hilbert adjunction therefore sends the quotient source-orthogonal at `a/r` back into the
source-orthogonal at `a`. Consequently, on the actual quotient domain,

```text
E_a (U_r y)      = P_a (U_r y)
E_a (U_r^* y)    = P_a (U_r^* y),       y in Y_(a/r),
```

where `E_a` is the co-Poisson quotient projection and `P_a` the plain extended-Sonin projection.
Lean proves these as `coPoissonQuotientInverse_eq_soninProjection_of_mem_next` and
`coPoissonQuotientForward_eq_soninProjection_of_mem_next` in
`BurnolCoPoissonQuotientDilationCollapse.lean`.

This deletes the co-Poisson source-projection correction from both physical Gamma orientations.
The exact-couple morphism `(29)` must now identify the first-trace edge with one pure Sonin
aperture-leakage Bockstein and prove inverse/dagger equality there. Burnol completeness is still
needed for the full operator-flatness statement `(2)`, but it is not needed for this reduction.

## Sharpening of the remaining input for `(2)`

`GammaCoPoissonSoninQuadrantZeta.lean` now proves, unconditionally, that a co-Poisson annihilator
character in the right half-strip is a zeta zero:

```text
riemannZeta_eq_zero_of_burnolCoPoissonAnnihilatorPoint
```

because Burnol's explicit indicator source is an unconditional inhabitant of the source layer and
its completed Mellin evaluation carries the factor `zeta(w)` times a factor nonzero on the open
strip for aperture `< 1`.

### What the missing theorem actually is

Burnol's own statements (Burnol, *Two complete and minimal systems associated with the zeros of the
Riemann zeta function*, J. Théor. Nombres Bordeaux 16 (2004) 65--94) fix the target exactly.  With
`L_a` the extended Sonine space at aperture `a`, `Y_a` the closed span of the zero evaluators
`Y_{a,rho,k}` (`0 <= k < m_rho`), and `P_a` the co-Poisson subspace (`0 < a < 1`):

> **Theorem 3.1.**  The vectors `Y_{a,rho,k}` are a minimal system in `L_a` if and only if `a <= 1`,
> and a complete system if and only if `a >= 1`.  **For `a < 1` the perpendicular complement to
> `Y_a` is the co-Poisson subspace `P_a`.**

That last clause is precisely the input `(2)` needs: for `0 < a < 1`,

```text
closure (span {Y_{a,rho,k}}) = P_a^perp ∩ L_a = burnolCoPoissonQuotientSpace a.
```

Burnol attributes its proof to *Entrelacement de co-Poisson*, Chap. 6, Theorems 6.24--6.25.

The evaluators exist at **every** zero, on and off the critical line, and not through the
absolutely convergent integral the corpus currently uses.  The reason is

> **Proposition 2.2** (Burnol, from *Entrelacement de co-Poisson* 6.10).  For `f` in `L_a` the
> completed right Mellin transform `M(f)(s) = pi^{-s/2} Gamma(s/2) f^(s)` is meromorphic on the
> whole plane with at most poles at `0` and `1`; the evaluations `f |-> M(f)^{(k)}(w)` for
> `w != 0,1` are continuous linear forms on `L_a`; and `M(F_+ f)(s) = M(f)(1-s)`.

This matters because the corpus's `burnolExtendedSoninEvaluationVector` is built from an absolutely
convergent integral and therefore exists only for `Re w != 1/2`.  Under RH every nontrivial zero is
on the line, so a completeness statement phrased only with the corpus's present evaluators would
have an empty index family and be *false* (the quotient is not trivial).  The continuation, not a
limiting construction, is what supplies the critical-line evaluators.

### The Lean sub-targets, in order

1. **meromorphic continuation.**  For `f` in `soninExtendedSpace a`, `M(f)` is meromorphic on `ℂ`
   with poles only at `0` and `1`.  (Burnol Prop. 2.2; the corpus already has the constant-head
   splitting `G(s) = -c(g) a^{1-s}/(s-1) + int_a^infinity g t^{-s} dt` used in his Theorem 4.8.)
2. **evaluator vectors at every point.**  Continuity of `f |-> M(f)^{(k)}(w)` on
   `soninExtendedSpace a`, hence a Riesz vector `Y_{a,w,k}` for every `w != 0,1` --- in particular
   on the critical line.
3. **the functional equation** `M(F_+ f)(s) = M(f)(1-s)` on `soninExtendedSpace a`
   (the corpus has `soninMellinEvaluation_fourier` under integrability hypotheses; it must be
   upgraded to the whole space via the continuation).
4. **the perpendicular-complement theorem** for `0 < a < 1`:
   `closure (span {Y_{a,rho,k} : zeta rho = 0}) = burnolCoPoissonQuotientSpace a`.

Only then does `coPoissonQuotientCommutator_ladderKernel_eq_zero` (already proved) plus its
confluent jets give `(2)`; `(8)` is then a substitution back into `(7)`, `(9)` is local
cancellation, and `(13)`--`(15)` follow from `(2)` by adjacent transpositions.

### First brick of sub-target 1

`formal/GaloisForLFunctions/RHTower/BurnolSoninMellinHeadTail.lean` (axiom-clean, umbrella
registered) proves the starting identity of Burnol's Theorem 4.8:

```text
integral_Ioc_soninMellinKernel        -- int_(0,a] t^(-w) dt = a^(1-w)/(1-w)  for Re w < 1
soninMellinEvaluation_head_tail       -- M(f)(w) = P(w) * ( c * a^(1-w)/(1-w) + int_a^infinity f t^(-w) dt )
```

The head term is already meromorphic on the whole plane with its only singularity the simple pole at
`w = 1`, so the entire analytic burden of the continuation sits on the tail integral.  The tail
converges absolutely for `Re w > 1/2`, which continues `M(f)` to `{Re w > 1/2} \ {1}`; crossing the
critical line needs Burnol's entire functions `C_a(u, 1-s) = F_+(1_{t>a} t^{-s})(u)` from
*Sur les "espaces de Sonine" associés par de Branges à la transformation de Fourier*, which is the
next brick.
