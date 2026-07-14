# The ordered Sonin prime-pair seam is one exterior tensor

- **ID:** `sonin-prime-seam-exterior-factorization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN OPERATOR SIMPLIFICATION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `sonin-two-particle-prime-coherence.md`;
  `xi-prime-seam-pair-asymptotics.md`
- **Lean status:** the one-particle Euler corners, the arithmetic normalized-energy endpoint, and
  the full finite zero-diagonal Gram-matrix compression modulo compacts are formalized.  Its exact
  reciprocal-prime weighted-difference specialization proves `(8d)`--`(8e)` in Lean and removes
  the Hilbert tensor product from the route.

## Statement

Let `C_p` be the positive Euler-normalized one-prime Sonin corner and let `a_p` be arbitrary complex
prime potentials.  For a finite prime set `F`, define the two one-particle sections

```text
A_F(a)=sum_(p in F)a_p C_p,
B_F   =sum_(p in F)    C_p.                                 (1)
```

The ordered two-particle difference section

```text
W_F(a)=sum_(p,q in F)(a_p-a_q)(C_p tensor C_q)              (2)
```

has the exact exterior factorization

```text
W_F(a)=A_F(a) tensor B_F-B_F tensor A_F(a).                 (3)
```

Thus the complete pair coboundary is a decomposable rank-two exterior tensor, not an irreducible
double-prime operator family.

The paper-proven ordered-pair Sonin Calkin estimate gives, for every compact operator `K`,

```text
sqrt(E_F(a)) <= ||W_F(a)-K||,                               (4)
E_F(a)=sum_(p,q in F)|a_p-a_q|^2/(p q).                    (5)
```

For the canonical Xi seam potentials

```text
a_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho))),               (6)
```

put

```text
D_F^wedge(rho)=dist(W_F(a(rho)), compact operators),
M_F=sum_(p in F)1/p.                                       (7)
```

Then the formalized arithmetic endpoint proves

```text
D_F^wedge(rho)=o(sqrt(M_F))
  -> E_F(rho)/M_F -> 0
  -> Re(rho)=1/2.                                          (8)
```

Imposing `(8)` on every actual Xi divisor fibre implies RH.

## One-particle Gram replacement

The tensor carrier is unnecessary.  Let `L_p` denote the unweighted Sonin dilation corner and put

```text
D_F(a)_(p,q)=(a_p-a_q)/sqrt(pq),
G_F(a)=sum_(p,q in F)D_F(a)_(p,q)L_p^*L_q.                (8a)
```

The diagonal of `D_F(a)` is zero.  The common paired-shell construction now proves in Lean that,
for every finite coefficient vectors `x,y` and every compact `K`,

```text
|<y,D_F(a)x>|
 <= ||y||_2 ||x||_2 ||G_F(a)-K||.                        (8b)
```

Equivalently, the complete finite matrix operator norm survives in the Calkin quotient:

```text
||D_F(a)x||_2 <= ||x||_2 ||G_F(a)-K||.                   (8c)
```

Take `x_p=p^(-1/2)`.  If `M_F=sum_p 1/p`, the elementary weighted-variance identity gives

```text
||x||_2^2=M_F,
||D_F(a)x||_2^2=M_F E_F(a)/2.                            (8d)
```

Therefore

```text
sqrt(E_F(a)/2) <= dist(G_F(a), compact operators).       (8e)
```

The factor `sqrt(2)` lost relative to `(4)` is immaterial for the submass endpoint.  Thus the
top-down operator chain can be run entirely on the original one-particle Sonin Hilbert space:

```text
dist(G_F(a(rho)),K)=o(sqrt(M_F))
 -> E_F(rho)/M_F -> 0
 -> Re(rho)=1/2
 -> RH on all Xi divisor fibres.                         (8f)
```

The operator in `(8a)` has the source factorization

```text
G_F(a)=L_conj(a)^* L_1-L_1^* L_a,                       (8g)
L_a=sum_p a_p p^(-1/2)L_p,
L_conj(a)=sum_p conj(a_p)p^(-1/2)L_p.
```

It is a one-particle Gram coboundary between the universal section and the two Schwarz-related
weighted sections.  No analytic Hilbert tensor-product API or two-particle compactness theorem is
needed.

## Proof

Expand the right side of `(3)`:

```text
A_F tensor B_F
 =sum_(p,q)a_p(C_p tensor C_q),

B_F tensor A_F
 =sum_(p,q)a_q(C_p tensor C_q).
```

Subtracting gives `(2)` term by term.  The diagonal coefficients vanish automatically.  Apply the
ordered-pair version of the tensor-square Calkin estimate in
`sonin-two-particle-prime-coherence.md` with coefficient `b_(p,q)=a_p-a_q`; this is exactly `(4)`.
Divide its square by `M_F` and use the Lean theorem

```text
E_F(rho)/M_F -> 2 S(rho),
S(rho)>0 off the critical line,
```

to obtain `(8)`.

## Top-down simplification

The prior source problem asked for a two-particle construction carrying every prime-pair
coefficient separately.  Equation `(3)` removes that algebraic realization gap.  It is enough to
construct the two canonical one-particle sections `(1)` on the same source carrier and control
their exterior tensor.

The tensor formulation states the missing source theorem as asymptotic Calkin collinearity:

```text
A_F(a(rho)) wedge B_F
   =o_Calkin(sqrt(M_F)).                                    (9)
```

Here `B_F` is the universal unweighted positive Euler direction and `A_F` is its horizontally
reflected Xi-seam weighting.  The obstruction is therefore a failure of these two source sections
to become projectively parallel.  This is a constraint statement; no dilation orbit is being used
as a generative flow.

The factorization also exposes the rank-one mean channel in the scalar variance identity.  The
normalized pair energy is the squared distance of `A_F` from the scalar direction generated by
`B_F`, measured in the reciprocal-prime coefficient Hilbert geometry.  The operator theorem sought
in `(9)` should consequently be a source-defined projective/exterior estimate, not a collection of
independent pairwise cancellations.

The sharper one-particle formulation is the upper estimate in `(8f)`.  It is strictly easier to
formalize and test: the lower estimate `(8e)` is already reduced to the existing common-shell Gram
compression, and the remaining source problem concerns one concrete zero-diagonal Gram coboundary
on the original Sonin carrier.

## Direct finite-pair alternative

The later formal Calkin criterion removes even the cofinal norm rate if one can extract the
zero-dependent seam from a completed finite-place source.  For every positive aperture and every
pair of primes `p,q`, Lean proves

```text
essentialNorm((a_p(rho)-a_q(rho)) L_p^*L_q)
 =|a_p(rho)-a_q(rho)|/sqrt(pq),                              (10)

(a_p(rho)-a_q(rho)) L_p^*L_q is compact
 <-> a_p(rho)=a_q(rho).                                     (11)
```

Consequently the following source theorem would already close the route without any
prime-cutoff-uniform estimate:

```text
for every Xi divisor rho and every prime pair p,q,
the completed prime--Gamma source realizes
(a_p(rho)-a_q(rho)) L_p^*L_q modulo compact operators.       (12)
```

If the completed representative in `(12)` is compact, `(11)` gives pairwise coherence.  The
formal cofinal-decay theorem then forces the common charge to be zero, and the orientation-energy
criterion gives RH.

`[OPEN ALTERNATIVE]` The finite quasi-inner theorem does not by itself prove `(12)`.  It proves
compactness only after the prime and its allocated Gamma component have been multiplied.  An
individual nonarchimedean ratio is not quasi-inner, and the Gamma component carries the
noncompact counterterm.  The missing value relation is therefore an exact **Calkin extraction**:
differentiate, polarize, or take a relative coboundary of the completed finite product in a way
whose zero-dependent FE--Schwarz coefficient is `(a_p(rho)-a_q(rho))` and whose remaining Gamma
term is compact.  This is a finite exact identity problem, not a cofinal rate problem, but its
conclusion must not be assumed by separating the locally noncompact factors before completion.

The finite alternative also eliminates the residual estimates from its open core.  At each fixed
prime Lean proves that the full Sonin Gram minus its principal Gram is Hilbert--Schmidt, with the
principal--residual linear cross itself Hilbert--Schmidt.  Therefore any exact finite completed-source
identity for the **full** two-prime coboundary descends automatically to `(12)` in the Calkin
quotient.  Only the completed-source value relation is missing; the residual and mixed terms need
new uniform estimates only in the cofinal-rate branch `(8f)`.

`[PARTLY DISCHARGED — FINITE TANGENT-CURVATURE PRODUCER]` Introduce independent real Euler
parameters `t_p,t_q` in the two local ratios while retaining the archimedean completion.  The
companion theorem `semilocal-euler-kernel-chart-differentiability.md` now proves that the resulting
semilocal kernel is exactly the image of the archimedean Sonin space under the invertible finite
Euler denominator.  Its orthogonal projection `P(t_p,t_q)` is operator-norm real analytic at the
empty Euler parameter.  Its second-fundamental forms are the one-sided Mellin dilation corners,
and the derivative of the pullback metric is exactly the full positive Euler dilation corner:

```text
B_p=(1-P)(partial_p P)P=-(1-P)M_(p^(-z))P,

(1-P) partial_p(M_t^*M_t)|_0 P
  =-(1/sqrt(p))(1-P)(U_p+U_p^(-1))P.                       (13a)
```

Thus norm differentiability, finite operator transfer, and identification with the actual Sonin
corner are closed; passage to the formal principal corner is already Hilbert--Schmidt modulo the
existing residual theorem.  What remains conjectural is the **zero-fibre compact curvature** or
polarization identity

```text
B_conj(a)^* B_1-B_1^* B_a
 = sum_(r,s in {p,q})
     (a_r(rho)-a_s(rho))/sqrt(rs) L_r^*L_s  modulo compacts. (13)
```

Compactness of the completed curvature would make the right side compact, and the formal two-prime
Gram compression would force `a_p(rho)=a_q(rho)`.

The remaining statement cannot follow from finite quasi-innerness alone.  The finite Euler chart
contains no Xi divisor point, while `(13)` is required only on actual zero fibres.  The missing
input is now a global source--divisor value relation: the Xi-zero radical or zeta-cycle evaluator
must annihilate the tangential connection term in the primal--dual semilocal pairing, leaving the
normal Gram coboundary compact.  Burnol's zero-indexed Sonine evaluators and the Connes spectral
realization supply the two literature ends of this interface, but their identification with the
semilocal connection is not proved in the literature or the corpus.

The formal theorem
`../../3-formalized/not_new_scientific_knowledge/cofinite-euler-connection-reader-rigidity.md`
now discharges the infinite-dimensional propagation in this paragraph.  Compactness on every
cofinite prime-tangent pair propagates automatically to any continuous real-bilinear connection
reader on the full analytic FE-odd Schwarz source fibre, and mixed derivatives of compact
two-parameter families are compact.  Thus the remaining statement is the finite operator value
relation identifying the prime-pair normal curvature in `(13)` with the mixed derivative of the
completed quasi-inner Hardy block, modulo the already controlled compact residual terms.

## Literature boundary

Equation `(3)` is the standard bilinearity identity `A wedge B=A tensor B-B tensor A`; `(4)` is the
existing paper-proven Sonin tensor lower estimate.  The synthesis is useful but is not scientifically
new.

Connes--Consani's
[*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974) supplies nonlinear
finite-place archimedean compensation, but it does not prove the projective cofinal rate `(9)`.
Connes--Consani--Moscovici's
[*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423) supplies stable semilocal
Sonin spaces, but no asymptotic exterior-collinearity theorem for the two sections `(1)` was located.

The formal continuation `xi-prime-seam-euler-zero-tangent.md` closes the scalar coefficient part:
the horizontal seam is exactly the derivative at local parameter zero of an explicit FE-paired
finite Euler flux, both pointwise and in the compact-carrier Banach algebra.  It now also closes the
scalar tangent-chart comparison.  The actual `a=1` tangent equals the empty `a=0` coefficient plus
the explicit Lambert tail

```text
sum_(m>=2)m log(p)p^(-ms),
```

with FE pairing applied termwise.  Thus no unknown value relation remains between the two scalar
charts.

The wider paper corpus sharpens the operator choice.  The one-prime quasi-inner defect has a
nonzero prime-dependent Dixmier residue, and the Gauss-paired `m`-prime channel system has critical
weak-Schatten depth `2m` (subject to the recorded independent audit of the residue theorem).
Consequently separate-channel compactness cannot give a cutoff-uniform fixed Schatten estimate.
On the positive side, the finite-product quantized-differential identity retains every local Weil
term linearly after legitimate trace-class smoothing, and the exact logarithmic-position
commutator produces the missing orbital factor `log(p^m)` before Sonin compression.  Lean already
proves the correct coordinate identity

```text
[log|x|,U_p]=-log(p)U_p
```

and the resolvent dressing of a bounded commutator through the exact Sonin intersection projection.
Thus a plausible completed-source mechanism must use a common Mellin-scattering form graph for
`[M_t,J_log]`, the Euler leakage, and the Burnol conductor, or prove a source-defined covariance
cancellation in the full multiplicative product.  Hartman--Peller compact/Schatten theory provides
the correct symbol-space language for testing such a cancellation, but no located theorem supplies
the required prime-cutoff-uniform exterior norm rate.

## Residual covariance is already uniformly trace class

The coupled all-prime residual column closes one further part of the operator upper estimate.  Let
`C_a` be the Hilbert--Schmidt column whose prime-power component is the weighted
principal-subtracted Sonin residual `R_alpha`, and let `D_b` be diagonal multiplication by an
arbitrary bounded charge field `b_alpha` on the prime-power output space.  Then

```text
T_a=C_a C_a^* is trace class,
[D_b,T_a] is trace class,
||[D_b,T_a]||_1 <= 2 ||b||_infinity ||C_a||_2^2.          (20)
```

Indeed, the trace ideal is two-sided and

```text
[D_b,C_a C_a^*]=D_b C_a C_a^*-C_a C_a^*D_b.
```

Both terms have trace norm at most `||b||_infinity ||C_a||_2^2`.  In the canonical prime-power
block decomposition, the `(alpha,beta)` block of `(20)` is exactly

```text
(b_alpha-b_beta) R_alpha R_beta^*.                        (21)
```

Thus the complete antisymmetric Gram coboundary made from two residual legs is not part of the
cofinal obstruction: it has a cutoff-independent trace-class realization.  Lean already proves
the load-bearing inputs `soninAllPrimeColumnOperator_isHilbertSchmidt`, the exact cross-overlap
block formula, and summability of all cross-overlap Hilbert--Schmidt energies in
`SoninCoupledPrimeResidual.lean`.

This reduction does not apply to the desired principal seam Gram by deleting the principal shell.
After writing each local corner as `L_alpha=P_alpha+R_alpha`, it removes only the `R^*R`
antisymmetric covariance.  The remaining source theorem must control the `P^*P` coboundary and
the two principal--residual crosses, with their cancellation performed inside the completed
prime--Gamma product.  Those are precisely the grades not assembled by the positive residual
operator.

`[OPEN CORE]` Transfer the empty-parameter Euler tangent functorially to the Schwarz-related
one-particle sections in `(8g)` and prove that their explicit higher-grade Lambert tail has
sufficiently small **Gram-coboundary Calkin image**, while retaining the global Poisson
normalization; equivalently prove the upper estimate in `(8f)` without using Xi zero locations.
The paper-proven critical all-grade corona theorem kills the same tail in the Marcinkiewicz
quotient, but this is not a Calkin theorem: each principal prime-power Sonin corner has nonzero
essential norm and only its principal-subtracted residual is Hilbert--Schmidt. Finite
quasi-innerness alone is insufficient because it controls the nonlinear completed product at each
finite `F`, not this cofinal first-Euler Gram coboundary.

## Gates

- [x] exact exterior-tensor factorization
- [x] ordered tensor lower estimate imported from the paper-proven parent
- [x] composition with normalized pair-energy asymptotics
- [x] top-down replacement of pairwise realization by one exterior tensor
- [x] replace the tensor-square estimate by the one-particle common-shell Gram compression
- [x] formalize the full finite matrix-vector Calkin lower estimate without cardinality loss
- [x] package the reciprocal-prime difference-matrix specialization `(8d)`--`(8e)` in Lean
- [x] source realization of the scalar seam coefficients as finite Euler first coefficients
- [x] exact scalar comparison of the empty and actual Euler tangent charts
- [x] uniform trace-class control of the pure residual antisymmetric covariance
- [x] exact analytic finite Euler chart of the completed semilocal Sonin kernel
- [x] operator-norm differentiability of its orthogonal projection at the empty parameter
- [x] exact metric-tangent identification with the actual positive Euler Sonin corner
- [x] finite bounded operator transfer of the scalar seam coefficients
- [x] cofinite Euler-tangent-pair compactness propagates to the complete analytic source fibre
- [x] finite compact semilocal families have compact iterated mixed derivatives
- [ ] alternatively, finite completed-source Calkin extraction `(12)` for every prime pair
- [ ] prove Xi-zero-fibre annihilation of the semilocal tangential connection
- [ ] prove the remaining compact normal-curvature identity `(13)`
- [ ] Gram-coboundary Calkin control of the principal and principal--residual Lambert tail
- [ ] source-pure one-particle upper estimate in `(8f)` (equivalently tensor collinearity `(9)`)

## Phase-polarized constraint reduction

The formal theorem
`../../3-formalized/not_new_scientific_knowledge/semilocal-projection-phase-polarization.md`
removes the algebraic mismatch between the symmetric mixed curvature in `(13)` and the
antisymmetric Sonin seam Gram.  At a self-adjoint base projection `P`, the canonical quarter-turn

```text
J_P(D)=i((1-P)DP-PD(1-P))
```

is a self-adjoint projection tangent whose normal corner is `i(1-P)DP`.  Therefore a
phase-polarized two-parameter idempotent family satisfies the exact identity

```text
P D_st P=-i(B_t^*B_D-B_D^*B_t).                           (22)
```

Only compactness of the compressed mixed derivative `P D_st P` is needed to make the oriented
normal Gram compact; neither the full mixed derivative nor the full family relative to `P` must be
compact.  For a complex seam packet, apply `(22)` separately to its real and imaginary weighted
Euler directions and recombine the two skew Grams.

`[OPEN CORE — SHARPENED]` Construct those two phase-polarized directions inside the completed
finite prime--Gamma semilocal family and prove that their base-compressed mixed derivatives are
compact on actual Xi zero fibres.  The phase rotation is now unconditional algebra; the remaining
input is precisely the completed source--divisor value relation and its compact cancellation.
