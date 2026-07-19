# Cofinal prolate--boundary Weil relative normal-form conjecture

- **ID:** `cofinal-prolate-boundary-weil-relative-normal-form-conjecture`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[OPEN RH CORE]`
- **Scientific status:** `[FRONTIER CONJECTURE] [ANTI-THEATRE PASS 2026-07-19]`
  `[IMPLIES RH] [NOT PROVED]`
- **Parent results:** the constrained-prolate fixed-mode spectral ladder, the positive/negative
  Fourier parity separation, the radial leakage Toeplitz law, the exact true-aperture metric and
  its Möbius frame bounds, and the polar--prime critical-Mellin defect formula.
- **Statement:** Every loss of coercivity of the full restricted Weil form is exhausted by a
  source-selected prolate Toeplitz ladder and translated two-edge boundary profiles; after these
  two channels are removed, the remainder is coercive at the next prolate leakage scale.

## Why this is the frontier conjecture

The 2025 Connes--Consani--Moscovici construction leaves two spectral assertions open: the true
semilocal ground state should be simple and of positive Fourier parity, and the constrained prolate
seed should approximate it strongly enough to transport the determinant to `Xi`.  The local corpus
now proves the complete fixed-depth source model behind those assertions:

```text
constrained prolate ladder
  + lambda^8 adjacent scale separation
  + lambda^(-4) positive/negative parity separation
  + explicit radial Toeplitz cross law with floor 1/2.
```

None of those fixed-depth facts controls a negative vector escaping through higher modes.  Conversely,
merely conjecturing that the restricted Weil form is nonnegative is exactly the Weil criterion and
contains no new mechanism.  The conjecture below inserts the missing scientific content between
those two statements: it predicts an explicit normal form and a quantitative localization law for
every possible nonpositive state.

## Prolate data and the source-only cofinal depth

Let `sigma` be `+` or `-`.  In the positive sector use the prolate indices `4j`; in the negative
sector use `4j+2`.  Under the Poisson--Müntz intertwining these become the two orthogonal inversion
parities of the aperture space, and the restricted Weil form reduces their direct sum.  Let

```text
C_(lambda,sigma) v_(j,lambda,sigma)
  =mu_(j,lambda,sigma) v_(j,lambda,sigma),

0<mu_(0,lambda,sigma)<mu_(1,lambda,sigma)<...<1           (PN1)
```

be the zero-integral constrained prolate leakage operator and its normalized eigenvectors.  Put

```text
k_(j,lambda,sigma)
  =R_lambda E(v_(j,lambda,sigma))                         (PN2)
```

in the true semilocal aperture Hilbert space.  These vectors are source-defined and do not use a
zeta zero, a Weil eigenvector, or a finite determinant zero.

For a fixed depth `J`, let `e_(J,sigma)(lambda)` be the maximum of the following **prolate-only**
errors for indices at most `J`:

1. the relative Fuchs leakage errors;
2. the Hermite-limit errors of the zero-integral constraint coordinates;
3. the bounded-Lipschitz errors of every normalized radial cross-leakage measure.

The proved fixed-depth results give

```text
e_(J,sigma)(lambda)->0             for every fixed J.     (PN3)
```

Define the activation scale and safe depth by

```text
Lambda_(J,sigma)
 =min{m in N : m>=J and
       sup_(lambda>=m)e_(J,sigma)(lambda)<=2^(-J)},

J_sigma(lambda)
 =max{J : Lambda_(J,sigma)<=lambda},                     (PN4)
```

with value zero before the first activation scale.  The minimum exists by `(PN3)`, and
`Lambda_(J,sigma)>=J` makes the maximum finite.  Then `J_sigma(lambda)->infinity`.  This
diagonal selector is completely determined by the prolate operator.  In particular it cannot be
chosen after inspecting `Xi`, the prime defect, or the spectrum of the restricted Weil operator.
An effective uniform PSWF estimate may later replace `(PN4)` by an explicit growth law.

## Explicit low-energy normal form

Put

```text
L_lambda=log(2*pi*lambda^2),
D_(lambda,sigma,J)
 =diag(sqrt(mu_(0,lambda,sigma)),...,sqrt(mu_(J,lambda,sigma))). (PN5)
```

Let

```text
D_r=1/pi integral_0^(pi/2)
      H_(floor(sec theta)) cos(4r theta)d theta,
T_J=(D_|i-j|)_(0<=i,j<=J).                               (PN6)
```

The radial law already proves

```text
T_J >=(1/2)I                 for every finite J.          (PN7)
```

Let `Q_(lambda,sigma,J)` be the Gram matrix of the **full intact restricted Weil form** on the
vectors `(PN2)`, and let `S_(lambda,sigma,J)` be the diagonal matrix of their endpoint orientation
signs.

### Part I: cofinal Toeplitz congruence

`[CONJECTURE]` At `J=J_sigma(lambda)`,

```text
|| T_J^(-1/2) [
     L_lambda^(-1) D^(-1) S Q_(lambda,sigma,J) S D^(-1)-T_J
   ] T_J^(-1/2) ||_op ->0                                  (PN8)
```

for both parities.  Unlike the proved fixed-depth regular-channel theorem, `(PN8)` is uniform at a
growing depth and contains the unsplit polar--prime critical-Mellin graph defect.

## Part II: prolate--boundary concentration compactness

For every fixed smooth profile `f` supported in `(0,L)`, define the two inversion-parity edge
packets

```text
b_(a,+,f)(x)=f(a-|x|),
b_(a,-,f)(x)=sign(x)f(a-|x|).                                (PN9)
```

The proved boundary saturation theorem shows that their leading prime frame energy cancels the
polar level for an infinite-dimensional profile space.  The proved Landau theorem shows that the
same packets detect every off-line divisor.  They therefore cannot be placed in an unnamed
coercive complement.

Let `B_a` and `m_a` be the exact frame and level from

```text
QW_a(u,u)=||B_a u||^2-m_a||u||^2.                            (PN10)
```

`[CONJECTURE: UNIVERSAL PROFILE LAW]` Let `a_n->infinity`, let `u_n` have one fixed inversion
parity, and suppose

```text
||u_n||=1,
sup_n ||B_(a_n)u_n||^2/m_(a_n)<infinity.                     (PN11)
```

After passage to a subsequence, `u_n` has a profile decomposition

```text
u_n
 =K_(lambda_n,sigma)c_n
  +sum_r b_(a_n-tau_n^(r),sigma,f_r)
  +r_n+o_H(1),                                               (PN12)
```

where:

1. `K_(lambda_n,sigma)c_n` lies in the source-selected Fuchs-safe span of `(PN2)` at the depth
   `(PN4)`;
2. the nonzero boundary profiles satisfy
   ```text
   0<=tau_n^(r)<a_n,
   |tau_n^(r)-tau_n^(s)|->infinity for r!=s;                 (PN13)
   ```
3. the profile masses are square-summable and exhaust the lost Hilbert norm;
4. the remainder `r_n` is profile-free and obeys a uniform bulk estimate;
5. Hilbert norm, frame energy, and the intact Weil form admit a common asymptotic decoupling.

More precisely, after orienting the prolate coordinates by `S`, the Weil energy has the normal form

```text
QW_(a_n)(u_n,u_n)
 =L_(lambda_n)c_n^*D_n T_(J_n)D_n c_n
  +sum_r BoundaryQW_(a_n-tau_n^(r),sigma)(f_r)
  +QBulk_n(r_n)+o(E_n),                                      (PN14)

QBulk_n(r_n)
 >=c_* L_(lambda_n)mu_(J_n+1,lambda_n,sigma)||r_n||^2,       (PN15)
```

for one universal `c_*>0`.  Here `E_n` is the sum of the positive prolate reference energy, the
boundary frame scales `m_(a_n-tau_n^(r))||f_r||^2`, and the bulk reference energy.  The boundary
term is not an abstract remainder: it is exactly

```text
BoundaryQW_(A,sigma)(f)
 =Q_Gamma(b_(A,sigma,f),b_(A,sigma,f))
  +2 Re integral_0^(2A) C_(b_(A,sigma,f))(h)dR(h).            (PN16)
```

Equation `(PN16)` retains the critical-Mellin carrier and its prime-divisor poles.  It may not be
replaced by its prime-number-theorem main term.

The new universal assertion is the **exhaustion clause** in `(PN12)`--`(PN15)`: constrained
prolate profiles and recentered two-edge profiles are the only two defects of compactness of the
semilocal Weil frame.  There is no fourth low-energy escape geometry.

## Exact RH-bearing theorem after the normal form

The profile law does not relabel the remaining sign as novelty.  Once `(PN8)` and
`(PN12)`--`(PN15)` are proved, the full no-negative-birth problem reduces to the single
source-orientation theorem

```text
BoundaryQW_(A,sigma)(f)>=0
for every A>0, both parities, and every smooth compact profile f. (PN17)
```

The positive-parity case on the canonical two-edge family is already known internally to be
equivalent to RH.  Thus `(PN17)` is the actual arithmetic estimate, not a claimed new criterion.
What the conjectural normal form adds is a universal theorem saying that **there is nothing else
to estimate**.

If `(PN17)` is proved directly from the Euler--Gamma--polar source, then `(PN7)`, `(PN14)`, and
`(PN15)` exclude every negative spectral sequence; nested-aperture exhaustion gives RH.  The
`lambda^(-4)` parity separation and `lambda^8` adjacent ladder then identify the surviving
positive-parity near-radical direction and its canonical Toeplitz--Schur correction.  The weighted
PSWF graph-rate theorem remains the additional input for the determinant version of the Connes
construction.

## Anti-theatre test

This card is killed, not promoted, if any of the following occurs.

1. **Fixed-depth collapse.**  A proof establishes `(PN8)` only for each fixed `J`; that theorem is
   already in the corpus and does not control spectral escape.
2. **RH renaming.**  The proof of the structural normal form `(PN8)`, `(PN12)`--`(PN15)` uses the
   Weil criterion, absence of off-line zeros, positivity of the true restricted form, or an
   equivalent RH estimate.  The RH-bearing boundary sign `(PN17)` is deliberately separate.
3. **Post-hoc depth selection.**  `J(lambda)` depends on `Xi` zeros, Weil eigenvalues, determinant
   zeros, or the sign of `QW_lambda`.  Only the prolate selector `(PN4)` or an explicit
   prolate-only replacement is admissible.
4. **Finite-section theatre.**  Positivity of finitely many matrices, numerical agreement, or one
   simple real finite determinant is offered in place of the profile exhaustion
   `(PN12)`--`(PN15)`.
5. **Abstract perturbation theatre.**  Davis--Kahan, Kato, min--max, or Schur complement is invoked
   without proving the source-specific relative bound for the intact prime--polar defect.  Those
   tools transfer the normal form; they do not supply it.
6. **Boundary-channel deletion.**  The infinite-dimensional translated two-edge family is placed
   in a nominally coercive remainder without proving `(PN12)` and retaining `(PN16)`.  The
   proved frame-saturation theorem forbids that shortcut.
7. **Literature collision.**  A published theorem already gives both growing-depth
   constrained-PSWF Toeplitz congruence and the prolate/two-edge profile exhaustion of the intact
   Weil form.  Classical Fuchs, Slepian, Dunster, generic rank-one constraints, and abstract
   concentration compactness do not meet this test.

## Preliminary literature audit through 2026-07-19

Targeted Google/arXiv searches found:

- classical and modern unconstrained PSWF concentration-eigenvalue bounds;
- Dunster's high-frequency PSWF asymptotics with explicit error control;
- Connes--Consani's semilocal/scaling architecture and the 2023 semilocal prolate wave operator;
- Connes--Consani--Moscovici's finite zeta spectral triples and their stated simple-even/prolate
  approximation problem.

No result found states or implies `(PN8)` or `(PN12)`--`(PN15)`: no growing-depth zero-integral
prolate normal form for the intact Weil operator, no Toeplitz radial limit uniform on a cofinal
sector, and no prolate/two-edge profile decomposition exhausting its semilocal frame defects.  The
conjecture therefore passes the anti-theatre search; priority must be re-audited after a proof exists.

Primary comparison sources:

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes and C. Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.
- A. Connes, C. Consani, and H. Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423.
- A. Connes, C. Consani, and H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Research attack

The conjecture divides into three genuinely source-specific frontier estimates.

### A. Growing-depth intact graph-defect estimate

Prove, at the safe depth `(PN4)`,

```text
|| D^(-1) S Q_defect S D^(-1) ||_op=o(L_lambda).            (A1)
```

This is the cofinal operator version of the currently open fixed-pair estimate `(WT17)`.  It must
keep the polar evaluation and Poisson-resummed prime source intact.

### B. Prolate--boundary concentration compactness

Prove the profile decomposition `(PN12)`--`(PN15)` and, after removing its prolate and boundary profiles, a
relative-compactness estimate of the form

```text
|Q_defect_lambda(r,r)|
 <=delta L_lambda <C_lambda r,r>.                              (B1)
```

for the profile-free remainder `r`, uniformly after a source-defined finite activation scale.
The prolate component is controlled by `(A1)`; the boundary component is retained in the exact
form `(PN16)`.  Equation `(B1)` is not allowed on the raw two-edge family, where the corpus
already proves leading frame saturation.  The absence of any fourth defect profile is the main new
analytic target.

### C. Weighted PSWF graph convergence

Prove the weighted-BV or sharp sup-norm PSWF-to-Hermite convergence already isolated in
`constrained-prolate-true-aperture-xi-moment-metric.md`.  This identifies the true aperture metric
and turns the normal-form ground state into the locally uniform determinant carrier.

The preferred order is `B -> A -> C`: profile exhaustion first isolates the two noncompact
channels; the cofinal Toeplitz estimate settles the prolate channel; `(PN17)` remains the explicit
arithmetic sign theorem on the boundary channel.  Graph convergence is needed for the determinant
refinement, not for the Weil-positivity implication.

## Lean status

This card is a conjecture and has no Lean theorem.  Its finite-dimensional algebraic skeleton is
already formalized: constrained secular roots, the fixed-depth Fuchs ladder, parity separation,
Toeplitz positivity, Schur correction, exact finite aperture reconstruction, and the abstract
relative-form transfer lemmas.  No formal declaration should package `(PN8)`, `(PN10)`, or
`(PN12)`--`(PN17)` behind a hypothesis and present the wrapper as progress.  Formalization begins only after
one of the source-specific analytic estimates is proved on paper.

## Gates

- [x] source-pure cofinal selector defined
- [x] explicit full-operator normal form stated
- [x] complement and cross-term escape included
- [x] positive/negative parity sectors included
- [x] anti-theatre and circularity kill tests recorded
- [x] preliminary external search found no matching theorem
- [ ] prove the prolate--boundary profile decomposition `(PN12)`--`(PN15)`
- [ ] prove the profile-free relative estimate `(B1)`
- [ ] prove the cofinal intact graph-defect estimate `(A1)`
- [ ] prove the cofinal Toeplitz congruence `(PN8)`
- [ ] prove the source-side boundary orientation `(PN17)`
- [ ] prove the weighted PSWF graph convergence
- [ ] formalize every proved analytic and operator layer unconditionally

## Log

- 2026-07-19 -- Created from the exact fixed-depth/complement gap left by the constrained-prolate
  Toeplitz and true-aperture-metric cards.  The first two-block formulation was rejected after the
  proved infinite-dimensional boundary saturation law was applied.  The surviving conjecture is a
  three-channel normal form: prolate, two-edge boundary, and coercive bulk.
