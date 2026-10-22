# Euler horizontal-charge separator

- **ID:** euler-horizontal-charge-separator
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; NOVELTY UNVERIFIED]`
- **Source:** exact charge decomposition in
  `../2-fully-proven/not_new_scientific_knowledge/horizontal-entry-charge-transfer.md`

## Target

Let `E_zeta` denote the complete von-Mangoldt Euler source together with the archimedean factor and
functional equation. Construct directly from `E_zeta` a locally finite even integer-valued measure
`Omega_E` on the ordinate axis such that, for every bounded interval `I` avoiding zero ordinates at
its endpoints,

```text
Omega_E(I)
  = sum_gamma in I
      (H_gamma^2 - sum_(Im rho=gamma) m_rho^2).           (1)
```

The right side is the off-line cross-charge `O_I`. The construction on the left may not use the
unknown zero divisor, values or derivatives of `xi` at proposed zeros, or a finite Euler head.

The significant theorem sought is not merely (1). Analytic continuation already makes the full
Euler source divisor-faithful. The source construction must also prove a one-sided law, for example

```text
Omega_E(I)=0                                               (2)
```

for a nonempty new class of windows, or an effective bound `Omega_E(I)<2`. Since `Omega_E(I)` is an
even nonnegative integer, the latter also gives (2).

## Why this is the entry constraint

The horizontal-multiplicity excess splits as

```text
horizontal excess = off-line cross-charge + multiplicity excess.
```

A reflected simple pair entering the critical line transfers two units from the first term to the
second. Pair-correlation statistics that see only the sum cannot prevent entry. A source theorem
for `Omega_E` separates the two channels and is therefore the minimal integer obstruction.

This formulation uses neither a height coordinate as the primary object nor a local jet. It is an
all-divisor correlation measure whose proposed left side is built from the complete Euler data.
A bounded interval is only a localization of the measure.

## Candidate construction

On `Re s>1`, the logarithmic Euler source has the pure frequency expansion

```text
-zeta'(s)/zeta(s) = sum_n Lambda(n)n^(-s).
```

The long mean of its two-point product is prime-diagonal because distinct logarithmic frequencies
do not coincide. On the divisor side, a corresponding two-point trace contains:

1. point-diagonal terms, giving `sum m_rho^2`;
2. reflected same-ordinate terms, giving `O_I`;
3. distinct-ordinate terms, killed by the proposed mean.

`[CONJECTURE]` There is an all-place renormalized Plancherel identity across the critical seam whose
prime-diagonal side separates terms 1 and 2 rather than only their sum. Its off-diagonal remainder
is `Omega_E`.

## Fake proof and exact failure

The naive proof says that uniqueness of the frequencies `log n` makes the prime two-point mean
diagonal and therefore forces `Omega_E=0`. This is false. Moving the identity from `Re s>1` to the
critical boundary crosses the zero poles; the individual pole transforms are causal exponential
modes, not orthogonal pure frequencies. Critical-line poles also create a divergent diagonal
mass. Interchanging analytic continuation, boundary limit, and the long mean discards precisely
the residue that could equal `Omega_E`.

Thus the open theorem is a renormalization statement, not prime-log independence by itself.

## Literature and parent-theory audit

- `[SEARCH]` Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh identify reflected
  symmetric-diagonal terms in unconditional Montgomery pair correlation and use them to bound the
  proportion of critical zeros under a thin-box hypothesis.
- `[SEARCH]` Goldston--Lee--Schettler--Suriajaya introduce horizontal multiplicity and show that the
  pair-correlation conjecture implies asymptotically 100 percent simple critical zeros.
- `[SEARCH]` Standard Montgomery pair correlation and long-mean orthogonality determine only
  asymptotic horizontal multiplicity; finite exceptional off-line orbits are invisible at relative
  precision.
- `[BRIDGE]` Krein--Langer negative index and generalized Schur theory already count off-line poles
  when the divisor supplies the carrier.
- `[BRIDGE]` `ChargeMotion.lean` already formalizes homotopy conservation and boundary jumps for
  divisor-fed winding charge; it does not construct the required charge from the Euler source.

No novelty is claimed for horizontal multiplicity, symmetric diagonal terms, the charge algebra,
or source uniqueness. Scientific novelty would begin only with a proved source-side separator and
a noncircular one-sided estimate.

## Falsifiers

1. A construction that first reconstructs the zero divisor and then evaluates (1) is faithful but
   conclusion-fed.
2. A relative/asymptotic formula with error `o(N(I))` cannot exclude one off-line orbit; the
   required absolute error is strictly less than `2`.
3. Any statistic factoring through `C_I-N_I` is collision-blind because that sum is conserved.
4. A bounded-support one-point Weil test cannot isolate the unknown infinite critical-line tail.
5. A finite Euler head cannot work by the formal finite-Euler no-amplification theorem.
6. Bare tempered local factors are insufficient: Helson zeta functions admit essentially
   prescribed zeros without the global zeta functional-equation constraint.

## Gates

- [x] 0 -> 1: exact integer target, collision law, fake proof, literature overlap, and falsifiers
  stated.
- [ ] 1 -> 2: construct `Omega_E` without the divisor and prove an absolute `<2` source bound on a
  nonempty new window or prove a global vanishing theorem.
- [ ] 2 -> 3: formalize the charge measure, source trace, and integer conclusion.
- [ ] 3 -> 4: independent proof and broad scientific-novelty audit.

## Relation to verified-height amplification

For an interval immediately above the Platt--Trudgian prefix, an explicit source estimate

```text
Omega_E(I)<2
```

would exclude every reflected off-line pair in that interval without resolving its horizontal
distance from the line. It would therefore amplify the verified range once the interval endpoints
and source trace are made effective. No such estimate has been proved here.

## Competing move: vertical phase defect and the prime-square entry seam

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Fix a nonzero real ordinate `tau` and define, first
for `Re s>1`,

```text
P_tau(s) = sum_p 2(1-cos(tau log p)) p^(-s),
R_tau(s) = sum_p sum_(k>=2)
             2(1-cos(k tau log p)) p^(-ks)/k.
```

Every coefficient of both series is nonnegative on the real axis.  The second series converges
normally on `Re s>1/2`.  With the logarithm branches normalized on the ordinary Euler half-plane,

```text
P_tau(s)+R_tau(s)
  = 2 log zeta(s)-log zeta(s+i tau)-log zeta(s-i tau).       (3)
```

Consequently, if `1/2<beta<1`, then `zeta(beta+i tau)` has order `m` if and only if the analytic
continuation of `P_tau` has at the real point `beta` the local logarithmic singularity

```text
P_tau(s) = -2m log(s-beta) + holomorphic.                    (4)
```

There is no cancellation in (4): `zeta(beta)` is nonzero, conjugation gives the same order at
`beta-i tau`, and `R_tau` is holomorphic there.  Thus a single off-line orbit is converted, without
jets, into an isolated real singularity of a positive prime-only Euler series.

The critical line is the first Euler-grade seam.  The `k=2` part satisfies, for real
`s -> 1/2+`,

```text
sum_p (1-cos(2 tau log p)) p^(-2s)
  = -log(2s-1) + O_tau(1),                                  (5)
```

while the `k>=3` part is holomorphic across `Re s=1/2`.  If `zeta(1/2+i tau)` has order `q`, (3)--(5)
give the prime-only boundary law

```text
P_tau(s) = -(2q-1) log(s-1/2) + O_tau(1).                   (6)
```

Hence a reflected pair of order `m` approaching from `beta` and `1-beta` carries two interior
prime-layer charges `2m+2m`; after collision it gives a line zero of order `2m` and prime-layer
boundary charge `4m-1`.  The missing unit is exactly the universal prime-square charge in (5).
This is an Euler-graded version of the divisor charge transfer: entry is possible only at the seam
where the square-prime layer ceases to be holomorphic.

`[ATTACK]` This does not yet construct `Omega_E` or exclude an orbit.  Landau positivity locates the
first real singularity of `P_tau` at `s=1`, but a nonnegative Dirichlet series may have further real
singularities after analytic continuation.  Proving that (4) is absent for every `tau` is merely RH
in this new language.  Equation (6) also shows why a prime-only boundary residue cannot by itself
separate entry: the universal square channel changes the residue by one exactly at the critical
line.

`[OPEN CORE]` Find a source property of the all-grade positive phase defect that is stronger than
Landau's first-singularity theorem and is stable after removal of the `s=1` pole, while retaining
coefficient positivity.  A successful property must forbid a secondary real logarithmic
singularity in `(1/2,1)` without subtracting a sign-indefinite prime main term.  That would turn the
Euler-grade collision law into a genuine no-entry theorem.

## Finite positive-phase pole-removal no-go

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The leading `s=1` singularity cannot be removed by
any nonzero finite stationary phase detector while retaining coefficient positivity.  Let
`tau_1,...,tau_r` be distinct real frequencies, let `A` be a nonzero positive semidefinite matrix,
and put

```text
w(x) = v(x)^* A v(x),       v_j(x)=exp(i tau_j x).
```

Then `w(x)>=0`, and its constant Fourier coefficient is `trace(A)>0`.  Hence

```text
sum_p w(log p) p^(-s)
  = trace(A) P(s) + sum_(lambda != 0) c_lambda P(s-i lambda),
```

where `P` is the prime zeta function.  At `s=1`, the first term is
`trace(A) log(1/(s-1))+O(1)`, while every nonzero-frequency term is regular there because zeta has
no zeros or poles on `Re z=1` away from `z=1`.  Thus every nontrivial finite positive phase square
retains a strictly positive leading prime pole.

The same obstruction holds for any finite sum of squared prime-phase amplitudes.  Consequently the
open core cannot be solved by a finite Fejer kernel, a finite Gram matrix of vertical shifts, or any
other stationary finite positive trigonometric weight.  A survivor must use prime-dependent
nonstationary weights, or an infinite renormalized Schur complement that removes the constant mode
without converting the secondary charge into a relative-density statistic.

## Route C verdict after the shift-pair and static-leakage attacks

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The exact charge carrier is now identified.  For the
uncancelled pair

```text
Xi(c-u), Xi(c+u),
```

the local intersection multiplicity at a same-ordinate zero pair `(rho,sigma)` is
`m_rho m_sigma`.  Twice the positive-real-`u` intersection mass is exactly `O_I`.  The complete
proof is in
`../2-fully-proven/not_new_scientific_knowledge/13-constraint-carrier-calculus/euler-shift-pair-incidence-resultant.md`.

This construction also proves why the reduced shifted quotient is not the charge carrier.  At an
exceptional shift it cancels `min(m_rho,m_sigma)`, while the resultant carries the product
`m_rho m_sigma`.  At `u=0`, the reduced diagonal intersection mass is `m(m-1)`, so the natural total
positive incidence cycle carries the conserved statistic `O_I+M_I`, not `O_I` alone.

`[PROVED BRIDGE; ROUTE CLOSED AS A STATIC MECHANISM]` Norm continuity of the anti-causal leakage at
`omega=0` does not exclude a persistent off-line zero.  In the rank-one Blaschke model with
transverse displacement `a`,

```text
rank L_(a,omega)=1,       ||L_(a,omega)||=omega/a,
```

for every `0<omega<a`.  The leakage converges to zero in norm as `omega` decreases to zero while its
rank remains one.  Its unit jump occurs at the moving crossing `omega=a`, so using that jump to
exclude entry requires an additional deformation of `a`; it is not a static theorem about the fixed
Xi source.  See
`../2-fully-proven/not_new_scientific_knowledge/shifted-hardy-leakage-static-continuity-no-go.md`.

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Poincare--Lelong now constructs the infinite
uncancelled current without enumerating the zero divisor:

```text
J_Xi=dd^c log|Xi(c-u)| wedge dd^c log|Xi(c+u)|.
```

A cutoff-independent thin-slice limit along `Im u=0`, `Re u>0` gives `Omega_E` exactly.  The
construction uses only the completed function, but it supplies no sign or mass bound.

`[OPEN CORE]` Route C now has one precise surviving demand: prove directly from the fixed
Euler--Gamma--theta source that the positive-real-shift mass of this canonical current is zero or
`<2` on a genuinely new window.  The current construction is closed; the one-sided source estimate
is all of the remaining scientific content.
The full route verdict is `../../../reports/rhtower_route_c_verdict_1107.md`.
The paper-level pipeline verdict is
`../2-fully-proven/not_new_scientific_knowledge/13-constraint-carrier-calculus/route-c-horizontal-charge-interim-verdict.md`.

## Reopening move: infinitesimal leakage rather than bare continuity

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The rank-one static-continuity attack does not close
all leakage mechanisms.  For a fixed same-ordinate collection of transverse layers `a_j>0` with
multiplicities `m_j`, let `L_omega` be the local shifted Hardy leakage.  Then

```text
omega^(-1)L_omega -> T_A
```

in operator norm.  After Paley--Wiener identification, `T_A` is the positive Laplace--Hankel
operator

```text
K_A(x,y)=2 sum_j m_j exp(-a_j(x+y)),
trace(T_A)=sum_j m_j/a_j,
||T_A||>=max_j m_j/a_j.
```

The proof and the unique power-scaling classification are in
`../2-fully-proven/not_new_scientific_knowledge/07-functional-analysis-operator-theory/infinitesimal-hardy-leakage-horizontal-layer-resolvent.md`.
For zeta, every right-hand displacement satisfies `0<a_j<1/2`, so one layer already forces
`||T_A||>2`.  The bare leakage tends to zero, but its first-order coefficient retains and amplifies
the off-line channel.

`[ATTACK]` Positivity holds only after an ordinate has been isolated.  The global logarithmic
leakage derivative mixes different ordinates through oscillatory exponential modes, and selecting a
fixed ordinate by first reading a pole would be conclusion-fed.  Thus the new open object is not the
finite Gram operator itself but an Euler-source construction of its ordinate-diagonal projection.

`[OPEN CORE]` Construct, before divisor expansion, a positive source operator `D_E` whose fibers are
the same-ordinate first-order leakage blocks `T_A`, and prove the absolute source bound

```text
||D_E(I)||<=2
```

on a genuinely new window.  Equivalently, prove that the source-defined global first-order leakage
has no ordinate fiber with norm greater than `2`.  This is a stricter target than continuity at
`omega=0` and a different realization of the positive-real thin slice of `J_Xi`; it remains open.

### Burnol co-Poisson quotient candidate for the missing diagonal

The paper theorem
`../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-quotient-bilateral-order-rh-law.md`
supplies a second source coordinate for the same diagonalization problem.  Let `E_b` project onto
the orthogonal complement of Burnol's closed co-Poisson source subspace and let

```text
H_(a,r)=U_r Pi_a U_r^*-U_r^*Pi_aU_r.
```

On a zero-evaluator fiber its normalized diagonal is exactly

```text
r^(2 Re(rho)-1)-r^(1-2 Re(rho)).
```

With `r=exp(t)`, the first scale derivative at `t=0` is `4(Re(rho)-1/2)`.  This makes the
infinitesimal Burnol phase-polarization a concrete candidate for the missing linear horizontal
charge reader.  The full quotient compression is overpowered because it also controls
off-diagonal correlations.  The paper theorem
`../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-berezin-diagonal-reflection-law.md`
now closes the diagonal-map interface: if `k_w^b` is the ordinary evaluation kernel, then
`E_b k_w^b` is the quotient reproducing kernel and

```text
<E_b k_w^b,H_(a,r)E_b k_w^b>
```

is a canonical source-defined Berezin diagonal.  It retains the exact zero-fibre value and is odd
under Fourier reflection, with no zero biorthogonal system.  What remains is the sign of this
scalar reader on the co-Poisson annihilator spectrum and an additional value relation identifying
or dominating the positive Cauchy layer operator `T_A`; no absolute `<=2` bound follows from the
linear reader alone.

## Global repair: Cauchy energy removes ordinate-phase cancellation

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The first-order anti-causal profile can be treated
globally without first projecting to one ordinate.  For a finite right-half divisor

```text
rho_j=1/2+a_j+i gamma_j
```

with multiplicities `m_j`, the normalized wrong-support profile is

```text
ell_1(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t),   t>0.
```

Its unweighted energy is the positive Cauchy Gram form

```text
E_off=integral_0^infinity |ell_1(t)|^2 dt
     =4 sum_(j,k) m_j m_k
        (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2).
```

Every ordered-pair contribution is positive after conjugate pairing.  In particular,

```text
E_off>=2 sum_j m_j^2/a_j.
```

Since every zeta displacement has `0<a_j<1/2`, one off-line zero forces `E_off>4`.  The complete
proof is in
`../2-fully-proven/not_new_scientific_knowledge/10-euler-gamma-completion/infinitesimal-euler-leakage-cauchy-energy-threshold.md`.
This removes the oscillatory-cancellation objection to a global first-order detector.

`[PARENT-THEORY ATTACK]` The Cauchy Gram calculation is standard exponential-sum theory.  Suzuki's
source kernel already gives fixed-`omega` innerness criteria; differentiating at `omega=0` returns
`-2 Xi'/Xi`, whose Euler part is the von-Mangoldt prime-power source.  Therefore the profile and its
energy are an exact RH encoding unless an independent source estimate is proved.

`[OPEN CORE]` Define the first-order wrong-support profile directly as the boundary-continuation
defect of Suzuki's explicit Euler--Gamma kernel and prove

```text
integral_0^infinity |ell_E(t)|^2 dt <= 4.
```

No ordinate localization is now required.  The bound itself, not the positive detector, is the
remaining arithmetic theorem.  It may not be obtained from innerness of `Theta_omega`, from a
zero-residue expansion, or from an RH-equivalent `L^2` tail criterion.

## Finite-divisor source construction closed: second-order Toeplitz Schur curvature

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The global first-order energy now has a construction
from the completed shifted source before any zero or residue expansion.  Let

```text
T_omega=P_+ M_(Theta_omega)|H^2_+,
L_omega=P_- M_(Theta_omega)|H^2_+.
```

Boundary unimodularity gives the exact finite-`omega` identity

```text
I-T_omega^*T_omega=L_omega^*L_omega.
```

For a finite right-half divisor, `omega^(-1)L_omega` converges to the first-order leakage `D`, and
therefore

```text
C_E=lim_(omega->0+) omega^(-2)(I-T_omega^*T_omega)=D^*D>=0.
```

In logarithmic Paley--Wiener coordinates, the kernel of `C_E` is

```text
C_E(y,z)=integral_0^infinity
  conjugate(ell_1(x+y)) ell_1(x+z) dx,
```

so the previously defined energy is exactly the boundary corner `C_E(0,0)`.  The Euler tangents are

```text
partial_omega c_omega(n)|_0=2 Lambda(n),
partial_omega^2 c_omega(n)|_0=4 (Lambda*Lambda)(n).
```

Thus `C_E` is the Schur defect between the one-prime von-Mangoldt tangent and the two-prime
Dirichlet-convolution tangent.  The full proof is in
`../2-fully-proven/not_new_scientific_knowledge/10-euler-gamma-completion/infinitesimal-euler-leakage-cauchy-energy-threshold.md`.

`[PROVED NO-GO]` Toeplitz contractivity does not bound the corner.  In the one-layer model,
`C_E(0,0)=2m^2/a`, which is unbounded as `a->0`, while every `T_omega` remains a contraction.  Corner
evaluation is not continuous in operator norm.

`[OPEN CORE]` Prove the zeta-specific boundary regularity estimate

```text
C_E(0,0)<=4
```

directly from the explicit Euler--Gamma source.  Finite-divisor construction, positivity, phase
cancellation, and prime-support identification are now closed.  The global extended-form limit and
its arithmetic corner bound remain; the bound cannot follow from generic Hardy--Toeplitz theory.

## Finite-tangent escape closed: distinct-prime-support filtration

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Higher transverse derivatives do not introduce an
independent source constraint.  For

```text
zeta(s-omega)/zeta(s+omega)=sum_n c_omega(n)n^(-s),
```

let `nu(n)` be the number of distinct prime divisors of `n`.  Then `c_omega(n)` vanishes at zero to
exact order `nu(n)`, with

```text
partial_omega^(nu(n)) c_omega(n)|_0
 =2^(nu(n)) nu(n)! product_(p|n) log p.
```

Thus the `k`th tangent is supported on integers with at most `k` distinct prime supports.  At the
completed-function level,

```text
log(F(s-omega)/F(s+omega))
 =-2 sum_(j>=0) omega^(2j+1)/(2j+1)!
   partial_s^(2j+1) log F(s),
```

so every finite tangent is a Bell polynomial in the odd logarithmic derivatives of the original
source.  The full proof is in
`../2-fully-proven/not_new_scientific_knowledge/shifted-euler-quotient-finite-tangent-prime-support-filtration.md`.

`[ROUTE CONSEQUENCE]` Taking more finite `omega` derivatives cannot by itself create the missing
all-prime rigidity.  It only increases the bounded prime-interaction grade.  Route C must now use a
nonperturbative law of the full shifted family, an infinite interaction-grade completion with a
proved boundary estimate, or the direct zeta-specific bound `C_E(0,0)<=4`.

## Bare nonperturbative shift cocycle closed by flatness

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The full shifted quotient obeys

```text
R_(omega+eta)(s)=R_omega(s-eta)R_eta(s+omega),
R_omega(s)=F(s-omega)/F(s+omega).
```

For zeta, its positive Euler coefficient streams satisfy the twisted convolution law

```text
c_(omega+eta)
 =(n |-> n^eta c_omega(n))
  * (n |-> n^(-omega)c_eta(n)).
```

All three-factor associations telescope to the same ratio, so the uncompressed cocycle curvature is
identically zero.  The proof is in
`../2-fully-proven/not_new_scientific_knowledge/shifted-euler-quotient-twisted-cocycle-flatness.md`.

`[ROUTE CONSEQUENCE]` The full all-prime family is nonperturbative and coefficient-positive on the
Euler side, but its bare algebraic cocycle is an exact coboundary.  The only nontrivial curvature is
created by Hardy compression:

```text
I-T_omega^*T_omega=L_omega^*L_omega.
```

Thus cocycle associativity and Euler coefficient positivity do not bound `C_E(0,0)`.  A live
full-shift route must prove a boundary regularity law for the compressed cocycle.

## Generic compressed-cocycle theory closed by a self-dual quartet

`[PROVED COUNTEREXAMPLE; NOT NEW SCIENTIFIC KNOWLEDGE]` For `0<a<1/2` and `gamma>0`, the polynomial

```text
F_(a,gamma)(s)
 =(((s-1/2)-a)^2+gamma^2)
  (((s-1/2)+a)^2+gamma^2)
```

has functional equation `F(1-s)=F(s)`, Schwarz symmetry, all four zeros in the open critical strip,
a unimodular centered shifted quotient, the exact full-shift cocycle, and contractive Toeplitz
compressions.  Its normalized wrong-support profile is

```text
ell_(a,gamma)(t)=4exp(-at)cos(gamma t),
```

so

```text
C_(a,gamma)(0,0)=4/a+4a/(a^2+gamma^2)>8
```

and the corner is unbounded as `a->0`.  The full proof is in
`../2-fully-proven/not_new_scientific_knowledge/self-dual-quartet-defeats-generic-shift-curvature-bound.md`.

`[ROUTE CONSEQUENCE]` Generic self-dual entire-function theory, critical-strip geometry,
unimodularity, full-shift cocycle flatness, Toeplitz contractivity, and Schur-defect positivity cannot
prove `C_E(0,0)<=4`.  The surviving Route C theorem must use the exact infinite Euler product and
explicit gamma/theta completion in a quantitative compressed-boundary law absent from this quartet.

## Euler positivity does not imply variation diminution

`[PROVED COUNTEREXAMPLE; NOT NEW SCIENTIFIC KNOWLEDGE]` On a fixed prime orbit, write
`x=p^omega>1`.  The positive local coefficients of the shifted Euler quotient are

```text
a_0=1,
a_k=x^k-x^(k-2)  for k>=1.
```

Their first PF2 minor is

```text
a_1^2-a_0a_2=x^(-2)-1<0.
```

Thus even one local orbit is not PF2, hence not PF-infinity.  The proof is in
`../../../3-formalized/not_new_scientific_knowledge/shifted-euler-prime-orbit-pf2-failure.md`.

`[ROUTE CONSEQUENCE]` Positive shifted-Euler coefficients do not automatically make Suzuki's
prime-dilation mixture variation-diminishing and cannot by themselves force an eventual one-sign
archimedean tail.  Any remaining exact-source theorem must prove a quantitative prime--gamma/theta
cancellation law rather than invoke coefficient positivity alone.

## Archimedean one-sign shortcut closed

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` For `0<omega<1/2`, Suzuki's integrated
archimedean kernel satisfies

```text
g_omega^(1)(x)
 ~-B_omega/(1/2-omega)x^(omega-1)   as x->0+,

g_omega^(1)(x)
 ~ A_omega/omega(1-x)^omega         as x->1-,
```

with `A_omega,B_omega>0`.  It is therefore negative near zero and positive near one.  The proof is
in
`../2-fully-proven/not_new_scientific_knowledge/suzuki-archimedean-primitive-forced-sign-change.md`.

`[ROUTE CONSEQUENCE]` The archimedean kernel itself has no one-sign law, while the positive Euler
weights fail PF2.  The surviving exact-source problem is now a quantitative cancellation theorem
for the complete all-prime dilation mixture against this forced gamma-kernel sign change.  Neither
side separately supplies the required sign or curvature bound.

## Positive Euler main term is annihilated by completion

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Let

```text
C_omega(s)=zeta(s-omega)/zeta(s+omega),
G_omega(s)=gamma(s-omega)/gamma(s+omega).
```

The positive Euler series `C_omega` has residue `1/zeta(1+2omega)>0` at `s=1+omega`, but
`G_omega` has a simple zero there.  Their product is finite:

```text
lim_(s->1+omega)G_omega(s)C_omega(s)
 =Xi(1)/Xi(1+2omega).
```

Equivalently, Suzuki's kernel and its integrated primitive have the exact vanishing moments

```text
integral_0^1 g_omega(x)x^(1+omega)dx/x=0,
integral_0^1 g_omega^(1)(x)x^(1+omega)dx/x=0.
```

The proof is in
`../2-fully-proven/not_new_scientific_knowledge/suzuki-euler-pole-archimedean-moment-annihilation.md`.

`[ROUTE CONSEQUENCE]` The completed source annihilates the dominant positive Euler/Tauberian main
term.  After this cancellation, the next singularity frontier is the shifted nontrivial divisor.
A live proof must control the fully canceled remainder by a source inequality; extracting its next
pole simply reconstructs the zero set.

## Exact surviving arithmetic carrier: shifted-Euler summatory error

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Let

```text
A_omega(X)=sum_(n<=X)c_omega(n),
M_omega(X)=X^(1+omega)/((1+omega)zeta(1+2omega)),
E_omega=A_omega-M_omega.
```

The zero `(1+omega)` moment of Suzuki's integrated gamma kernel gives the exact Stieltjes identity

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x]) g_omega^(1)(t/x)dE_omega(t).
```

The positive average term `M_omega` contributes exactly zero.  The proof is in
`../2-fully-proven/not_new_scientific_knowledge/suzuki-tail-is-exact-summatory-error-transform.md`.

`[ROUTE CONSEQUENCE]` The only surviving arithmetic datum inside Suzuki's one-sign criterion is the
fully pole-subtracted all-prime discrepancy `E_omega`.  Any estimate obtained from its next Mellin
pole is divisor-fed.  A live theorem must control this signed error transform without first locating
shifted zeros.

## Final elementary arithmetic split: floor discrepancy plus Möbius tail

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` For `0<omega<1/2`, the surviving summatory error has
the exact decomposition

```text
E_omega(X)
 =sum_(d<=X)mu(d)d^(-omega)R_omega(X/d)
  -X^(1+omega)/(1+omega)
   sum_(d>X)mu(d)d^(-1-2omega),
```

where

```text
R_omega(Y)=sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).
```

Each piece is only `O_omega(X^(1-omega))` under absolute values.  The proof is in
`../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/shifted-euler-error-floor-mobius-tail-coupling.md`.

`[ROUTE CONSEQUENCE]` Separate floor-error bounds, separate Möbius-tail bounds, and their triangle
inequality cannot control Suzuki's signed error transform.  A pointwise
`X^(1/2-omega+epsilon)` bound would suffice, but generalized-totient theory warns that raw floor
fluctuations may be larger and later canceled by the transform.  The remaining source theorem is a
coupled transformed cancellation, not necessarily a pointwise half-power estimate for `E_omega`.
