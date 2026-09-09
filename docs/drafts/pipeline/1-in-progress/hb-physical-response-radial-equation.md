# HB: original physical response equation

Goal: theta cusp → Xi occurrence → complete source → original outgoing
response and physical adjoint residue → Hawking-clock extinction → RH.
RH is open; frontier map is read-only.

Weighted admission of the original causal response is now proved for
`3/2 < Re w < 2`, `Im w != 0`, including its literal physical angular
pairing. Its equality with the original complete-source endpoint Green
integral is proved on that overlap. For every source copy tested against
that same copy, this original complete response now has a meromorphic
continuation to both of its fundamental QNMs. Its exact scalar Laurent
coefficient and analytic remainder are now proved. The next obligation
is nonvanishing of its complete source factors and identification with
the physical adjoint pairing.

## Proposed bridge

1. Prove the original joint distribution equation against every separated
   smooth compact radial/modular test. Move both radial derivatives and
   the complete modular Laplacian onto the test. Use the existing
   `CoreField.planarTest`, full modular Green identity, and exact native
   core-operator action; modular seams and elliptic charts remain included.
2. Approximate the physical angular test by smooth modular cusp cutoffs
   at scale N. Prove convergence of both the test pairing and its
   differentiated pairing using integrable majorants. The cutoff transition
   must scale with N, so its hyperbolic first and second derivatives stay
   bounded; a fixed-width transition has growing derivatives.
3. Pass the compact-test equation to the actual physical pairing using
   the proved height norm of the response and complete source. The result
   must retain the original angular eigenvalue and radial coefficient
   `sech(t)^2`, and identify the complete projected forcing.
4. Derive the projected response's actual radial endpoint conditions,
   then identify it with the original radial Green response on the
   positive-frequency overlap and continue that same observable to QNMs.

For the physical angular field E satisfying Delta_H E=lambda E, the
intended distribution equation for R=P(yU) is

```text
<f'',R> + lambda <sech(t)^2 f,R> - w^2 <f,R> = -<f,P(yF)>.
```

The exact Lean statement will use the existing Hilbert convention,
`<test,response>`, with every coefficient conjugation made explicit.
No noncompact-test, domain, endpoint, or continuation premise may be
inserted at the actual-source capstone.

Current individually audited Lean results: steps 1–3 are closed. The
original compact equation, complete core-operator action, constructed
modular cutoffs, and mass-pairing limit are proved. The actual physical
vertical derivative is now admitted in angular L2. The full chart cutoff
formula retains both derivative terms and bounds the Laplacian by
`(|lambda|+C)|E|+2 C y |E_y|`. These terms give integrable response
pairings and prove the differentiated integral limit. The capstone
`physicalCuspResponse_radial_equation` gives the actual complete-source
radial equation, with no supplied noncompact-test or response premise.
The seven leaves closing that limit and equation contain 18 public
theorems; individual final audits were warning-free, with only standard
Lean axioms. See the [exact proof and scope](../3-formalized/hb-physical-response-radial-equation.md).

Step 4 has the actual Dirichlet endpoint: the physical response and its
actual radial derivative lie in the original closed radial graph. Its
zero extension is H1 and has a continuous representative vanishing at
t=0. The inside endpoint limit is zero. Its actual two classical interior
derivatives, global spatial bound, exact physical mode matching, and
complete-source finite-interval Green transport are also proved.
Equality with the original complete-source endpoint Green response is now
proved on the overlap. Continuation of the same response to both of its
own fundamental QNMs is also proved. Full physical adjoint identification,
complete-source pole survival, spin-two/AIME reconstruction, and independent extinction
remain open. See the [endpoint proof and scope](../3-formalized/hb-physical-response-dirichlet-endpoint.md).

## Closed endpoint bridge

The original rotated energy identity retains the complete weighted graph
norm, beyond the weighted mass estimate already extracted from it. Write
`a=Re w`, `b=Im w`, `B=||cuspWeightLimit(y) F||`, and
`K=a|w|/((a^2+b^2)(a^2-9/4))`. For `a>3/2`, the existing mass estimate
gives `||v_N||<=K B`, while the logarithmic-slope term obeys
`||r_N||<=(3/2)||v_N||`. With `X_N=||jointCuspWeight_N U||`, the rotated
identity, Cauchy–Schwarz, and `||(jointCuspWeight_N U)_3||<=X_N` give

```text
a X_N^2 <= |w| K B^2 + (9/4) a K^2 B^2 + 3 |b| K B X_N.
```

Absorbing the mixed term by a square yields the uniform bound

```text
X_N^2 <= (2 |w| K/a + (9/2) K^2 + 9 b^2 K^2/a^2) B^2.
```

The full limiting cusp weight includes its constant part; height admission
already supplies its L2 admission. The uniform graph estimate is formalized
and gives height admission of the original radial derivative. Contraction
by each compact angular test preserves the original radial Dirichlet graph;
weak limits of both components retain that graph. Zero extension commutes
with its actual distributional derivative, giving H1 admission and a
continuous zero endpoint trace. Eight leaves with 23 public theorems and
seven supporting declarations passed warning-free individual audits.

## Closed complete-source Green identification

The actual profile P now satisfies `w^2 P-P''-lambda sech(t)^2 P=F`
classically on t<0, with the original complete angular integral F and
`lambda=u^2-1/4`. All four source channels remain. Its original zero
extension gives a uniform spatial bound. The frequency `chi=-i*u` is the
original angular momentum, satisfies `1/4+chi^2=-lambda`, and lies in the
proved connection-nonzero chamber on the response overlap.

For original modes H,N and connection c, the actual currents
`J_H=H'P-HP'`, `J_N=N'P-NP'` obey `J_H'=HF`, `J_N'=NF`, and
`c P=N J_H-H J_N`. The theorem
`physicalCuspProfile_green_transport` integrates both complete source
pairings from every finite interior base point. Seven leaves with 22
public theorems and four definitions passed warning-free individual
audits; all 26 new public declarations use only standard Lean axioms.
See the [classical equation and exact Green transport](../3-formalized/hb-physical-response-classical-green-transport.md).

The complete F is uniformly bounded on the overlap: all three principal
frequencies lie in their original Green chambers, their original response
bounds transfer to the continued coefficients, and the reduced compact
profile is bounded. The actual equation then bounds P''. A backward
unit-interval derivative estimate gives a uniform bound for P' all the
way to the outer endpoint.

The original H,H' tend to zero at the horizon, while N tends to zero and
N' tends to -1 at the outer endpoint. Together with the physical P trace
and the actual bounds, these prove both endpoint currents vanish. The
true exponential bound for H admits HF absolutely to the horizon;
compact outer bounds admit NF to zero. Consequently,

```text
P(t) = [N(t) integral(-infinity..t, H F)
       +H(t) integral(t..0, N F)] / c.
```

This is also equality with the original Hilbert response almost everywhere.
Seven further leaves contain 20 public theorems and one definition; all
passed individual final builds without warnings and new-only axiom audits.
See the [exact endpoint identification](../3-formalized/hb-physical-response-endpoint-green-identification.md).

## Closed same-copy response continuation

The finite resolvent reduction is now proved with every original angular
period retained. Write `F=M A+sum_i h V_i C_i`, where the actual principal
responses satisfy `L_lambda_i V_i=M A_i`. At the independent target
frequency, the original native Green response minus its exact radial
lift gives U(J), satisfying `L_lambda U(J)=M J`. Put
`delta_i=lambda_i-lambda`, `D=product_i delta_i`, and
`E_i=product_(j!=i) delta_j`. The actual full response P obeys

```text
D P = D U(A) + sum_i E_i C_i [V_i-U(A_i)].
```

This holds for every source-target pair on the original overlap, including
angular collisions; it does not recover P where D is zero. Actual radial
jets, complete-source equations, spatial bounds, zero traces, and original
Wronskian uniqueness are used to establish the identity.

For the same source and target Xi copy, the three gaps factor exactly as
`3 rho(5 rho-2)/4`, `rho(2-rho)/4`, and `(3 rho-2)(5 rho-4)/4`.
The original Xi zero is nonreal, so every factor and D are nonzero without
an RH or noncollision premise. Dividing gives
`continuedPhysicalSelfResponse`, equal to both the original Hilbert
response and complete-source endpoint Green integral on the overlap.
It is meromorphic at every fixed t<0 throughout `Re(w)>-2`, `Im(w)!=0`,
including both fundamental QNMs of each actual Xi copy.

See the [exact finite reduction and same-copy continuation](../3-formalized/hb-physical-self-response-continuation.md).
Meromorphy here is pointwise in the original interior radial variable;
Hilbert-class equality is established on the initial overlap.

## Closed scalar Laurent coefficient; remaining source incidence

Scalar-amplitude linearity now gives U(J)=J U(1), including both original
integrals and the endpoint finite part. The exact effective coefficient
`A_eff=A-sum_i C_i A_i/delta_i` multiplies U(1). All three original
principal connections and the source denominator are proved nonzero at
both target QNMs, so the retained principal sum is analytic there.

The original target connection has a derived nonzero derivative d.
For the full analytic reduced-source numerator N_c and clearing factor
`E(w)=-(w-2s)c(w)`, the actual scalar residue is
`R=A_eff N_c(w_star,t)/[-(w_star-2s)d]`.
Both native radial source moments remain in N_c. The actual response
equals `R/(w-w_star)` plus an analytic germ. It has a nonremovable pole
exactly when both A_eff and N_c(w_star,t) are nonzero. These are the
remaining source obligations; denominator noncollision and simple-zero
normalization are closed.

See the [exact source formula, analytic remainder, and audit](../3-formalized/hb-physical-self-response-laurent-coefficient.md).
This scalar Laurent coefficient still needs identification with the
full physical retarded/advanced adjoint pairing.

For strict-right Xi copies, the source-identified residual period and
the complete cutoff correction now combine exactly to
`A_eff=Lambda(5rho/2-1)Lambda(rho/2)^2 Lambda(1-3rho/2)/2`.
The cutoff transition, terminal power integral, and all three principal
coefficients are retained before cancellation. Its zero condition is
exactly `xi(5rho/2-1)=0` or `xi(rho/2)=0` or `xi(3rho/2)=0`.
See the [complete angular source evaluation](../3-formalized/hb-effective-angular-source.md).
The actual fundamental horizon and normalizable modes now coincide
exactly with `z^(w/2) sqrt(1-z)`. Both native source integrals combine
into one elementary first-subtracted Mellin moment on [0,1], with
absolute admission and independence of the splitting point proved.
The full residue is that nonvanishing mode times
`A_eff M clearedOnset/E'(w)`. Pole survival is therefore independent
of the interior observation point. See the
[full radial source reduction](../3-formalized/hb-fundamental-radial-source-moment.md).
The remaining pole-survival problem is nonvanishing at these three Xi
arguments together with the elementary radial moment and original
temporal onset factor. Physical adjoint
identification, spin-two/AIME reconstruction, and independent extinction
remain open. Cross-copy
recovery at a zero angular gap requires a confluent construction or
another exact argument; the proved cofactor identity does not remove
that obligation. The frontier map remains read-only.
