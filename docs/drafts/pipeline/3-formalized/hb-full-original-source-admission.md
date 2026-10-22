# HB full original-source admission

- **Stage:** 3-formalized.
- **Goal:** unconditional closed Lean proof/falsification of RH; open.
- **Scope:** exact original-wave cusp residual, its joint L² admission, and its constructed operator-domain response.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact theorem

For every actual Xi occurrence, both physical branches, and original amplitude
and transformed-onset coefficient, a whole nonempty right frequency half-plane
admits the following construction. An explicit field U0 retains the full scalar
square and all three principal cusp powers. The difference between the original
forcing and the actual differentiated wave of U0 belongs to the original joint
L² space. Its constructed joint energy response u belongs to the unbounded
operator domain, satisfies `(A+w²-1)u=F`, and obeys

`||u|| <= ||F||/(Re(w)*|w|)`.

No source-integrability, angular-diagonalization, or response premise is supplied.
The frequency region is proved nonempty for every occurrence. This does not yet
give the classical modular representative of the joint correction, time-causal
inversion, constrained Einstein reconstruction, or the extinction pairing.

## Exact absorption of the gradient source

Use the corpus's actual theta scalar S and original potentials
`Q=S²/2`, `E=|grad S|²_bilinear`. This energy is complex bilinear, without
complex conjugation. The proved identities are

`Delta Q=2LQ+E`, `L=(s+1)(s+2)`, `coexact Q=J`, `coexact E=2K`.

For original tortoise t<0 let `u=1/r=-sinh(t)/cosh(t)` and `z=1-u²`.
Lean proves `0<u<1`, `u'=u²-1`, `z'=2uz`, and that z is exactly the squared
angular weight in the joint energy domain. Write

`R=exp(w*t)*a²*(1+u)^(2s)*T`, `c=s(s-1)/4`, `A0=(5s²+15s+4)/4`.

The actual original normalized forcing, with both angular potentials retained, is

`F_orig=-2zuR*[A0*Q+c*u²*((s+2)²*Q-E/2)]`.

Choose the explicit lift `b=-c*R*u³`. Its actual derivatives are proved from
`R'=[w+2s(u-1)]R`. Set `a1=w+2s(u-1)` and

`P2=a1²*u³+6*a1*u²*(u²-1)+2s*(u²-1)*u³`
`   +6u*(u²-1)²+6u³*(u²-1)`.

Then `b''=-c*R*P2`. For the actual wave
`W_w U=w²U-partial_t² U-z*Delta U`, the exact identity is

`F_orig=W_w(bQ)+C*Q`,

where

`C=R*[-2zu*(A0+c*(s+2)²*u²)+c*(w²*u³-P2)-2z*L*c*u³]`.

The same cancellation is proved directly for the original covectors using
`D_ang J=2LJ+2K`. Thus the full gradient source is carried by bQ; its admission
does not require a separately assumed gradient-remainder estimate.

## All three principal responses and the exact cutoff residual

For rho equal to the actual Xi parameter, retain both original Weyl coefficients
in `P(y)=c_plus*y^rho+c_minus*y^(1-rho)`. The exact half-square is

`Q0=P²/2=sum_i J_i*y^k_i`,

with `k=(2rho,1,2-2rho)` and
`J=(c_plus²/2,c_plus*c_minus,c_minus²/2)`. The cross term is retained.
For these three explicit powers only, use

`chi_i=I*(k_i-1/2)`, `1/4+chi_i²=k_i*(1-k_i)`,
`K_i=[k_i*(k_i-1)/2-L]*J_i`.

Let g_i be the previously constructed endpoint Green response with these
original radial parameters and coefficients. The exact tortoise derivatives
of the actual Green integrals are proved. Therefore `d_i=g_i-b*J_i` satisfies

`w²*d_i-d_i''-z*k_i*(k_i-1)*d_i=C*J_i`.

Use the actual smooth height cutoff eta, zero below height 2 and one above
height 3. Define the full differential commutator

`M_i=Delta(eta*y^k_i)-eta*k_i*(k_i-1)*y^k_i`.

No cutoff derivative is dropped. The explicit field is

`U0=bQ+sum_i d_i*eta*y^k_i`.

Actual radial second derivatives and finite-sum metric angular differentiation
give the pointwise identity, for every t<0 and every positive-height chart point,

`F_orig-W_w U0=C*(Q-eta*Q0)+sum_i z*d_i*M_i`.

The commutator terms have the displayed positive sign. Neither this identity nor
the joint inverse assigns an angular eigenvalue to the full theta square.

## Joint admission proof

The radial measure is Lebesgue measure restricted to t<0. Any profile
`exp(w*t)*H(u(t))`, with H continuous on [0,1] and Re(w)>0, belongs to radial
L²: compactness bounds H and the exact exponential is square integrable.
This admits b and C with all amplitude derivatives included.

For each actual Green response, divide by its proved horizon factor `z^(w/2)`.
The existing endpoint theorems give finite limits at both z=0 and z=1.
Extend this normalized response continuously to [0,1], and use the exact identity

`z^(w/2)=exp(w*t)*(1+u)^w`.

The compact-profile argument now admits g_i, d_i, and z*d_i on the entire
half-line. A sufficient common frequency threshold is
`1+sum_i |Im chi_i|`; every larger real part lies in all three Green chambers.

Angularly, above height 3, `Q-eta*Q0` equals half the native squared-scalar
remainder. The corpus's bound retains both cusp legs and every tail term.
Each M_i is continuous and vanishes above height 3 by an equality of actual
local field germs and the proved power Laplacian. On the lower part of the
modular fundamental domain, continuity gives a compact-box bound. Finite
invariant modular measure therefore admits both the full square residual and
every commutator in angular L².

Products of these actual radial and angular L² functions belong to joint L²
by the product-integrability theorem for their squared norms. Finite summation
admits the complete displayed residual. The resulting L² vector agrees almost
everywhere with `F_orig-W_w U0`. Applying the previously proved joint inverse
gives the actual unbounded-domain response and its frequency estimate.

## Lean surface and audit

Canonical prefix: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSource`.
Namespace: `RHTower.D4BMJointSource`.

Suffixes: `RadialUnit`, `Amplitude`, `LiftJets`, `GradientReduction`,
`RadialAdmission`, `AngularAdmission`, `CompactPower`, `GreenAdmission`,
`PrincipalData`, `CutoffCommutator`, `ResidualCoefficients`, `ResidualAssembly`,
`GreenTortoiseJets`, `PrincipalEquation`, `ExplicitResidual`, `FieldDifferential`,
`Response`.

The final theorem is `originalSource_response`. Its forcing is identified with
the actual differential residual by `cuspResidualVector_actual_ae` and
`originalWaveResidual_eq`; `explicitField_wave` proves the full derivative
identity.

Development used foreground `lake env lean` scratch checks. All seventeen exact
canonical `lake build <module>` audits passed, each compiling only its new leaf
plus bookkeeping (two jobs). All seventeen source pairs and thirty-four installed
olean/ilean artifact pairs match the audited bytes. All leaves are wired once
into RHTower; no umbrella or dependency build was run. One scratch axiom audit
of only the sixty new public theorems found only `propext`, `Classical.choice`,
and `Quot.sound`. Source indexing, scoped proof-debt checks, and whitespace
checks passed.

Global `lint --check-generated` reports one unrelated concurrent module
unreachable from RHTower: `MobiusDivisorPrimePairRatioProfile`, alongside existing
large-file warnings. It reports no new HB leaf issue. The unrelated module was
left untouched. The frontier map was not edited; no new route-independent law
was added to STATUS.

## Remaining hard obligations

Construct a classical modular representative of the joint correction and prove
its original coexact wave equation, including the cusp patch and radial boundary
conditions. Prove frequency dependence and time-causal inversion for the actual
source family. Continue the constrained Einstein sectors and left-QNM action
pairing, then establish the independent Hawking-clock extinction step. The
admitted inverse alone does not constrain Xi zeros. No numerical experiment or
computational certificate enters this construction.
