# HB: direct source-period attack on radiative extinction

Status: analytical source reduction; physical extinction and RH unproved. Frontier map remains read-only.

## Reflection, conjugation, and the positive-current test

The actual local action identity `D4BMActionBoundary.literal_action_boundary_near_zero`
and literal differential Bianchi identity hold for arbitrary complex source parameters.
They retain the boundary divergence; they do not select Xi occurrences. The fixed-domain
translation test therefore still requires the completed boundary pairing, as recorded in
`hb-fixed-clock-source-translation.md`.

A second test uses the physical reader itself. Write `rho=x+i t`,
`nu=(rho-1)/2`, `mu=nu^2-1/4`, and
`psi=scalar nu`. All quantities here are the existing literal full Eisenstein field,
including its Fourier tail. Let `S rho=1-conj rho`.

**Conjecture tested:** reflection and conjugation turn the reader's Green identity into
a nonnegative norm with coefficient proportional to `x-1/2`.

The exact coefficients distinguish two different identities:

```
mu(rho)-mu(S rho) = (x-1/2) * (i t-1/2),
mu(rho)-conj(mu(S rho)) = (1-2 rho)/4,
mu(rho)-conj(mu(rho)) = i (x-1) t.
```

The first coefficient multiplies the **bilinear** product `psi(rho)*psi(S rho)`.
Adding conjugation to the second reader changes the spectral coefficient to the second
line. Pairing the reader with its own conjugate gives the positive density `|psi|^2`,
but its coefficient is the third line, nonzero at every Xi occurrence since
`0<x<1` and `t!=0`. In particular it does not vanish on the critical line.
Thus these Green identities do not furnish the proposed positive clock-defect identity.
This rejects that specific substitution, not extinction of the complete nonlinear action.

**Positive survivor, formalized.** With original chart coordinates and original
hyperbolic Laplacian, define

```
J_j = conj(psi) * partial_j psi - psi * partial_j conj(psi).
y^2 * (partial_0 J_0 + partial_1 J_1)
    = i (x-1) t * |psi|^2.
```

Proof: expand both product derivatives; the first-derivative products cancel.
Use the full literal equation `Delta psi=mu psi` and its conjugate, then the third
coefficient identity above. The real number `(x-1)*t` is nonzero. Therefore this
current is divergence-free at a point exactly when the actual reader vanishes there.
The current is not divergence-free everywhere: the existing exact horizontal mean at
height one is `Lambda(rho-1)`, which is nonzero by the physical cutoff calibration.
This is an unconditional source-specific obstruction, with a positive density and an
exact coefficient, rather than a hypothetical off-line Xi example.

The survivor identifies a required term for any attempted Hermitian positive-current
proof. It does not identify this angular current with the complete Einstein left-QNM
action. The solved `++`/`+-` corrections, independent SS/SV/VV channels, changing
metric weights, horizon, characteristic and source-contact terms remain in that
separate comparison. No boundary flux in that comparison is set to zero here.

The broader corpus search also returned `SymplecticCyclicObstruction` and
`PairedTranslationResolventCalculus`. The former requires a common cyclic generator
self-adjoint for the alternating pairing; this has not been established for the two
literal causal sources. The latter proves a positive half-line contact identity for
real damped-exponential packets, not for the complete complex Einstein pairing.
Neither hypothesis may be imported as the missing source law.

**Second pass: the literal nonlinear source, rather than the reader.** The source
field is `S=scalar(rho-1/2)`, with eigenvalue `lambda=rho(rho-1)`. Its current has
the different, critical-line-centered identity

```
div J_S = 4 i delta t |S|^2,  delta=x-1/2.
```

The existing original source is `Q=fullSquarePotential=S^2/2`, with
`E=fullGradientEnergy=y^2[(partial_0 S)^2+(partial_1 S)^2]` and
`Delta Q=2 lambda Q+E`. Applying the same actual derivative calculation gives

```
div J_Q - (conj(Q) E-Q conj(E)) = 8 i delta t |Q|^2,
delta t Im[div J_Q-(conj(Q) E-Q conj(E))]
    = 8 delta^2 t^2 |Q|^2 >= 0.
```

This is the stronger positive survivor: an exact positive local defect density
for the **original quadratic theta source**, retaining its complete nonlinear
gradient contribution. No clock or frequency is adjusted. The gradient term is
complex bilinear before pairing; replacing it with a Hermitian gradient square
would change the source equations.

On a finite smooth angular region D, ordinary Stokes gives the paper consequence

```
delta t Im[integral_boundary(D) J_Q.n ds
             -integral_D (conj(Q) E-Q conj(E)) dmu]
    = 8 delta^2 t^2 integral_D |Q|^2 dmu,
dmu=dx dy/y^2.
```

No infinite-cusp limit or renormalized sign is asserted. The precise remaining
test is whether the full physical causal Einstein pairing cancels the left-hand
flux-minus-gradient-work expression after its `++`/`+-` corrections and all
physical faces are included. The local identity proves neither that cancellation
nor equality of this expression with the reduced complete cokernel. It separates
the source's correct spectral center from the reader's different Green density.

**Lean status, 12 September 2026.**
`ThetaCuspHawkingBMSourceHermitianCurrent.lean` proves the actual reader's exact
spectral density, nonnegative orientation, node classification, and existence of
strictly positive divergence, followed by `source_divergence`,
`square_divergence_sub_gradient_contact`, and `square_oriented_contact_balance`.
Public source conclusions take only an actual Xi occurrence and an original
positive-height chart point; no source equation, covariance, sign, or extinction
premise is supplied. The finite-region Stokes consequence above remains a paper
consequence, not an integrated Lean theorem. Scratch check and exact cached leaf
audit passed without warnings; the leaf audit took 237 seconds. The module is wired
into `RHTower.lean`; no umbrella or full build was run.

## Consequences for the whole HB proof chain

The reader obstruction rejects the substitution of a Hermitian reader norm for
the physical projection. It does **not** reject source conservation, full-source
reflection, a direct sign estimate, or HB. The half-square identity gives a
source-centered positive density, but does **not** prove that this density is the
Einstein action's clock-defect energy. These are different quantities until an
actual comparison is proved.

The current corpus distinguishes three levels which must remain separate:

1. The literal causal response and physical projected mode/action are constructed.
   The normalizable temporal radial join retains both horizon branches and its
   source/contact and counterterm contributions. Its angular integration and
   comparison with the complete independent-channel nonlinear action remain open.
2. `hbXiPeierlsCanonicalFullCokernelCausalCutAt` is a fixed global algebraic model
   with `hbXiPeierlsPropagator` as retarded response and zero advanced response in
   both graded channels. Its exact realization theorem is a theorem about that
   defined split. It does not identify the actual Einstein retarded and advanced
   inverses or the complete physical left-QNM functional with that model.
3. For that reduced complete cokernel, the source-clock transduction is closed:
   `K=-Sigma*|D|^2`, `Sigma>0`, and `|D|^2=delta^2*|cocycle|^2`, with nonzero
   original cocycle. This is the receiver for a source theorem, not the producer.

### Competing mechanisms and their decisive tests

**Source reflection: positive transport and the surviving reader defect.** The
team's `ThetaCuspHawkingBMLiteralSourceReflection` now proves the full scalar,
coexact vector and fundamental metric branch exchange from divisor reversal,
Bessel order reflection and the nonreal completed functional equation. The
new `ThetaCuspHawkingBMSourceReflectionTransport` transports the four-amplitude
raw metric/source family, the switched mixed tensor and its onset contacts,
and the actual constructed mixed-stream response. Its 415-line leaf passed
scratch checking and the exact cached leaf build (164 seconds), without
warnings or increased limits, and is wired once into `RHTower.lean`. Source
SHA-256: `873fecaa24fa5056862718f9ba0de7a39c4e7276d803add870e5a53eb6671029`.
The extinction goal remains open; this card is not promoted as a complete proof.
API indexing and scoped whitespace checks completed. The repository-wide formal
lint check reported a separate shared-workspace failure: the newly present
`ThetaCuspHawkingBMScalarStreamMasterIdentity` is unreachable from the theorem-area
umbrella. No lint error was reported for the new reflection-transport leaf; this
is not recorded as a passing global lint run. No owned Lean process remains.

Write `qR=xiZeroCopyReflectEquiv q`, `b'=!b`, and `nu(q)=(rho-1)/2`.
The source's three principal indices reverse, `i -> i.rev`, with

```
k_i(qR)=k_(i.rev)(q),  A_i(qR)=A_(i.rev)(q),
s(qR,b)=s(q,b').
```

This transports the actual principal Green responses, their native full-square
subtractions, and all three differentiated cusp cutoffs. Consequently the
continued joint forcing, its admitted class, and its original wave response
agree after branch exchange. At **fixed physical reader** `r`, the resulting
physical profile, complete reconstructed mixed stream and volume-weighted
Einstein current obey

```
F(qR,b;r,w)=F(q,b';r,w),
A(qR,r,b;w)=A(q,r,b';w),
Hcontact(qR,r,b;w)=Hcontact(q,r,b';w).
```

The already proved `physicalProjectedModeAction_transport` supplies the exact
finite radial boundary identity for this same physical current. With
`lambda_r=nu(r)^2-1/4`, original left radial mode `g_r`, and the actual bilinear
angular factor `N_r=modeAngularSquare(physicalModeAngularJet r z)`, it reads

```
A_rad(t)-A_rad(s)
  = N_r * (-(lambda_r-2)*integral_s^t g_r(x)*F(q,b;r,w,x) dx
           -(Hcontact(t)-Hcontact(s))).
```

Thus the reflected source transports the bulk pairing and **both** finite
endpoint contacts simultaneously at fixed reader. No positivity of the
complex bilinear factor `N_r` is asserted. Infinite horizon/cusp limits and the
completed independent-channel action require their own original admissions;
the field identity is not permission to drop any endpoint or counterterm.

The physical frequency `w`, onset, radial inverse, angular measure and testing
weights remain unchanged. The positive transport result concerns the existing
constructed mixed-stream source and response. It does not yet identify all
independent SS/SV/VV channels or the fully corrected nonlinear action.

For the diagonal physical reader, the exact surviving difference is

```
A(qR,qR,b;w)-A(q,q,b';w)
  = A(q,qR,b';w)-A(q,q,b';w).
```

The reader itself satisfies `scalar(nu(qR))=scalar(nu(q)+1/2)`. Its eigenvalue
difference is `lambda(qR)-lambda(q)=(rho-1/2)/2`, which never vanishes at an
actual Xi occurrence because `Im rho != 0`. The literal eigen-equation and the
reader's proved nonzero Weyl mean therefore rule out equality of the two full
reader fields even on the critical line. This rejects the individual-reader
shortcut; it does not show that the complete nonlinear action difference is
nonzero. Its positive survivor is the fixed-reader action transport and the
exact reader-change remainder, including the transported source contact.

The existing `ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo` is a separate
obstruction: canonical left-coordinate source packets exchange only on the
critical line. Actual literal field exchange is now proved without that
condition, so one must derive their proposed physical incidence rather than
identify those two transports by definition. In addition, the source identity
here is complex-linear branch/parameter exchange. The finite-clock receiver
uses a conjugate-linear cocycle-weighted packet operation. Equality of those
operations after physical realization is still a mathematical obligation.

| Mechanism | Source evidence | Required next mathematical result |
|---|---|---|
| Fixed finite clock translation | Exact original onset/history and terminal-flux balances; local literal action variation | Show that the **sum** of translated history, horizon, cusp, characteristic, source-contact, and metric-weight terms has zero actual left-QNM projection. Stationarity of the kernel alone does not show this. |
| Source Hermitian balance | The new full-source half-square identity, including gradient work | Identify its flux-minus-work with the complete corrected action, or derive a coercive estimate controlling that action. Positivity before the required cusp/causal limits is insufficient. |
| Source reflection and Peierls reciprocity | Existing source-fixed cyclic/skew theorem makes a branch-swapped cubic cut odd | Derive literal branch exchange, admitted causal response transport, complete cyclicity/skewness with every boundary term, and the actual oriented BM incidence. Individual physical reader equality is unnecessary, but its failure must be handled in the projection comparison. |
| Direct sign without clock invariance | Exact negative-square transduction on the reduced model | Prove the opposite sign from the **original** complete physical source/action and justify transfer to the reduced model. A positive norm of an unrelated source or a reoriented convention does not supply this sign. |

For precision, let `C` denote the intended complete physical causal orbit, after
all specified corrections, independent SS/SV/VV channels, weights, and physical
faces have been included. The exact sufficient interface is

```
C = K,                  Re C >= 0.
```

Together with the proved transduction these give
`0 <= Re C = -Sigma*|D|^2 <= 0`, hence `D=0`, hence `delta=0` because the
original source cocycle is nonzero. No clock adjustment enters this implication.
Neither displayed interface property has been proved for that complete physical
quantity here; adding them as Lean premises would not close HB.

A second sufficient interface uses the **reflected sum**, so it need not assert
that either individual physical action has the opposite sign. Work at the
original fixed nonzero source normalization for which susceptibility positivity
is already proved. Retain independent SS/SV/VV coefficients throughout the
construction, and exchange their branch amplitude labels in the reflected cut
`Cswap(qR)`. The precise additional target is

```
Re(C(q)+Cswap(qR)) >= 0,
C(q)=K(q),  Cswap(qR)=K(qR).
```

The two established transductions would then give
`0 <= -Sigma(q)|D(q)|²-Sigma(qR)|D(qR)|² <= 0`.
Both susceptibilities are positive at that original normalization, so both
defects vanish. This does not assert strict susceptibility for arbitrary or
zero amplitudes. Exact oddness of the complete physical cut is one possible
producer of the first inequality; no equality of the individual reader fields
is needed. The new transport result supplies a concrete source/response part
of this test, not its complete cyclic/skew action identity, reflected boundary
admission, or incidence.


An exact equality is not the only possible interface. Writing `C=K+R`, it would
suffice to derive, from the actual equations and boundaries,

```
Re C >= 0,       Re R <= theta*Sigma*|D|^2,       theta < 1.
```

Then `0 <= Re C <= -(1-theta)*Sigma*|D|^2` gives the same extinction conclusion.
This identifies a strict relative-error target for an alternative quantitative
attack. No such estimate is established, and an absolute small-error bound would
not suffice uniformly as `delta` tends to zero. This observation is an interface
calculation, not a new source theorem or a formalized conditional wrapper.

The whole-chain source-reflection test must also respect the literal completion
factor: `reflectedCompletedLambda` is `GammaR*zeta`, not definitionally the totalized
completed zeta at every complex argument. Functional-equation transport for the
original nonreal Xi parameters can discharge the exceptional-point exclusions;
an unrestricted parameter claim cannot silently ignore them.

Broad searches for passivity and reciprocity supplied two further comparisons:

- [Borja and Ortega, Introduction to Passivity-based Control, 15 August 2026](https://arxiv.org/html/2608.15222v1),
  Definition 1 and Theorem 1: the storage inequality constrains a specified
  input/output supply pairing. For HB, the missing transfer is identification of
  that pairing with the actual left-QNM action. Choosing a different passive output
  would change the target. The paper supplies neither that identification nor
  finite-clock extinction.
- [Vu et al., Reciprocity can halve what a mechanical network can learn, 3 September 2026](https://arxiv.org/html/2609.04169v1),
  Theorem 1: symmetry of an invertible stiffness matrix constrains the response on
  overlapping drive/read coordinates. The useful HB test is whether reciprocity
  survives its distinct source and reader maps. That finite-dimensional theorem
  does not establish covariance or a sign for the full causal Einstein projection.

The whole-chain deep requests on action identification, source sign, and retarded
reflection were partial; their unfinished semantic stages and unverified ingredient
sets are retained in the search artifacts. A separate whole-corpus theta/reflection
hybrid request completed. None establishes exhaustive semantic coverage. Candidates
were checked against source definitions, including the canonical response split and
the assumptions of the source-fixed reflection theorem.

Corpus-wide deep/hybrid requests used translation/support, cyclic quartic
response, homogeneous character selection, conjugate Green/resolvent identities,
and retarded variational elimination, without a module filter. The retrieved
snapshots inventoried 57,236–57,237 files; most compiler metadata remained pending
and semantic coverage was unmeasured. One reader/norm hybrid request was partial
with interrupted retrieval stages. Returned ingredient groups were inspected but
not treated as proofs; in particular Keldysh resolvent algebra does not by itself
supply a Schwinger–Keldysh physical action.

Broad recent-paper searches also led to two checked primary sources:

- [Moody et al., QMaxCal, 18 June 2026](https://arxiv.org/html/2606.19947v1),
  equations (8)–(10): a drift-difference square controls path-space relative
  entropy under a shared diffusion model. HB has no independently established
  such path measure. Optimizing the reference drift cannot supply the prescribed
  common-clock theorem.
- [Gruber et al., Flexible and Stable Dynamics Discovery with Onsager's
  Variational Principle, 23 June 2026](https://arxiv.org/html/2606.24106v1),
  Definition 2.1: the variational balance requires a specified free energy,
  convex dissipation potential, and process map. These are not established for
  HB's complete complex causal action. This remains an unproved transfer, not a
  counterexample or an extinction theorem.

A further whole-corpus deep source-transport request completed without retrieval
errors, inventory 57,245 files, but without measured exhaustive semantic
coverage. Its generated matrix-defect and generic transport suggestions did
not discharge physical action incidence. A hybrid variational/reciprocity
request (57,246 files) recovered the actual `pairedSource_cubic`: its varying
test/volume term is `testWeightSlope * quadraticResidual` and must remain until
the **complete** quadratic equation is solved. Neither the source's scalar
reflection nor a fixed-background symplectic formula erases that term.

[Ghomi, 28 August 2026](https://arxiv.org/html/2608.28410v1), Theorem 1.1 and
Corollary 3.2, supply a different mechanism worth testing: a convex geometric
functional along a reflection path has equal endpoint values; the original
first-variation equation makes its endpoint derivative zero, forcing constancy
and then rigidity. For HB, the corresponding attempt requires a source-derived
convex complete action with its original boundary variations. No such
convexity or stationary endpoint has been proved for the complex causal
Einstein action. The result does not license choosing a new positive
functional. Broad crossing/polarization/variational searches returned no
additional usable recent theorem in this request; the direct arXiv search
pages failed to fetch. No claim of exhaustive literature coverage is made.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains the complete physical quantity `2 Ω(B(p,p)/2, B(m,m)/2)`, including full tensor corrections, time onset, horizon and AdS terms. A scalar source moment is a test of a proposed cancellation mechanism, not a replacement for that target.

## Frozen cancellation conjecture and tests

Conjecture: the literal source relations force cancellation between the complete causal bulk pairing and its actual endpoint terms at the fixed Hawking clock. This remains unproved. No zero-pairing premise may be inserted in its construction.

The working method is conjecture → attempted proof or falsification → pivot. Do not resume general action-current infrastructure unless a specific step in a source-level proof needs it. Failed proof attempts and falsified statements must be distinguished.

The current positive result is the [exact onset decomposition of the full original mixed scalar source](../3-formalized/hb-full-source-onset-reduction.md). It reuses the existing global angular inverse and identifies the actual time-dependent remainder as a fixed ingoing onset pulse. The incoming horizon profile is explicitly `H-s(s-1)Q/4`; it must remain in the causal pairing. The next primary test is cancellation between this horizon contribution and the pulse response in the complete tensor action, including the missing scalar-scalar and vector-vector channels. Do not substitute an isolated scalar-pole or normalization theorem for that test.

**Active tensor test.** The [Einstein radial action current](../3-formalized/hb-mixed-radial-action-current.md) is proved by differentiating the actual volume-weighted action current. The [original-source contact reduction](hb-causal-onset-contact-cancellation.md) identifies the pulse term that cancels the particular field's explicit `D_chi=integral exp(-6v)*chi'^2` coefficient. The remaining local contribution has only `C_chi=integral exp(-6v)*chi²` and the exact complex factor `2s+3`. This is a local analytical source identity; actual causal horizon admission and global integration remain open. The explicit unresolved term is equation (6) in that card: the pulse's horizon pairing through `roughLaplacian-1`, its cross terms with the particular field, and its original-source contact terms. Equation (7) reduces the cross terms to one source-derived test while retaining time and cusp boundaries. Evaluate that causal pulse term next; do not repeat the squared-onset coefficient check. Full extinction also requires every other tensor-sector pairing. With independent branch polarizations, SS–VV and SV–SV carry different amplitude monomials; do not combine their coefficients without a source-derived relation. No physical extinction is proved.

1. **Test: the original fundamental source is a cubic endpoint primitive.** The exact reduction below leaves one period with an explicitly fixed coefficient. At `s=w=0`, the source integral is `2/3`; the coefficient of the remaining period is nonzero. Thus the proposed universal pure-cubic-primitive identity fails. This is not a counterexample to extinction at a Xi divisor, and does not retire HB. The positive result is the explicit primitive-plus-period decomposition.
2. **Test: the complementary period is obtained by exchanging the two physical QNM branches.** The period identity exchanges `(w,2s)`. The actual target frequencies have real part between `-2` and `-1`, whereas the source rates `2s` have real part between `-4` and `-2`. Thus simple physical branch exchange does not perform the needed period exchange. The canonical left connection covectors also act on source/response coordinates at a fixed spectral parameter; their proved normalization is not the missing source-rate exchange. This rejects that proposed proof step, not every possible augmented adjoint identity.
3. **Positive source test: do radial and angular completion use independent affine arguments?** They do not. The original radial quadratic coefficient factors through the same `5 rho/2-1` and `3 rho/2` arguments appearing in the evaluated angular source, and their functional-equation complements. The exact identities are below. Whether the *full tensor causal pairing* uses these factors with the required orientation remains open.

**Causal value construction.** The [source-only circle kernel](hb-causal-horizon-circle-kernel.md) gives an analytical formula for the full horizon response using the literal theta-square field, the original radial source polynomial, and finite hyperbolic circle averages. Its pulse comparison closes by an exact radial flux identity and cancellation of the moving AdS image endpoint. The [scalar Riemann kernel](../3-formalized/hb-causal-riemann-kernel.md) has actual derivative, original BM wave, characteristic, causal support, and AdS boundary theorems in Lean. Full angular Green identification, horizon admission, and evaluation of the resulting Einstein pairing remain open. The next cancellation test uses this explicit source-only response, retaining every tensor sector and all endpoint terms.

## Actual radial source, without setting w = 2s

The starting definitions are `D4BMJointSource.fundamentalSourceCore` and `fundamentalSourceMoment`, together with `D4BMLaplaceRadial.sourceRemainder`. The corpus already identifies the original two-endpoint moment with its full first-subtracted Mellin integral at every physical fundamental QNM.

Put `y=sqrt(1-z)`, `alpha=2s-w`, `beta=2s+w+2`, and

```
A = (5s²+15s+4)/4
C = s(s-1)(alpha+2)(beta+3)/8.
```

The factorization follows directly from

```
(s+2)² - [(w+1)(w+2)/2 - (s+1)(s+2)]
  = (2s-w+2)(2s+w+5)/2.
```

The actual density transforms to

```
2 a² y² (1-y)^w (1+y)^(2s) (A+C y²) dy.
```

This is a change of coordinate in the original source, not a new source model. The original horizon finite part must be transported with the coordinate change.

Let `D=beta(beta+1)(beta+2)`, `U=s(s-1)(alpha+2)`, `V=5s²+15s+4`, and define the denominator-cleared cubic `P(y)=c0+c1 y+c2 y²+c3 y³` by

```
c3 = -U beta(beta+1)(beta+2)/4
c2 = -U alpha beta(beta+1)/4
c1 = -beta [U(3beta+6+alpha²)+2V(beta+2)]/4
c0 = -alpha [U(5beta+8+alpha²)+2V(beta+2)]/4
R  = c1+alpha c0.
```

Its exact polynomial identity is

```
(1-y²)P'(y) + (alpha-beta y)P(y)
  = 2D y²(A+C y²) + R.
```

Both this denominator-cleared identity and the original source factorization passed `lake env lean` scratch checks, with only `propext`, `Classical.choice`, and `Quot.sound`. They have no premises. They are not installed as standalone corpus leaves: the integral/physical-pairing result, rather than two isolated algebra lemmas, is the intended deliverable.

Multiplying by `(1-y)^w(1+y)^(2s)` identifies the left side as the derivative of

```
(1-y)^(w+1)(1+y)^(2s+1) P(y).
```

For `Re w>-2`, `w+1 != 0`, and `D != 0`, define the endpoint period by

```
I(w,s) = lim_(b→1-) [integral_0^b (1-y)^w(1+y)^(2s) dy
                     + 2^(2s)(1-b)^(w+1)/(w+1)].
```

The Taylor remainder at `y=1` is first order, so the subtracted integral converges. Transporting the original `z`-cutoff finite part gives the analytical formula

```
fundamentalSourceMoment(w,s,a) = -a² [c0 + R I(w,s)] / D.
```

To check the finite-part transport, set `z=epsilon`, `b=sqrt(1-epsilon)`. Then `epsilon=(1-b)(1+b)`. The primitive's leading divergent term cancels the original source subtraction and the period subtraction because

```
-2(w+1)P(1) = 2D(A+C)+R.
```

Every remaining endpoint error is `O(epsilon^(Re w+2))`, hence tends to zero. The AdS endpoint is `y=0` and contributes `-c0`. This establishes the paper reduction; the integral identity and its complete Lean admission are not yet formalized.

## Substitution of the actual Xi parameters

For `rho=q.1`, the source rates are `s=rho-2` and `s=-rho-1`; the two target frequencies are `w=-1-rho/2` and `w=-2+rho/2`. They remain independent slots.

| Source rate | Target | alpha+2 | beta+3 | beta |
|---|---|---|---|---|
| `rho-2` | `-1-rho/2` | `5rho/2-1` | `3rho/2` | `3rho/2-3` |
| `rho-2` | `-2+rho/2` | `3rho/2` | `5rho/2-1` | `5rho/2-4` |
| `-rho-1` | `-1-rho/2` | `1-3rho/2` | `2-5rho/2` | `-5rho/2-1` |
| `-rho-1` | `-2+rho/2` | `2-5rho/2` | `1-3rho/2` | `-3rho/2-2` |

Since actual Xi divisors have nonzero imaginary part, `D != 0` in all four cases. The target-branch exchange swaps the two factors in C; it does not change C at a fixed source rate. Both source branches have

```
A = (5rho²-5rho-6)/4.
```

Writing `x=5rho/2-1`, `v=3rho/2`, the two C coefficients are

```
C_plus  = (rho-2)(rho-3) x v / 8
C_minus = (rho+1)(rho+2) (1-v)(1-x) / 8.
```

Thus `C_plus*C_minus` contains the completion polynomial `x(x-1)v(v-1)`. These are exactly the two non-repeated affine arguments in `physicalSelfSourceCoefficient_fourLambda`; the repeated argument is `rho/2`. This is an exact source normalization relation, not evidence by itself that the full pairing vanishes.

## Complementary-period candidate: required admission and missing identification

In the ordinary convergence chamber, splitting the complete interval at zero gives

```
I(w,s) + I(2s,w/2)
  = integral_(-1)^1 (1-y)^w(1+y)^(2s) dy
  = 2^(w+2s+1) integral_0^1 t^w(1-t)^(2s) dt.
```

Continuation to the physical parameters cannot use the same first subtraction in both terms. For the exchanged term, `-4<Re(2s)<-2`, so subtract the three actual Taylor terms of `(2-t)^w`:

```
2^w [1 - w t/2 + w(w-1)t²/8].
```

The corresponding restored boundary terms are

```
2^w [1/(2s+1) - w/(2(2s+2)) + w(w-1)/(8(2s+3))].
```

The remainder is `O(t³)`, giving absolute admission because `Re(2s)+3>-1`. These coefficients are forced by the candidate period, not adjustable counterterms. None has yet been identified with the actual augmented Einstein horizon/AdS/onset terms. The continuing hard attack is that identification with the *complete* scalar-scalar, scalar-vector, and vector-vector source and its causal corrections. A scalar period completion must not be promoted to physical extinction without it.

## Actual source-reflection test, 12 September 2026

This tests cancellation in the requested physical pairing, not the deferred invented differential generator. No extinction theorem or new Lean leaf results from the test.

At the input, reflection `rho -> 1-rho` exchanges `s=rho-2` and `t=-rho-1` without changing the original clock or onset. The completed angular scalar is even in its centered parameter: in its Fourier coefficient `n^u sum_(d|n) d^(-2u)`, the divisor substitution `d -> n/d` gives the coefficient at `-u`; the Bessel factor satisfies `K_u=K_(-u)`, and the two Weyl terms exchange by the completed functional equation. Hence the literal half-square is unchanged. This literal source identity is now proved in Lean; the actual metric/source coefficients exchange with their scalar/vector amplitude labels, and the source-reflection transport result above reaches the constructed mixed response at each fixed physical reader. It does not establish the complete corrected physical pairing's reflection law.

The marked physical reader has a different transformation. The current definitions and proved formulas are `physicalAngularParameter_eq`, `physicalScalar_principal`, `physicalScalar_cutoff_calibration`, and `physicalFundamentalFrequency_eq`. For their actual testing field `psi_q`, put

```
nu_q=(rho-1)/2,               mu_q=nu_q²-1/4=rho(rho-2)/4,
nu_Rq=-rho/2,                mu_Rq=(rho²-1)/4,
mu_q-mu_Rq=(1-2rho)/4.
```

The difference is nonzero at every actual Xi occurrence because `Im rho != 0`. In particular it is not a defect that disappears on the critical line. The two original fundamental frequencies obey

```
w_+(Rq)=w_-(q)+1/2,
w_-(Rq)=w_+(q)-1/2.
```

These are comparisons of the original frequencies, not replacements of them. Thus input branch exchange does not preserve the marked angular eigenspace or exchange the prescribed QNM frequencies without a shift. The independent angular source equations give the exact paper identity

```
(Delta-mu_q)(psi_q-psi_Rq)=(1-2rho)psi_Rq/4.
```

The right-hand field is nonzero: the existing cutoff-calibration theorem gives a nonzero actual period for it. The Xi zero removes one Weyl coefficient, but leaves the explicit principal reader terms

```
psi_q,principal  = Lambda(rho-1)y^(1-rho/2),
psi_Rq,principal = Lambda(-rho)y^((1+rho)/2),
```

with both coefficients nonzero. Consequently an argument using antisymmetry at a *fixed* reader must still evaluate the difference of the two actual readers, including its forced bulk and principal cusp terms. Antisymmetry alone does not cancel this difference. This does not prove that the complete nonlinear difference is nonzero: every solved correction, all nine independent channel pairings, and their original boundary terms can still contribute to its evaluation.

There is a further scope restriction on a proposed arithmetic cancellation. `physicalSelfSourceCoefficient_fourLambda` assumes `1/2 < Re rho`. Its reflected copy lies in the opposite half-strip. Substituting that copy into the theorem, or continuing an identity known only at discrete Xi occurrences by the identity theorem, is not licensed. No new formula for the reflected complete physical source coefficient is asserted here.

The direct unresolved task remains evaluation of the complete source pairing with these original readers. Neither the source reflection identity nor the one vanished Weyl coefficient proves `Cphys=0` or `Re Cphys>=0`. The reduced identity `K=-Sigma|D|²`, with `Sigma>0`, remains a receiver until that actual cancellation or sign is produced.

The deep four-source and source-reflection searches and the hybrid response-pairing method search returned no retrieval errors with 57,233 inventoried files; most compiler metadata remained pending. Candidate statements, source methods and ingredient groups were inspected. Abstract reflection-odd Peierls theorems require source/reader incidence; the retrieved rotation, matrix-norm and generic Maass-flux ingredients do not evaluate the present pairing. Broad searches used scattering, crossing, sum rules, resonance and reciprocity. [Khankhoje–Kundu, 12 June 2026](https://arxiv.org/html/2606.14486v1), Sections I–III, distinguish full reciprocal scattering from coefficients that omit coupling and boundary effects. Their linear electromagnetic reciprocity does not supply an Einstein source identity or the marked QNM-reader comparison. No numerical work or external theorem premise was used.
