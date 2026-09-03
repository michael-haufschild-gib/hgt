# Restricted prime--Gamma cubic homotopy defect

- **ID:** ULF-RPGT-001
- **Stage:** 1-in-progress
- **Type:** CANDIDATE · generic operator theorem paper-closed · arithmetic formation theorem open
- **Source:** successor to retired `ULF-INHD-001` and `ULF-DSA-001`
- **Statement:** A pre-divisor prime--Gamma boundary phase has one canonical projection
  displacement whose cube is nuclear and has integral trace equal to the enclosed Xi multiplicity.
  Cubic degree is forced: it is the first grade that is both trace class at critical Hardy
  regularity and odd under reflection.  The missing RH theorem is a degree-three cyclic
  transgression from the literal source colligation to this completed defect.

## Big-picture law

Do not transport a source covariance to a completed zero projector.  Compare the completed
source-formed Hardy polarization with the zero-free Gaussian Euler--continuum polarization and
cube their relative displacement:

```text
R_(D,0) = U_(D,0)* P U_(D,0),
R_(D,x) = U_(D,x)* P U_(D,x),
mathsf T_(D,x) = (R_(D,0)-R_(D,x))^3.
```

`ULF-FACHD-001` proves this formation-anchored version and its independence of the chosen
positive Gaussian scale.  Since every `Phi_x` is zero-free, its relative trace equals the older
normal form `(R_(D,0)-P)^3`; the latter remains useful for generic operator calculations but is no
longer the conceptual source endpoint.

At the natural `H^(1/2)` boundary, `Delta_D` is Hilbert--Schmidt but need not be nuclear.  Its
square is nuclear but reflection-even.  Its cube is the first nuclear reflection-odd quantity,
and its trace is the integral relative index.  The older polar kernel/cokernel projector is only
the endpoint-support shadow of this one cubic operator.

The fusion is

```text
continued prime--Gamma current
  -> multiplicative all-place boundary phase
  -> additive Hardy polarization
  -> one Hilbert--Schmidt projection displacement
  -> its integral nuclear cubic defect.
```

Addition and multiplication meet only after completion.  The cube expands into the difference of
the two positive Hankel channels, so the unsquared logarithmic current is retained without making
either quadratic channel the answer.  Integrality is not imposed on a prime sum: it is the odd
Chern character of their relative completion.

This constructs the requested object.  It does not yet prove source properness excluding a
nonzero component jump.

## Checked corpus facts

Searches used before fixing the object:

```text
scripts/formal_tools.py research "continuedPrimeArchSourceRelativeTrace rectangle zero sum"
scripts/formal_tools.py research "continuedPrimeArchSourceRelativeTrace eq logDeriv XiC"
scripts/formal_tools.py research "one prime source defect rho infinity rho p Hardy"
scripts/formal_tools.py research "balanced index reflection zero unsigned defect"
scripts/formal_tools.py research "literal Euler half density contraction no go"
scripts/formal_tools.py research "one prime Euler Gram commutator canonical Hardy projection noncompact"
scripts/formal_tools.py research "finite Euler Calkin independence noncompact additive combination"
scripts/formal_tools.py research "prime quasi inner Dixmier residue"
scripts/formal_tools.py research "Burnol base nuclear synthesis covariance"
```

1. `continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC` identifies the continued
   pole--Gamma--von-Mangoldt source with `XiC'/XiC` at every admissible point.
2. `rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum` gives its exact
   multiplicity-weighted contour law without a supplied zero list.
3. `fieldOneFiniteStageSphericalScatteringSymbol` is the literal finite all-place product
   `rho_infinity product rho_p`, already unit modulus before any divisor, **but only on the real
   critical-line parameter**.  It is evidence for the local product law, not a strict-right
   formation sequence.  Treating it as a phase on `boundary D` was an error.
4. `connesConsaniOnePrimeSourceDefect` is the literal nonzero Hardy seam
   `(1-P) M_(rho_infinity rho_p) P`; its block-product law preserves the local factors.
5. `HedenmalmThetaKakutaniBalancedIndexNoGo` proves signed reflected index cancels while unsigned
   defect survives.  The object must retain both chiral defects in one grading.
6. `LiteralEulerHalfDensityContractionNoGo` proves raw all-prime Euler multipliers have divergent
   operator norm.  Completion cannot be an ordinary bounded Euler-product limit.
7. `HardyTitchmarshEulerConcrete` and `FiniteEulerCalkinIndependence` prove raw finite Euler
   corners are noncompact and Calkin-independent on the full spectral line.  A relative phase
   topology, not finite compact approximation, is forced.
8. `SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel` proves a literal coefficientwise
   Euler/Wold subtraction: both principal currents are non-summable, their positive mismatch is
   summable and source-defined.  This is an infinitesimal model for the required boundary anomaly,
   not yet its Hardy-space construction.
9. `RoutePPrimitiveBurnolBaseNuclearSynthesis` gives a different prime-mixed nuclear covariance
   with trace `< 1`.  The retired `ULF-INHD-001` proves it cannot be transported to a completion
   horizon by a bounded landing.  It is evidence for scale only, not a budget for the object below.
10. `direct-relative-winding-anchor.md` already retires a naked contour integer.  New content here
    is the same-boundary polar/Hankel identity; without its source formation estimate this remains
    a receiver.

## 1. Pre-divisor source phase

Use the centered spectral coordinate `z`, so

```text
s = 1/2 + i z,
RH axis = { Im z = 0 },
strict-right zeros = { -1/2 < Im z < 0 }.
```

Let `D` be a positively oriented rational rectangle compactly contained in
`-1/2 < Im z < 0`, with admissible boundary.  Fix a piecewise `C1` unit-speed parametrization
`gamma_D : S1 -> boundary D` and a basepoint.  On the boundary define the source connection

```text
omega_D(t) = gamma_D'(t) * continuedPrimeArchSourceRelativeTrace(gamma_D(t)).
```

No zero, divisor copy, or zero ordinate occurs in this definition.  Define its normalized unitary
parallel transport

```text
u_D(t) = exp(i * integral_0^t Im omega_D(r) dr).
```

The total integral is an integer multiple of `2*pi`, so `u_D` is periodic.  Equivalently,

```text
u_D(t)
  = XiC(gamma_D(t)) / |XiC(gamma_D(t))|
    * |XiC(gamma_D(0))| / XiC(gamma_D(0)).
```

The equivalence uses only the source identity `continued source = XiC'/XiC` on the boundary.
The first formula is the source definition; the second proves regularity.

Prime mixing occurs before observation.  In the absolute-convergence chart the connection is the
sum of all prime-power and archimedean logarithmic currents, while exponentiation forms one
multiplicative phase.  Hardy compression is applied only after this product.  Cross-prime terms
therefore occur in its Fourier/Hankel coefficients; no direct sum over primes remains.

## 2. One projection displacement and one cubic defect

Let `H = L2(S1)`, let `P` be the Hardy projection onto `H2`, put `Q=1-P`, and let `U_D=M_(u_D)`.
Define the Toeplitz compression

```text
A_D = P U_D P : H2 -> H2.
```

Conjugate the observer rather than compressing prime cells separately:

```text
R_D = U_D* P U_D,
Delta_D = R_D-P,
mathsf T_D = Delta_D^3.                                (RPGT.1)
```

This is the object nobody asked for.  `Delta_D` is the change of additive polarization caused by
the fully mixed multiplicative source phase.  It is Hilbert--Schmidt at critical regularity;
`mathsf T_D` is one self-adjoint nuclear integral operator with integer trace.

The familiar polar defect is derived from it, not the primary object.  If `W_D` is the polar
partial isometry of `A_D`, put

```text
Pi_D = diag(1 - W_D W_D*, 1 - W_D* W_D)
     = diag(Pi_(ker A_D*), Pi_(ker A_D)).                (RPGT.1p)
```

The `+1/-1` endpoint spectrum of `Delta_D` is exactly the two blocks of `Pi_D`; all non-endpoint
spectral values occur in opposite pairs and cancel in the cubic trace.

## 3. Integral--nuclear homotopy theorem

`ULF-RUCRI-001` gives the dependency-closed theorem that directly governs `mathsf T_D`:

```text
mathsf T_D
  = R_D Q R_D - P (1-R_D) P,                            (RPGT.2c)

Tr mathsf T_D
  = ||H_(u_D*)||_HS^2 - ||H_(u_D)||_HS^2
  = wind(u_D) in Int.                                   (RPGT.3c)
```

Moreover the integral kernel of `Delta_D` is

```text
d_D(z,w) = (conj(u_D(z))*u_D(w)-1) K_P(z,w),            (RPGT.4c)
```

and the kernel of `mathsf T_D` is its threefold cyclic convolution.  This formula makes all-prime
mixing literal: exponentiating the Euler logarithm creates mixed prime monomials inside
`conj(u_D(z))*u_D(w)-1` before the three kernels are composed.

The following older polar formulation remains useful for unsigned multiplicity.

**Theorem RPGT-A.** Let `u : S1 -> U(1)` be piecewise `C1`.  Put `A=P M_u P` and let `W` be its
polar partial isometry.  Then:

1. the two Hankel seams

   ```text
   H_u     = Q M_u P,
   H_uStar = Q M_(conj u) P
   ```

   are Hilbert--Schmidt;
2. `A` is Fredholm and

   ```text
   1 - A* A = H_u* H_u,
   1 - A A* = H_uStar* H_uStar;                         (RPGT.2)
   ```

3. `Pi(u)=diag(1-WW*,1-W*W)` is positive finite-rank, hence nuclear;
4. Coburn's alternative makes one of `ker A`, `ker A*` zero, so

   ```text
   Tr Pi(u) = |wind(u)| in Nat;                          (RPGT.3)
   ```

5. with `Gamma=diag(+1,-1)`,

   ```text
   Str_Gamma Pi(u)
     = dim ker(A*) - dim ker(A)
     = wind(u)
     = ||H_uStar||_HS^2 - ||H_u||_HS^2;                 (RPGT.4)
   ```

6. each kernel projection is dominated by its own contraction defect, hence

   ```text
   Tr Pi(u) <= ||H_uStar||_HS^2 + ||H_u||_HS^2.          (RPGT.5)
   ```

**Proof.** Piecewise `C1` gives `u in H1(S1)`, hence
`sum |n| |uHat(n)|^2 < infinity`; the two weighted positive/negative Fourier sums are precisely the
two Hankel Hilbert--Schmidt norms.  The block multiplication identities give `(RPGT.2)`, so `A` is
unitary modulo compact operators and Atkinson gives Fredholmness.  Polar decomposition identifies
the two complements of the initial/final spaces with `ker A` and `ker A*`.  Coburn's theorem and
the Toeplitz index formula give `(RPGT.3)`.  The Fourier winding identity
`wind(u)=sum n |uHat(n)|^2` gives `(RPGT.4)`.  For every contraction,
`Pi_(ker A) <= 1-A*A` and `Pi_(ker A*) <= 1-AA*`; taking traces gives `(RPGT.5)`.  QED.

For the source phase, the argument principle and the corpus contour theorem give the exact fusion

```text
Tr mathsf T_D
  = Tr Pi_D
  = Str_Gamma Pi_D
  = wind(u_D)
  = (1/(2*pi*i)) integral_(boundary D)
      continuedPrimeArchSourceRelativeTrace(z) dz
  = sum_(rho in D) multiplicity(rho).                    (RPGT.6)
```

Because `D` lies in the strict-right chamber, the winding is nonnegative; ordinary trace and
supertrace of the polar support coincide.  Reflection replaces `u_D` by its adjoint, sends
`Delta_D` to the oppositely oriented projection pair, and swaps the two polar blocks:
`Tr mathsf T_D` changes sign while `Tr Pi_D` survives.  One operator carries orientation through
its odd trace; its endpoint support carries unsigned multiplicity.

## 4. Why this escapes the retired `T`

`ULF-INHD-001` tried to map vanishing finite horizon projectors through a bounded Hilbert--Schmidt
landing.  Dense-core continuity forced the result to vanish.

Here finite all-place stages already have nonzero Hardy seams.  No finite defect projector is
transported, and `mathsf T_D` is not a trace-norm limit of finite cubic defects.  It is formed after the
all-prime phase is restricted to a compact boundary, where it lies in `H^(1/2)`.  Realizing that
phase as a proper limit of finite source phases remains the open theorem.  Its nuclear domination
comes from its own two seams `(RPGT.2)`, not from an unrelated Burnol covariance.

This also explains why the full-line noncompactness theorems do not kill the construction: they
forbid raw compact completion on `L2(R)`.  `mathsf T_D` is a compact-window relative index.  Passing
cofinally to all windows requires a renormalized formation law, not operator-norm convergence.

## 5. Exact RH closure

If RH fails, functional-equation symmetry supplies a strict-right zero.  A rational admissible
rectangle `D` can be chosen around it inside `-1/2 < Im z < 0`.  Then `(RPGT.6)` gives

```text
Tr mathsf T_D >= 1.                                     (RPGT.7)
```

Therefore the following source theorem closes RH immediately.

**RPGT-Formation (open).** From literal natural-number Euler formation and Poisson/theta
self-duality, construct on every admissible `D` a canonical zero-winding counterphase `a_D`, before
any divisor is supplied, such that `v_D=a_D^(-1)u_D` is the relative completed phase and

```text
||H_(v_D*)||_HS^2 + ||H_(v_D)||_HS^2 <= B_D < 1.         (RPGT.8)
```

The counterphase must be the boundary integration of a coefficientwise source anomaly, not an
outer factor chosen from Xi zeros.  Since `wind(a_D)=0`, `(RPGT.3)`--`(RPGT.6)` remain unchanged.
Then `(RPGT.5)` and `(RPGT.8)` imply `Tr mathsf T_D<1`, contradicting `(RPGT.7)`.

A sharper sufficient form matches the corpus's subtraction pattern:

```text
0 <= ||H_(v_D*)||_HS^2 - ||H_(v_D)||_HS^2 < 1.           (RPGT.9)
```

By `(RPGT.4)`, this difference is already the integral source winding.  Thus the missing theorem
is not target positivity.  It is a strict source bound for the residual of two completion energies
after their common metric anomaly is removed.

`(RPGT.8)` is a sufficient closure statement, not the current attack.  Fresh corpus audit gives
two exact locks:

- global ordinary Hilbert--Schmidt admission of the literal physical prime-normal boundary is
  equivalent to RH (`everyThetaMobiusPrimeNormalHalfDensityDiagonalHilbertSchmidt_iff_riemannHypothesis`);
- coefficient-faithful Wold domination of the Gamma-six boundary Hessian is equivalent to neutral
  grade, hence globally to RH (`forall_xiGammaSixBoundaryWoldDominated_iff_riemannHypothesis`).

So no global Wold majorant may be cited as the producer.  The viable theorem must be pre-divisor
and cutoff-relative.

## 6. Formation attack forced by the corpus

### 6.1 Raw cubic residual is not the sub-unit budget

The scalar cubic mismatch gives the right subtraction law but the wrong magnitude.  Corpus proves

```text
D_2 = (95/16) (log 2)^3,
2/3 < log 2,
D_n >= 0.
```

Therefore

```text
sum_n D_n >= D_2 > (95/16)(2/3)^3 = 95/54 > 1.          (RPGT.10)
```

This kills direct identification of the cubic residual with the required `<1` Hankel energy.
The stronger corpus overshoot theorem shows its raw magnitude exceeds `2000` times the canonical
wall--Xi cubic residual.  Identity-scale landing is impossible.  The cubic theorem supplies the
topology of subtraction, not the final capacity.

Moreover `XiWardCubicApertureIntertwiningRateNoGo` proves no linear aperture-translation
intertwiner can create the necessary rate change.  Any surviving lift must be nonlinear/polar and
must break aperture covariance.  `mathsf T_D` is nonlinear at the minimal odd nuclear grade and
has exactly that form.

### 6.2 Restricted-unitary completion

The correct ambient space is the restricted unitary group

```text
U_res(P) = { U unitary | [P,U] is Hilbert--Schmidt }.
```

Its connected components are labelled by `index(PUP)`.  The two Hankel seams are the off-diagonal
coordinates of this group.  `Pi_D` is the finite-rank `K0` endpoint boundary, while
`mathsf T_D` is its cubic trace-class Chern character, created when a source path leaves its
identity component at completion.

Every genuine zero-free Euler--Gamma regularization on a strict-right window has boundary phase in
the zero-index component.  The corpus's finite scattering symbol does not supply such a family: it
is defined only on the critical line.  An explicit pre-divisor replacement is therefore required,
not optional.

One canonical candidate, fixed before any divisor, is the additive-theta damped Euler logarithm

```text
L_x(s) = sum_(n>=2) (Lambda(n)/log n) exp(-pi*x*n^2) n^(-s),
E_x(s) = exp(L_x(s)),                                  (RPGT.10a)
```

for `x>0`.  Since `0 <= Lambda(n)/log n <= 1`, `L_x` is entire and `E_x` is entire and zero-free.
It retains the unsquared Euler-log coefficient and tends to `zeta(s)` on `Re(s)>1` as `x -> 0+`.

The counterterm is no longer unspecified.  Put

```text
M_x(s) = integral_1^infinity exp(-pi*x*u^2) u^(-s) du,
A_x'(s)=M_x(s),  A_x(2)=0,
Phi_x(s)=(1/2)s*pi^(-s/2)*Gamma(s/2)*exp(L_x(s)+A_x(s)). (RPGT.10b)
```

`ULF-GECRF-001` proves `M_x,A_x` entire, `Phi_x` zero-free on `Re(s)>0`, and

```text
logDeriv(Phi_x)=logDeriv(h_infinity)-J_x+M_x,
J_x=sum Lambda(n) exp(-pi*x*n^2)n^(-s).                 (RPGT.10c)
```

Locally uniformly on `Re(s)>1`, `M_x -> 1/(s-1)`, `A_x -> Log(s-1)`, and `Phi_x -> xi`.
Thus `M_x` is the literal continuum heat zero-mode whose subtraction removes the universal prime
metric density; it is not a fitted scalar.  The phase of `Phi_x` on `boundary D` has winding zero
for every `x>0`.  What remains open is weak `H^(1/2)` convergence to the completed boundary phase
and its chiral corona estimate.  A positive completed winding can appear only as loss of
compactness.

Thus RH is not “positivity of a completed operator”; it is **conservation of chiral Euler charge
under the singular theta completion after removal of the universal anomaly**.

The direct strong form is:

**RPGT-Properness (open).** Construct zero-winding finite counterphases `a_(D,N)` from literal
natural-number Euler/Wold data such that the relative finite phases `v_(D,N)` remain in
`U_res(P)^0` and converge to `v_D=a_D^(-1)u_D` in the restricted metric

```text
d_res(v,w) = ||M_v-M_w|| + ||[P,M_v-M_w]||_HS.          (RPGT.11)
```

Fredholm index is locally constant in this metric.  Hence every finite index is zero, the limit
index is zero, and `(RPGT.6)` excludes every strict-right zero.  This is a formation/properness
theorem, not a target estimate.

### 6.3 Local sub-unit form: exclude quantized profiles, not total energy

`(RPGT.10)` shows total residual energy need not be below one.  What must be below one is every
possible **escaping Möbius profile**.  This terminology is rigorous, not heuristic.  Mironescu's
profile decomposition for bounded `W^(1/2,2)(S1;S1)` sequences says that all loss of phase/degree
compactness is carried by finitely many disk automorphisms; in the paper's Gagliardo normalization
each one costs the sharp quantum `4*pi^2`.  Hyder--Martinazzi's degree inequality gives the same
quantum as `2*pi` in their half-harmonic-energy normalization.  Diffuse excess energy may remain,
but it cannot carry a degree jump.

Therefore a weaker viable formation theorem is:

```text
finite phases bounded in U_res(P),
weak relative limit = v_D,
every escaping Mobius profile has normalized energy < 1. (RPGT.12)
```

Degree quantization then forces the escaping profile list to be empty; no component jump is
possible and `Pi_D=0`.  This is the faithful Ferrero--Washington analogue: the integer is escaped
Möbius charge, while equidistribution supplies a sub-unit bound per profile.  Total source mass
may exceed one.

The next attack is therefore a relative `H^(1/2)` telescope:

1. use the zero-free phases from `(RPGT.10a)` and their finite natural-number truncations; the
   critical-line scattering products are only local-factor checks, not this sequence;
2. subtract the Wold/Gamma principal phase coefficientwise on the same natural-number source;
3. prove either restricted-metric convergence `(RPGT.11)` or the no-atom estimate `(RPGT.12)`,
   retaining all cross-prime terms;
4. identify the limit with `a_D^(-1)u_D` by the continued source-current theorem;
5. conclude component conservation, rather than compare a source covariance with a target
   projector.

`SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel` proves the scalar third-jet shadow of
step 2: non-summable Euler and Wold principal terms cancel coefficientwise, leaving a positive
summable defect.  `(RPGT.10)` proves that defect cannot itself be the budget.  Next work must lift
the subtraction to the full boundary current and prove properness or local anti-concentration.
No scalar residue transport or global Wold majorant is enough.

### 6.4 Exact weighted-seam properness theorem

The corpus's canonical formation number gives a stronger, explicit alternative to `(RPGT.12)`.
Let `N e_j = j e_j` on the Hardy basis and define the first-moment nuclear seam cost

```text
C_Theta(u)
  = Tr((N+1) H_u* H_u) + Tr((N+1) H_(u*)* H_(u*)).     (RPGT.13)
```

The subscript records that `N+1` is the additive Fourier/oscillator grade.  It is not a fitted
zero weight: `ULF-TAFM-26` already proves that the formation-number connection is the unique
augmentation-normalized connection and that `(N+1)^(-1)` is compact.

**Theorem RPGT-B -- weighted nuclear seams are a proper charge cost.**  If `u:S1->U(1)` is smooth,
then

```text
C_Theta(u)
  = (1/2) sum_(n != 0) |n| (|n|+1) |uHat(n)|^2.        (RPGT.14)
```

Consequently, if zero-winding phases `u_k` converge weakly in `H^(1/2)` to `u` and

```text
sup_k C_Theta(u_k) < infinity,                          (RPGT.15)
```

then `u_k` is precompact in `H^(1/2)`, `wind(u)=0`, and the endpoint polar defect `Pi(u)` vanishes.

**Proof.**  On `e_j(z)=z^j`,

```text
||H_u e_j||^2 = sum_(q>j) |uHat(-q)|^2.
```

Tonelli and `sum_(j=0)^(q-1)(j+1)=q(q+1)/2` give the negative-frequency half of `(RPGT.14)`;
the same calculation for `u*` gives the positive half.  Since `|u|=1`, `(RPGT.14)` plus the fixed
`L2` norm bounds `u_k` in `H^1`.  Rellich compactness gives strong `H^(1/2)` convergence along
every subsequence with the prescribed weak limit.  The Fourier degree functional
`sum_n n |uHat(n)|^2` is continuous under strong `H^(1/2)` convergence, so its integer value
remains zero.  Coburn's alternative then makes both endpoint polar-defect blocks zero.  QED.

For the elementary Blaschke charge

```text
b_a(z)=(z-a)/(1-conj(a)z),    |a|<1,
```

the only nonzero contraction defect is the rank-one projection onto

```text
k_a(z)=sqrt(1-|a|^2)/(1-conj(a)z).
```

Its exact costs are

```text
Tr(N |k_a><k_a|)       = |a|^2/(1-|a|^2),
Tr((N+1)|k_a><k_a|)   = 1/(1-|a|^2).                  (RPGT.16)
```

Thus a charge approaching the completion boundary has infinite proper cost.  Bound dipoles may
form and annihilate; an unpaired charge cannot ionize to the corona under `(RPGT.15)`.

### 6.5 Chiral corona transgression: the direct sub-unit theorem

The weighted properness law is sufficient but stronger than Ferrero--Washington requires.  The
integer can be recovered from the **difference of trace mass lost by the two unweighted seams**.
This avoids any demand that total formation energy remain bounded in `H1`.

For a phase `u` set

```text
E_+(u) = sum_(n>=1) n |uHat(n)|^2  = ||H_(u*)||_HS^2,
E_-(u) = sum_(n>=1) n |uHat(-n)|^2 = ||H_u||_HS^2.     (RPGT.17)
```

**Theorem RPGT-C -- chiral corona transgression.**  Let `u_k:S1->U(1)` be smooth phases with
`wind(u_k)=0`, uniformly bounded in `H^(1/2)`, and converging weakly in `H^(1/2)` to `u`.  Pass to
a subsequence on which both chiral energies converge, and define their escaped masses

```text
kappa_+ = lim_k E_+(u_k) - E_+(u),
kappa_- = lim_k E_-(u_k) - E_-(u).                    (RPGT.18)
```

Then `kappa_+,kappa_- >= 0` and

```text
Tr mathsf T(u) = wind(u) = kappa_- - kappa_+.         (RPGT.19)
```

In particular, if `wind(u)>=0` and `kappa_-<1`, then `Pi(u)=0`.

**Proof.**  Weak lower semicontinuity gives nonnegativity of both losses.  The Fourier degree
identity gives `E_+(u_k)-E_-(u_k)=0` at every finite stage.  Taking the two energy limits and
subtracting yields `(RPGT.19)`.  If `q=wind(u)>=0`, then `q=kappa_- - kappa_+ <= kappa_-<1`.
But `q` is an integer, hence `q=0`; Coburn's alternative gives `Pi(u)=0`.  QED.

This has an exact corona interpretation.  For one escaping Blaschke profile, with normalized
kernel `k_a` and number operator `N`,

```text
Tr((1-exp(-tau*N)) |k_a><k_a|)
  = |a|^2 (1-exp(-tau)) / (1-|a|^2 exp(-tau))
  -> 1 as |a| -> 1,                                   (RPGT.20)
```

for every `tau>0`.  Reversing limits kills the value.  Thus `kappa_-` is a singular, noncompact
observer of high-mode seam mass, not a bounded landing of a zero finite horizon.  The old
dense-core no-go does not apply: finite source phases already have nonzero Hankel seams, and only
the ordered completion/cooling limit creates the integer.

The exact remaining source theorem is correspondingly weaker than `(RPGT.15)`:

```text
zero-free Euler--theta phases u_x weakly approach u_D,
sup_x (E_+(u_x)+E_-(u_x)) < infinity,
kappa_-(D) < 1.                                       (RPGT.21)
```

Then `(RPGT.19)` and `(RPGT.6)` close RH.  The `<1` estimate must be proved directly for the
negative chiral tail of these same Hankel seams.  Merely transporting the unrelated Burnol
covariance of trace `<1` would repeat `ULF-INHD-001`; a valid comparison must be an identity of
singular tail functionals in this changed source topology.

### 6.6 Cubic law: source clock and target index have the same forced grade

Fresh corpus audit changes the formulation again.

1. `RoutePPrimitiveBurnolApertureDampingSemigroup` proves that every primitive prime-depth feature
   diagonalizes one forward contraction semigroup, with energy multiplier
   `exp(-2c log n)=n^(-2c)`.
2. `RoutePPrimitiveBurnolMatrixCompleteColligation` proves that transported, deleted-boundary, and
   cocycle channels conserve the full complex sesquilinear pairing.  Cross-prime matrix entries,
   not only diagonal trace, survive.
3. The exact natural-number base atom simplifies to

   ```text
   routePPrimeGammaBaseCubicWeight(n)
     = Lambda(n)/(4*n*log(n)^3).
   ```

`ULF-RUCRI-001` proves the new fusion identity.  If

```text
J(t)=sum_(n>=2) Lambda(n)n^(-(1+t))=-zeta'(1+t)/zeta(1+t),
```

then

```text
B_base
  = (1/8) integral_0^infinity t^2 J(t) dt
  = (1/4) sum_(n>=2) Lambda(n)/(n*log(n)^3)
  < 1.                                                   (RPGT.21c)
```

More strongly, this budget belongs to the explicit Gaussian formation itself.  With

```text
Theta_Lambda(x)=J_x(1),
Theta_0(x)=M_x(1),
```

the Gaussian Mellin law gives

```text
J(t)     = pi^(t/2)/Gamma(t/2) * integral x^(t/2-1) Theta_Lambda(x) dx,
1/t      = pi^(t/2)/Gamma(t/2) * integral x^(t/2-1) Theta_0(x) dx,
J(t)-1/t = normalized Mellin_x(Theta_Lambda-Theta_0).     (RPGT.21e)
```

Hence `B_base=integral K_3(x)J_x(1)dx` for one explicit positive Mellin--Gamma kernel `K_3`.
The Route-P capacity and the Gaussian boundary phase no longer live on different source objects.
The continuum heat zero-mode is exactly the universal pole current under the same transform;
literal integer formation differs by its spectral gap `log 2`.

The budget is also dynamic.  If `C_B` is the prime-mixed Burnol label Gram operator and `D_c` its
diagonal damping semigroup (full eigenvalue `exp(-c*(log n+i*kappa))`, energy multiplier
`n^(-2c)`), matrix-complete colligation gives

```text
C_def(c)=C_B-D_c* C_B D_c >= 0,
Tr C_def(c)=sum (1-n^(-2c)) Lambda(n)/(4*n*log(n)^3),
B_base=integral_0^infinity d/dc Tr C_def(c) dc.          (RPGT.21f)
```

Thus `B_base` is total positive action of a one-sided source homotopy, while
`Tr mathsf T_D` is integral boundary charge of the completed projection homotopy.  The missing
cyclic morphism is a bulk-to-boundary action inequality, not equality of two static scalars.

Thus the strict sub-unit budget is the third inverse moment of the **safe** Euler contraction
clock.  Independently, `mathsf T_D=(U_D*PU_D-P)^3` is the first odd nuclear Chern character of the
completed Hardy polarization.  The two cubes are no longer a numerical analogy:

```text
source:  Gamma-subordinated third inverse moment of prime-log damping,
target:  third power of the restricted projection displacement.
```

The exponent three is forced on the target.  Degree one retains orientation but is not trace
class in the critical `S_2` topology.  Degree two is trace class but reflection-even.  Degree
three is trace class, reflection-odd, and its trace is integral.  This simultaneously explains why
linear source currents are non-nuclear, quadratic positivity is selection-blind, and cubic Green,
Cauchy, Loewner, and Gamma-six readers repeatedly survive the corpus no-gos.

The exact remaining theorem is now a map of cyclic defects, not vectors or scalar budgets:

**RPGT-Cyclic transgression (open).**  Gaussian Euler--continuum formation induces, before divisor
specialization, a degree-three trace-contractive boundary morphism from the matrix-complete Burnol
aperture colligation to the restricted Hardy projection pair such that

```text
||mathsf T_D||_1
  = ||(1-P)V_D P||_3^3 + ||(1-P)V_D* P||_3^3
  <= B_base < 1.                                       (RPGT.21d)
```

Here `V_D` denotes multiplication by the canonically counterphased relative phase, not the raw
completed phase `u_D`.  For every bounded real branch `psi_(D,x)` of that relative phase,
Duhamel's commutator formula and unitary invariance give the unconditional reduction

```text
||mathsf T_(D,x)||_1
  = ||[P,exp(i*M_(psi_(D,x)))]||_3^3
  <= ||[P,M_(psi_(D,x))]||_3^3
  = 2 ||(1-P)M_(psi_(D,x))P||_3^3.                    (RPGT.21g)
```

Hence nonlinear exponentiation is not the obstruction.  The remaining producer is an additive,
matrix-complete Hankel estimate for the anomaly-subtracted Euler--Gamma current, followed by a
genuine `S_3` completion limit.  Weak `H^(1/2)` convergence supplies neither step.

The existing Route-P base Cauchy cube does not itself supply this estimate.  Its source Gram is
indexed by primitive prime-depth cells, whereas its conormal target Gram is indexed by completed
Xi residues.  The corpus already proves that global domination between those two packets is the
terminal RH capacity law
`routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis`.  Moreover, trace of the source
Gram sees only its diagonal, while Schatten-three mass of a summed Hankel operator contains full
cyclic triple products.  Therefore the required bridge must factor the **finite additive boundary
Hankel operator itself** through source features before completion.  A post-completion comparison
of the prime Gram with a zero/conormal Gram is forbidden as circular.

This theorem closes RH immediately by `(RPGT.6)`.  It evades the retired bounded-landing theorem
because it need not map a finite source vector to a completed zero projector.  It must preserve
the cyclic three-chain and its trace after the universal non-trace-class metric terms are
subtracted.  A bounded one-particle factorization is explicitly forbidden; a closed-graph,
mapping-cone, or determinant-line transgression is allowed.

This is real narrowing, not completion theatre.  Any proposed bridge can now be falsified on
three exact tests:

```text
it must intertwine prime-log and Hardy homotopies at cyclic degree three;
it must preserve mixed matrix coefficients, not only diagonal trace;
its trace norm must be bounded by the explicit Gamma-clock mass (RPGT.21c).
```

Generic restricted unitaries fail the last test, so `(RPGT.21d)` can only come from literal
integer/theta formation.

### 6.7 What the object means: completion as dipole ionization

Every literal finite relative Euler--Gamma phase has zero winding.  At critical regularity it may
contain positive/negative Möbius profiles in neutral pairs.  A completed nonzero
`Tr mathsf T_D` means one
chirality escaped through conformal infinity before the pair recombined.  Therefore

```text
finite literal formation = neutral dipole gas,
completion noncompactness = possible dipole ionization,
Tr mathsf T_D           = unbalanced escaped integral charge,
C_Theta                = theta/formation separation cost.       (RPGT.22)
```

This is the joint interpretation of the corpus's fixed mixed inertia, hyperbolic rapidity,
Krein--Langer negative directions, recurrent closed observers, and open lifted history.  They are
readers of whether a neutral formation pair can separate to infinite completion distance.

The generic theorem is complete.  The arithmetic statement remains one inequality, not a new
object:

**RPGT-Theta confinement (open).**

1. **Higher law sought.** Literal integer/Poisson self-duality binds the two chiral seams after
   coefficientwise subtraction of the universal metric anomaly; completed Euler formation cannot
   ionize a neutral Möbius dipole at finite formation-number action.
2. **Checked corpus boundary.** Prime-Bohr formation exists strongly in Haar `L2` for every
   `Re(s)>1/2`, but the arithmetic height orbit is dense and Haar-null, so ambient `H2` supplies no
   restriction map.  Full `C(PrimeTorus)`-linear RFHM sewing erases every nonempty native prime
   support.  Fixed finite-prime phases recur with unbounded lifts.  The moving-support diffuse Ward
   law has vanishing local/quadratic phase and a nontrivial collective scalar anomaly, but its Ward
   tangent already uses `XiC` and it proves no contour seam cost.
3. **Exact RH closure.** Construct source-only counterphases `a_(D,k)` and finite mixed phases
   `v_(D,k)` with weak limit `a_D^(-1)u_D`, zero winding, and

   ```text
   sup_k C_Theta(v_(D,k)) < infinity.                  (RPGT.23)
   ```

   Theorem RPGT-B gives `wind(u_D)=0` on every strict-right rectangle.  Equation `(RPGT.6)` then
   excludes every strict-right Xi zero; functional-equation symmetry gives RH.

This is stronger than the local sub-unit profile law but more canonical: the cost is forced by the
same Hardy polarization that defines `mathsf T_D`, and by the already-proved augmentation connection.  It
does not ask for a bounded Euler multiplier, a shared scalar ghost, or a zero-dependent inner
factor.

The preferred weaker closure is `(RPGT.21)`: it asks only for a sub-unit bound on the one chiral
corona mass that can create positive winding.

### 6.8 Why prime-Bohr normality is not the producer

The normalized prime-Bohr wave

```text
F_s(z)=zeta(2 sigma)^(-1/2) product_p
       (1-p^(-2 sigma))^(1/2)/(1-p^(-s)z_p)
```

already exists as a strong Haar-`L2` limit exactly for `sigma>1/2`, and its squared modulus is the
product-Poisson state.  This is a genuine pre-divisor completion, but it lives on the independent
prime torus.  The physical height orbit `z_p=p^(-it)` is Haar-null.  Point restriction from its
ambient Hilbert quotient is undefined, while declaring full source linearity makes native-support
insertion reversible and triggers the JAS erasure theorem.

The additive heat aperture is the correct kind of nonreversible corner: it acts directly on the
same natural-number coefficients and its finite part recovers completed intensity.  But its known
echo theorem is a zero detector, not `(RPGT.21)` or `(RPGT.23)`.  The missing construction must use theta/heat
formation to bound the **first moment of the two already-oriented Hardy seams**, before finite-part
or zero extraction.  Merely recovering `zeta(s)` as an asymptotic coefficient leaves `mathsf T_D` a
receiver.

### 6.9 Literature boundary for the compactness claim

- Mironescu, [Profile decomposition and phase control for circle-valued maps in one
  dimension](https://www.numdam.org/item/CRMATH_2015__353_12_1087_0/), proves the generic finite
  Möbius-profile decomposition and the sharp `4*pi^2` quantum at `p=2`.
- Hyder--Martinazzi,
  [One-dimensional half-harmonic maps into the circle and their degree](https://arxiv.org/abs/2405.18037),
  proves the sharp degree-energy loss bound in the alternate `2*pi` normalization.
- These sources validate profile quantization only.  They contain no ordinary-prime/Gamma/theta
  counterphase, no prime-mixed coefficientwise anomaly subtraction, and no bound `(RPGT.21)`.

### 6.10 Cyclic exponential-Hankel surrogate: margin and exact exclusion boundary

The next source-first test keeps all cross-frequency terms.  For a prime-power event
`n=p^k`, set

```text
a_(p,k) = k log p,
c_(p,k) = 1 / (2 p^k k^2 log p),
e_a(x)  = exp(-a x),
H_X     = sum_(p^k <= X) c_(p,k) |e_a><e_a|.          (RPGT.24)
```

This is not the earlier diagonal scalar budget.  Its finite feature Gram is

```text
G_X((p,k),(q,l))
  = sqrt(c_(p,k)c_(q,l)) / (a_(p,k)+a_(q,l)).         (RPGT.25)
```

Therefore finite-dimensional cyclicity gives the exact identities

```text
Tr H_X = sum_(p^k <= X) 1/(4 p^k k^3 log(p)^2),

Tr(H_X^3)
  = sum_(i,j,r)
      c_i c_j c_r /
      ((a_i+a_j)(a_j+a_r)(a_r+a_i)),

Tr(H_X^3) <= (Tr H_X)^3.                              (RPGT.26)
```

The last inequality is spectral: all eigenvalues are nonnegative and the sum of their cubes is
at most the cube of their sum.  Thus an infinite positive trace-class limit `H`, together with
the elementary strengthening `B_base < 1/2`, would imply

```text
2 ||H||_3^3 = 2 Tr(H^3) <= 2 B_base^3 < 1/4 < 1.      (RPGT.27)
```

Runpod evaluated the full Gram, not just its diagonal, through `p^k <= 10000`.  It found

```text
Tr H_X                    = 0.40215445468965655,
||H_X||                   = 0.3855625981008574,
2 Tr(H_X^3)               = 0.11464151462336479,
mixed share of Tr(H_X^3)  = 0.686809074484133.
```

Raw data and interpretation are in
`docs/drafts/pipeline/2-fully-proven/computations/predivisor-relative-operator-route-audit/`.
The `68.68%` mixed share validates the full-cyclic requirement in hostile falsifier 18.  It also
shows that numerical size is not the present obstruction.

**[RETIRED SUBROUTE: bounded exponential-Hankel landing].**  No identity in the checked corpus
equates `(RPGT.24)` with either chiral block of the literal anomaly-subtracted scattering current.
Three exact locks prevent declaring such an identity:

1. `not_summable_norm_routeKPhysicalEndpointBoundaryRankOne` proves that literal ordinary-prime
   endpoint atoms are not absolutely nuclear;
2. `vonMangoldtAdditivePositiveLogJetGram_add_pointedBianchiBoundary_ne_momentHankel` proves that
   the positive successor carrier plus actual additive pointed Bianchi boundary cannot be a
   moment-Hankel target;
3. any coefficientwise bounded factorization whose finite zero-winding stages converge in
   `S_3` makes their cubic defects converge in `S_1`; trace continuity then preserves trace zero.
   It cannot create the required completed trace one.

Consequently `(RPGT.24)` is a valid positive budget surrogate but not the missing producer.  The
surviving conjecture is narrower:

**[CONJECTURE RPGT-C3, OPEN].**  The literal Euler--Gamma--theta current admits a degree-three
mapping-cone or determinant-line transgression whose completed cubic trace is not the `S_1` limit
of the finite zero-index traces, while its two chiral moduli are contractively represented by the
full cyclic kernel `(RPGT.25)` after the non-Hankel cross term is formed.  The transgression must be
constructed before Xi specialization and before taking norms.

This formulation deliberately excludes a bounded one-particle map, a direct sum of the two
positive source legs, and any post-completion zero Gram.  Those three classes are now closed.

### 6.11 Existing singular transgressions are receivers, not the producer

The corpus contains the three natural implementations of `RPGT-C3`; each is already closed.

1. **Closed graph / mapping cone.**  The theorem
   `isClosableShiftedCorona_iff_zeroFree_above` identifies closability of the shifted arithmetic
   corona at `z` with zero-freeness of the entire strict-right region above `Re z`.  Invoking this
   closability to create the boundary class would assume the desired zero-free conclusion.
2. **Singular corona quotient.**  Every finite arithmetic packet dies in the canonical corona, and
   `no_routeRTwoThreeStokesCalkinPrequotientComparison_factorization_mod_compact` proves that away
   from neutral grade no linear corona reporter recovers the actual pre-quotient Stokes comparison,
   even modulo compact operators.
3. **Existing Evans determinant candidate.**  `one_lt_finrank_exteriorPower_evansExcessTarget`
   proves that its top exterior target has dimension greater than one, so it is not a determinant
   line.  `det_evansGram_update_neg` proves that the scalar Gram determinant is orientation-blind.

**[RETIRED SUBROUTE: RPGT-C3 as mapping-cone/corona/Evans determinant transgression].**  These
mechanisms either assume the right-strip zero-free law, erase the literal finite source before the
physical comparison, or lose the orientation needed for trace one.  They cannot be used to prove
`(RPGT.21d)`.

The surviving statement is now strictly analytic and same-boundary:

**[CONJECTURE RPGT-Theta-S3, OPEN].**  After the literal Euler--Gamma anomaly is cancelled at the
current level, theta/heat formation gives a pointwise integral-kernel identity for the two chiral
Hardy blocks of the already-completed relative phase.  The identity bounds their full cyclic
`S_3` mass by the positive kernel `(RPGT.25)` without passing through finite zero-winding
approximants, a singular quotient, a closed-graph admission, or a zero-labelled Gram.

This is exactly the remaining content of `(RPGT.21d)`, with every known topological workaround
removed.  A qualitative Peller/Besov estimate is insufficient; the identity must preserve the
literal arithmetic normalization and all mixed cyclic terms.

## 7. Hostile falsifiers

1. If `a_D` is defined from an inner/outer factorization of `XiC`, `(RPGT.8)` is RH rewritten.
2. If the estimate uses `B_base` without a degree-three cyclic morphism to `mathsf T_D`, it repeats
   the impossible landing of `ULF-INHD-001`.
3. If finite phases are required to converge in ordinary operator norm, the literal Euler
   contraction no-go kills the construction.
4. If only the signed index is retained, functional-equation reflection cancels it.  Both polar
   defects and ordinary trace are mandatory.
5. If primes are compressed separately and their indices added, cross-prime formation is lost.
6. If the common principal anomaly is removed after taking norms, unsquared Euler coefficients are
   already destroyed.  Subtraction must occur at phase/current level.
7. If `(RPGT.8)` is proved from `(RPGT.6)` plus zero-freeness, the argument is circular.
8. Without `(RPGT.8)`, `(RPGT.9)`, or `(RPGT.21d)`, `mathsf T_D` is a rigorous same-boundary
   receiver, not an RH proof.
9. The raw positive cubic mismatch cannot be the sub-unit budget: its prime-two atom already
   exceeds one by `(RPGT.10)`.
10. Global Wold domination or global ordinary Hilbert--Schmidt admission is an existing exact RH
    receiver.  Only pre-divisor restricted properness or local anti-concentration is admissible.
11. Ambient prime-torus `H2` normality cannot be restricted to the Haar-null arithmetic orbit, and
    full `C(PrimeTorus)` source linearity kills native support.  The producer must be a
    nonreversible theta/Toeplitz corner.
12. A scalar moving-support normalizer is not a confinement theorem.  It neither controls
    `C_Theta` nor avoids the already-completed Xi Ward tangent.
13. The finite Connes--Consani scattering phase lives on the critical line.  Using it as a
    strict-right boundary approximation silently assumes an unavailable analytic family.
14. A finite or entire zero-free Euler gauge has zero closed-contour contribution.  It may move
    chiral seam mass but cannot change winding; coefficient cancellation alone is not formation.
15. The Burnol `<1` covariance cannot be declared equal to `kappa_-`.  Only a same-seam singular
    tail identity could transfer that constant; any bounded factorization repeats the retired
    dense-core landing.
16. A quadratic displacement trace cannot be the selector: it is reflection-even.  A linear
    displacement trace is unavailable at the critical `S_2` boundary.  Cubic is the minimal
    admissible odd nuclear grade.
17. Identity `(RPGT.21c)` alone is still scalar.  Any claimed closure that discards the
    matrix-complete Burnol cross terms before reaching the triple Hardy kernel has not constructed
    the required transgression.
18. The diagonal cubic coefficient budget does not dominate Schatten-three Hankel mass with
    constant one.  Already the two-mode Hankel block
    `A=[[1,1],[1,0]]` has `Tr |A|^3=2*sqrt(5)>3`, whereas the separate weighted coefficient
    cubes are `1+2=3`.  Any valid `(RPGT.21d)` must transport the full cyclic Gram, including
    cross-frequency interference.  This is exact: the eigenvalues are
    `(1+sqrt(5))/2` and `(1-sqrt(5))/2`; cubing their absolute values gives `2*sqrt(5)`, and
    `2*sqrt(5)>3` follows by squaring the positive sides (`20>9`).
19. A generic zero-winding phase can carry arbitrarily large paired chiral mass.  Thus no
    topology-only or winding-only estimate can prove `(RPGT.21d)`; the estimate must use the
    literal Euler--Gamma--theta source and a canonical anomaly removal before taking norms.
20. Duhamel reduces the nonlinear phase to the additive current with constant one, but does not
    identify boundary Fourier modes with prime-log labels.  Treating `(RPGT.21g)` as the missing
    source transgression silently skips the arithmetic frequency-transport theorem.
21. Route-P's positive base Cauchy cube is not the missing factorization.  Its prime-labelled
    trace budget versus zero-labelled conormal trace is already classified by
    `routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis`.  Reusing that comparison
    would violate the upstream-operator requirement.
22. Peller's `S_3`--`B_3^(1/3)` theorem identifies the correct function space but only gives norm
    equivalence, not the sharp source normalization needed for `<1`.  Qualitative Besov
    membership cannot spend the fixed arithmetic margin.
23. The positive exponential-Hankel surrogate has the right cubic size but the wrong provenance.
    Its direct absolutely summable realization would give `S_3` convergence of finite
    zero-winding stages and hence preserve cubic trace zero.
24. The literal ordinary-prime endpoint cannot be substituted for the damped surrogate:
    `not_summable_norm_routeKPhysicalEndpointBoundaryRankOne` rules out absolute nuclear assembly.
25. An additive Gamma/Bianchi moment-Hankel correction cannot supply the missing cross term:
    strict successor anti-Hankel curvature survives every such correction.
26. Shifted-corona closability cannot be used as source infrastructure: the corpus proves it is
    equivalent pointwise to the desired strict-right zero-free region.
27. The canonical singular corona kills every finite arithmetic packet and cannot recover the
    actual pre-quotient Stokes comparison even modulo compacts off neutral grade.
28. The existing Evans exterior target is not a determinant line, and its scalar Gram determinant
    is invariant under source-orientation reversal.

## Gates

- [x] one pre-divisor definition, no supplied zero
- [x] genuine all-prime mixing before compression
- [x] one graded object retains signed orientation and unsigned multiplicity
- [x] paper proof of integrality, nuclearity, exact conservation, and exact cubic norm identity
- [x] exact RH-chain edge stated
- [x] kill raw cubic residual as direct `<1` budget
- [x] kill global Wold/ordinary-Hilbert--Schmidt domination as producer
- [x] classify every possible critical degree jump by finite escaping Möbius profiles
- [x] prove exact weighted-seam/H1 properness and single-charge divergence on paper
- [ ] prove exact chiral-corona transgression and sub-unit selection theorem on paper
- [x] kill ambient prime-Bohr restriction and full prime-torus-linear sewing as producers
- [x] replace the invalid critical-line phase sequence by an explicit zero-free, unsquared,
  additive-theta damped Euler exponential
- [x] derive its canonical continuum heat counterterm and safe-half-plane Xi limit on paper
- [x] construct one pre-divisor prime-mixed nuclear operator
  `mathsf T_D=(U_D*PU_D-P)^3` whose trace is the integral relative index
- [x] prove cubic minimality at the critical restricted-unitary boundary
- [x] identify the exact `<1` source budget as the third inverse moment of the safe Euler clock
- [x] identify the exact target nuclear norm as the sum of the two chiral Schatten-three masses
- [x] kill constant-one diagonal-coefficient domination by the exact two-mode Hankel block
- [x] reduce phase exponentiation to the additive-current `S_3` commutator with constant one
- [x] exclude post-completion Route-P prime-Gram/zero-Gram domination as an RH-equivalent receiver
- [x] compute the full cyclic exponential-Hankel surrogate and verify that mixed triples dominate
- [x] retire direct bounded exponential-Hankel landing by source provenance and trace continuity
- [x] exclude additive moment-Hankel repair by the exact successor-curvature lock
- [x] retire shifted-corona closed-graph admission as zero-freeness-equivalent
- [x] retire existing singular-corona and Evans-determinant transgressions
- [ ] construct canonical literal-source counterphase in restricted-unitary topology
- [ ] prove weak `H^(1/2)` boundary convergence of `(RPGT.10b)` in the strict-right strip
- [ ] prove the native one-chirality corona bound `(RPGT.21)`, or the stronger weighted seam bound
  `(RPGT.23)`
- [ ] construct the matrix-complete degree-three cyclic/Besov transgression `(RPGT.21d)`
- [x] attack and retire `RPGT-C3` in its mapping-cone/corona/Evans determinant realizations
- [ ] prove direct same-boundary theta kernel identity `RPGT-Theta-S3`
- [ ] dependency-close paper proof
- [ ] formalize in Lean only after dependency closure

## 8. Helson/multiplicative-Hankel audit

**[RETIRED SUBROUTE: multiplicative Helson landing].**  Replacing the additive Hardy frequency
matrix by the multiplicative matrix `K_a(j,k)=a(jk)` does preserve all factor-pair cross terms, but
it does not supply the missing signed cubic landing.

The corpus already contains the exact coefficient-faithful trace-class realization.  Under
`HelsonSummable a`, `helsonOperator a` is trace class,

```text
||K_a||_1 <= sum_n d(n) |a(n)|,
<e_j,K_a e_k> = a(jk).
```

It also contains the decisive finite countermodel.  Let `a(2)=c>0` and `a(n)=0` otherwise.  On
`span(e_1,e_2)`,

```text
K_a = [[0,c],[c,0]],
spec(K_a) = {c,-c},
Tr(K_a^3) = c^3 + (-c)^3 = 0,
Tr(|K_a|^3) = 2 c^3.
```

Thus coefficient positivity is not operator positivity.  The signed cubic loses the required
index, while the absolute cubic is orientation-blind.  This is not repaired by a general Helson
moment theorem: nonnegativity of a multiplicative Hankel matrix requires the whole coefficient
stream to be a multivariate moment sequence, not merely pointwise nonnegative coefficients.

The additive Gamma--Hankel alternative is equally closed.  Its finite quadratic form is exactly
the positive weighted Laplace energy, including every off-diagonal term.  But uniform control of
the cofinal finite Möbius sections is already equivalent to RH, via
`mobiusLaplaceCanonicalFiniteSectionEnergyBounded_iff_riemannHypothesis`.  Using that ceiling in
the proposed `S_3` estimate would therefore assume the endpoint source law rather than prove it.

Finally, generic Helson continuation cannot provide the divisor selector.  Andersson's
factorization theorem, formalized by `exists_continuable_phase_with_prescribed_divisor`, realizes
an arbitrary locally finite signed divisor strictly left of `Re s=1` by a continuable Helson zeta
function.  Hence the Helson class by itself has no critical-line rigidity to transport into trace
one.

Primary audit:

- K.-M. Perfekt and A. Pushnitski, *On Helson matrices: moment problems, non-negativity,
  boundedness, and finite rank*, arXiv:1611.03772.
- J. Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713.
- O. F. Brevig and K.-M. Perfekt, *Failure of Nehari's Theorem for Multiplicative Hankel Forms in
  Schatten Classes*, arXiv:1409.3117.

**Positive survivor.**  Multiplicative indexing is a valid exact bookkeeping device: the
coefficient-faithful `ell^1_d -> S_1` map and its Fredholm crossing covector are fully formalized.
The obstruction is classification, not existence.  To be useful here, a future multiplicative
operator must additionally prove a literal prime--Gamma moment-measure identity and an oriented
divisor-selective landing.  Neither follows from Helson structure, Schatten membership, or
positive coefficients.

This retires the Helson implementation only.  It does not refute every non-translation,
matrix-valued same-boundary theta identity.  The broader `RPGT-Theta-S3` class remains open.
Route K does not supply a shortcut: `XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence` already
matches the exact reflected quadratic and quartic source moments while retaining the cofinite RVM
diagonal and nonzero cofinal cycle holonomy.  But
`riemannHypothesis_of_routeKAllOrderReflectedEnergyIncidence` proves that matching the complete
moment tower by one self-adjoint Hilbert--Schmidt operator implies RH before any determinant or
index is formed.  The surviving gate must therefore be a finite-degree, orientation-sensitive
theta identity that lands the cubic restricted-unitary defect directly; extending positive
moment admission to all orders would only restate the Route-P moment cone.  No numerical
calculation is relevant to this algebraic distinction.

## 9. Exact saturation, Gauss, and K1 audits

Three further corpus-complete tests narrow `RPGT-Theta-S3` without adding a numerical task.

1. **Canonical relative curvature saturates the nuclear inequality.**  The theta Mellin-six
   survival construction is already the literal pre-divisor realization of “two compact,
   non-trace-class metrics with trace-class difference.”  Theorems
   `primeHodgeHistory_relativeCurvature_trace_index_integralNuclear` and
   `primeHodgeHistoryRelativeCurvature_closed` prove that its relative curvature has index trace
   `1`, trace norm `1`, and operator norm `1/3`.  Thus the small operator norm is irrelevant to the
   proposed contradiction, and the natural relative-Hodge object lies exactly on, not below, the
   nuclear unit wall.  The signed two-sided family sharpens this to
   `Tr T(t)=sign(t)` and `||T(t)||_1=|sign(t)|`.  Scalar attenuation produces a subunit nuclear
   norm only by attenuating the trace away from the integer unit, as already closed in
   `CCMRoutePCompletedCubicGreenIntegralDefectNoGo`.
2. **The physical Gauss cubic is not a hidden trace-class lift.**  The formerly open cubic outer
   defect is fully convergent by `tendsto_norm_gaussCubicOuterDefectVector_comp` and
   `tendsto_norm_gaussCubicPropagatedRelativeErrorVector_comp`.  Downstream positivity then proves
   `tendsto_gaussCubeTwoSidedDiagonal_sum_atTop`: the actual two-orientation cubic diagonal has
   nonnegative terms and divergent partial sums.  Hence this physical cubic channel cannot be the
   finite nuclear defect sought here; cancellation would have to precede its positive diagonal.
3. **K1/Hochschild topology does not supply the metric gap.**  The corrected rational-adelic
   multiplier class is a genuine Hochschild one-cycle and its Kummer regulator is exactly
   `-log p`.  This is a valid pre-divisor orientation carrier.  Its Xi landing, however, is defined
   with an explicit `rho : XiDivisorSupport`, and the associated trace-one ordinary convergence is
   proved equivalent to critical-line placement locally and to RH globally by
   `riemannHypothesis_iff_xiReflectionIncidenceTraceOneSourceOrdinaryLanding`.  The identity in
   the minimal trace-norm unitization also has norm exactly one.  Topological nontriviality
   therefore does not manufacture the strict metric contraction or an upstream divisor selector.

**Route consequence.**  These tests do not disprove every conceivable source-specific
matrix-valued theta identity, but they close the three remaining ready-made producers.  Any valid
`RPGT-Theta-S3` theorem must be a new signed, nonpositive, finite-degree kernel identity whose
cancellation occurs before nuclear absolute value.  It cannot be obtained by rescaling the
canonical relative curvature, taking the positive Gauss cubic diagonal, or composing the existing
K1 class with its divisor-indexed Xi landing.

Additional hostile falsifiers:

29. Replacing trace norm by operator norm is invalid: the canonical trace-one curvature has
    operator norm `1/3` but trace norm exactly `1`.
30. The convergent Gauss cubic propagation does not imply nuclear summability; its physical
    two-orientation positive cubic diagonal diverges.
31. A genuine K1/Hochschild class with nonzero Kummer regulator is not yet an index-one Xi
    producer.  The available landing supplies `XiDivisorSupport`, and its convergence is already
    RH-equivalent.

## 10. Fixed theta `det_2` and rank-two metric-commutator audit

**[RETIRED SUBROUTE: fixed Fredholm determinant plus canonical Green commutator].**  The corpus
does contain a substantially stronger pre-divisor object than the proposed pair of hypothetical
completions.  `thetaKernelOperator` is one fixed Hilbert--Schmidt operator and
`thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero` identifies
`det_2(I+z thetaKernelOperator)` with the centered Xi divisor exactly.  Nonzero source spectrum,
including algebraic multiplicity and finite-rank Riesz fibres, is already reconstructed without
choosing an enumeration of zeros.

Its canonical metric identity does not provide the missing contraction.  With
`G=thetaMetricOperator`, `B=thetaKernelOperator`, and `C=pinnedBoundaryCLM`, the exact Green law is

```text
G B - B* G = i C.
```

Here `C` is self-adjoint of exact rank two and mixed inertia `(1,1)`; its two nonzero eigenvalues
are `+1/sqrt(12)` and `-1/sqrt(12)`.  On an eigenmode `B f = mu f`,

```text
<C f,f> = 2 Im(mu) <G f,f>.
```

The metric energy is strictly positive on nonzero vectors, but `G` is unconditionally not bounded
below.  Hence the small finite-rank commutator gives no uniform spectral gap and cannot force
`Im(mu)=0`.  Requiring `<C f,f>=0` on every nonzero eigenmode is already exactly RH by
`thetaFredholmEigenmodesPinnedGreenIsotropic_iff_riemannHypothesis`.

Functional-equation pairing closes the natural matrix repair.  A divisor mode and its
critical-line reflection have zero cross-pairing for `C`, while their diagonal currents are exact
opposites.  Therefore every reflection-symmetric Hermitian rank-two correction vanishes on the
pair (`thetaXiReflectionSymmetricRankTwoCorrection_eq_zero`) and cannot reduce its hyperbolic
excess.  Breaking reflection first merely exposes the unresolved global Krein-chamber sign;
`HedenmalmHankelKreinChamber` identifies that sign as horizontal monotonicity of `|Xi|^2`, not as
ambient positivity.

A local Riesz projection at a nonzero source eigenvalue is finite rank and has the correct
algebraic multiplicity, but any trace-one projection or relative projection difference still has
trace norm at least one.  Multiplying it by the subunit boundary eigenvalue attenuates its trace,
exactly as in the scalar-fusion no-go.  Thus the fixed `det_2` source solves divisor realization,
not the strict nuclear comparison.

**Positive survivor.**  The exact pre-divisor Hilbert--Schmidt determinant, multiplicity-exact
Riesz calculus, singular positive metric, and rank-two Green port form a complete source-side
spectral package.  A future continuation may use them only with a new chiral, source-nonlocal
operator identity whose cancellation occurs before trace norm.  Canonical metric isotropy,
reflection-symmetric rank-two correction, or Riesz normalization cannot be used as the missing
`RPGT-Theta-S3` theorem.

Additional hostile falsifiers:

32. Small norm of `G B - B* G` does not imply real spectrum because `G` is positive but not
    bounded below.
33. The canonical rank-two defect is mixed-sign and reflection-pair blind; its symmetric
    correction is identically zero on actual paired Xi modes.
34. A local Riesz fibre supplies integral multiplicity but cannot be nuclear-subunit at trace one;
    normalization reaches the same sharp unit wall as every other projection/index carrier.

## 11. Chiral boundary-port and independent Euler--Wold cubic audits

**[RETIRED SUBROUTE: normalized rank-two Livsic port].**  Splitting the fixed Green defect into
its positive and negative boundary eigenchannels does break reflection before scalar reduction,
but it does not create a free contraction.  The raw port eigenvalue has magnitude
`1/sqrt(12)<1`; the port fundamental symmetry that carries an integer winding is obtained by
dividing by that same eigenvalue.  Thus raw port amplitude is subunit but nonintegral, while the
normalized index port has norm one.  This is the two-channel version of the scalar-fusion wall.
The negative channel also prevents ordinary dissipative/Schur passivity; removing it is precisely
the unresolved Krein-chamber condition, not a source consequence of finite rank.

The independent Euler--Wold construction closes a different missing obligation and sharply
classifies what remains.  `SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel` builds,
before every Xi selection, the literal negative Euler third jet with all prime-power `k^2`
multiplicities and subtracts the positive Wold counterterm coefficientwise.  The remainder is a
strictly positive summable source defect, and natural cutoffs converge to its strictly negative
total.  Hence source orientation and summability are real; they are not supplied by a divisor.

`SourceHorizontalEulerWoldIndependentKreinXiResidueTransport` then transports the independent
Euler and Wold pure third jets through both completed Gamma residues and restores exact analytic
multiplicity.  Linear grade-forgetting, however, gives

```text
-2 D_N / H_N^3 * routePJuliaSharedOrientationOrbitBlock(c),
```

where `D_N` converges and `H_N -> infinity`.  Every finite matrix is nonzero and correctly
oriented, but the intrinsic prime-clock limit is zero.  Keeping the unnormalized current avoids
collapse but fails identity-scale landing in the opposite quantitative direction:
`RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot` proves from the prime-two
atom alone that its magnitude exceeds `2000` times the canonical wall--Xi cubic Malgrange
magnitude.

**Positive survivor.**  There is now an unconditional pre-Xi, sign-correct, coefficient-faithful,
summable cubic defect and an exact multiplicity-preserving completed-residue transport.  The
remaining theorem is narrower: construct a non-scalar, source-derived contraction that survives
the cofinal prime clock and transports the full cyclic matrix, without selecting an Xi residue or
renormalizing by a target scalar.  Neither raw identity scale nor intrinsic cubic clock scale can
do this.

Additional hostile falsifiers:

35. Dividing the rank-two Green port by `1/sqrt(12)` to recover integer winding removes the entire
    subunit gain.
36. The independent Euler--Wold cubic source is not missing orientation or multiplicity; its
    intrinsic normalized residue landing vanishes entrywise.
37. Retaining the unnormalized cubic current is not a small correction: its magnitude exceeds the
    canonical Xi cubic residual by a rigorously certified factor greater than `2000`.

## 12. Boundary translation, bilateral ghost, and noncentrality audit

The remaining matrix order cannot be recovered by translating a positive Hardy kernel.  W-H200
proves complete positivity after shifting the source convergence wall by `1/2`, but the literal
unshifted denominator is obtained by Hadamard multiplication with

```text
M(z,w) = (z + conjugate(w)) / (z + conjugate(w) + 1).
```

`XiWardCubicBoundaryTranslationSchurWall` proves that for any two distinct positive real nodes
the determinant of this multiplier is strictly negative.  Thus boundary translation itself
creates a negative square; no Schur-positive denominator correction can turn the shifted result
into the literal same-boundary Loewner current.

The negative square has an exact minimal carrier.  Bilateral grade `a,-a` converts the full Hardy
debt into one prime-independent rank-one ghost,

```text
K_a = P_a P_a* - G_a G_a*,
P_a(lambda) = 2 lambda / (lambda^2-a^2),
G_a(lambda) = 2 a / (lambda^2-a^2).
```

Adding `G_a G_a*` makes the packet positive, but `P_a` is strictly amplified away from grade zero.
The ghost therefore cannot be paid without increasing the positive corner.

The obvious Gamma repair is also classified.  A prime-independent scalar ghost, an arbitrary
finite matrix ghost, or an arbitrary module-valued ghost with central prime--Gamma action can fit
primes two and three only at horizontal grade zero.  Source/Gamma naturality of the shared ghost
is pointwise equivalent to critical-line placement and globally equivalent to RH.  Replacing the
central action by the natural multiplicative co-shift does not help selectively: off the line,
forward and reflected ground profiles have distinct shift eigenvalues, so every invariant
boundary containing their difference contains both profiles separately.

**Positive survivor.**  The live construction must use genuinely prime-mixing, noncentral
dynamics and must break exact co-shift covariance through a controlled anomaly.  The anomaly must
pay the single bilateral rank-one ghost without the amplified `P_a` corner, while retaining the
Euler--Wold cubic labels and cofinal matrix norm.  Central enlargement, positive wall
translation, and equivariant singular boundary absorption are closed search classes.

Additional hostile falsifiers:

38. The shifted-positive Hardy Pick kernel cannot be transported to the literal boundary by a
    positive Schur multiplier; the universal translation multiplier has a negative two-node
    determinant.
39. Bilateral completion reduces, but does not remove, the obstruction: one shared ghost remains
    and its positive completion strictly amplifies the surviving source column.
40. Increasing central ghost rank or dropping positivity/topology does not evade prime-two/three
    rigidity.  Exact co-shift covariance likewise cannot selectively absorb the odd mode.

## 13. Controlled-covariance-anomaly and first-trace audits

The proposed noncentral repair cannot be obtained from the existing logarithmic clock anomaly.
For every bounded arithmetic clock, the finite-depth Sonin pullback/clock commutator converges
strongly to zero, and its Fisher-score discrepancy vanishes in the cofinal limit.  Exponentiating
to the logarithmic Weyl relation does not retain a transverse operator either: the commutator
collapses to a scalar central character.  A nonzero first-order rescaling would require a new,
noncanonical rate datum not present in the source complex.

The pure-Hodge transgression does retain the unsquared horizontal displacement, but its balanced
graph capacity is uniformly bounded exactly at displacement zero and diverges otherwise.  Thus it
is a detector with the desired odd orientation but no uniform nuclear envelope.  The affine
zero-clock packet is nonzero, while its odd jet is identically zero; the cofinal boundary
renormalization tends to the already RH-equivalent critical coefficient.

The squarefree first-trace anomaly solves a different half of the problem.  It is an upstream
analytic function whose analytic order equals Xi multiplicity, and its Fisher quotient has residue
twice that multiplicity.  This is a meromorphic scalar residue rather than a trace-class subunit
operator.  Normalizing the residue to an integral unit again reaches the sharp trace-norm wall.

**Positive survivor.**  Exact multiplicity is available before individual-zero specialization,
and exact horizontal oddness is available before divisor selection, but current constructions do
not put both in one uniformly nuclear operator.  Any useful covariance anomaly must be
nonvanishing without an external rate rescaling and must remain noncentral after completion.

Additional hostile falsifiers:

41. An unscaled bounded-clock Sonin commutator vanishes cofinally; it cannot carry a unit escape
    charge.
42. Pure-Hodge odd transgression is uniformly capacity-bounded only at the RH locus.
43. Meromorphic first-trace residues recover multiplicity, but residue normalization is not a
    subunit trace-class construction.

## 14. Completed Julia source-order and transverse-reporter audit

P-G206 and P-G207 already carry the proposed source/divisor interface farther than the abstract
relative-complex formulation.  The global coefficient-faithful Julia exterior coupling is
positive before any finite packet, survives both completed Gamma/polar residue gauges, and retains
full analytic multiplicity at every Xi copy.  Its rank-one Gram block has zero Schur short even
though the Xi coordinate is nonzero.  Four-orientation Wold regularization repairs that local
short, but the resulting endpoint quantum exceeds the available Euler source budget.

The literal pre-divisor orbit-source firewall is decisive: any local Loewner order transports by
trace closedness to the post-residue inequality, but every strict-right copy violates that order
at sufficiently deep truncation.  Global pre-divisor Loewner order and positive Gram conservation
are each equivalent to RH.  Complete positive splitting overspends, the natural Krein-signed split
still overspends, and fixed Route-O compensation is invisible at the cubic horizon.

A transverse Euler/Wold reporter can be chosen with cofinal value strictly between zero and the
source budget, and exact multiplicity reappears as a scalar factor.  This does not produce an
index: the reporter is continuously scaled source mass.  The unique negative counterleg realizes
the same signed trace, but rotation by the fundamental symmetry converts it to a physical trace
that overspends.  Exact Hardy sewing cancellation exists only in the indefinite form, whose
strict-right fibre fails bilateral moderation.  The exact joint-depth Krein landing likewise
reaches the Xi relative resolvent only as a scalar analytic continuation; its balanced-reflection
cross term is not summable, so no Hilbert operator extends across the wall.

**Positive survivor.**  Source-to-Xi coupling, completed residue transport, multiplicity, and a
strictly budgeted transverse scalar are all unconditional.  Missing theorem is not another source
estimate: it is a new signed/relative polar--Gamma colligation whose *operator* survives the
balanced wall and whose integral charge is not obtained by normalizing that scalar.

Additional hostile falsifiers:

44. Ordinary positive pre-divisor source order is globally equivalent to RH and fails locally at
    every hypothetical strict-right copy.
45. Existing indefinite cancellation is scalar-continuable but not Hilbert-operator-continuable
    across the balanced wall.
46. A budgeted transverse reporter cannot also dominate the completed endpoint; multiplicity as a
    scalar factor does not create relative-index integrality.

## 15. Ordered-Xi/RVM relative-completion trace cancellation

The strongest literal two-completion candidate in the corpus is the ordered-Xi signed prime
operator relative to its smooth Riemann--von Mangoldt skeleton.  Their difference is an
unconditional self-adjoint Schatten-one diagonal operator.  It is nevertheless target-fed by the
actual ordered Xi ordinates, carries no horizontal-displacement coordinate, and places each
relocation coefficient `d_p` in one marked-prime sector and `-d_p` in the other.

`XiOrderedPrimeRelativeTraceCancellation.lean` now proves unconditionally that

```text
Tr(xiOrderedSignedPrimeRVMCorrection) = 0,
Tr(xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) = 0,
Tr(xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) != 1.
```

The proof expands the Schatten-one trace in the coordinate Hilbert basis, splits the absolutely
summable series over the two signed prime sectors, and cancels each pair.  It uses neither a zero
location assumption nor a numerical estimate.  This is the exact obstruction to Steps 4--5 of
the proposed relative-homotopy route: trace-class difference alone does not make the chosen
operator a difference of projections, and this concrete relative difference has zero charge,
not Kakutani escape multiplicity one.

**Verdict.**  The proposed Step 1--6 relative projection route is retired.  Its available
pre-divisor or relative-completion realizations either saturate the unit trace-norm wall, lose the
operator at the balanced boundary, or have exact trace zero.  The broader `RPGT-Theta-S3` route
remains open only for a genuinely new prime-mixing, noncentral colligation with an independently
proved unit index and pre-absolute-value nuclear cancellation.

Additional hostile falsifiers:

47. Paired signed Xi/RVM trace-class relocation has exact ordinary trace zero.
48. Target-fed spectral relocation cannot serve as an upstream horizontal detector.
49. Relative-index integrality cannot be invoked until actual Fredholm/projection hypotheses and
    the arithmetic identification of the resulting integer are constructed.

## 16. Prime-harmonic singular-graph lift and sharp nuclear saturation

The strongest topology-changing source currently in the corpus is not an abstract dense-core
average.  `DeningerBigWittCrossPrimeHarmonicSingularGraphSource.lean` constructs actual normalized
prime-two Big-Witt horizon rows.  Their algebraic one-leg trace is exactly `1`, their ambient
Calderón--Witt `ell^2` realization tends to zero, and their graph realization tends to the
vertical singular vector `(0,1)`.

The canonical ordinary operator lift has now been completed without hypotheses.  Apply the
trace-norm-continuous positive rank-one embedding to those graph packets and to their vertical
limit.  New module
`GaloisForLFunctions.RHTower.DeningerBigWittPrimeHarmonicGraphTraceNormSaturation` proves:

```text
source rank-one packets -> |(0,1)><(0,1)| in Schatten-one norm,
Tr |(0,1)><(0,1)| = 1,
||(0,1)><(0,1)||_1 = 1,
ambientProjection ∘ |(0,1)><(0,1)| = 0.
```

This gives the exact ambient/graph dichotomy.  Any construction factoring through the ambient
projection loses the charge because the vertical generator maps to zero.  The canonical
charge-faithful graph lift retains ordinary trace one, but pays nuclear norm exactly one.  Ambient
collapse therefore supplies no strict trace-norm gain: the missing singular coordinate contains
all charge and all of its unavoidable unit nuclear cost.

**Verdict.**  Retire the prime-harmonic graph-to-rank-one continuation as a subunit route.  Retain
its positive survivor: a genuine arithmetic source sequence reaches a trace-one Schatten-one
operator before divisor specialization, and the exact obstruction is sharp saturation rather
than lack of source provenance.  A continuing `RPGT-Theta-S3` construction must create signed
operator cancellation before the positive rank-one/nuclear absolute value; ambient norm collapse
or graph completion alone cannot do it.

Additional hostile falsifiers:

50. Source-derived ambient collapse does not imply trace-norm collapse after a charge-faithful
    singular completion.
51. The vertical one-leg generator has a canonical ordinary trace-one lift, but its genuine
    approximation-number trace norm is exactly one.
52. Projecting before the lift erases the entire charge; lifting before projection preserves the
    charge only in the singular graph sector.
