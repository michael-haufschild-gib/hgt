# Blaschke-dressed atomic Anderson recurrence law

- **ID:** `blaschke-anderson-recurrence-law`
- **Stage:** 1-in-progress
- **Type:** EXACT INFINITE QUASI-LOCAL RANDOM-HAMILTONIAN RECURRENCE LAW
- **Labels:** `[PAPER-PROOF CANDIDATE] [RESIDUAL NOVELTY PLAUSIBLE] [KERNEL LEAN-PROVEN] [CAPSTONE LEAN-OPEN]`
- **Parent:** `anderson-local-spectral-depth-law`
- **Date opened:** 2026-07-31

## Public sentence

> In an exactly solvable infinite localized quantum system, the accuracy
> cost of returning home reveals both spatial dimension and localization
> volume.

## Model

Fix \(d\ge1\) and \(a_k\in(0,1)\) for \(1\le k\le d\).  On the unit
circle define the Blaschke factors
\[
 B_{a_k}(z)=\frac{z-a_k}{1-a_kz}.
 \tag{1}
\]
Their Fourier coefficients are
\[
 u_{a}(n)=
 \begin{cases}
 -a,&n=0,\\
 (1-a^2)a^{n-1},&n\ge1,\\
 0,&n<0.
 \end{cases}
 \tag{2}
\]
Let \(U\) be the convolution unitary on \(\ell^2(\mathbb Z^d)\) whose
Fourier multiplier is
\[
 \prod_{k=1}^dB_{a_k}(z_k),
 \]
equivalently whose kernel is
\[
 u(\mathbf n)=\prod_{k=1}^du_{a_k}(n_k).
 \tag{3}
\]

Let \((E_{\mathbf y})_{\mathbf y\in\mathbb Z^d}\) be iid random variables
on \([0,2\pi)\) with any density bounded by a finite constant \(B\) relative
to normalized Lebesgue measure.  Define
\[
 D_E\delta_{\mathbf y}=E_{\mathbf y}\delta_{\mathbf y},
 \qquad
 H_E=UD_EU^*.
 \tag{4}
\]
This is a translation-ergodic bounded self-adjoint random Hamiltonian,
obtained by a deterministic quasi-local unitary dressing of the atomic iid
operator.  It has exponentially decaying, generally infinite-range hopping.
The disorder randomizes eigenvalues; the localized eigenbasis is prescribed
by the dressing.

## Frozen theorem candidate

Put
\[
 \xi_k=\frac1{-\log a_k},
 \qquad
 \rho_k=-2\log a_k=\frac2{\xi_k}.
 \tag{5}
\]
For a fixed site \(x\), define its first positive stroboscopic amplitude
return
\[
 \tau_x(\eta)=
 \min\left\{n\ge1:
 \left|\langle\delta_x,e^{-inH_E}\delta_x\rangle\right|
 \ge1-\eta\right\}.
 \tag{6}
\]
Then for almost every disorder realization,
\[
 \boxed{
 \log\tau_x(\eta)\sim
 \frac{\prod_{k=1}^d\xi_k}
      {2^{d+1}(d+1)!}
 \bigl(\log(1/\eta)\bigr)^{d+1}}
 \qquad(\eta\downarrow0).
 \tag{7}
\]
The same full-measure event works for every \(x\in\mathbb Z^d\).
Moreover, almost surely there is \(\eta_0(x)>0\) such that, for all
\(\eta<\eta_0(x)\), the state has exited the target at time \(1\) and
\(\tau_x(\eta)\) is its first subsequent stroboscopic return.

For the standard pure-state trace-distance tolerance \(\varepsilon\), put
\(\eta_\varepsilon=1-\sqrt{1-\varepsilon^2}\).  Since
\(\log(1/\eta_\varepsilon)=2\log(1/\varepsilon)+O(1)\), (7) is equivalently
\[
 \boxed{
 \log\tau_x^{\rm tr}(\varepsilon)\sim
 \frac{\prod_{k=1}^d\xi_k}{(d+1)!}
 \bigl(\log(1/\varepsilon)\bigr)^{d+1}.}
 \tag{7a}
\]

Consequently,
\[
 \boxed{
 d=
 \lim_{\eta\downarrow0}
 \frac{\log\log\tau_x(\eta)}
      {\log\log(1/\eta)}-1.}
 \tag{8}
\]
Unlike the abstract minimax law, (7) concerns the actual first return after
exit of one fixed infinite Hamiltonian drawn from a specified exponentially
quasi-local random ensemble.

## Exact localization theorem

The eigenvectors
\[
 \phi_{\mathbf y}=U\delta_{\mathbf y}
 \]
form an orthonormal basis and
\[
 H_E\phi_{\mathbf y}=E_{\mathbf y}\phi_{\mathbf y}.
 \tag{9}
\]
For every \(x,z\in\mathbb Z^d\),
\[
 \boxed{
 \sup_{t\in\mathbb R}
 \left|\langle\delta_x,e^{-itH_E}\delta_z\rangle\right|
 \le
 2^d\prod_{k=1}^da_k^{|x_k-z_k|}
 =
 2^d\exp\left[-\sum_{k=1}^d
 \frac{|x_k-z_k|}{\xi_k}\right].}
 \tag{10}
\]
The Hamiltonian matrix itself obeys
\[
 |\langle\delta_x,H_E\delta_z\rangle|
 \le
 2\pi\,2^d
 \exp\left[-\sum_{k=1}^d
 \frac{|x_k-z_k|}{\xi_k}\right].
 \tag{11}
\]
Thus (7) and exponential dynamical localization hold for the same
realization and the same local observer.

## Dependency-closed paper proof candidate

### Blaschke unitarity

For \(|z|=1\),
\[
 |B_a(z)|=1.
\]
Multiplication by \(B_a\) is therefore unitary on \(L^2(\mathbb T)\).
Fourier transform transports it to convolution by (2) on
\(\ell^2(\mathbb Z)\).  Tensoring proves unitarity of \(U\).  Formula
(9), bounded self-adjointness, and ergodicity follow immediately from
(4), because \(U\) is deterministic and translation invariant.

### Exact dynamical localization

For \(r\in\mathbb Z\), direct summation gives
\[
 \sum_{m\in\mathbb Z}|u_a(m)u_a(m+r)|
 =
 \begin{cases}
 1,&r=0,\\
 2(1-a^2)a^{|r|},&r\ne0.
 \end{cases}
 \tag{12}
\]
The spectral expansion and \(|e^{-itE_{\mathbf y}}|=1\) imply
\[
 \begin{aligned}
 \left|\langle\delta_x,e^{-itH_E}\delta_z\rangle\right|
 &\le
 \sum_{\mathbf y}
 |u(x-\mathbf y)u(z-\mathbf y)|\\
 &=\prod_{k=1}^d
 \sum_{m\in\mathbb Z}
 |u_{a_k}(m)u_{a_k}(m+x_k-z_k)|.
 \end{aligned}
\]
Equation (10) follows from (12), using
\(2(1-a_k^2)\le2\).  Replacing each phase by
\(|E_{\mathbf y}|\le2\pi\) proves (11).

### Exact local spectral depth

At site \(x\), only centres
\(\mathbf y\le x\) coordinatewise have nonzero weight.  Relabel
\(\mathbf n=x-\mathbf y\in\mathbb N_0^d\).  The weights are
\[
 p_{\mathbf n}
 =\prod_{k=1}^d q_{a_k}(n_k),
 \quad
 q_a(0)=a^2,
 \quad
 q_a(n)=(1-a^2)^2a^{2(n-1)}\ (n\ge1).
 \tag{13}
\]
They are strictly positive on \(\mathbb N_0^d\) and sum to one.
There is a finite constant \(C=C(a_1,\ldots,a_d)\) such that
\[
 \left|
 -\log p_{\mathbf n}
 -\sum_{k=1}^d\rho_kn_k
 \right|\le C
 \qquad(\mathbf n\in\mathbb N_0^d).
 \tag{14}
\]
An anisotropic simplex lattice count therefore gives
\[
 \boxed{
 N_p(L)=\#\{\mathbf n:-\log p_{\mathbf n}\le L\}
 \sim
 \frac{L^d}{d!\prod_{k=1}^d\rho_k}.}
 \tag{15}
\]
The corresponding reverse-water information satisfies
\[
 {\cal H}_p(L)=\frac12\int_0^LN_p(u)\,du
 \sim
 \frac{L^{d+1}}
 {2(d+1)!\prod_{k=1}^d\rho_k}.
 \tag{16}
\]

### Almost-sure actual return

The local amplitude is exactly
\[
 \langle\delta_x,e^{-inH_E}\delta_x\rangle
 =
 \sum_{\mathbf n\in\mathbb N_0^d}
 p_{\mathbf n}e^{-inE_{x-\mathbf n}}.
 \tag{17}
\]
The participating energies are independent phases with uniformly bounded
density.

The countable projective pigeonhole estimate gives, for every phase
realization,
\[
 \log\tau_x(\eta)
 \le{\cal H}_p(\log(1/\eta))
 +o({\cal H}_p(\log(1/\eta))).
 \tag{18}
\]
The normalized-head Haar estimate and the bounded-density transfer give,
with \(M=N_p(2L)\) and
\(L=\log(1/\eta)\),
\[
 {\mathbb P}(\tau_x(\eta)\le N)
 \le
 N\,B^M N_p(2L)
 \exp\left[
 \frac\pi4-{\cal H}_p(L)+\frac L2
 \right].
 \tag{19}
\]

Set \(\eta_m=e^{-m}\) and
\[
 N_m=\left\lfloor
 \exp((1-\epsilon){\cal H}_p(m))
 \right\rfloor.
\]
By (15)--(16), \(M\log B=O(m^d)=o({\cal H}_p(m))\), so the right side of
(19) is summable in \(m\).
Borel--Cantelli gives, almost surely,
\[
 \log\tau_x(e^{-m})
 \ge(1-\epsilon){\cal H}_p(m)
\]
for all sufficiently large \(m\).  Interpolation between consecutive
integers, followed by \(\epsilon\downarrow0\), and (18) yield
\[
 \log\tau_x(\eta)
 \sim{\cal H}_p(\log(1/\eta)).
 \tag{20}
\]
There are countably many sites, so intersecting their probability-one
events proves simultaneous validity for every \(x\).  Substituting
\(\rho_k=2/\xi_k\) into (16) proves (7).

## What the theorem does and does not say

It proves:

1. one infinite random Hamiltonian has exponential dynamical localization
   and the exact almost-sure first-return law simultaneously;
2. spatial dimension is the recurrence-accuracy exponent minus one;
3. the leading coefficient is the anisotropic localization-cell volume
   \(\prod_k\xi_k\) divided by a universal geometric factor;
4. the result holds for every integer dimension and every positive vector
   of localization lengths.

It does not prove:

1. the same exact constant for the nearest-neighbour iid Anderson model;
2. finite-range hopping—the exact model has exponentially decaying
   infinite-range hopping;
3. a continuous-time scale independent of energy units;
4. interacting many-body localization, thermality, gravity, or cosmology;
5. a physically normalized continuous-time return law: the proved object is
   a Floquet/stroboscopic return, and changing energy units changes the
   continuous-time scale.

## Novelty and hostile gate

The weight small-deviation exponent collides with Rozovsky and Aurzada.
Campos Venuti (2015) studies average recurrence-time densities under
rational independence and a Gaussian approximation, including a formal
countable-discrete extension.  It does not prove an almost-sure first
positive return at vanishing target size, an exact depth-entropy constant,
or a localization-geometry transfer.  Grünbaum--Velázquez--Werner--Werner
and subsequent work study monitored first detection, whose repeated
projections change the dynamics and whose return law is a different
observable.  Kotowski--Oszmaniec (2026) prove tight finite-dimensional
closed-system bounds and random-Hamiltonian saturation, but not the
countably infinite localization-depth law.

No direct literature collision was found for the following conjunction:

- explicit ergodic infinite self-adjoint random Hamiltonian;
- exact all-time dynamical localization;
- exact local spectral-depth count in arbitrary dimension;
- almost-sure actual first-return asymptotic with localization-length
  coefficient, robust across every iid eigenphase law with uniformly
  bounded density.

Hostile rejection conditions:

1. prior literature already contains this conjugated-diagonal
   Blaschke/Laurent ensemble and the same return law;
2. the model is judged physically empty because \(U\) is fixed and the
   disorder randomizes only eigenvalues;
3. exponential long-range hopping is deemed outside the intended
   Anderson-locality class;
4. the Borel--Cantelli law silently assumes independent time samples
   rather than reusing powers of one fixed phase packet;
5. any operator, lattice-count, probability, or recurrence claim remains
   absent from the formal corpus at submission.

The exact model is an application, not the universal headline theorem.
The universal target is the abstract implication from regularly varying
local spectral depth and independent uniformly bounded-density eigenphases
to an almost-sure first-return asymptotic.  A conventional nearest-neighbour
Anderson transfer would be a separate major theorem; standard one-sided
localization estimates do not currently supply its required lower
spectral-weight law.

## Formal status

The following claims are now proved in
`formal/GaloisForLFunctions/RHTower/BlaschkeLocalizedKernelLaw.lean`:

- scalar kernel normalization;
- exact positive-shift absolute overlap;
- exact positive-shift signed orthogonality;
- strict positivity of every nonorigin local spectral weight;
- positive logarithmic decay slope;
- the exact affine logarithmic-depth progression;
- the exact infinite geometric tail;
- the exact quadratic finite integrated-depth formula;
- exact floor-based active-depth radius and membership classification;
- an explicit two-sided quadratic integrated-depth law with a complete
  linear remainder.

The following infinite-system consequences are proved in
`formal/GaloisForLFunctions/RHTower/BlaschkeLocalizedSurvivalRecurrenceLaw.lean`:

- exact identification of the countable survival tail;
- a deterministic positive survival return for every phase packet, with
  visible-head deadline and exact infinite-tail budget;
- the exhaustive never-exits/post-exit-return alternative with the same
  exact tail budget.

The arbitrary-water finite-head estimate is now proved in
`formal/GaloisForLFunctions/RHTower/ProjectiveWeightedBoundedDensityQuantile.lean`.
It retains full water entropy, pays only the exact half-logarithmic
worst-pivot loss, propagates through all clocks up to \(N\), and allows a
correlated phase law dominated by a finite multiple of Haar measure.

The deterministic countable-to-finite event bridge is proved in
`formal/GaloisForLFunctions/RHTower/SummableWeightedHeadReduction.lean`.
An amplitude return of the complete countable packet forces an amplitude
return of every positive-mass normalized finite head, with the exact defect
amplification \(\eta/m\), where \(m\) is head mass.

The measurable infinite-phase lift is proved in
`formal/GaloisForLFunctions/RHTower/SummableWeightedInfinitePhaseQuantile.lean`.
The complete countable early-hit event is measurable, is contained in the
pullback of the normalized-head event, and inherits the finite-head
full-water-entropy bound from any dominated finite marginal.  No
independence or distributional assumption on the discarded tail is used.
The same module proves the exact rescaling from normalized-head entropy back
to the original unnormalized local spectral weights.

The corpus also contains the anisotropic constructive recurrence ceiling in
`ProjectiveWeightedHaarQuantileActiveSupport.lean` and
`ProjectiveWeightedCoherenceCeiling.lean`.  This removes the apparent
factor-two loss produced by uniform phase resolution: the upper deadline
pays the same water entropy as the early-hit obstruction, plus only a cost
linear in active depth.  Its countable-head composition is now proved in
`SummableWeightedHeadEntropyCeiling.lean`: finite-head coherence implies
full countable coherence with exact defect
\(m\eta+2\,\mathrm{tail}\), and every normalized-head canonical
water-entropy deadline becomes a complete countable deadline.

The exact Blaschke active-head identity and probability specialization are
proved in `BlaschkeLocalizedInfinitePhaseQuantile.lean`.  At water level
\(e^L\), active-head water entropy equals
`blaschkeDepthWaterEntropy a L` exactly, and the full countable early-hit
probability pays that exact exponent.

The scale-wise lower clock is now proved in
`BlaschkeLocalizedEarlyReturnClock.lean`.  For shifted scales
\(L_k=k+K\), every fixed positive fractional gap below the quadratic
spectral-depth clock gives a polynomial-times-Gaussian early-hit budget.
First Borel--Cantelli therefore yields eventual almost-sure avoidance
without independence across clocks or scales.  The same module proves that
every finite head of countable product Haar is exactly finite product Haar
and supplies the explicit integer deadline
\[
 \left\lfloor
 \exp\!\left((1-\delta)
 \frac{(L_k-c)^2}{4\rho}-L_k\right)
 \right\rfloor .
\]
Thus the lower-clock statement is no longer conditional on an abstract
finite-marginal domination input in the Haar ensemble.

The matching constructive water clock is proved in
`SummableWeightedHeadFixedWaterCeiling.lean` and
`BlaschkeLocalizedUpperReturnClock.lean`.  Any feasible normalized-head
water level produces a complete countable return while paying the exact
unnormalized head entropy.  For the active Blaschke head this specializes
without slack to
\[
 \log T_L\le {\cal H}_a(L)
 +(R_a(L)+1)\log C_{\rm phase},
\]
at the exact full-packet defect
\[
 \eta_L^{+}=(R_a(L)+1)e^{-L}
 +2(1-a^2)(a^2)^{R_a(L)+1}.
\]
Hence lower obstruction and constructive upper return now have the same
quadratic depth-entropy coefficient; their remaining costs are linear in
active depth or logarithmic in target reparameterization.

The measurable hit event is now identified with the actual first positive
return in `CountableWeightedFirstReturn.lean`, using an extended-natural
clock so nonexistence cannot be hidden by a default value.  The complete
same-target capstone is proved in
`BlaschkeLocalizedFirstReturnSandwich.lean`: for almost every product-Haar
phase packet and every fixed \(\delta>0\), eventually
\[
 \lfloor e^{(1-\delta)Q_k-L_k}\rfloor
 <\tau(e^{-L_k})\le T_k,
\]
where
\[
 \log T_k\le
 {\cal H}_a(L_k+\sqrt{k})
 +(R_a(L_k+\sqrt{k})+1)\log C_{\rm phase}.
\]
The target calibration is unconditional:
`BlaschkeLocalizedReturnDefect.lean` proves the exact constructive defect
is at most \(C_a(1+L)e^{-L}\), and
`BlaschkeLocalizedReturnDefectLimit.lean` proves the square-root shift makes
that defect at most \(e^{-L_k}\) eventually.  Thus the two clocks concern
the same actual first-return observable and the same target accuracy.

Direct foreground Lean checks pass. `#print axioms` for audited new
load-bearing theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Operator construction, anisotropic counting, the Blaschke asymptotic
normalization of the exact two-sided sandwich, interpolation from integer
logarithmic scales to all target accuracies, and the closed-form
almost-sure first-return limit remain Lean-open. Nothing beyond the listed
proved claims is manuscript-authorized until formalized. Manuscript must
not mention the formalization.
