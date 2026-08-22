# Arithmetic static-local hardness--recurrence window law

- **ID:** `arithmetic-static-local-hardness-recurrence-window-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** effective quenched plateau-entry / recurrence-window theorem
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Inputs:** `local-clifford-return-excised-phase-incidence-law`,
  `generic-two-local-spectral-monodromy`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY CANDIDATE]
  [LEAN DEFERRED BY CORPUS REFACTOR]`
- **Date:** 2026-08-08

## Public sentence

A single time-independent two-local Hamiltonian with integer couplings can be selected
algorithmically so that its Choi/thermofield-double orbit reaches the full `2^n/log n` spectral-
phase complexity scale in **every sufficiently long time window**, while approximate quantum
returns also occur in every sufficiently long time window.  The same Hamiltonian gives a weaker
exponential law from one fixed product state.  All window lengths are finite and computable from
the Hamiltonian.

This is the first explicit computable upper bound on the syndeticity constant in the static-local
programme.  Its deadline is enormous and it does not prove Brown--Susskind linear growth or the
conjectured exponential physical time scale.

## What is new relative to the preceding card

`computable-static-local-exponential-state-complexity-law` selected integer local Hamiltonians and
hard endpoints by a terminating search, but it gave no upper bound on the endpoint time.  The
present theorem finds the missing clock.  Finite algebraic description prevents every bounded
integer spectral action from being too small.  A finite Fejer packet then converts that arithmetic
separation into a uniform moving-window phase-hitting law.  Combining this with the completed-phase
circuit obstruction gives an effective, quenched, approximate-complexity plateau theorem.

The conclusion is stronger than one first hitting time: a definite fraction of every long enough
window lies in one robust hard phase cell.

## Theorem A -- arithmetic moving-window phase law

Let `D>=2`, put `d=D-1`, and let `H` be a `D` by `D` Hermitian matrix whose characteristic
polynomial lies in `Z[X]`.  Label its distinct eigenvalues `E_1,...,E_D` and assume the projective
frequencies

\[
 \omega_j=E_{j+1}-E_1\qquad(1\le j\le d)               \tag{1}
\]

are rationally independent.  Put

\[
 R=\max(1,\|H\|_{\mathrm{op}}).                         \tag{2}
\]

For `0<rho<=1`, define

\[
 \mu_\rho=\left({\rho\over2\pi}\right)^d,
 \qquad
 N_\rho=\left\lceil
   \left({8\pi d\over\rho\mu_\rho}\right)^2
 \right\rceil,                                          \tag{3}
\]

and

\[
 \boxed{
 \mathcal T(D,R,\rho)=
 8(2N_\rho+1)^d(2dN_\rho R)^{D!-1}.}                    \tag{4}
\]

Let `T^d=(R/2pi Z)^d`, with angular sup-distance `dist_infty`.  For every phase centre
`theta_* in T^d` and every starting time `u>=0`,

\[
 \boxed{
 \left|\left\{t\in[u,u+\mathcal T(D,R,\rho)]:
 \operatorname{dist}_\infty(t\omega,\theta_*)<\rho
 \right\}\right|
 \ge {\mu_\rho\over2}\mathcal T(D,R,\rho).}             \tag{5}
\]

Thus every phase cube of radius `rho` is visited in every interval of length `(4)`, and it is
occupied for at least the explicit fraction `mu_rho/2` of that interval.

### Proof of Theorem A

#### 1. Algebraic description bounds every truncated spectral action

Every `E_j` is an algebraic integer.  Let `L` be the splitting field of the characteristic
polynomial.  It is Galois over `Q`, has degree at most `D!`, and every automorphism of `L` permutes
the eigenvalues.  Because all roots of the characteristic polynomial are eigenvalues of the
Hermitian matrix,

\[
 |\sigma(E_j)|\le R                                      \tag{6}
\]

for every `sigma in Gal(L/Q)`.

Fix a nonzero `k in Z^d` with `||k||_infty<=N`.  Rational independence makes

\[
 \beta_k=k\mathbin\cdot\omega\ne0.                       \tag{7}
\]

It is an algebraic integer, and every conjugate satisfies

\[
 |\sigma(\beta_k)|
 \le\sum_{j=1}^d|k_j|\,|\sigma(E_{j+1})-\sigma(E_1)|
 \le2dNR.                                                \tag{8}
\]

The field norm of `beta_k` is a nonzero rational integer.  Dividing that norm by all conjugates
except the identity gives

\[
 \boxed{
 |k\mathbin\cdot\omega|
 \ge(2dNR)^{-(D!-1)}}                                    \tag{9}
\]

uniformly for `0<||k||_infty<=N`.  This is the arithmetic input.  A minimum pairwise spectral gap
would not imply `(9)`.

#### Lean progress -- steps 1 and 3

`formal/GaloisForLFunctions/HTGeometry/ArithmeticWindowPhase.lean` (new, umbrella-wired,
axiom-clean) proves the two quantitative cores of Theorem A's proof.

| Card item | Declaration |
|---|---|
| **`(9)`**, the Liouville separation: a product of modulus at least one with all but one factor below `B` forces the remaining factor above `B^{-(m-1)}` | `abs_ge_of_abs_prod_ge_one`, `inv_pow_le_abs` |
| the antiderivative of a pure oscillation, `e^{it beta}/(i beta)` | `hasDerivAt_expWindow` |
| **`(17)`**, the window oscillation bound `|int_u^{u+T} e^{it beta} dt| <= 2/|beta|`, uniformly in the window position | `norm_integral_exp_window_le` |

`(9)` is stated as pure arithmetic -- the field-norm bookkeeping of step 1 supplies the hypothesis
`1 <= |prod of conjugates|` and the conjugate bound `(8)`, and the lemma turns them into the
separation.  `(17)` is exact: the antiderivative has modulus `1/|beta|` at every point, so the
window integral is at most `2/|beta|` regardless of where the window sits.

##### Step 1's number theory is closed

`formal/GaloisForLFunctions/HTGeometry/AlgebraicIntegerSeparation.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the field norm of a nonzero algebraic integer is a nonzero rational integer, so the product of all embedding moduli is at least one | `one_le_prod_norm_embeddings` |
| **`(9)`**: all embeddings but one below `B` force the remaining one above `B^{-(n-1)}` | `inv_pow_le_norm_embedding` |

The proof is `Algebra.norm_eq_prod_embeddings` for the product over complex embeddings,
`Algebra.norm_ne_zero_iff` for nonvanishing and `Algebra.coe_norm_int` for integrality; the
separation is then the erase-one-factor estimate.  What step 1 still supplies from the card's own
setting is the conjugate bound `(8)` itself -- that Galois conjugates of the eigenvalues stay below
`2dNR` -- which is a statement about the spectral form, not about number fields.

##### `(17)`--`(18)` are assembled

`formal/GaloisForLFunctions/HTGeometry/WindowMeanSeparatedModes.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| **`(17)` aggregated**: a packet of separated nonzero modes has window mean at most `\|K\| c 2/(T beta)` | `norm_window_mean_le` |
| **`(18)`**: hence a packet with constant coefficient `mu` has window mean at least `mu` minus that error | `window_mean_ge` |

Both hold uniformly in the window position `u`, which is what "every shifted time window" asks for.
The separation `beta` is exactly the arithmetic input `(9)`, now supplied by
`inv_pow_le_norm_embedding`.

##### Step 2 is closed in one dimension

`formal/GaloisForLFunctions/HTGeometry/TorusFejerDisplacement.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the Fejér kernel `F_N = \|D_N\|²/(N+1)` and its nonnegativity | `torusFejer`, `torusFejer_nonneg` |
| its cosine expansion, and the vanishing of every off-diagonal mode | `norm_dirichletSum_sq`, `integral_cos_mode` |
| the kernel has Haar mean one | `integral_torusFejer` |
| **`(15)`**: the quadratic tail `F_N(x) <= pi²/((N+1)x²)` | `torusFejer_le` |
| its two inputs: `\|D_N(x)\| <= 1/\|sin(x/2)\|` and Jordan's inequality | `norm_dirichletSum_le`, `abs_div_pi_le_abs_sin_half` |
| **`(14)`**: the mean displacement `(1/2pi)int \|x\| F_N <= 2pi/sqrt(N+1)` | `integral_abs_mul_torusFejer_le` |
| the Fejér mean `P = f * F_N` of `f` | `fejerConv` |
| **`(16)`**: an `L`-Lipschitz `f` obeys `\|\|P - f\|\|_infty <= 2 pi L/sqrt(N+1)` | `abs_fejerConv_sub_le` |
| **`(10)`**: the tent `q_rho`, its positivity cube, and its `1/rho`-Lipschitz constant | `torusTent`, `torusTent_pos_iff`, `abs_torusTent_sub_le` |
| **`(11)`**: the tent has Haar mean `rho/2pi` | `integral_torusTent` |
| `(16)` for the tent itself | `abs_fejerConv_torusTent_sub_le` |
| the Fejér mean of a `[0,1]`-valued function stays in `[0,1]` | `fejerConv_nonneg`, `fejerConv_le_one` |
| the telescoping bound `\|prod a - prod b\| <= sum \|a-b\|` on the unit ball | `abs_prod_sub_prod_le` |
| **`(16)` in `d` dimensions**: `\|\|P - f\|\|_infty <= 2 pi d/(rho sqrt(N+1))` | `abs_productFejerTent_sub_le` |

The proof of `(14)` is exactly the card's: split at `delta = pi/sqrt(N+1)`, bound the inner
contribution by `delta` times the total mass and the outer contribution by `pi` times the tail
integral `int_delta^pi pi²/((N+1)x²)dx <= pi²/((N+1)delta)`; the two halves are equal at that
`delta`.  The reciprocal-square integral is evaluated by the antiderivative `-x^{-1}`
(`integral_inv_sq`), so no improper-integral theory is used.

The `d`-dimensional packet is carried by the Fubini factorization: convolving the product tent
against `F_N^{otimes d}` is the product of the one-dimensional Fejér means (`productFejerTent`), so
`(16)` in `d` dimensions is the telescoping bound applied to the one-dimensional displacement.

##### Step 2 on the circle: `(12)`--`(13)` are closed

`formal/GaloisForLFunctions/HTGeometry/PeriodicTentPacket.lean` (new, umbrella-wired, axiom-clean)
repeats the construction with a genuinely `2pi`-periodic tent, which is what the Fourier statements
`(12)`--`(13)` require.

| Card item | Declaration |
|---|---|
| the whole-turn lattice and the distance to it; `1`-Lipschitz and turn-invariant | `turnLattice`, `turnDist`, `abs_turnDist_sub_le`, `periodic_turnDist` |
| on `\|x\| <= pi` the turn distance is `\|x\|` | `turnDist_eq_abs` |
| **`(10)` on the circle**: the periodic tent, its positivity ball, its `1/rho`-Lipschitz constant | `perTent`, `perTent_pos_iff`, `abs_perTent_sub_le`, `periodic_perTent` |
| **`(11)`**: its mass is `rho`, i.e. Haar mean `rho/2pi` | `integral_perTent` |
| the Fourier coefficient of a periodic function, and periodicity of the integrand | `perFourierCoeff`, `periodic_fourierIntegrand` |
| the shifted mode integral `int f(theta-x)e^{inx}dx = 2pi e^{in theta} hat f(n)` | `integral_shift_mode` |
| **`(12)` in one dimension**: the Fejér mean is a trigonometric polynomial on the `(N+1)²` differences `p-q` | `fejerConv_eq_modeSum`, `fejerConv_eq_pairSum` |
| **`(13)` in one dimension**: `\|hat f(m)\| <= ` the Haar mean; for the tent, `<= rho/2pi` | `norm_perFourierCoeff_le`, `norm_perFourierCoeff_perTent_le` |
| the constant coefficient is the Haar mean | `perFourierCoeff_zero`, `perFourierCoeff_perTent_zero` |
| **`(12)` in `d` dimensions**: the packet is a finite sum of modes indexed by tuples of pairs | `packetMode`, `periodicProductFejerTent_eq_modeSum` |
| **`(13)` in `d` dimensions**: every mode weight is at most `((N+1)^{-1} rho/2pi)^d` | `norm_packetMode_le` |
| the diagonal modes are the constant ones, and they sum to `mu_rho = (rho/2pi)^d` | `packetMode_diagonal`, `sum_diagonal_packetMode` |
| **the packet splits as `mu_rho` plus its nonconstant modes** | `periodicProductFejerTent_eq_const_add` |
| **`(16)` on the circle**, in one and in `d` dimensions | `abs_fejerConv_perTent_sub_le`, `abs_periodicProductFejerTent_sub_le` |

The `d`-dimensional expansion is left ungrouped -- indexed by tuples of pairs rather than by
frequency vectors -- which is not a loss: the `(N+1)^{2d}` terms each of weight
`((N+1)^{-1} mu_rho^{1/d})^d` give the aggregate `(N+1)^d mu_rho`, which is *smaller* than the
card's grouped `(2N+1)^d mu_rho`.  Grouping is therefore unnecessary for step 3.

##### Step 3 is closed: `(17)`--`(19)` and `(5)`

Same module.  Evaluating the packet along `theta = t omega` turns every mode into a pure
oscillation, and the already formal `window_mean_ge` then delivers the moving-window floor.

| Card item | Declaration |
|---|---|
| the frequency `k · omega` a mode carries, and its time-independent amplitude | `packetFreq`, `packetAmp`, `norm_packetAmp_le` |
| **each mode is a pure oscillation in `t`** | `packetMode_linearPhase` |
| **`(18)`**: the moving-window mean of the packet is at least `mu_rho` minus the aggregate oscillation error | `window_mean_periodicProductFejerTent_ge` |
| the Fejér mean of a periodic function is continuous (it *is* the trigonometric polynomial) | `continuous_fejerConv` |
| **`(19)`**: the tent itself inherits that floor, up to the uniform displacement `(16)` | `window_mean_periodicProductTent_ge` |
| the cube-visit set and its measurability | `cubeVisit`, `measurableSet_cubeVisit` |
| the tent is dominated by the indicator of the cube | `periodicProductTent_le_indicator` |
| **`(5)`**: every moving window of length `T` spends at least the displayed fraction inside the cube | `measureReal_cubeVisit_ge` |

`measureReal_cubeVisit_ge` is Theorem A's conclusion with all three error terms explicit and
uniform in the window position `u`: the separation `βmin` enters only as the hypothesis `hsep`,
which is exactly `(9)` applied to `k · omega`.

##### `(8)` and the assembly: Theorem A is formal

`formal/GaloisForLFunctions/HTGeometry/SpectralFormConjugateBound.lean` and
`formal/GaloisForLFunctions/HTGeometry/ArithmeticWindowCapstone.lean` (both new, umbrella-wired,
axiom-clean) close the arithmetic half and glue the two halves together.

| Card item | Declaration | Module |
|---|---|---|
| the integer spectral form `beta_k = sum k_j (E_{j+1} - E_1)` | `spectralForm` | `SpectralFormConjugateBound` |
| every embedding of it is the same integer combination of the embedded eigenvalues | `embedding_spectralForm` | same |
| **`(8)`**: coefficients `<= N` and eigenvalue embeddings `<= R` force every conjugate below `2dNR` | `norm_embedding_spectralForm_le` | same |
| **`(9)`** for the spectral form: `\|beta_k\| >= (2dNR)^{-(n-1)}` | `inv_pow_le_norm_embedding_spectralForm` | same |
| the mode frequency `k · omega` *is* the distinguished embedding of a spectral form | `packetFreq_eq_embedding` | `ArithmeticWindowCapstone` |
| **the uniform separation of every nonconstant mode** | `inv_pow_le_abs_packetFreq` | same |
| **the explicit thresholds**: `N` and `T` large enough make both error terms `<= mu_rho/4` | `half_mul_le_measureReal_cubeVisit` | `PeriodicTentPacket` |
| **Theorem A, unconditional** | `half_mul_le_measureReal_cubeVisit_of_algebraic` | `ArithmeticWindowCapstone` |

The final statement takes an algebraic spectrum `E : Fin (d+1) -> 𝓞 K` with all complex embeddings
bounded by `R` and no integer relation among the anchored gaps, and concludes that for every window
position `u`, every window of length `T` satisfying
`8(N+1)^d <= T (2dNR)^{-(n-1)}` and `8 pi d <= rho (rho/2pi)^d sqrt(N+1)` obeys

`(rho/2pi)^d/2 · T <= |{t in (u, u+T] : t omega lies in the cube of half-width rho around c}|`.

No genericity, no first-hit argument, and no hypothesis beyond the two displayed thresholds: the
separation `(9)` is supplied internally by the number theory rather than assumed.

##### What remains

Theorem A is complete.  Theorems B, C and D of the card are untouched.
For the multi-dimensional kernel the corpus also owns a Bohr-side stack, in
the Bohr almost-periodic setting that this card's moving-window mean lives in:
`HTGeometry/BohrFejerKernel.lean` (`fejerKernel`, `fejerKernel_nonneg`, `fejerKernel_eq_sum`,
`continuous_fejerKernel`, **`bohrMean_fejerKernel`** -- mean one),
`HTGeometry/BohrFejerConvergence.lean` (**`norm_bohrMean_fejer_sub_le`** -- quantitative Fejér
convergence with an explicit tail term `4‖f‖/((N+1)c)` governed by the frequency separation `c`),
and `HTGeometry/BohrMultiFejerMean.lean` (`bohrMean_multiFejerKernel` -- the multi-dimensional
kernel has mean one).  The separation `c` there is exactly what `(9)` supplies.

#### 2. A finite Fejer packet detects a phase cube

On `T=R/2pi Z`, let

\[
 q_\rho(x)=\max\left(1-{|x|_T\over\rho},0\right),
 \qquad
 f(\theta)=\prod_{j=1}^dq_\rho(\theta_j-\theta_{*,j}).   \tag{10}
\]

Then `0<=f<=1`, its positivity set is the open cube in `(5)`, and

\[
 \int_{T^d}f\,dm=\mu_\rho.                               \tag{11}
\]

Let `F_N` be the order-`N` Fejer kernel, normalized to have Haar integral one, and put

\[
 P=f*(F_N^{\otimes d}).                                  \tag{12}
\]

The polynomial `P` has Fourier support `||k||_infty<=N`, constant coefficient `mu_rho`, and

\[
 |\widehat P(k)|\le\int f\,dm=\mu_\rho.                 \tag{13}
\]

For completeness, the one-dimensional Fejer displacement obeys

\[
 \int_T|x|_T F_N(x)\,dm(x)\le {2\pi\over\sqrt{N+1}}.    \tag{14}
\]

Indeed, for the representative `|x|<=pi`, split at
`delta=pi/sqrt(N+1)`.  The inner contribution is at most `delta`.  Outside it use

\[
 F_N(x)\le{\pi^2\over(N+1)x^2};                          \tag{15}
\]

the tail mass is at most `pi/((N+1)delta)`, and multiplying it by the maximal distance `pi`
proves `(14)`.

The product tent in `(10)` is `1/rho`-Lipschitz for the `l^1` distance.  Therefore `(14)` and
`(3)` give

\[
 \|P-f\|_\infty
 \le {2\pi d\over\rho\sqrt{N_\rho+1}}
 \le {\mu_\rho\over4}.                                 \tag{16}
\]

#### 3. Every shifted time window has positive cube occupation

For a nonzero Fourier mode, `(9)` implies, uniformly in the starting time `u`,

\[
 \left|{1\over T}\int_u^{u+T}e^{itk\cdot\omega}\,dt\right|
 \le {2\over T|k\cdot\omega|}
 \le {2(2dN_\rho R)^{D!-1}\over T}.                     \tag{17}
\]

There are fewer than `(2N_rho+1)^d` nonconstant modes.  Combining `(13)`, `(17)`, and the choice
`T=mathcal T(D,R,rho)` gives

\[
 {1\over T}\int_u^{u+T}P(t\omega)\,dt
 \ge\mu_\rho-{\mu_\rho\over4}={3\mu_\rho\over4}.      \tag{18}
\]

Equation `(16)` now yields

\[
 {1\over T}\int_u^{u+T}f(t\omega)\,dt
 \ge{\mu_\rho\over2}.                                  \tag{19}
\]

Since `f<=1` and vanishes outside the cube, `(19)` proves `(5)`.  Notice that the estimate is
unchanged by shifting the time interval.  This is what upgrades a first-hit theorem to a
moving-window law.  QED.

## Theorem B -- effective hard windows and recurrence windows

Fix a unit input `Omega` with spectral weights

\[
 p_j=|\langle e_j,\Omega\rangle|^2,
 \qquad C_H(\Omega)=\sum_jp_j^2.                       \tag{20}
\]

Let `Z` be a finite family of unit target states.  For `r>=1`, let

\[
 h_r(Z)=\dim_\mathbb C\operatorname{span}
       \{z^{\otimes r}:z\in Z\}.                       \tag{21}
\]

Choose `0<a_0<a_1<=1` and assume

\[
 \boxed{
 h_r(Z)r!\left({16C_H(\Omega)\over a_0^2}\right)^r<1.} \tag{22}
\]

Set

\[
 \rho={a_1-a_0\over4}.                                  \tag{23}
\]

Then there is a relative phase centre `theta_*` such that, for every `u>=0`,

\[
 \boxed{
 \begin{aligned}
 \big|\{t\in[u,u+\mathcal T(D,R,\rho)]:
  |\langle e^{-itH}\Omega,z\rangle|^2<a_1
  \text{ for every }z\in Z\}\big|\\
 \ge {\mu_\rho\over2}\mathcal T(D,R,\rho).
 \end{aligned}}                                         \tag{24}
\]

Independently, for every `0<delta<=1`, every interval of length
`mathcal T(D,R,delta)` contains a set of times of measure at least
`mu_delta mathcal T(D,R,delta)/2` on which

\[
 \inf_{\alpha\in\mathbb R}
 \|e^{-itH}\Omega-e^{i\alpha}\Omega\|<\delta.          \tag{25}
\]

Thus robust target avoidance and approximate recurrence are both syndetic: neither can disappear
for an arbitrarily long time.

### Proof of Theorem B

The completed-phase incidence theorem gives

\[
 m\{\theta:\exists z\in Z,
 |\langle\Phi_H(\theta),z\rangle|^2\ge a_0\}
 \le h_r(Z)r!\left({16C_H(\Omega)\over a_0^2}\right)^r<1. \tag{26}
\]

The event is invariant under common phase, so `(26)` descends unchanged to the relative
`d`-torus.  Choose `theta_*` outside it.  If
`dist_infty(theta,theta_*)<rho`, then

\[
 \|\Phi_H(\theta)-\Phi_H(\theta_*)\|\le\rho.            \tag{27}
\]

For every unit `z`,

\[
 \left||\langle\Phi_H(\theta),z\rangle|^2
       -|\langle\Phi_H(\theta_*),z\rangle|^2\right|
 \le2\rho.                                               \tag{28}
\]

Hence all target overlaps in that cube are strictly smaller than

\[
 a_0+2\rho={a_0+a_1\over2}<a_1.                          \tag{29}
\]

Theorem A proves `(24)`.

For `(25)`, apply Theorem A to the cube of radius `delta` centred at the relative origin.  After
factoring out `e^{-itE_1}`, the norm difference from the initial state is at most the angular
sup-distance, proving the claim.  QED.

### Lean progress -- the cube-stability half of Theorem B

`formal/GaloisForLFunctions/HTGeometry/PhaseOrbitCubeStability.lean` (new, umbrella-wired,
axiom-clean) proves the three deterministic steps `(27)`--`(29)` on top of the corpus's `phaseOrbit`.

| Card item | Declaration |
|---|---|
| two unimodular phases differ by at most their argument difference | `norm_expPhase_sub_le` |
| **`(27)`**: the orbit of an orthogonal family of total weight `<= 1` moves by at most the sup-distance | `norm_phaseOrbit_sub_le`, `norm_phaseOrbit_sub_le_radian` |
| **`(28)`**: the overlap score with a unit target is `2`-Lipschitz in the state | `abs_score_sub_le` |
| **`(29)`**: a bound at the cube centre survives on the whole cube, with loss `2 rho` | `score_le_of_norm_sub_le` |

`(27)` is Pythagorean: the component errors are pairwise orthogonal because the family is, so the
squared orbit displacement is the weighted sum of `|e^{i alpha}-e^{i beta}|^2 = 4 sin^2((alpha-beta)/2)`,
each at most the squared angular gap.  The radian form removes the `2 pi` that the corpus's
turn-parametrised `phaseOrbit` carries.

### Lean progress -- Theorem B is closed

`formal/GaloisForLFunctions/HTGeometry/ArithmeticWindowHardCell.lean` (new, umbrella-wired,
axiom-clean) supplies `(26)`, the robust cell, and the assembly with Theorem A.

| Card item | Declaration |
|---|---|
| the coordinate inner product is the Euclidean one, and the norm bound it carries | `finiteComplexInner_eq_inner`, `sq_norm_toLp`, `norm_toLp_le_one` |
| **`(28)` in coordinates**: the overlap score is `2`-Lipschitz in the state | `abs_finitePureStateFidelity_sub_le` |
| two unimodular phases differ by at most the *turn* distance of their arguments | `norm_exp_ofReal_mul_I_sub_le_turnDist`, `turnDist_neg` |
| the spectral phase orbit in radian phases, and its identification with the torus orbit | `radianOrbit`, `torusReplicaPhaseOrbit_eq_radianOrbit`, `charPhase_single_index` |
| **`(27)`**: the orbit moves by at most the angular sup-distance | `norm_radianOrbit_sub_le` |
| **the relative-torus descent**: a common phase shift multiplies the orbit by a unimodular scalar, which the overlap score does not see | `radianOrbit_add_const`, `finitePureStateFidelity_radianOrbit_add_const` |
| **`(26)`**: with no return set excised, the capture event has mass at most the replica design budget | `measureReal_capture_le_replicaMoment` |
| **`(22)` produces a hard phase centre** | `exists_hard_phase_centre` |
| **`(29)`**: the centre carries a whole hard cube, with loss `2 rho` | `finitePureStateFidelity_lt_of_turnDist_le` |
| the trajectory phase, its relative centre, and the fact that a cube-visit time is a hard time | `flowPhase`, `relCentre`, `finitePureStateFidelity_flowPhase_lt` |
| **`(24)`** | `half_mul_le_measureReal_hardWindow` |
| **`(25)`** | `half_mul_le_measureReal_recurrenceWindow` |

`(26)` is not new mathematics here: it is the corpus's return-excised phase-incidence law
`measureReal_capture_le_return_add_replicaMoment` -- the card's declared parent input -- specialized
to the empty return set.  Its right-hand side is literally
`dim span{z^{otimes r}} * r! * (16 C_H(Omega)/a_0^2)^r`, with `h_r(Z) = finrank (replicaTargetSpan r z)`
and `C_H(Omega) = occupationCollision p`.  Since the torus box has Haar mass one, `(22)` makes the
capture event a proper subset, which is `exists_hard_phase_centre`.

The descent to the relative torus is done pointwise rather than measure-theoretically.  There is no
need to push `(26)` through the quotient: the hard centre is chosen in the full torus, and for a
time `t` whose *relative* phases lie in the cube around it, the explicit common shift
`s = theta_{*,0} - (psi_0 - t E_0)` moves the trajectory phase into the full-torus cube, and
`finitePureStateFidelity_radianOrbit_add_const` says the overlap score never saw `s`.  That reduces
the `j = 0` coordinate to `turnDist 0 = 0` and every other coordinate to
`turnDist(t omega_i - relCentre psi theta i)`, which is exactly membership in `cubeVisit`.

Both conclusions are stated for an algebraic spectrum, exactly as Theorem A is: real energies `E`
that are the distinguished embedding of algebraic integers with all conjugates below `R`, and no
integer relation among the anchored gaps.  The window length is the same `T` as in Theorem A, and
the occupation fraction is the same `mu_rho/2`, uniformly in the window position `u`.

## Theorem C -- ordinary integer two-local Hamiltonians

Fix `n>=2`, `D=2^n`, and `Omega=|0>^{tensor n}`.  There is an integer-coefficient traceless
two-local Pauli Hamiltonian

\[
 H_n=\sum_{1\le |S|\le2}\ \sum_{\alpha\in\{X,Y,Z\}^S}
 A_{S,\alpha}P_{S,\alpha},
 \qquad A_{S,\alpha}\in\mathbb Z,                       \tag{30}
\]

with all-to-all two-site supports allowed, such that:

1. its characteristic polynomial has Galois group `S_D` over `Q`;
2. `Omega` has nonzero overlap with every eigenvector; and
3. its spectral collision satisfies

\[
 C_{H_n}(\Omega)<4(2/3)^n.                               \tag{31}
\]

The sequence `H_n` may be selected by one terminating algorithm.

Now fix a finite dictionary of local gates.  Let `M_n>=2` bound the number of padded gate choices,
including locations, at one word position, and put `ell_n=ceil(log_2 M_n)`.  For
`0<epsilon<1/2`, define

\[
 a_0=1-4\epsilon^2,
 \quad a_1=1-\epsilon^2,
 \quad
 r_n=\left\lfloor{a_0^2\over128}(3/2)^n\right\rfloor,    \tag{32}
\]

and, whenever `r_n>=4ell_n`,

\[
 s_n=\left\lfloor{r_n\over4\ell_n}\right\rfloor-1,
 \qquad
 \rho_\epsilon={3\epsilon^2\over4}.                     \tag{33}
\]

Write `C_epsilon` for ancilla-free state-preparation complexity from `Omega`, up to projective
Euclidean error `epsilon`, over that dictionary.  With

\[
 R_n=\max(1,\|H_n\|_{\mathrm{op}})
 \le\max\left(1,\sum_{S,\alpha}|A_{S,\alpha}|\right),    \tag{34}
\]

every time window of the computable length

\[
 T_n^{\mathrm{hard}}=
 \mathcal T(2^n,R_n,\rho_\epsilon)                       \tag{35}
\]

obeys

\[
 \boxed{
 \left|\{t\in[u,u+T_n^{\mathrm{hard}}]:
 C_\epsilon(e^{-itH_n}\Omega)>s_n\}\right|
 \ge{1\over2}
 \left({\rho_\epsilon\over2\pi}\right)^{2^n-1}
 T_n^{\mathrm{hard}}}                                    \tag{36}
\]

for every `u>=0`.  In particular, one reaches approximate state complexity

\[
 s_n=\Omega\left({(3/2)^n\over\log M_n}\right)           \tag{37}
\]

by a finite computable deadline, and hard endpoints continue to occur with bounded gaps forever.

For every `0<delta<=1`, projective `delta`-returns to `Omega` also occur in every interval of the
computable length

\[
 T_n^{\mathrm{return}}(\delta)=
 \mathcal T(2^n,R_n,\delta),                              \tag{38}
\]

with the positive moving-window occupation supplied by `(25)`.

### Proof of Theorem C

#### 1. Simultaneous collision, cyclicity, and symmetric Galois group

Consider the real Gaussian ensemble containing every one-site and every two-site Pauli
orientation, with equal variance on each fixed support.  Product-local Clifford invariance and the
product-stabilizer second-moment identity give

\[
 \mathbb E_H C_H(\Omega)\le(2/3)^n.                       \tag{39}
\]

Consequently the set where `(31)` holds has positive measure.  Simple spectrum and cyclicity of
`Omega` are generic.  On the simple-spectrum locus collision is continuous, so there is a rational
open coefficient box `B` on which simplicity, cyclicity, and `(31)` all hold.

The generic characteristic polynomial of the full two-local Pauli family has Galois group `S_D`
over its rational-function field by `generic-two-local-spectral-monodromy`.  We need an `S_D`
rational specialization inside `B`, not merely somewhere in coefficient space.  The following
short quantitative Hilbert argument supplies it.

Write `B=prod_i(a_i,b_i)` with rational endpoints and make the birational substitution

\[
 T_i={a_i+b_iY_i\over1+Y_i}.                             \tag{40}
\]

Every positive integral `Y_i` maps into `B`, and `Q(T_1,...,T_m)=Q(Y_1,...,Y_m)`, so the generic
Galois group remains `S_D`.  After clearing denominators, Castillo--Dietmann's quantitative Hilbert
irreducibility theorem bounds specializations `Y in Z^m`, `||Y||_infty<=H`, whose Galois group is
a fixed proper subgroup `K<S_D` by

\[
 O_{f,\eta}(H^{m-1+[S_D:K]^{-1}+\eta}).                 \tag{41}
\]

There are finitely many subgroups of `S_D`, and every proper subgroup has index at least two.
Choose `eta<1/2`.  The union of all bad specializations, together with discriminant and
denominator zeros, is `o(H^m)`, whereas the positive box `{1,...,H}^m` contains `H^m` points.
For large `H` there is therefore a positive integral specialization with group `S_D`.  Its image
under `(40)` is a rational point of `B` satisfying all three required properties.

Clear the common denominators of its Pauli coefficients.  Scaling preserves eigenvectors,
collision, cyclicity, and the Galois group, and produces `(30)`.  Since Pauli matrices have entries
in the Gaussian integers and the scaled matrix is Hermitian, its monic characteristic polynomial
has coefficients in `Z`.

The `S_D` relation-rigidity argument shows that the only rational eigenvalue relation is the trace
relation.  Hence the `D-1` projective frequencies are rationally independent, as required by
Theorem A.

#### 2. The circuit union leaves a robust hard phase cell

Let `Z_(n,s_n)` be all outputs of words of length at most `s_n`.  Then

\[
 h_{r_n}(Z_{(n,s_n)})\le|Z_{(n,s_n)}|
 \le M_n^{s_n+1}\le2^{r_n/4}.                            \tag{42}
\]

By `(31)--(32)` and `r!<=r^r`,

\[
 r_n!\left({16C_{H_n}(\Omega)\over a_0^2}\right)^{r_n}
 <\left({64r_n(2/3)^n\over a_0^2}\right)^{r_n}
 \le2^{-r_n}.                                            \tag{43}
\]

Thus the left side of Theorem B's condition `(22)` is smaller than
`2^{-3r_n/4}<1`.

Apply Theorem B with `a_0=1-4epsilon^2` and `a_1=1-epsilon^2`.  If a target `z` projectively
approximates a unit state `psi` within `epsilon`, then

\[
 |\langle\psi,z\rangle|^2
 \ge(1-\epsilon^2/2)^2\ge1-\epsilon^2=a_1.              \tag{44}
\]

Therefore target avoidance at threshold `a_1` implies `C_epsilon>s_n`.  Equations `(24)` and
`(23)` now give `(35)--(36)`.  The recurrence claim is `(25)`.  QED.

#### 3. Uniform computability

Enumerate rational two-local Pauli coefficient vectors.  For each candidate, all required tests
are decidable:

- the characteristic polynomial and its Galois group are effective over `Q`;
- the Krylov determinant deciding cyclicity is rational;
- for a simple algebraic spectrum, the projectors

\[
 P_j=\prod_{k\ne j}{H-E_kI\over E_j-E_k}                 \tag{45}
\]

are algebraic, so the collision is a real algebraic number and comparison with `(31)` is
decidable.

The existence proof makes the search terminate for every `n`.  Clearing denominators then gives
`H_n`; `(3)--(4)` compute both window lengths from its integer coefficients.  This proves the
uniform-computability statement without performing a numerical search in the proof.

## Theorem D -- effective full-scale Choi/thermofield-double alternation

Use the same integer two-local Hamiltonian `H_n` from Theorem C.  On two `n`-qubit registers let

\[
 |\Phi_D\rangle={1\over\sqrt D}\sum_{x\in\{0,1\}^n}|x\rangle|x\rangle,
 \qquad
 |\Phi_{H_n}(t)\rangle=(e^{-itH_n}\otimes I)|\Phi_D\rangle. \tag{47}
\]

In an eigenbasis of `H_n`, basis independence of the maximally entangled vector gives

\[
 |\Phi_{H_n}(t)\rangle
 ={1\over\sqrt D}\sum_{j=1}^D e^{-itE_j}
       |e_j\rangle|\overline{e_j}\rangle.                \tag{48}
\]

Thus this trajectory has the same projective frequency vector as Theorems A--C and exactly uniform
spectral weights.

Let `Delta` be pure-state trace distance.  Fix

\[
 0<\delta_0<\delta_1<1/2,
 \qquad
 \eta_{\delta_1}=1-\sqrt{1-4\delta_1^2},                 \tag{49}
\]

and define

\[
 B_D(\delta_1)=D e^{D/2}
   \left({\pi\eta_{\delta_1}\over2}\right)^{(D-1)/2},
 \qquad
 \kappa_{\delta_1}=-{1\over2}
  -{1\over2}\log\left({\pi\eta_{\delta_1}\over2}\right). \tag{50}
\]

Assume `kappa_(delta_1)>0`.  For a finite local gate dictionary on the `2n` qubits, let `M_n>=2`
bound padded gate choices per word position.  Whenever

\[
 A_n=\kappa_{\delta_1}(D-1)-\log D-{1\over2}>0,          \tag{51}
\]

put

\[
 s_n^{\rm Choi}=
 \left\lfloor{A_n\over2\log M_n}\right\rfloor-1         \tag{52}
\]

and assume the displayed floor is at least one.  Then

\[
 s_n^{\rm Choi}=\Omega\left({2^n\over\log M_n}\right).  \tag{53}
\]

Set

\[
 \rho_{\rm Choi}=\delta_1-\delta_0,
 \qquad
 T_n^{\rm Choi}=\mathcal T(D,R_n,\rho_{\rm Choi}).       \tag{54}
\]

If `C_(delta_0)^(Phi)` denotes circuit complexity from the reference state `|Phi_D>` at trace error
`delta_0`, then every shifted window obeys

\[
 \boxed{
 \begin{aligned}
 &\left|\left\{t\in[u,u+T_n^{\rm Choi}]:
 C_{\delta_0}^{\Phi}(|\Phi_{H_n}(t)\rangle)>s_n^{\rm Choi}
 \right\}\right|\\
 &\hspace{35mm}\ge{1\over2}
 \left({\rho_{\rm Choi}\over2\pi}\right)^{D-1}
 T_n^{\rm Choi}
 \end{aligned}}                                         \tag{55}
\]

for every `u>=0`.

The reference `|Phi_D>` is a tensor product of `n` Bell pairs.  If the chosen dictionary has an
exact product-to-`|Phi_D>` preparation of cost `b_n`, then product-reference complexity of the same
endpoints is at least `s_n^(Choi)-b_n`.  For a standard dictionary containing a Bell-pair creator,
`b_n=O(n)`, so `(53)` is unchanged.

For any `0<delta_R<=1`, set

\[
 T_n^R=\mathcal T(D,R_n,\delta_R).                       \tag{56}
\]

Every interval of length `T_n^R` contains positive-measure projective `delta_R`-returns to
`|Phi_D>`.  In particular, partitioning time after any `u` into three consecutive blocks of lengths

\[
 T_n^R,\qquad T_n^{\rm Choi},\qquad T_n^R               \tag{57}
\]

gives times

\[
 u\le t_R<t_H<t_R'\le
 u+2T_n^R+T_n^{\rm Choi}                                \tag{58}
\]

at which the Choi orbit respectively returns within `delta_R`, has complexity greater than
`s_n^(Choi)` at error `delta_0`, and returns within `delta_R` again.  Each admissible set has positive
measure in its block, so the times can be chosen away from block endpoints and the inequalities are
strict.  The cycle can be restarted after `t_R'` and therefore repeats forever with an explicit
computable upper bound on every three-regime cycle.

### Proof of Theorem D

The universal Choi phase-target entropy law states that, for every normalized target `z`,
independently of the eigenbasis,

\[
 m\{\theta:\Delta(\Phi(\theta),z)\le\delta_1\}
 \le B_D(\delta_1).                                      \tag{59}
\]

Words of length at most `s` produce at most `M_n^(s+1)` targets, so

\[
 m\{\theta:C_{\delta_1}^{\Phi}(\Phi(\theta))\le s\}
 \le M_n^{s+1}B_D(\delta_1).                             \tag{60}
\]

The logarithm of the right side is

\[
 (s+1)\log M_n+\log D+{1\over2}
       -\kappa_{\delta_1}(D-1).                          \tag{61}
\]

Equations `(51)--(52)` make `(61)` at most `-A_n/2<0`.  Therefore the circuit
`delta_1`-balls do not cover the relative phase torus.  Choose a centre `theta_*` outside their
union.

If `dist_infty(theta,theta_*)<rho_Choi`, the corresponding normalized Choi vectors differ in
Euclidean norm by at most `rho_Choi`; their pure-state trace distance is no larger.  Were
`Phi(theta)` within trace distance `delta_0` of one circuit target, the triangle inequality would
place the centre within

\[
 \delta_0+\rho_{\rm Choi}=\delta_1                      \tag{62}
\]

of the same target, a contradiction.  The phase cube is thus uniformly hard at error `delta_0`.
Theorem A gives `(55)`.

The return statement follows by applying Theorem A to the relative-origin cube of radius
`delta_R`, exactly as in Theorem B.  Apply that return law to the first and third blocks in `(57)`
and the hard law to the middle block.  This proves `(58)` and the repeatable explicit alternation.
QED.

### Exact relation to the prior Choi theorem

`universal-static-choi-complexity-plateau` already proves:

1. completed-time complexity `Omega(D/log M)` for almost every maximally projective static
   Hamiltonian;
2. qualitative syndetic hard endpoints; and
3. ordered recurrence--hardness--recurrence alternation.

It explicitly leaves the syndeticity constant `L` and every quantitative alternation gap open.
Theorem D does not reclaim those qualitative conclusions as new.  It supplies their first explicit
computable `L` for an algorithmically selected static two-local integer Hamiltonian and strengthens
mere hits to positive occupation in every such window.

## Conjecture--failure--repair log

### C0. Bandwidth plus projective rank bounds first plateau entry

**Conjecture.** Fixed dimension, bounded operator norm, and maximal projective rational rank give a
uniform phase-filling deadline.

**Verdict:** `[FALSE]`.  Rational independence is qualitative.  Frequencies may approach a
rational hyperplane arbitrarily closely while the operator norm stays bounded, making the filling
time arbitrarily large.

### C1. Minimum spectral-gap anti-concentration is enough

**Conjecture.** A lower bound on all pairwise energy gaps controls phase filling.

**Verdict:** `[FALSE]`.  The frequency vector `(1,2+eta)` has pairwise energy gaps at least one in
the spectrum `{0,1,2+eta}`, but the bounded action `2omega_1-omega_2=-eta` is arbitrarily small.
This independently confirms that the previously retired minimum-gap invariant is structurally
wrong.

### C2. Truncated spectral action is the correct finite invariant

**Conjecture.** If

\[
 \Delta_N=\min_{0<\|k\|_\infty\le N}|k\cdot\omega|>0.    \tag{63}
\]

then a degree-`N` Fejer detector forces every robust phase cell to be occupied in every window of
length `O((2N+1)^d/Delta_N)`.

**Verdict:** `[PROVED]` in Theorem A, Steps 2--3.  Abstract quantitative torus filling is known;
the proof is included to close dependencies and preserve explicit constants.

### C3. Finite integer description supplies the missing action bound

**Conjecture.** Algebraic integrality and maximal projective rank force an explicit lower bound on
`Delta_N` from dimension and spectral height alone.

**Verdict:** `[PROVED]` in `(6)--(9)`.  The field norm gives exponent `D!-1`.

### C4. A collision-good local Hamiltonian can simultaneously be arithmetic-generic

**Conjecture.** One can choose a rational full-two-local Hamiltonian inside the open
collision-good, cyclic locus while retaining generic `S_D` spectral Galois group.

**First attempt:** Zariski density alone.  **Verdict:** `[INSUFFICIENT ARGUMENT]`; Zariski density
does not by itself state the required Euclidean local specialization.

**Repair:** Map the positive integral orthant birationally into the open box and use quantitative
Hilbert irreducibility.  **Verdict:** `[PROVED]` in `(40)--(41)`.

### C5. The arithmetic clock quantifies Choi hardness--recurrence alternation

**Conjecture.** Applying Theorem A to the equal-weight Choi orbit turns the prior qualitative
syndeticity theorem into an explicit moving-window law at the full spectral-phase complexity scale.

**Verdict:** `[PROVED]` in Theorem D.  It gives positive hard occupation in every window, explicit
return windows, and an explicit repeatable recurrence--hardness--recurrence cycle.  The qualitative
syndeticity and alternation were already known in the corpus and are not reclaimed as new.

### C6. The algebraic deadline has Brown--Susskind scale

**Conjecture.** The resulting deadline is exponential in Hilbert-space dimension.

**Verdict:** `[NOT PROVED; CURRENT BOUND FAR WORSE]`.  A generic bounded action can have a full
`S_D` orbit, so the norm argument naturally pays degree up to `D!`.  The theorem proves effective
entry and bounded gaps, not the conjectured physical scale, linear ramp, or ramp ordering.

## Novelty and literature audit

1. Dumas--Fischler, *Filling times for linear flow on the torus with truncated Diophantine
   conditions* (arXiv:2112.11786), reviews and proves sharper abstract filling estimates.  Torus
   filling itself is therefore **not** claimed as new.
2. Castillo--Dietmann, *On Hilbert's irreducibility theorem* (arXiv:1602.00314), supplies `(41)`.
   Arithmetic specialization itself is not new.
3. Jia--Wolf, *Hay from the haystack* (arXiv:2205.06977), constructs constant-description families
   with exponential exact complexity and proves approximate hardness for most family members.  It
   does not give the autonomous orbit/window theorem above.
4. Haferkamp et al., *Linear growth of quantum circuit complexity* (Nature Physics 2022), proves
   linear growth for random circuits, explicitly distinguishing those circuits from ordinary
   time-independent Hamiltonian dynamics.
5. Bohdanowicz--Brandao, *Universal Hamiltonians for exponentially long simulation*
   (arXiv:1710.02625), obtains steady static-local complexity growth under computational-complexity
   assumptions.  The present theorem is unconditional but much weaker in time scaling and growth
   shape.

The exact novelty candidate is the composition: one algorithmically selectable ordinary static
two-local integer Hamiltonian, an explicit arithmetic bound on the previously nonquantitative
syndeticity constant, full spectral-phase-scale robust Choi/thermofield-double complexity, and explicit positive
occupation in every sufficiently long window, together with effective ordered recurrence windows.
The product-input theorem is a second, weaker corollary.  No matching theorem was located in
targeted title/abstract/concept searches.  This is not yet a priority certification.

## Hostile review

### What survives

1. **Unconditional:** no ETH, chaos, random-matrix, complexity-class, or thermodynamic-limit
   assumption occurs in Theorems A--C.
2. **Quenched:** one Hamiltonian is selected and then held fixed forever.
3. **Approximate:** `(36)` excludes the complete finite circuit union at fixed positive error.
4. **Effective:** after the integer coefficients are selected, the window horizons are explicit and
   computable.
5. **Persistent:** the conclusion holds in every shifted window, not only along a sparse sequence.
6. **Recurrence included:** hard windows and return windows are two consequences of the same
   arithmetic phase law.
7. **Full spectral-phase scale:** the Choi/thermofield-double complexity lower bound is
   `Omega(2^n/log M_n)`, matching the dimension of its `2^n-1` phase torus up to logarithmic
   factors.

### What a hostile general-journal reviewer must reject if overstated

1. The bound `(4)` is astronomically larger than the Brown--Susskind time scale; it has a `D!`
   exponent and a phase-volume penalty.
2. The theorem does not show monotone or linear growth, the first local maximum, maximal
   complexity, plateau duration at physical scale, or the expected recurrence scale.
3. The `Omega(2^n/log n)` conclusion is full scale for the `2^n-1`-dimensional spectral-phase
   orbit, not for arbitrary states on `2n` qubits, whose ambient state space is much larger.  The
   fixed-product-input theorem reaches only `Omega((3/2)^n/log n)`.
4. Hamiltonians are two-local in interaction order but all-to-all; geometric finite-range remains
   open for the arithmetic specialization used here.
5. The selected integer couplings have no useful uniform height bound in `n`; the construction is
   computable, not experimentally feasible.
6. The result concerns state complexity over a fixed finite dictionary, not basis-independent
   unitary complexity.
7. Abstract torus filling and Hilbert specialization are known.  Publication novelty rests on the
   static-local approximate-complexity composition and requires an external specialist priority
   audit.

**Programme verdict:** genuine frontier movement from non-effective existence to effective
moving-window occupation, but not yet the full Brown--Susskind growth--plateau--recurrence law and
not yet sufficient for the master paper's Nature-level claim.

## Formal status

Theorems A and B are Lean-closed and axiom-clean.  What remains is the *existence* half of Theorem C
-- the selection of an integer two-local Pauli Hamiltonian with symmetric Galois group, cyclic
initial state and small collision -- and Theorem D, which reuses it.  That step rests on
Castillo--Dietmann's quantitative Hilbert irreducibility theorem `(41)` together with the parent card
`generic-two-local-spectral-monodromy`; neither is in mathlib or in this corpus.  Everything in
Theorem C downstream of that selection (`(42)`--`(44)` and the application of `(24)`--`(25)`) is
elementary and consumes only what is already formal.

The original plan for the split was:

1. algebraic-integer field-norm spectral-action bound;
2. product-Fejer moving-window lemma;
3. robust phase-cell transfer;
4. quantitative-Hilbert specialization bridge; and
5. circuit-window corollary.

## Theorem C's selection: the exact missing theorem, and a route to it (2026-08-22)

The "Formal status" note above is stale in one respect: **Hilbert irreducibility is now Lean-closed**
(`HTGeometry.HilbertIrreducibility.hilbert_irreducibility`, and the Galois-preserving multivariate
form `gal_card_of_specialisation`, both unconditional and axiom-clean).  What Theorem C's selection
still lacks is that theorem's *hypothesis*: `Nat.card Gal = D!` for the generic two-local
characteristic polynomial over `ℚ(Y)`.  The parent card `generic-two-local-spectral-monodromy` is
fully formalized but concludes about **balanced integer** relations, from *topological* monodromy;
"geometric monodromy ⟹ Galois group" is Riemann existence and is not formalized.

An elementary route that avoids Riemann existence entirely -- single-transverse block
decomposition, Kummer independence of the block discriminants over `ℚ(i)`, and transport to the
full family by a field embedding `ℚ(i)(Y) ↪ Frac(F[[t]])` rather than a specialisation -- is
written out in full in the sibling card
`./algebraic-two-local-instant-exact-complexity.md`, section "§1's missing bridge".  The first
brick is built: `HTGeometry/SquareInQuadraticExtension.lean`
(`isSquare_or_isSquare_mul_of_isSquare_algebraMap`, `not_isSquare_algebraMap`), axiom-clean and
wired.

Note also that Castillo--Dietmann's *quantitative* Hilbert irreducibility is only needed for an
explicit height bound on the selected coefficients; the card's Theorem C as stated needs only the
*existence* of an integer two-local Pauli Hamiltonian with symmetric Galois group, cyclic initial
state and small collision, which `gal_card_of_specialisation` supplies once its hypothesis is in
place (its avoidance polynomial `g` absorbs the discriminant, the cyclicity determinant and the
collision condition simultaneously).

## Theorem C's Galois hypothesis is now Lean; the residue is an *open-box* Hilbert theorem (2026-08-22)

The "Formal status" and the 2026-08-22 note above are both stale.  The sibling card
`../3-formalized/algebraic-two-local-instant-exact-complexity.md` is closed at stage 3, and with it:

| Theorem C clause | Status |
|---|---|
| `S_D` Galois group of an *integer two-local* characteristic polynomial | **Lean** — `TwoLocalWitness.exists_integer_twoLocal_symmetric_gal` |
| `Ω` has nonzero overlap with every eigenvector (cyclicity) | **Lean** — irreducibility of the characteristic polynomial makes *every* nonzero rational vector cyclic (`SymmetricGaloisCyclicity.linearIndependent_krylov_of_irreducible`), and `AlgebraicOrbit.finiteComplexInner_ne_zero_of_linearIndependent` turns that into nonvanishing overlaps |
| the only rational eigenvalue relation is the trace relation, hence `(1)`'s rational independence of the projective frequencies | **Lean** — `ker_relationForm_eq_constLine_of_gal` |
| tracelessness `(30)` | **Lean** — `trace_witnessHam` |
| the collision bound `(31)`, `C_{H_n}(Ω) < 4(2/3)^n` | **open** |
| `(42)`–`(44)` and the application of `(24)`–`(25)` | elementary, consumes only what is already formal |

### The one remaining crux, stated exactly

`(31)` is an **open** condition on the coefficients, not a Zariski-open one: the collision is a
continuous function of the Hamiltonian on the simple-spectrum locus, but it is not a polynomial.
Hilbert irreducibility as the corpus has it (`hilbert_multivariate`, `gal_card_of_specialisation`)
delivers a rational specialisation avoiding the zero locus of any prescribed nonzero *polynomial*,
which cannot express `(31)`.  What Theorem C needs is the version the card's own proof uses at
`(40)`: a specialisation **inside a prescribed rational box**.

### Why this is within reach, and exactly how

Reading the corpus's Hilbert core, the good rational specialisations it produces are
`b = s₀ + 1/t` with `t` an arbitrarily large integer (`Main.infinite_of_thin_bad`), i.e. they
accumulate at one integer `s₀` from above.  `s₀` is produced by `exists_regular_int`, which only
needs `s₀` to avoid the finitely many roots of one nonzero polynomial (`exists_int_not_root`).
So:

1. **`exists_int_not_root_gt`** — a nonzero polynomial has finitely many roots, so for every `N`
   there is an integer `> N` that is not a root.  Propagating it gives `exists_regular_int_ge` and
   hence *good rational specialisations larger than any prescribed bound*.
2. **The Möbius substitution `(40)`**, `T = (a + bY)/(1+Y)`, maps `Y > 0` into `(a,b)` and is
   birational, so `ℚ(T) = ℚ(Y)` and the Galois group is unchanged.  Combining 1 and 2 gives
   Hilbert irreducibility **with the specialisation in any prescribed rational box**.
3. The multivariate recursion (`SeveralVariables.hilbert_several`) must carry the same bound
   coordinatewise; it chooses one coordinate at a time, so the same strengthening applies.

### The second half: producing the box

The Gaussian-ensemble half of `(39)` is *already* Lean and unconditional:
`PauliEnsembleSimpleSpectrum.integral_collision_pauliEnsemble_zeroProductState_le` (mean collision
`≤ (2/3)^n` at the all-zero product state) and
`measureReal_collision_pauliEnsemble_zeroProductState_ge_le` (its Markov form, so the set where
`C_H(Ω) < 4(2/3)^n` has measure at least `3/4`).  Simple spectrum is almost sure
(`isOrthoEigenBasis_injective_pauliEnsemble_ae`).  What has to be added is that the set
`{J : simple spectrum ∧ C < 4(2/3)^n}` is **open** — the collision is continuous there because the
gauge-invariant cross-weight is (`LagrangeSpectralProjector.continuousAt_spectralCrossWeight`),
given continuity of the eigenvalues along the path — and a nonempty open set contains a rational
box.

### Why the *generic* Galois group of the full two-local Pauli family is not an extra obstacle

Theorem C's Hamiltonian ranges over all two-local Pauli coefficients, whereas the Lean `S_D` result
is for the sub-family `∑ a_i Z_i + ∑ b_{ij} Z_iZ_j + ∑ u_i X_i`.  The passage is the **easy**
direction of specialisation, not the hard one: `card Gal = D!` is equivalent to irreducibility of
one resolvent (`GaloisSpecialization.gal_card_of_irreducible_resolvent`,
`exists_irreducible_resolvent`), the resolvent commutes with the coefficient specialisation
(`resolvent_map`), and *irreducible after specialisation ⟹ irreducible before* is
`Polynomial.Monic.irreducible_of_irreducible_map` plus Gauss's lemma for the monic (hence
primitive) resolvent.  So the sub-family's `S_D` transfers upward to the full family for free.

### An alternative that avoids the ensemble entirely

Collision is scale invariant, so for the corpus's own witness family
`H(R) = D + R·∑_i w_i X_i` one has `C_{H(R)}(Ω) = C_{D/R + ∑ w_i X_i}(Ω) → C_{∑ w_i X_i}(Ω)`.  The
limit is exactly `2^{-n}`, because the eigenvectors of `∑ w_i X_i` are the `2^n` product states
`|±⟩^{⊗n}`, each overlapping `|0⟩^{⊗n}` with modulus `2^{-n/2}`; and its spectrum `∑ ± w_i` is
simple for `w_i = 3^i` by the same signed-digit argument that gives `witnessDiagonal_injective`.
That replaces `(39)` by an explicit computation, at the cost of eigenvalue continuity along a
one-parameter path — and it needs Hilbert irreducibility with `R` **large**, which is item 1 above
in one variable only.

### Sharper form of the missing Hilbert statement (same day, corrected)

The box is *not* the right primitive.  What the corpus's Hilbert core actually produces is
`b = s₀ + 1/t` with `t` arbitrarily large, so the good set is contained in `(s₀, s₀+1)` for one
integer `s₀` chosen only to avoid the roots of one nonzero polynomial.  Strengthening
`exists_int_not_root` to "there is a non-root **greater than any prescribed `N`**" therefore makes
the good set **unbounded above**, and that single strengthening is enough:

> **Möbius at a chosen centre.**  For any rational `r` and any `N`, apply the unbounded form to the
> cleared substitution `Y ↦ F(r + 1/Y)`.  Its good points satisfy `Y > N`, so the corresponding
> specialisations `T = r + 1/Y` of `F` lie in `(r, r + 1/N)` — an arbitrarily small interval around
> an arbitrarily chosen rational centre.

A box `∏ (a_i, b_i)` is then reached by centring at `r_i = (a_i + b_i)/2` and taking
`N > 2/(b_i - a_i)`.  No quantitative Hilbert irreducibility (Castillo–Dietmann) is needed: only
the *qualitative* theorem with an unbounded good set.

### Ordered plan for the remaining work

1. `exists_int_not_root_gt` — a nonzero complex polynomial has a non-root integer above any bound.
2. `exists_regular_int_gt`, `exists_regular_int_family_gt` — immediate consequences.
3. `infinite_gt_of_thin_bad` — the assembly, with the extra conjunct `s₀ < b` in the good set.
4. `hilbert_irreducibility_int_gt`, `hilbert_irreducibility_gt`,
   `hilbert_irreducibility_int_family_gt`, `hilbert_irreducibility_family_gt`.
5. `exists_infinite_specialisation_gt` (`Multivariate`) and `hilbert_several_gt`
   (`SeveralVariables`) — the two long proofs, each a copy of the existing one carrying the extra
   conjunct through `Set.Infinite.mono` and through the choice of `c` at each recursion step.
6. `hilbert_multivariate_gt`, `gal_card_of_specialisation_gt`.
7. The Möbius layer: cleared substitution `T_i = r_i + 1/Y_i` on a multivariate coefficient ring,
   with the induced isomorphism `ℚ(T) ≅ ℚ(Y)` so the generic Galois group is unchanged.
8. The collision box: `{J : simple spectrum ∧ C_J(Ω) < 4(2/3)^n}` is open (continuity of the
   gauge-invariant cross-weight plus continuity of the eigenvalues) and has measure `≥ 3/4`, hence
   contains a rational box.
9. Transfer of `S_D` from the corpus's sub-family to the full two-local Pauli family through the
   *easy* direction of specialisation on the resolvent.
10. Theorem D, which reuses the selected Hamiltonian and is otherwise elementary.

### Items 1–6 are DONE (2026-08-22, same session)

`formal/GaloisForLFunctions/HTGeometry/HilbertIrreducibility/LargeSpecialisation.lean` (new,
umbrella-wired, axiom-clean, olean built):

| Item | Declaration |
|---|---|
| 1 | `exists_int_not_root_gt` |
| 2 | `exists_regular_int_gt`, `exists_regular_int_family_gt` |
| 3 | `infinite_gt_of_thin_bad` |
| 4 | `hilbert_irreducibility_int_gt`, `hilbert_irreducibility_gt`, `hilbert_irreducibility_int_family_gt`, `hilbert_irreducibility_family_gt` |
| 5 | `exists_infinite_specialisation_gt`, `hilbert_several_gt` |
| 6 | `hilbert_multivariate_gt`, **`gal_card_of_specialisation_gt`** |

```text
gal_card_of_specialisation_gt (N : ℤ) {m D : ℕ} {f : Polynomial (MvPolynomial (Fin m) ℚ)}
    (hf : f.Monic) (hfdeg : f.natDegree = D) (hsep : …) (hgal : … = D.factorial)
    {g : MvPolynomial (Fin m) ℚ} (hg : g ≠ 0) :
  ∃ y : Fin m → ℚ, (∀ i, ((N : ℤ) : ℚ) < y i) ∧ MvPolynomial.eval y g ≠ 0 ∧
    Nat.card (f.map (MvPolynomial.eval y)).Gal = D.factorial
```

So the Galois-preserving specialisation may now be demanded **arbitrarily large in every
coordinate**, on top of avoiding any prescribed nonzero polynomial.  Items 3–6 were obtained by
carrying the extra conjunct `s₀ < b` through the existing proofs verbatim; the only mathematical
change is item 1.

### What item 7 has to build, precisely

Largeness alone is *not* enough for `(31)`: with all `u_i > N` but arbitrary ratios the transverse
part can be degenerate (`u = (N,…,N)` gives `∑_i u_i X_i = N ∑_i X_i`, whose eigenvectors inside a
Hamming sector can overlap `Ω` by as much as `√(C(n,k))·2^{-n/2}`, so the collision is only
`O(1/√n)`).  The box is therefore genuinely needed, and it is obtained from item 6 by the
substitution `Y_i = r_i + 1/Z_i`:

1. the ring isomorphism `Frac(ℚ[Y]) ≅ Frac(ℚ[Z])`, `Y_i ↦ r_i + 1/Z_i`, an involution with inverse
   `Z_i ↦ (Y_i − r_i)⁻¹`, built by `IsFractionRing.lift` of `MvPolynomial.aeval` in both
   directions and `RingEquiv.ofHomInv`;
2. clearing denominators *monically* by the root-scaling trick: with `M` the largest `Z`-pole order
   among the coefficients `c_k(Y)` of `f`, the polynomial
   `f̃(X) := Z^{MD}·f(r + 1/Z, X/Z^M)` has coefficients `Z^{Mk}c_k(r+1/Z) ∈ ℚ[Z]` and is monic;
3. the Galois group is unchanged, by the isomorphism in 1 and by
   `CharpolyScaleGalois.card_gal_comp_scale` for the root scaling in 2;
4. applying `gal_card_of_specialisation_gt` with `N > 2/(b_i − a_i)` then puts
   `Y_i = r_i + 1/z_i ∈ (r_i, r_i + 1/N)` inside the box.
