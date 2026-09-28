# Fourier-kernel admission reconstruction and contact-localization law

- **ID:** `ulf-grm-fourier-kernel-admission`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CLASSICAL BOCHNER/RADON--NIKODYM PARENTS]`
  `[CANONICAL OBSERVER GENERATION] [EXACT CONSERVATION] [FOURTH-ORGAN PREDICTION]`
  `[FINITE CORE LEAN-CERTIFIED] [ANALYTIC LIMIT PAPER-LEVEL] [NOT RH]`
- **Statement:** A signed measure intervention, its complete phase response, its positive-definite
  kernel pencil, and its spectral contact profiles determine one another. The least positive
  compensator is exactly the worst generalized Rayleigh defect over finite phase packets.

## 1. Why this theorem is needed

The existing joint-admission theorem proves exact fusion after a jointly cone-reflecting positive
observer family is supplied. That hypothesis is too permissive to be a generative field law: one
could fit coordinate observers to the source cone.

For measure-valued sources, phase response removes that choice. Characters generate a canonical
family of positive quadratic tests. The same family:

1. reconstructs the signed intervention by Fourier uniqueness;
2. reconstructs positivity by the Bochner order;
3. computes the exact source admission gauge by a generalized eigenvalue;
4. generates the low-energy contact/escape profiles of the critical kernel pencil.

Thus this card strengthens
`jointly-conservative-admission-descent-and-migrating-obstruction-law.md`: joint conservativity is
proved for a canonical atlas rather than assumed.

## 2. Setup

Let `mu` be a nonzero finite positive Borel measure on `R`, and let `eta` be a finite real signed
Borel measure. For any finite signed measure `nu`, write

\[
 \widehat\nu(t)=\int_{\mathbb R}e^{-itx}\,d\nu(x).
 \tag{FKA.1}
\]

For a finite phase packet `t=(t_1,...,t_m)` and coefficients `z in C^m`, put

\[
 p_{t,z}(x)=\sum_{j=1}^m z_je^{-it_jx},
 \qquad
 Q_\nu(t,z)=\sum_{j,k=1}^m\overline{z_j}z_k
                  \widehat\nu(t_k-t_j).
 \tag{FKA.2}
\]

Define the positive compensation/admission gauge

\[
 \kappa_\mu(\eta)=\inf\{c\ge0:\eta+c\mu\ge0\}\in[0,+\infty].
 \tag{FKA.3}
\]

For a packet with `Q_mu(t,z)>0`, define its defect threshold

\[
 r_{t,z}(\eta\mid\mu)
 =\left(-\frac{Q_\eta(t,z)}{Q_\mu(t,z)}\right)_+.
 \tag{FKA.4}
\]

If `Q_mu(t,z)=0` and `Q_eta(t,z)<0`, declare the threshold to be `+infinity`; if both clauses do
not hold, declare it zero.

## 3. Fourier quadratic identity and positivity reconstruction

### Theorem 3.1

For every finite packet,

\[
 \boxed{Q_\nu(t,z)=\int_{\mathbb R}|p_{t,z}(x)|^2\,d\nu(x).}
 \tag{FKA.5}
\]

Consequently

\[
 \boxed{\nu\ge0\quad\Longleftrightarrow\quad
 Q_\nu(t,z)\ge0\text{ for every finite phase packet}.}
 \tag{FKA.6}
\]

The family of matrices

\[
 K_\nu(t_1,...,t_m)
 =\bigl(\widehat\nu(t_k-t_j)\bigr)_{j,k}
 \tag{FKA.7}
\]

also reconstructs `nu` uniquely.

### Proof

Expanding `|p_(t,z)|^2` and interchanging a finite sum with the integral gives `(FKA.5)`.
Positivity of `nu` implies all quadratic forms are nonnegative.

Conversely, nonnegativity of every packet says that the continuous function `hat nu` is positive
definite. Bochner's theorem supplies a finite positive measure `nu_+` with Fourier transform
`hat nu`. Fourier uniqueness for finite measures gives `nu=nu_+`. This proves `(FKA.6)`.

Taking the two-time packets `(0,t)` reads `hat nu(t)` as an off-diagonal matrix coefficient.
Hence the kernel family reconstructs the complete Fourier transform, and Fourier uniqueness
reconstructs `nu`. QED.

## 4. Exact fusion and conservation identity

### Theorem 4.1 — phase-kernel admission conservation

One has the exact identity

\[
 \boxed{
 \kappa_\mu(\eta)
 =\sup_{m,t,z} r_{t,z}(\eta\mid\mu).}
 \tag{FKA.8}
\]

Equivalently, `kappa_mu(eta)` is the least `c>=0` for which every finite Hermitian pencil

\[
 \boxed{K_\eta(t_1,...,t_m)+cK_\mu(t_1,...,t_m)}
 \tag{FKA.9}
\]

is positive semidefinite.

If `eta^-` is the negative Jordan part of `eta`, then

\[
 \boxed{
 \kappa_\mu(\eta)<\infty
 \Longleftrightarrow
 \eta^-\ll\mu\text{ with }\frac{d\eta^-}{d\mu}\in L^\infty(\mu),
 \qquad
 \kappa_\mu(\eta)=\left\|\frac{d\eta^-}{d\mu}\right\|_\infty.}
 \tag{FKA.10}
\]

### Proof

For fixed `c>=0`, Theorem 3.1 gives

\[
 \eta+c\mu\ge0
 \Longleftrightarrow
 Q_\eta(t,z)+cQ_\mu(t,z)\ge0
 \quad\text{for every }(t,z).
 \tag{FKA.11}
\]

When `Q_mu>0`, this is precisely `c>=-Q_eta/Q_mu` whenever the right side is positive. When
`Q_mu=0` and `Q_eta<0`, no finite `c` is feasible. Taking the least common upper bound over all
packets proves `(FKA.8)` and `(FKA.9)`, including the infinite case.

Let `N` support the negative Jordan part and be disjoint from a support of `eta^+`. On `N`,
positivity of `eta+c mu` is exactly `eta^- <= c mu`; outside `N` this domination is sufficient.
The Radon--Nikodym theorem identifies the least such `c` with the essential supremum in
`(FKA.10)`. QED.

## 5. Cofinal finite-matrix reconstruction

Enumerate `Q` as `(q_n)_(n>=0)` with `q_0=0`. Let

\[
 \mathcal P_N=\operatorname{span}\{e^{-iq_0x},...,e^{-iq_Nx}\}
 \tag{FKA.12}
\]

and let `kappa_N` be the worst threshold `(FKA.4)` among packets in `P_N`.

### Theorem 5.1

\[
 \boxed{\kappa_N\uparrow\kappa_\mu(\eta).}
 \tag{FKA.13}
\]

Thus the full source gauge is the monotone limit of generalized negative eigenvalues of one
canonical nested sequence of finite phase-kernel pencils.

### Proof

Monotonicity follows from `P_N subset P_(N+1)`. If `eta+c mu` is nonnegative, every rational
packet pencil is positive. Conversely, positivity on every rational packet makes `hat eta+c hat
mu` positive definite on the dense subgroup `Q`. Continuity extends positive definiteness to
`R`; Theorem 3.1 gives `eta+c mu>=0`. Hence the feasible `c`-sets have the same intersection, which
proves `(FKA.13)`. QED.

## 6. Fourth-organ theorem: spectral contact localization

Assume now `eta=h mu`, where `h` is real, integrable, and bounded below. Put

\[
 \alpha=\operatorname*{ess\,inf}_\mu h.
 \tag{FKA.14}
\]

The rational phase polynomials are dense in `L^2((1+|h|)mu)`: if a vector is orthogonal to every
`e^(-iqx)`, its finite weighted measure has a continuous Fourier transform vanishing on the dense
set `Q`, hence vanishing everywhere, and Fourier uniqueness kills the vector.

### Theorem 6.1 — ground energy and contact profiles

\[
 \boxed{
 \inf_{0\ne p\in\bigcup_N\mathcal P_N}
 \frac{\int h|p|^2\,d\mu}{\int|p|^2\,d\mu}
 =\alpha.}
 \tag{FKA.15}
\]

If `alpha<0`, then `kappa_mu(eta)=-alpha`. For every normalized phase-polynomial sequence with

\[
 \int h|p_n|^2\,d\mu\longrightarrow\alpha,
 \tag{FKA.16}
\]

and every `delta>0`,

\[
 \boxed{
 \int_{\{h\ge\alpha+\delta\}}|p_n|^2\,d\mu\longrightarrow0.}
 \tag{FKA.17}
\]

Conversely, for every `delta>0`, phase polynomials can approximate a normalized indicator of
`{h<alpha+delta}` and therefore produce a Rayleigh quotient below `alpha+2 delta`.

### Proof

The lower bound in `(FKA.15)` is immediate from `h>=alpha` almost everywhere. By the definition of
essential infimum, `A_delta={h<alpha+delta}` has positive measure. Approximate its normalized
indicator in `L^2((1+|h|)mu)` by rational phase polynomials. Both the denominator and weighted
quadratic numerator converge, proving the reverse bound.

For a normalized minimizing sequence,

\[
 \int(h-\alpha)|p_n|^2\,d\mu\longrightarrow0.
\]

On `{h>=alpha+delta}` the integrand is at least `delta|p_n|^2`; Markov's inequality gives
`(FKA.17)`. The same weighted approximation proves the converse statement. QED.

This is the promised theorem in a fourth, whole-space spectral/coercivity organ. The low-energy
profiles are not arbitrary test vectors: the phase kernel forces them to concentrate on the
source contact set where the negative-density gauge is saturated.

## 7. The fused grammar

The theorem now links four structurally different organs by proved maps:

\[
\boxed{
\begin{array}{c}
\text{signed source intervention }\eta\\
\downarrow\ \text{Fourier transform}\quad\downarrow\ \text{quadratic pushforward}\\
\text{phase history }\widehat\eta
\longrightarrow
\text{positive kernel pencil }K_\eta+cK_\mu\\
\downarrow\ \text{extremal eigenvalue}\\
\text{admission gauge }\kappa_\mu(\eta)
\longrightarrow
\text{spectral contact/escape profiles.}
\end{array}}
\tag{FKA.18}
\]

The conservation identity is `(FKA.8)`. It is stronger than generic data processing: no observer
family is selected after seeing the cone, and no source coordinate is discarded.

## 8. Arithmetic reflection prediction and exact RH boundary

Let `mu` be any finite positive measure supported on `[0,+infinity)` whose essential support is
unbounded above, meaning `mu((R,+infinity))>0` for every `R`. Fix `a in R` for which
`int e^(2|a|x) dmu(x)<infinity`, and define the reflected exponential scores

\[
 h_a(x)=e^{2ax}-1,
 \qquad \eta_a=h_a\mu.
 \tag{FKA.19}
\]

### Corollary 8.1 — reflection-tension phase transition

\[
 \boxed{
 \bigl(\kappa_\mu(\eta_a),\kappa_\mu(\eta_{-a})\bigr)
 =\begin{cases}
 (0,1),&a>0,\\
 (0,0),&a=0,\\
 (1,0),&a<0.
 \end{cases}}
 \tag{FKA.20}
\]

Hence

\[
 \boxed{\Theta_\mu(a):=max\{\kappa_\mu(\eta_a),
 \kappa_\mu(\eta_{-a})\}=\mathbf 1_{a\ne0}.}
 \tag{FKA.21}
\]

For `a>0`, the critical reflected pencil has density

\[
 h_{-a}+1=e^{-2ax}.
 \tag{FKA.22}
\]

It has ground energy zero but no finite-support contact point. Every normalized minimizing phase
sequence escapes to `+infinity`: for every real `R`,

\[
 \boxed{\int_{(-\infty,R]}|p_n|^2\,d\mu\longrightarrow0.}
 \tag{FKA.23}
\]

The analogous escape is reflected when `a<0` and the support is unbounded in that direction.

### Proof

If `a>0`, `h_a>=0`, so its gauge is zero. The essential infimum of `h_(-a)` is `-1` because the
support is unbounded above; `(FKA.10)` gives gauge one. The other signs and `a=0` are immediate.
This proves `(FKA.20)`--`(FKA.21)`.

For `(FKA.23)`, the critical quadratic energy is `int e^(-2ax)|p_n|^2 dmu`. On `(-infinity,R]`
the density is at least `e^(-2aR)`, so the mass of that set is at most `e^(2aR)` times the energy,
which tends to zero. Existence of a minimizing phase sequence follows from Theorem 6.1. QED.

For an Xi divisor parameter, `a=Re(rho)-1/2`; therefore zero reflection tension is equivalent to
the critical-line condition. This is an exact selection **receiver**, reconstructed entirely from
phase-kernel order. It is not yet a proof of RH. The missing producer is now sharply typed:

\[
 \boxed{\text{derive }\Theta_\mu(a_\rho)=0\text{ for every Xi divisor point from one pre-divisor
 source law.}}
 \tag{FKA.24}
\]

Neither functional-equation reflection nor simultaneous finite gauge proves `(FKA.24)`:
off-center points have finite gauges `(0,1)` or `(1,0)`. A valid producer must force **zero**
two-orientation tension, not merely reflected existence, finite compensation, or tempered entry.

## 9. Hostile boundaries

1. **Bochner/Radon--Nikodym machinery is classical.** Correct. Field content is their forced
   composition with intervention admission and spectral contact, not a novelty claim for parent
   ingredients.
2. **Finite phase samples suffice.** False. Only the monotone cofinal limit reconstructs the full
   order gauge.
3. **Fourier faithfulness alone implies admission.** False. It reconstructs `eta`; the extremal
   kernel pencil computes whether it is admitted.
4. **A finite gauge selects the central line.** False by `(FKA.20)`. Zero reflected tension is
   load-bearing.
5. **Functional-equation reflection forces zero tension.** False. It exchanges the two entries of
   `(0,1)`.
6. **Temperedness repairs the producer.** False as a general theorem; symmetric shifted Euler
   products already isolate that boundary, and fixed-completion rigidity collides with Sarnak
   rigidity.
7. **Contact localization proves Route O coercivity.** No. It predicts the exact form of ground
   escape once a literal route comparison identifies its quadratic form with this kernel pencil.
8. **This proves RH.** False. `(FKA.24)` is the remaining arithmetic law.

## 10. Parent mathematics and corpus status

- Bochner's theorem and Fourier uniqueness provide `(FKA.6)`.
- Radon--Nikodym order intervals provide `(FKA.10)`; kernel Radon--Nikodym theorems are a modern
  operator-valued parent.
- Rayleigh--Ritz localization provides the spectral face.
- Corpus predecessors reconstruct measures from characteristic functions and prove abstract
  joint-admission conservation, but do not construct the canonical phase-kernel atlas or identify
  its exact admission gauge and contact profiles.

This theorem is a Frankenstein law in the intended sense: known theories are joined by one new
interpretation and one exact conserved quantity. Its value is that it replaces an assumed
cone-reflecting route atlas by a source-generated one and exposes the precise zero-tension theorem
an RH producer must prove.

## 11. Gates

- [x] common intervention grammar inherited from full frontier;
- [x] canonical fusion across signed source, phase, and positive-kernel organs;
- [x] exact reconstruction and conservation identity;
- [x] fourth-organ spectral contact/escape theorem;
- [x] arithmetic reflection prediction and exact selector boundary;
- [x] finite order-reflection, reconstruction, pencil-admission, and contact inequality formalized;
- [x] analytic Fourier uniqueness, Radon--Nikodym gauge, and cofinal limit formalized;
- [ ] literal pre-divisor arithmetic proof of zero reflection tension.

## 12. Lean certification boundary

`GaloisForLFunctions.HTGeometry.FourierKernelAdmission` certifies:

- `finiteKernelQuadratic_nonneg_iff` — all quadratic packets jointly reflect the finite source cone;
- `finiteKernelQuadratic_injective` — complete quadratic response reconstructs the carrier;
- `dominatedAt_iff_finiteKernelPencil_nonneg` — compensated source admission is exactly positivity
  of every kernel pencil;
- `finiteContactPenalty_le_spectralExcess` — finite spectral excess controls all mass separated
  from the contact set;
- `finiteKernelAdmission_contact_capstone` — closed conjunction of all four finite laws.

The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`. Its axiom audit uses
only `propext`, `Classical.choice`, and `Quot.sound`. The analytic finite-measure statements
`(FKA.5)`--`(FKA.23)` are formalized in `PhasePacketOrderReflection`, `PhaseKernelAdmissionGauge`
and `PhaseKernelContactLocalization`; see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PhasePacketOrderReflection`, `GaloisForLFunctions.HTGeometry.PhaseKernelAdmissionGauge`, `GaloisForLFunctions.HTGeometry.PhaseKernelContactLocalization`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.PhasePacketOrderReflection` (45 constants), `GaloisForLFunctions.HTGeometry.PhaseKernelAdmissionGauge` (42 constants), `GaloisForLFunctions.HTGeometry.PhaseKernelContactLocalization` (44 constants), all axiom-audit clean; with the finite core `FourierKernelAdmission`. Namespace `PhaseKernel`.

| Claim | Lean declaration |
|-|-|
| (FKA.1)–(FKA.2) Fourier transform, phase packets, quadratic form | `fourierTransform`, `phasePacket`, `packetForm`, `packetEnergy`, `signedFourier`, `signedPacketForm`, `signedPacketEnergy` |
| Thm 3.1 (FKA.5) `Q_ν(t,z) = ∫ |p_{t,z}|² dν` | `packetForm_eq_packetEnergy`, `signedPacketForm_eq` |
| Thm 3.1 (FKA.6) `ν ≥ 0` iff all packet forms `≥ 0` (Stone–Weierstrass on `AddCircle`, outer/inner regularity) | `nonneg_iff_forall_signedPacketEnergy_nonneg`, `le_iff_forall_packetEnergy_le`, `exists_rationalPacket_approx`, `le_of_forall_rationalPacketEnergy_le` |
| Thm 3.1 (FKA.7) kernel matrices reconstruct `ν`; two-time packets read `ν̂` | `kernelMatrix`, `eq_of_kernelMatrix_eq`, `fourierTransform_eq_charFun` |
| (FKA.3)–(FKA.4) gauge and packet thresholds | `admissionGauge`, `packetThreshold`, `packetThreshold_le_iff` |
| Thm 4.1 (FKA.8), (FKA.11) gauge = worst threshold | `admissionGauge_eq_iSup_packetThreshold`, `nonneg_add_smul_iff` |
| Thm 4.1 (FKA.9) least `c` with every Hermitian pencil PSD | `kernelPencil`, `kernelPencil_isHermitian`, `kernelPencil_posSemidef_iff`, `admissionGauge_le_iff_kernelPencil`, `admissionGauge_eq_iInf_kernelPencil` |
| Thm 4.1 (FKA.10) Radon–Nikodym gauge, finiteness criterion | `nonneg_add_smul_iff_negPart_le`, `le_smul_iff_rnDeriv_le`, `admissionGauge_eq_essSup`, `admissionGauge_lt_top_iff` |
| Thm 5.1 (FKA.12)–(FKA.13) rational enumeration, nested pencils, `κ_N ↑ κ` | `ratPhase`, `truncatedGauge`, `truncatedGauge_le_iff`, `truncatedGauge_mono`, `iSup_truncatedGauge`, `tendsto_truncatedGauge`, `le_iff_forall_rationalPacketEnergy_le` |
| §6 rational phase polynomials dense in `L²((1+|h|)μ)` | `exists_ratPacket_eLpNorm_lt`, `exists_ratPacket_indicator_approx` |
| Thm 6.1 (FKA.15) ground energy `= ess inf h` | `rationalRayleighSet`, `isGLB_rationalRayleighSet`, `essInf_mul_packetEnergy_le`, `exists_ratPacket_rayleigh_lt` |
| Thm 6.1 `α < 0 ⇒ κ = -α` | `admissionGauge_withDensityᵥ`, `toReal_admissionGauge_withDensityᵥ_of_neg` |
| Thm 6.1 (FKA.16)–(FKA.17) contact localization | `tendsto_contactMass_zero` |
| Cor 8.1 (FKA.19)–(FKA.21) reflection gauges and tension `1_{a≠0}` | `reflectedScore`, `reflectionGauge_pair`, `reflectionTension_eq` |
| Cor 8.1 (FKA.22) critical density, ground energy zero, no contact point | `reflectedScore_neg_add_one`, `isGLB_criticalRayleigh`, `criticalDensity_ne_ground` |
| Cor 8.1 (FKA.23) escape to `+∞`; minimizing sequences exist | `tendsto_mass_Iic_zero`, `exists_escaping_minimizing_sequence` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
