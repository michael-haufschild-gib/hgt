# Burnol cofinite Cartier wall trace and complete-jet horizon

- **ID:** `burnol-cofinite-cartier-wall-trace-horizon`
- **Stage:** 3-formalized
- **Formalized companion:** `burnol-cofinite-cartier-wall-trace-horizon-formalized.md`
- **Type:** THEOREM / SINGULAR SOURCE INTERFACE / COMPLETE-JET NO-GO CLOSURE
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** R
- **Parents:** `../../3-formalized/new_scientific_knowledge/burnol/burnol-all-prime-window-hilbert-cartier-jet-wall.md`,
  `burnol-gamma-bockstein-first-wall-extraction-law`, and
  `burnol-first-wall-cartier-residue-cancellation-law`
- **Lean:** `GaloisForLFunctions.RHTower.BurnolPrimeCartierWallTrace`,
  `GaloisForLFunctions.RHTower.BurnolCofiniteHorizonGerm`,
  `GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall`.

## Lean formalization (2026-08-09)

| Statement | Lean declaration |
|---|---|
| `(CH1)` | `burnolAllPrimeCompletionMultiplier`, `burnolAllPrimeCompletionMultiplierReflected` |
| `(CH2)` | `tendsto_burnolCartierZeroWallTrace`, `tendsto_burnolAllPrimeCompletionReflected_div_one` |
| `(CH3)` | `burnolPrimeSideband`, `nat_cpow_sideband` |
| `(CH4)` | `tendsto_burnolCartierSidebandTrace`, `tendsto_burnolCartierReflectedSidebandTrace` |
| `(CH5)` | `tendsto_burnolAllPrimeCompletion_sidebandResidue` |
| `(CH6)` | `tendsto_burnolAllPrimeCompletionReflected_sidebandResidue` |
| `(CH7)`, `(CH8)` | `tendsto_burnolAllPrimeCompletion_div_zero`, `tendsto_burnolAllPrimeCompletionReflected_div_one` |
| `(CH9)`, `(CH11)` | `burnolSidebandSet`, `burnolSideband_exists_index`, `burnolSideband_infDist_le` |
| `(CH10)` | `burnolSideband_infDist_tendsto`, `burnolSidebandReflected_infDist_tendsto`, `burnolSideband_re_le_infDist` |
| `(CH12)` | `burnolHorizonGap`, `burnolHorizonGap_eq`, `burnolHorizonGap_pos_iff` |
| `(CH13)`, `(CH15)` | `burnolGerm_uniform_decay` |
| `(CH14)` | `burnolGermJoint_unit_tendsto_zero` |
| `(CH16)` | `burnolGerm_unit_tendsto_zero`, `burnolDecay_eventually_lt` |
| `(CH17)` | `burnolGermReflected_uniform_decay` |
| nonclosed range | `burnolGermWitness_summable`, `burnolGermWitness_not_summable`, `burnolGerm_preimage_forced` |
| `(CH18)`, `(CH19)` | `tendsto_burnolCartierZeroWallTrace`, `tendsto_burnolCartierSidebandTrace`, `tendsto_burnolCartierReflectedSidebandTrace` |
| `(CH20)`, `(CH21)` | `burnolAllPrimeInverseCompletionCoefficient`, `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` |
| `(CH22)`, `(CH23)` | `xiDivisor_burnolCartier_headEnergyDefect_eq_horizonGap_mul_headFlux` |

The nonclosed-range theorem is formalized constructively rather than through the open mapping
theorem: the coefficient field `u_p = p^{-1/2}` has square-summable germ data on every safe disc
(`burnolGermWitness_summable`), so its finite truncations converge in every compact-open seminorm,
yet the only possible preimage is `u` itself (`burnolGerm_preimage_forced`, from nonvanishing of
`C_p(ρ)` in the open strip), which is not square summable (`burnolGermWitness_not_summable`,
from divergence of `∑ 1/p`).  No Fréchet open mapping theorem is needed.

## Result

For every ordinary prime put

\[
 C_p(s)=\frac{s^2(s-1)}{2(p^s-1)},\qquad
 C_p^\vee(s)=C_p(1-s).                                  \tag{CH1}
\]

These are the two coefficient-faithful Burnol--Xi completion orientations.  Their prime-dilation
walls are not merely sets of bad points.  They carry canonical Cartier traces which recover the
uncompleted coefficient with exact unit gain.

At the common zero-frequency wall, completion hides the coefficient as a simple zero, but

\[
 \boxed{-2\log p\,\partial_s[C_p(s)u_p]_{s=0}=u_p,\qquad
  2\log p\,\partial_s[C_p^\vee(s)u_p]_{s=1}=u_p.}       \tag{CH2}
\]

At every nonzero prime-dilation frequency

\[
 \lambda_{p,k}=\frac{2\pi i k}{\log p},\qquad k\ne0,    \tag{CH3}
\]

the corresponding normalized principal parts give the same recovery law:

\[
\begin{aligned}
 \frac{2\log p}{\lambda_{p,k}^2(\lambda_{p,k}-1)}
   \operatorname*{Res}_{s=\lambda_{p,k}} C_p(s)u_p
   &=u_p,\\
 -\frac{2\log p}{\lambda_{p,k}^2(\lambda_{p,k}-1)}
   \operatorname*{Res}_{s=1-\lambda_{p,k}} C_p^\vee(s)u_p
   &=u_p.
                                                               \tag{CH4}
\end{aligned}
\]

Thus both Gamma orientations have one and the same coefficient-faithful singular boundary
coordinate: derivative at the common nilpotent wall and normalized residue at every semisimple
sideband.

This singular trace cannot be replaced by arbitrarily many ordinary analytic jets.  If
`rho=sigma+i t` lies in the open strip, the maximal cofinite pole-free radius of the forward
completion around `rho` is exactly `sigma`; the reflected radius is exactly `1-sigma`.  On the
full disks of those radii, diagonal multiplication by the complete analytic completion germs is
continuous and injective but has nonclosed range.  This remains true after retaining both
orientations jointly.  Hence every finite jet, every countable complete jet, and the entire
compact-open germ in both orientations still loses the inverse-completion domain.

The positive replacement is exact: Route R must use the singular wall trace `(CH2)--(CH4)`, or an
equivalent boundary/hyperfunction topology containing it.  More analytic interior observations
cannot prove the missing source landing.

## 1. Local divisor of the completion

For `k != 0`, `p^lambda_(p,k)=1`, and the numerator in `(CH1)` is nonzero.  Since

\[
 \left.\frac d{ds}\,2(p^s-1)\right|_{s=\lambda_{p,k}}
 =2\log p,
\]

`C_p` has a simple pole there with

\[
 \operatorname*{Res}_{s=\lambda_{p,k}}C_p(s)
 =\frac{\lambda_{p,k}^2(\lambda_{p,k}-1)}{2\log p}.     \tag{CH5}
\]

Reflection reverses the local coordinate.  Therefore `C_p^vee` has a simple pole at
`1-lambda_(p,k)` and

\[
 \operatorname*{Res}_{s=1-\lambda_{p,k}}C_p^\vee(s)
 =-\frac{\lambda_{p,k}^2(\lambda_{p,k}-1)}{2\log p}.    \tag{CH6}
\]

Equations `(CH4)` follow immediately.

The apparent point `k=0` is different.  One factor of `s` cancels the denominator and gives

\[
 C_p(s)=-\frac{s}{2\log p}+O(s^2)\quad(s\to0).          \tag{CH7}
\]

Consequently

\[
 C_p'(0)=-\frac1{2\log p},\qquad
 (C_p^\vee)'(1)=\frac1{2\log p},                        \tag{CH8}
\]

which proves `(CH2)`.  This is the all-prime version of the Gamma--Bockstein mechanism: ordinary
completion evaluates the first-wall coefficient to zero, while the transverse Cartier derivative
recovers it with unit gain.

No Xi divisor, zero, or critical-line datum enters `(CH2)--(CH8)`.

## 2. Exact cofinite analytic horizons

Fix

\[
 \rho=\sigma+i t,\qquad 0<\sigma<1.                    \tag{CH9}
\]

Let `d_p^+(rho)` be the distance from `rho` to the genuine pole set
`{lambda_(p,k): k != 0}` of `C_p`, and let `d_p^-(rho)` be the distance from `rho` to the pole set
`{1-lambda_(p,k): k != 0}` of `C_p^vee`.

### Theorem 1 — cofinite radius law

As `p` tends to infinity through ordinary primes,

\[
 \boxed{d_p^+(\rho)\longrightarrow\sigma,\qquad
        d_p^-(\rho)\longrightarrow1-\sigma.}           \tag{CH10}
\]

Equivalently:

1. every disk about `rho` of radius `R<sigma` is pole-free for every forward coordinate;
2. every disk of radius `R>sigma` contains a genuine forward pole for every sufficiently large
   prime;
3. the reflected statements hold with `1-sigma` in place of `sigma`.

### Proof

Every forward pole lies on `Re s=0`, so its distance from `rho` is at least `sigma`.  Choose an
integer `k_p` nearest to

\[
 \frac{t\log p}{2\pi}.
\]

If `t != 0`, then `k_p != 0` for all sufficiently large primes and

\[
 \left|\frac{2\pi k_p}{\log p}-t\right|
 \le\frac\pi{\log p}.
\]

Hence the corresponding pole distance is at most

\[
 \sqrt{\sigma^2+\frac{\pi^2}{(\log p)^2}}
 \longrightarrow\sigma.                               \tag{CH11}
\]

If `t=0`, use `k_p=1`; the bound has `2pi/log p` in place of `pi/log p` and has the same limit.
This proves the first limit.  Reflection moves the pole line from `Re s=0` to `Re s=1`; the same
argument gives the second. `QED`

The signed horizon gap is therefore

\[
 h_+(\rho)-h_-(\rho)=\sigma-(1-\sigma)=2\sigma-1.       \tag{CH12}
\]

It vanishes exactly on the critical line, but `(CH12)` is a detector, not a producer.

## 3. Complete analytic germs still have nonclosed range

Write `D_r={z in C: |z|<r}` and let `Hol(D_r;ell^2(P))` carry its usual compact-open Frechet
topology.  Define

\[
\begin{aligned}
 (\mathcal T_\rho^+u)(z)_p&=C_p(\rho+z)u_p,
     &&z\in D_\sigma,\\
 (\mathcal T_\rho^-u)(z)_p&=C_p(1-\rho-z)u_p,
     &&z\in D_{1-\sigma}.                               \tag{CH13}
\end{aligned}
\]

### Theorem 2 — maximal-germ nonclosed-range law

Both maps in `(CH13)` are continuous injective linear maps from `ell^2(P)` into the displayed
Frechet spaces.  Neither image is closed.  The joint map

\[
 \mathcal T_\rho^+\oplus\mathcal T_\rho^-:
 \ell^2(\mathbb P)\longrightarrow
 \operatorname{Hol}(D_\sigma;\ell^2)\times
 \operatorname{Hol}(D_{1-\sigma};\ell^2)               \tag{CH14}
\]

is also continuous and injective with nonclosed image.

### Proof

Fix `R<sigma`.  On `|z|<=R`, `Re(rho+z)>=sigma-R>0`.  Uniformly on this compact set,

\[
 |C_p(\rho+z)|\ll_{\rho,R}p^{-(\sigma-R)}.              \tag{CH15}
\]

Indeed, the polynomial numerator is bounded there and

\[
 |p^{\rho+z}-1|\ge p^{\sigma-R}-1.
\]

Finite exceptional primes are harmless.  The same estimate for all complex derivatives follows
after differentiating: each derivative introduces only a fixed power of `log p`, still dominated
by the positive power in `(CH15)`.  Thus `T_rho^+` is an `ell^2`-valued holomorphic map and is
continuous in every compact-open seminorm.  Evaluation at `z=0` proves injectivity because every
`C_p(rho)` is nonzero in the open strip.

For the standard unit coordinate `e_p`, `(CH15)` gives

\[
 \mathcal T_\rho^+e_p\longrightarrow0
 \quad\text{in }\operatorname{Hol}(D_\sigma;\ell^2),   \tag{CH16}
\]

while `||e_p||=1`.  If the image were closed, it would be Frechet.  The continuous bijection from
the Banach space `ell^2` onto its image would then have continuous inverse by the open mapping
theorem, contradicting `(CH16)`.  Hence the forward image is nonclosed.

For the reflected map use, on `|z|<=R<1-sigma`,

\[
 |C_p(1-\rho-z)|\ll_{\rho,R}p^{-((1-\sigma)-R)}.        \tag{CH17}
\]

This proves the reflected assertion.  The two estimates simultaneously send `e_p` to zero in
both factors of `(CH14)`, so the same inverse-continuity contradiction proves the joint assertion.
`QED`

### Corollary 3 — all interior jet repairs fail

Every finite jet is a continuous quotient of the compact-open germ.  The complete countable jet
at `z=0` carries no more information than the germ topology.  Therefore none of the following can
make inverse completion continuous or its range closed:

1. any fixed finite transverse jet;
2. all derivatives at the Xi fibre with their compact-open topology;
3. full vector-valued analytic germs on every safe disk;
4. the joint maximal germs in both Gamma orientations.

The obstruction is not finite jet order.  It is the exclusion of the singular boundary trace.

## 4. Coefficient-faithful singular completion

Let `PP_p^+` and `PP_p^-` denote the principal-part data of a meromorphic coordinate at the two
prime-dilation walls, augmented at the common zero-frequency point by the first derivative.  The
formulas `(CH2)` and `(CH4)` define trace maps

\[
 \operatorname{Tr}_p^+:PP_p^+\to\mathbb C,
 \qquad
 \operatorname{Tr}_p^-:PP_p^-\to\mathbb C.             \tag{CH18}
\]

### Theorem 4 — coefficient-faithful two-orientation Cartier trace

For every coefficient field `u=(u_p)` and every nonzero sideband label `k`,

\[
 \boxed{
 \operatorname{Tr}_p^+(C_pu_p)
 =u_p
 =\operatorname{Tr}_p^-(C_p^\vee u_p).}                \tag{CH19}
\]

The same equality holds using only the normalized zero-wall derivatives `(CH2)`.  Consequently,
after adjoining either singular trace to the germ target, the diagonal completion has a
coefficientwise left inverse.  With the `ell^2` norm on the recovered trace, it is bounded below
and its graph range is closed.

### Proof

Equation `(CH19)` is `(CH2)` at the nilpotent wall and `(CH4)` at every semisimple sideband.  If
the target graph norm contains

\[
 \sum_p|\operatorname{Tr}_p^+(F_p)|^2
 \quad\text{or}\quad
 \sum_p|\operatorname{Tr}_p^-(F_p)|^2,
\]

then `(CH19)` makes that summand exactly `||u||_2^2`.  Hence the completion map is bounded below.
Its inverse on the image is continuous, and the graph image is closed. `QED`

This is a topology theorem, not the missing arithmetic estimate.  For the Route-R vector

\[
 U_{\rho,p}=\frac{c_\rho}{p\log p\,C_p(\rho)},          \tag{CH20}
\]

the trace in `(CH19)` is exactly `U_(rho,p)`.  Therefore source admission of the trace in `ell^2`
is equivalent to the already proved wall

\[
 U_\rho\in\ell^2\quad\Longleftrightarrow\quad
 \Re\rho\le\frac12.                                    \tag{CH21}
\]

The theorem constructs an exact boundary coordinate absent from the compact-open germ topology;
it does not assume its square summability.

## 5. Relation to the explicit Route-R current

The formalized head-energy transgression is

\[
 E_{1/2}(U_\rho f_0)-E_{1/2}(f_0)
 =(2\Re\rho-1)J_\rho.                                  \tag{CH22}
\]

Combining `(CH12)` with `(CH22)` gives the exact two-horizon form

\[
 \boxed{
 E_{1/2}(U_\rho f_0)-E_{1/2}(f_0)
 =[h_+(\rho)-h_-(\rho)]J_\rho.}                        \tag{CH23}
\]

Thus both factors in the physical energy defect are boundary quantities:

1. `h_+-h_-` is the signed separation of the two cofinite prime-dilation walls;
2. `J_rho` is the reflection-odd first-wall Bockstein residue already constructed in the parent
   card.

For a hypothetical right-half divisor, both are strictly positive by existing results.  Interior
analytic completion cannot reverse either sign because Theorem 2 says it does not continuously
retain the boundary coefficient at all.

The remaining producer is now correctly typed:

> **SINGULAR CARTIER TRACE DISSIPATIVITY.**  Construct, before divisor specialization, the
> Stokes boundary form on the trace graph `(CH18)` and prove that its reflection-odd zero-wall
> marginal on the actual zero-divided Burnol section is nonpositive.  Under the already proved
> landing of that marginal, this is `J_rho <= 0`.

This law must live on the singular trace graph.  A theorem stated only for completed `L2` vectors,
ordinary analytic germs, complete interior jets, or their two-orientation product cannot imply it.

## 6. Conjecture / proof-or-fail loop

1. **A sufficiently high finite transverse jet closes inverse completion.** `[FAILED]`  Every
   finite jet retains a diagonal weight `p^(-sigma)` times a polynomial in `log p`; it still tends
   to zero.
2. **The complete analytic jet closes inverse completion.** `[FAILED]`  Theorem 2 proves
   nonclosed range even in the full compact-open germ space.
3. **Adding the reflected complete jet supplies the missing lower bound.** `[FAILED]`  Both
   maximal germ images send `e_p` to zero in their respective Frechet topologies; the joint range
   remains nonclosed.
4. **Functional-equation reflection identifies the two horizons at the same fibre.** `[FAILED —
   CONCLUSION LAUNDERING]`  Reflection sends the fibre at `rho` to the fibre at `1-rho`.  Equality
   of their same-fibre radii is exactly `Re rho=1/2` and cannot be imported from global FE
   symmetry.
5. **The prime-dilation boundary has no coefficient-faithful coordinate.** `[FAILED]`  Equations
   `(CH2)` and `(CH4)` construct exact unit-gain traces in both orientations.
6. **Equality of the two normalized traces signs the physical first-wall quadrature.** `[FAILED]`
   The trace equality `(CH19)` holds for every coefficient field, including off-line model fields.
   The unequal physical head gains remain.  Using trace equality alone would be another RH
   re-encoding.
7. **The signed horizon gap itself proves the desired sign.** `[FAILED]`  Equation `(CH12)` is
   positive on the right half, and `(CH23)` then exposes the already proved positive energy
   amplification.
8. **Strongest survivor.** `[PAPER-PROVED]`  Complete interior analytic data in both orientations
   provably cannot retain the Route-R coefficient, whereas the derivative/residue Cartier wall
   trace recovers it exactly and gives an explicit closed graph topology in which a genuine source
   Stokes sign theorem can be stated.

## 7. Anti-theatre audit

- No sign of `J_rho`, critical-line placement, same-fibre norm identity, source-dagger identity,
  or RH is assumed.
- The two horizon radii are proved in both directions, including cofinite pole intrusion beyond
  the boundary.
- Nonclosed range is proved for full germs, not inferred from failure of one finite jet.
- The singular trace is an explicit derivative/residue formula, not a named missing map.
- Trace equality is not advertised as the missing sign; the failed implication is recorded.
- The exact open theorem is a boundary-form inequality on the constructed trace graph.

## 8. Novelty boundary

Pole lattices of `p^s-1`, compact-open holomorphic function spaces, residue recovery, and the open
mapping theorem are classical separately.  Internal collision audit found finite-prime
common-indicial pole lattices and generic factorial-jet criteria, but no cofinite two-orientation
radius law `(CH10)`, maximal-germ nonclosed-range theorem `(CH13)--(CH17)`, or unified
zero-derivative/sideband-residue Cartier trace `(CH19)` for the Burnol all-prime completion.
Candidate novelty is this coefficient-faithful synthesis and its exact Route-R frontier
consequence.  External priority is unverified.

## Lean formalization (partial, 2026-08-09)

Modules: `RHTower/BurnolAllPrimeCompletionWall`, `RHTower/BurnolPrimeCartierWallTrace`.

| Paper item | Lean declaration |
|---|---|
| `(CH1)` | `burnolAllPrimeCompletionMultiplier`, `burnolAllPrimeCompletionMultiplierReflected` |
| `(CH3)` | `burnolPrimeSideband`, `nat_cpow_sideband` |
| `(CH5)` | `tendsto_burnolAllPrimeCompletion_sidebandResidue` |
| `(CH4)` | `tendsto_burnolCartierSidebandTrace` |
| `(CH7)`, `(CH8)` | `tendsto_burnolAllPrimeCompletion_div_zero`, `tendsto_burnolAllPrimeCompletionReflected_div_one` |
| `(CH2)` | `tendsto_burnolCartierZeroWallTrace` |
| `(CH12)` | `burnolHorizonGap`, `burnolHorizonGap_eq`, `burnolHorizonGap_pos_iff` |
| `(CH21)` | `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` |
| `(CH23)` | `xiDivisor_burnolCartier_headEnergyDefect_eq_horizonGap_mul_headFlux` |

Residues and transverse derivatives are formalized as limits of the explicit difference quotients,
which is exactly what a simple pole and a removable-singularity derivative assert.

Still open in Lean: the cofinite radius law `(CH10)`--`(CH11)` and the maximal-germ nonclosed-range
theorem `(CH13)`--`(CH17)`.

## Gates

- [x] exact two-orientation prime-dilation divisors
- [x] cofinite analytic radii proved
- [x] full compact-open germ maps constructed
- [x] single- and two-orientation nonclosed ranges proved
- [x] zero-hidden Cartier derivative recovered with unit gain
- [x] every nonzero sideband residue recovered with unit gain
- [x] explicit coefficient-faithful singular graph completion identified
- [x] relation to the explicit Route-R current and energy transgression proved
- [ ] specialist novelty audit
- [ ] singular Cartier trace dissipativity from pre-divisor source structure
- [ ] Lean formalization after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — classified maximal cofinite analytic horizons in both Gamma orientations, proved
  complete-germ nonclosed range, constructed the all-prime zero-wall and sideband Cartier traces,
  and isolated singular trace dissipativity as the only correctly typed continuation of this
  producer lane.
- 2026-08-09 — first unconditional Lean layer built and umbrella-wired; see the Lean
  formalization table above for the exact declaration-to-equation map.
