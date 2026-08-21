# The unweighted anti-causal Cauchy trace is the unique phase-noncancelling Hankel energy

- **ID:** `anti-causal-cauchy-trace-unique-phase-noncancellation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / POSITIVE NO-GO RESIDUE
- **Scientific status:** `[PROVED HERE] [NOT A NOVELTY CLAIM] [NOT RH]`
- **Parents:**
  - `infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  - `../squarefree-fixed-current-right-half-ward-localization.md`;
  - `../../1-in-progress/source-polarized-laurent-pluecker-tangent-ward-law.md`.
- **Statement:** In the natural power-weighted Hankel energy scale of a finite right-half divisor,
  the unweighted `L2` trace is the unique nonnegative power for which every cross mode contributes
  positively for every pair of ordinates.  Standard Hilbert--Schmidt/Quillen energy has the wrong
  weight and cannot inherit the four-unit per-zero exclusion by discarding cross terms.

## Weighted divisor energies

Let

```text
ell(t)=2 sum_j m_j exp(-z_j t),
z_j=a_j+i gamma_j,
a_j>0,  m_j>0.                                           (1)
```

For `alpha>=0`, define

```text
E_alpha(ell)=integral_0^infinity t^alpha |ell(t)|^2 dt.   (2)
```

Termwise integration gives

```text
E_alpha(ell)
 =4 Gamma(alpha+1) sum_(j,k) m_j m_k
    Re[(z_j+conj(z_k))^(-(alpha+1))].                    (3)
```

Indeed, for `Re lambda>0`,

```text
integral_0^infinity t^alpha exp(-lambda t) dt
 =Gamma(alpha+1)lambda^(-(alpha+1)).                     (4)
```

## Unique entrywise positivity

Write

```text
z_j+conj(z_k)=r exp(i theta),       |theta|<pi/2.         (5)
```

Then the cross entry in `(3)` has sign

```text
sign cos((alpha+1)theta).                                 (6)
```

For `alpha=0`, one has `|theta|<pi/2`, hence

```text
Re[(z_j+conj(z_k))^(-1)]>0                               (7)
```

for every pair.  This is the strictly entrywise-positive Cauchy kernel used by the four-unit Ward
threshold.

For every `alpha>0`, choose

```text
pi/(2(alpha+1))<theta<min(pi/2,3pi/(2(alpha+1))).          (8)
```

The interval is nonempty, and `cos((alpha+1)theta)<0`.  Every angle in `(-pi/2,pi/2)` occurs as
`arg(x+iy)` with `x>0`.  Taking two divisor modes with `a_j+a_k=x` and
`gamma_j-gamma_k=y` therefore makes their cross entry in `(3)` negative.

Consequently:

> Among the power weights `t^alpha`, `alpha>=0`, the unweighted energy `alpha=0` is the unique
> energy whose Gram expansion is entrywise positive for every right-half divisor packet.

## Why this matters for the HT Ward route

For one mode of multiplicity `m`,

```text
E_0=2m^2/a.                                               (9)
```

Every nontrivial-strip displacement has `0<a<1/2`, so `(9)` is strictly greater than four.  Since
all cross entries are positive at `alpha=0`, the same lower bound survives in every multimode
packet.

The standard Hilbert--Schmidt norm of a Hankel operator with kernel `ell(x+y)` is instead

```text
||H_ell||_HS^2=integral_0^infinity t |ell(t)|^2 dt=E_1.  (10)
```

Its cross kernel is the square of the Cauchy denominator and can have negative real part.  Thus a
Quillen, restricted-Grassmannian, or determinant-line estimate controlling only `(10)` does not
yield the phase-independent diagonal lower bound `(9)`.

**No-go.**  The cofinal half-form BKS conjecture cannot stop at Hilbert--Schmidt implementability,
Quillen curvature, or an `E_1` bound.

**Positive successor.**  The required source-rigged quantization must have a genuine boundary
trace map into unweighted Hardy `L2`.  This explains why the escaping Pluecker tangent and its
source half-density are load-bearing: they must improve one half-order beyond ordinary determinant
geometry and retain the unique phase-noncancelling Cauchy trace.

## Anti-theatre verdict

The theorem does not prove that the source trace is bounded by four.  It proves that replacing the
trace by a more standard determinant/Hankel norm loses the exact no-cancellation property needed
for RH.  Any successful topological proof must therefore construct the unweighted trace itself,
not merely a nearby Sobolev or operator-ideal norm.

## Gates

- [x] all power-weighted energies computed
- [x] unweighted Cauchy cross entries proved strictly positive
- [x] every positive weight shown to admit a negative cross entry
- [x] Hilbert--Schmidt/Quillen weight identified as `alpha=1`
- [x] positive source-rigged boundary-trace successor stated
- [ ] construct that trace for the completed squarefree reciprocal-horizon seam
- [ ] prove its capacity-to-Hardy norm is at most one

## Lean formalization (2026-08-21) — COMPLETE

New module `formal/GaloisForLFunctions/RHTower/WeightedAntiCausalCauchyTrace.lean`
(namespace `RHTower`; all declarations audited to `propext`, `Classical.choice`, `Quot.sound`).
It sits on the corpus off-line Cauchy stack (`RHTower.finiteOfflineProfile`,
`RHTower.finiteOfflinePairIntegrand`) and on the corpus complex-rate Euler integral
`GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi`
(`∫_0^∞ t^{s-1} e^{-w t} dt = Γ(s) w^{-s}` for `Re s > 0`, `Re w > 0`), which is the Lean form of
the card's equation `(4)`.

- `offlineCrossRate a γ j k = (aⱼ + a_k) - i(γⱼ - γ_k)` — the Cauchy rate `conj zⱼ + z_k` of `(5)`;
  `offlineCrossRate_re` gives `Re = aⱼ + a_k > 0`.
- `weightedOfflinePairIntegrand`, `weightedOfflinePairIntegrand_integrableOn`,
  `integral_weightedOfflinePairIntegrand` — the weighted cross-mode integrand, its integrability on
  the half-line, and its exact integral `4 mⱼ m_k Γ(α+1) w^{-(α+1)}`.
- `weightedOfflineEnergy alpha a γ m = ∫_{t>0} t^α ‖ℓ(t)‖² dt` and **`weightedOfflineEnergy_eq`** —
  equation `(3)`, unconditionally for every `α > -1`:
  `E_α = 4Γ(α+1) ∑_{j,k} mⱼ m_k Re[(conj zⱼ + z_k)^{-(α+1)}]`.
- **`re_cpow_neg_ofReal`** — the polar sign law `(6)`:
  `(w^{-c}).re = ‖w‖^{-c} cos(c · arg w)` for `w ≠ 0`, `c` real.
- **`re_offlineCrossRate_cpow_neg_one_pos`** — equation `(7)`: at `α = 0` every cross entry is
  strictly positive, for every right-half divisor packet.
- **`exists_offlinePacket_re_cpow_neg_lt_zero`** — the converse half, equation `(8)`: for every
  `α > 0` there is an explicit two-mode right-half packet (`aⱼ = cos θ/2`, ordinates `0` and
  `sin θ`, with `θ` the midpoint of the card's interval `(π/(2(α+1)), min(π/2, 3π/(2(α+1))))`)
  whose cross entry has strictly negative real part.  Together with the previous item this is the
  uniqueness statement: `α = 0` is the only nonnegative power weight that never cancels phase.
- **`finiteOfflineCauchyEnergy_single`** — equation `(9)`: `E₀ = 2m²/a` for one mode; and
  `finiteOfflineCauchyEnergy_single_gt_four`: `E₀ > 4` whenever `0 < a < 1/2` and `m ≥ 1`.
- **`lintegral_hankelSquare_eq_firstMoment`** — equation `(10)`: the double half-line integral
  `∫_{x>0}∫_{y>0} g(x+y)`, i.e. the Hilbert–Schmidt square of the Hankel operator with kernel
  `ℓ(x+y)`, equals the first-moment energy `∫_{t>0} t·g(t)`.  So the Hilbert–Schmidt/Quillen norm
  sits at `α = 1`, exactly the weight the previous item shows to lose entrywise positivity.
  (Supporting: `lintegral_Ioi_add_left`, the half-line translation identity.)

Wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] all power-weighted energies computed in Lean (`weightedOfflineEnergy_eq`)
- [x] unweighted Cauchy cross entries proved strictly positive in Lean
- [x] every positive weight shown to admit a negative cross entry in Lean
- [x] Hilbert–Schmidt/Quillen weight identified as `alpha = 1` in Lean

The two unchecked gates below are the card's own **open research targets** (construct the
source-rigged boundary trace; bound its capacity-to-Hardy norm), not proven theorems.
