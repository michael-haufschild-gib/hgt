# Burnol Poisson-subordinate smooth Cartier entrance wall

- **ID:** `burnol-poisson-subordinate-smooth-cartier-entrance-wall`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / PRE-DIVISOR SOURCE CONSTRUCTION / OPERATOR-DOMAIN CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** R
- **Parents:** `burnol-all-prime-window-hilbert-cartier-jet-wall`,
  `route-r-reciprocal-log-fisher-half-density-entrance-wall`, and the formalized modules
  `BurnolCoPoissonSubWindow.lean` and `DeningerMultiplier.lean`.
- **Lean:** deliberately deferred while `HTGeometry` and `RHTower` are being refactored.

## Result

The all-prime Burnol entrance wall can be carried by an honest source which is smooth for every
power of the prime-log differential. This removes the lack of differential regularity of the
reciprocal-log source without moving the critical wall.

For every ordinary prime put

\[
 G_p(t)=\operatorname{CoP}\left(x^{-1}{\bf1}_{[p^{-1},1]}(x)\right)(t),
 \qquad D e_p=(\log p)e_p,
\]

and, for `y>0`, define the fixed pre-divisor source

\[
 X_y=\left(A_{y,p}G_p\right)_{p\in\mathbb P},
 \qquad
 A_{y,p}=p^{-1}\exp\!\left(-y\sqrt{\log p}\right).       \tag{PS1}
\]

Then:

1. `X_y` belongs to the Hilbert direct sum and to `Dom(D^k)` for every natural `k`.
2. `X_y` is Gevrey-2 for `D`, but has zero positive analytic radius:
   `X_y` is not in `Dom(exp(aD))` for any `a>0`.
3. `X_y` is the Poisson subordination of the singular all-prime Burnol boundary
   `(p^{-1}G_p)_p`:

   \[
   e^{-y\sqrt D}
   =\frac{y}{2\sqrt\pi}\int_0^\infty
       s^{-3/2}e^{-y^2/(4s)}e^{-sD}\,ds.                 \tag{PS2}
   \]

4. If `rho` lies in the open critical strip, `c_rho != 0`, and

   \[
   C_p(w)=\frac{w^2(w-1)}{2(p^w-1)},
   \]

   then the multiplicity-leading inverse-completed Cartier jet

   \[
   U_{y,\rho,p}
   =\frac{A_{y,p}c_\rho}{C_p(\rho)}                     \tag{PS3}
   \]

   satisfies the sharp classification

   \[
   \boxed{
   U_{y,\rho}\in\bigcap_{k\ge0}\operatorname{Dom}(D^k)
   \quad\Longleftrightarrow\quad
   \Re\rho\le\frac12.}                                 \tag{PS4}
   \]

   If `Re rho>1/2`, `U_(y,rho)` is not even in `ell^2(P)`.

Thus the first wall is not caused by a rough source. It persists on a literal, coefficient-faithful,
Gevrey-2 Euler--Gamma--Burnol source. Conversely, positive analytic radius cannot be imposed
without shifting or erasing the wall. The remaining comparison must therefore be a genuine
zero-analytic-radius Stokes boundary map; no everywhere-defined continuous map on the ordinary
`D^infinity` prime-log Fréchet carrier can realize positive physical gain.

## 1. Source Hilbert and smooth-domain estimates

The existing exact Burnol-window estimates are

\[
 \frac{2(p-1)^2}{p}\le \|G_p\|_2^2\le8p.                \tag{PS5}
\]

For every `k>=0`, the upper estimate gives

\[
 \|D^kX_y\|^2
 \le8\sum_{p}
   \frac{(\log p)^{2k}e^{-2y\sqrt{\log p}}}{p}.          \tag{PS6}
\]

The prime sum is bounded by the corresponding integer tail. With `u=log x`, its integral is

\[
 \int_{\log2}^{\infty}u^{2k}e^{-2y\sqrt u}\,du<\infty.  \tag{PS7}
\]

Indeed, with `v=2y sqrt(u)` the full integral from zero is a constant multiple of
`Gamma(4k+2)`. Eventual monotonicity supplies the elementary integral comparison. This proves
`X_y in Dom(D^k)` for every `k`, including `k=0`.

The same estimate gives constants `M_y,R_y>0` such that

\[
 \|D^kX_y\|\le M_yR_y^k(k!)^2.                          \tag{PS8}
\]

Hence the source is Gevrey-2. The precise Gevrey label is not used in the wall proof; it records
the Stokes category selected by the square-root subordination.

## 2. Zero analytic radius is forced

Let `a>0`. For `p>=2`, `(p-1)^2>=p^2/4`, so the lower half of `(PS5)` yields

\[
 \|e^{aD}X_y\|^2
 \ge\frac12\sum_p
   \frac{\exp(2a\log p-2y\sqrt{\log p})}{p}.             \tag{PS9}
\]

Since `sqrt(u)=o(u)`, the exponential factor is at least one for every sufficiently large prime.
Euler's divergence of `sum_p 1/p` proves `(PS9)` diverges. Therefore

\[
 X_y\notin\operatorname{Dom}(e^{aD})\qquad(a>0).         \tag{PS10}
\]

This is the exact breaking point. Polynomial prime-log regularity of every order is compatible
with the critical wall; any positive exponential prime-log regularity is not.

## 3. Pre-divisor Poisson provenance

For every `lambda>0`, the elementary subordination identity is

\[
 e^{-y\sqrt\lambda}
 =\frac{y}{2\sqrt\pi}\int_0^\infty
   s^{-3/2}e^{-y^2/(4s)}e^{-s\lambda}\,ds.               \tag{PS11}
\]

Applying `(PS11)` at `lambda=log p` proves `(PS2)` coefficientwise. Thus the damping in `(PS1)`
is not fitted after seeing a divisor. It is the positive Poisson extension of the singular
ordinary-prime boundary `(p^{-1}G_p)_p` under the already fixed prime-log generator. It preserves
prime, window, endpoint, and Gamma-completion provenance.

Writing `X_y` as a function of the extension variable also gives the source equation

\[
 \partial_y^2X_y=DX_y                                  \tag{PS12}
\]

and the positive inward flux law

\[
 -\frac12\partial_y\|X_y\|^2
 =\langle\sqrt D X_y,X_y\rangle\ge0.                   \tag{PS13}
\]

Equations `(PS12)`--`(PS13)` are genuine pre-divisor Stokes data. They do not assert the missing
physical landing.

## 4. Exact inverse-completion wall

Put `sigma=Re rho`. From the all-prime Burnol completion,

\[
 U_{y,\rho,p}
 =K_\rho e^{-y\sqrt{\log p}}\frac{p^\rho-1}{p},
 \qquad
 K_\rho=\frac{2c_\rho}{\rho^2(\rho-1)}\ne0.             \tag{PS14}
\]

If `sigma<=1/2`, then

\[
 |p^\rho-1|\le p^\sigma+1\le2\sqrt p.
\]

Consequently, for every `k`,

\[
 \sum_p(\log p)^{2k}|U_{y,\rho,p}|^2
 \le4|K_\rho|^2\sum_p
   \frac{(\log p)^{2k}e^{-2y\sqrt{\log p}}}{p}<\infty.  \tag{PS15}
\]

This proves the forward implication of `(PS4)`.

Suppose `sigma=1/2+delta` with `delta>0`. Reverse triangle inequality gives
`|p^rho-1|>=p^sigma/2` eventually. Therefore

\[
 |U_{y,\rho,p}|^2
 \ge\frac{|K_\rho|^2}{4p}
   \exp(2\delta\log p-2y\sqrt{\log p}).                 \tag{PS16}
\]

The exponential factor is eventually at least one, again because `sqrt(u)=o(u)`. The cofinite
tail of `(PS16)` dominates a nonzero multiple of `1/p`, so Euler divergence proves
`U_(y,rho) notin ell^2`. This proves the reverse implication and `(PS4)`.

## 5. Operator-category consequence

Let

\[
 \mathcal S_D=\bigcap_{k\ge0}\operatorname{Dom}(D^k)
\]

with its standard graph-seminorm Fréchet topology. Formula `(PS10)` gives an explicit element of
`S_D` on which every positive physical multiplier `e^(aD)` fails even to take values in the base
Hilbert space. Hence, for `a>0`:

- `e^(aD)` is not an everywhere-defined operator `S_D -> ell^2`;
- a closed or continuous everywhere-defined comparison on `S_D` cannot agree coefficientwise
  with physical prime dilation;
- adding any finite number, or all countably many, prime-log differential graph seminorms cannot
  prove the Route-R landing.

This escapes neither by ordinary smoothness nor by a Hilbert graph closure. The only surviving
category is a singular boundary-value category which uses the Poisson extension variable and its
Stokes trace before physical specialization.

This conclusion is stronger than the prior reciprocal-log source theorem: that source was outside
`Dom(D)`, leaving open whether source differential regularity was the obstruction. The present
source lies in every `Dom(D^k)`, so that explanation is now eliminated.

## 6. Route R consequence and exact remaining theorem

For a hypothetical right-half Xi divisor, the Lean corpus already proves

\[
 J_\rho=\operatorname{burnolCartierDividedShiftHeadFlux}(\rho)>0. \tag{PS17}
\]

The theorem here constructs, before divisor restriction:

1. an honest all-prime Burnol source with full prime-log differential regularity;
2. a positive Poisson/Stokes extension and inward flux;
3. coefficient-faithful multiplicity-leading Xi jets;
4. a fixed inverse-completion domain which excludes every right-half divisor.

Therefore a source theorem asserting that the Poisson-Stokes trace of `(PS12)` remains in the
fixed physical inverse-completion domain at every Xi fibre rules out every right-half divisor and
derives the required `J_rho<=0` statement vacuously. The assertion is still RH-bearing and is not
proved here.

The improvement is categorical and concrete: the remaining theorem cannot be blamed on a rough
Cartier potential, lack of iterated source differentials, choice of prime exhaustion, or an
ordinary closed-graph defect. It is precisely singular Gevrey-2 Poisson-Stokes boundary descent
into the fixed physical conormal.

## 7. Heavy conjecture / proof-or-fail loop

1. **Completion dissipation signs the bare current.** `[FAILED]` Log currents add. Removing a
   negative completion anomaly can expose the positive bare port.
2. **Positive compression transports completed negativity.** `[FAILED]` Existing Lean proves
   completed/theta and bare same-fibre currents have opposite signs at a hypothetical right zero.
3. **Smooth the reciprocal-log Fisher atom subexponentially.** `[PROVED IN COEFFICIENT FORM]`
   `exp(-sqrt(log p))` lies in every prime-log domain and retains the exact entrance wall.
4. **Ordinary `D^infinity` continuity supplies landing.** `[FAILED]` Positive physical gain is
   `exp(aD)`, which is not defined on all of `S_D`; `(PS10)` is an explicit counterexample.
5. **Pair the two Gamma orientations.** `[FAILED]` Reciprocal determinants cancel, but positive
   paired energy leaves the already-formalized square `(g-g^(-1))^2|c_rho|^2`.
6. **Cancel completion anomalies over several primes.** `[FAILED]` Every completion normal current
   has the same negative orientation; positive combinations cannot cancel, signed combinations
   lose the inequality.
7. **Use aperture-uniform Bessel growth.** `[FAILED AS A PRODUCER]` Doubled Burnol jets already
   recover `exp(L(rho-1/2))` exactly. Uniform capacity is itself the right-zero exclusion.
8. **Derive fixed-head contraction from ambient isometry.** `[FAILED]` Explicit off-line zero
   transfer is unitary and strictly amplifies the fixed head. Tail-to-head transfer is real.
9. **Make the fixed atom a two-head extremizer.** `[FAILED AS AN INFERENCE]` Extended Sonin space
   has a large zero-head kernel; no source orthogonality or extremal theorem selects this atom.
10. **Use rational Cartier orbit rigidity.** `[FAILED AS A PRODUCER]` Corpus proves rational
    physical landing is equivalent to mate-gain one. Honest Mellin endpoint characters have
    nonintegral exponential dilation and need not be rational.
11. **Lift subexponential damping to an honest Burnol source.** `[PROVED]` Window estimate `(PS5)`
    yields `(PS6)` and gives the literal source `(PS1)`.
12. **Classify its exact regularity and Xi wall.** `[PROVED]` Equations `(PS9)`--`(PS16)` prove
    Gevrey-2 smoothness, zero analytic radius, and the exact inverse-completion wall `(PS4)`.
13. **Transport its positive flux through the existing Kummer Poisson--Green comparison.**
    `[FAILED AS A PHYSICAL DESCENT]` The source flux reaches the resolved Xi complex, where strict
    `D_1 D_0=0` holds. Fixed physical head evaluation does not descend through that homology.
    Existing corpus identifies the required Gamma/co-Poisson Hodge--Green boundary descent with
    horizontal neutrality, hence with RH. Positivity in the resolved carrier cannot be read as the
    scalar sign of `J_rho` without the singular boundary map isolated above.

## 8. Anti-theatre audit

- `X_y`, `D`, `C_p`, and `U_(y,rho)` are explicit.
- Source and Poisson subordination are constructed before any divisor is chosen.
- Both convergence and divergence directions are proved.
- The source uses actual Burnol prime windows, not a detached coefficient sequence.
- No RH, critical-line placement, same-fibre norm identity, source dagger, `J_rho<=0`, or physical
  landing is assumed.
- Existing first-trace Hilbert nonclosability is not renamed: `(PS10)` proves a distinct,
  stronger obstruction on the full prime-log smooth carrier.
- No RH claim is made. Singular physical boundary descent remains open.

## Lean formalization (partial, 2026-08-09)

Modules: `RHTower/BurnolPoissonSubordinateWall`, `RHTower/BurnolAllPrimeCompletionWall`,
`RHTower/BurnolPrimeLogSummability`.

| Paper item | Lean declaration |
|---|---|
| `(PS1)` | `burnolPoissonWeight`, `burnolPoissonWeight_pos` |
| `(PS6)`, `(PS7)` | `burnolSummable_poissonWeight_logPow` |
| `(PS9)`, `(PS10)` | `burnolNotSummable_poissonWeight_expGain` |
| `(PS3)`, `(PS14)` | `burnolPoissonInverseCompletionCoefficient`, `burnolPoissonInverseCompletionCoefficient_eq`, `norm_burnolPoissonInverseCompletionCoefficient` |
| `(PS15)` | `burnolSummable_poissonInverseCompletion_of_re_le_half` |
| `(PS16)` | `burnolNotSummable_poissonInverseCompletion_of_half_lt_re` |
| `(PS4)` | `burnolPoissonSmoothWall` |

The `u^{2k} e^{-2y sqrt u} <= C/u^2` domination that carries `(PS6)`--`(PS7)` is
`burnolPow_mul_exp_neg_sqrt_le`.

Still open in Lean: the Poisson subordination identity `(PS2)`/`(PS11)` and the extension-variable
source equations `(PS12)`--`(PS13)`.

## Gates

- [x] source-pure construction
- [x] internal corpus and failed-route audit
- [x] heavy conjecture/falsification loop
- [x] dependency-closed Hilbert and all-differential-domain proof
- [x] zero analytic-radius classification
- [x] coefficient-faithful multiplicity-leading inverse-completion wall
- [x] exact surviving operator category identified
- [ ] prove singular Gevrey-2 Poisson-Stokes boundary descent
- [ ] formalize after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — constructed Poisson-subordinate all-prime Burnol source, proved full prime-log
  smoothness with zero analytic radius, and proved its exact smooth inverse-Xi-completion wall.
- 2026-08-09 — first unconditional Lean layer built and umbrella-wired; see the Lean
  formalization table above for the exact declaration-to-equation map.
