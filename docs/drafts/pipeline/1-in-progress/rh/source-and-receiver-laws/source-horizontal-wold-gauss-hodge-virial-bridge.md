# Source-horizontal Wold–Gauss–Hodge virial bridge

- **ID:** source-horizontal-wold-gauss-hodge-virial-bridge
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + OPEN PRODUCER
- **Source:** `rh-current-frontier-map.md` · Route-T prime-clock completion × Gauss Hodge mass × Route-P/Ward boundary language
- **Statement:** Literal finite Wold prime sums converge to the inverse-Euler Green carrier whose Euler response is Gauss Hodge mass; at Gauss depth one the coefficient transport is an explicit positive, cofinally divergent gauge.

## Goal

Construct a genuine cross-route source carrier rather than another RH receiver. Route T supplies a
coefficient-faithful finite prime deformation. Gauss supplies a label-faithful positive Hodge
current with exact critical radical. The missing operation is now a gauge-covariant arithmetic
Ward boundary law acting before the positive Hodge fold.

This card does **not** claim RH. It proves the exact bridge, kills two plausible shortcuts, and
isolates one harder producer with no hidden zero-side sign assumption.

## Gates

- [x] 0 → 1 in-progress: source-derived finite carrier, exact Gauss handoff, hostile no-go audit
- [ ] 1 → 2 fully-proven: prove gauge-covariant pre-zero Ward bound/annihilation theorem
- [x] Bridge formalized: `SourceHorizontalWoldGaussHodgeVirialBridge.lean`
- [ ] 2 → 3 RH formalized: blocked on producer, not Lean mechanics
- [ ] 3 → 4 publication-ready: blocked on unconditional RH closure

## Heavy-conjecture loop

1. **Conjecture: a singular/Dixmier trace can read the retained off-diagonal horizontal
   transport.**

   **FAIL.** Cyclic traces kill commutators. A fixed matrix-corner reader retains the transport but
   loses centrality. Current weak-Schatten trace theory supplies no coefficient-faithful noncyclic
   reader with the required source invariance.

2. **Conjecture: positive mean-square extraction of the source resolvent forces the critical
   wedge signs.**

   **FAIL.** Squaring folds the resolvent phase and cannot distinguish the negative high-order,
   low-shift wedge isolated by the literal Gauss-Hodge resolvent endpoint.

3. **Conjecture: the first missing Gauss iterate (`m=3`) follows cheaply from self-adjointness and
   the proved one-step/double-defect bounds.**

   **FAIL WITH POSITIVE SURVIVOR.** Expansion leaves the third reflected-ratio chain. Existing
   estimates control one weighted defect on the harmonic input, not the full length-three defect
   chain. The local propagated-iterate wall remains real.

4. **Conjecture: Route T's centered prime-clock profile already is the Gauss virial carrier.**

   **FAIL, THEN PIVOT.** If
   
   \[
     F(u)=\sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)!}
       \left(\frac1{2k+1}-1\right),
   \]
   
   then the centered profile omits the raw `sinh` mode. Completing it gives
   
   \[
     G(u)=F(u)+\sinh u
         =\sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)(2k+1)!}.
   \]
   
   This is the existing inverse-Euler Green profile, not a new duplicate definition.

5. **Conjecture: the completed finite Wold carrier reaches the Gauss Hodge shape without losing
   prime coefficients.**

   **PROVED.** At cutoff `N`,
   
   \[
     G_N(u)=F_N(u)+\sinh u
       =\sum_{n\le N} \frac{w_1(p_n)}{\log p_n}
          \sinh\!\left(u\frac{\log p_n}{\log p_N}\right).
   \]
   
   Hence every finite stage retains ordered prime labels and exact Wold coefficients. Lean proves
   `G_N(u)→G(u)` and also proves convergence of the coefficient-faithful finite responses
   
   \[
     G_N'(u)=\sum_{k\ge0}
       \frac{u^{2k}}{(2k)!}\,M_N(2k)
       \longrightarrow G'(u).
   \]
   
   Existing inverse-Euler mechanics gives `u G'(u)=sinh u`, so
   
   \[
     u^2G'(u)=u\sinh u.
   \]
   
   With `u=(log p)t`, literal Gauss Hodge mass is therefore
   
   \[
     H_{m,p}(t)=2a_{m,p}u^2G'(u),
     \qquad a_{m,p}=\operatorname{gaussReciprocalCharacterWeight}(m,p).
   \]

6. **Conjecture: centered Wold polar properness can replace annihilation of completed Gauss
   virial.**

   **FAIL WITH SHARP POSITIVE SURVIVOR.** Lean proves the exact reserve decomposition
   
   \[
     W_T(u)+\frac{\log2}{2}uG(u)
       =\frac{\log2}{2}u\sinh u,
   \]
   
   and
   
   \[
     uG(u)>0\quad\Longleftrightarrow\quad u\ne0.
   \]
   
   Thus centered Wold polar work is strictly smaller than completed virial at every off-center
   rate. Properness cannot silently supply the missing Hodge law.

7. **Conjecture: Gauss and Wold coefficients differ only by a bounded harmless gauge.**

   **FAIL WITH EXACT CLASSIFICATION.** At actual Gauss depth one,
   
   \[
     a_{1,p}=\Gamma_p\,\frac{w_1(p)}{\log p},
     \qquad
     \Gamma_p=
       \frac{(\log2)(p-1)p^3}{(p+1)^2(\log p)^2}>0.
   \]
   
   Lean proves the quantitative lower bound
   
   \[
     \Gamma_p\ge \frac{\log2}{18}p
   \]
   
   and `Γ_(p_n)→∞` along ordered primes. Therefore old dominated-convergence arguments cannot
   transport the Gauss packet through the Wold limit. The coefficient mismatch is the new hard
   arithmetic content, not normalization noise.

8. **Conjecture: nevertheless a literal two-scale finite source approximates each Hodge label.**

   **PROVED.** Define
   
   \[
     \mathcal V_{N,m,p}(t)
       =2a_{m,p}(t\log p)^2G_N'(t\log p).
   \]
   
   Lean proves, for every Xi divisor copy `q` and prime label `p`,
   
   \[
     \mathcal V_{N,m,p}(t_q)\longrightarrow H_{m,p}(q).
   \]
   
   At `m=1` the finite formula retains the exact factor
   `2 Γ_p (w_1(p)/log p)`. This is the first literal nested Wold–Gauss source approximation to the
   Hodge current; it is not defined from the desired sign or from an off-line selector.

## Paper proof of surviving theorem `[PROVED HERE]`

1. Existing finite Taylor resummation gives the displayed formula for `F_N`. Adding `sinh u`
   cancels the unique raw subtraction term, proving the exact prime-sum formula for `G_N`.
2. Existing all-order moment convergence `M_N(2k)→1/(2k+1)`, together with the uniform mass bound
   `M_N(2k)≤M_N(0)<2` eventually, permits dominated convergence against the `cosh |u|` series.
   This proves `G_N'(u)→G'(u)` coefficientwise and after summation.
3. The inverse-Euler identity `uG'(u)=sinh u` gives `u²G'(u)=u sinh u`. Substitute this into the
   already-proved reciprocal-character formula for Gauss Hodge mass.
4. Every term of `uG(u)` is nonnegative:
   
   \[
     uG(u)=\sum_{k\ge0}
       \frac{u^{2k+2}}{(2k+1)(2k+1)!}.
   \]
   
   The `k=0` term is `u²`, so the sum is strict exactly for `u≠0`. Algebra then gives the reserve
   decomposition and strict no-go.
5. Unfolding the depth-one Gauss residue, Fisher density, and Wold coefficient gives the exact
   `Γ_p` formula. For `p≥2`, use `p-1≥p/2`, `p+1≤3p/2`, and `log p≤2√p`; hence
   `(p+1)²(log p)²≤9p³`, yielding `Γ_p≥(log2/18)p`. Ordered primes tend to infinity, so `Γ_(p_n)`
   does as well.
6. Multiply `G_N'(t log p)→G'(t log p)` by the fixed literal Gauss coefficient and square clock.
   The limit is exactly `H_{m,p}` by step 3.

## Exact open producer

The next theorem is not “prove positivity” and not “find another endpoint.” It is:

> **Gauge-covariant source Ward law.** On the literal finite prime–polar–Gamma carrier, retain both
> reflection orientations and the two prime scales until after applying the depth-one gauge
> `Γ_p`. Prove a boundary identity or uniform partial-mass bound for the finite responses
> `V_(N,1,p)(t)` which survives the simultaneous Wold cutoff and Gauss prime cutoff.

Why this closes RH: labelwise limits are exactly `H_(1,p)(q)`. Existing Lean proves that the
all-prime Hodge family is summable exactly when the centered divisor rate is zero, and that this
for every divisor copy is RH. A source-derived uniform nonnegative partial-mass bound therefore
forces every retained rate to vanish.

Hostile constraints:

- no bounded scalarization can absorb `Γ_p`, since `Γ_(p_n)→∞`;
- no cyclic trace of a commutator can see the required oriented transport;
- no reflection sum may be taken before the Hodge fold, because it erases the horizontal class;
- no theorem may define the finite response through Xi zeros, an off-line selector, or assumed
  Hodge signs;
- a valid proof must use the actual Gauss codiagonal/residue law or an exact prime–Gamma boundary
  counterterm to neutralize gauge growth.

Most plausible Frankenstein mechanism is a two-scale anomalous Ward identity: Route T supplies
the inner inverse-Euler Green response, Gauss supplies the divergent outer gauge and codiagonal,
and Route P's completed boundary calculus supplies the counterterm. Required novelty is exact
gauge cancellation before positivity, followed by Fatou/monotone passage after positivity.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldGaussHodgeVirialBridge.lean`

Verification:

- direct `lake env lean` — PASS
- targeted `lake build GaloisForLFunctions.RHTower.SourceHorizontalWoldGaussHodgeVirialBridge` — PASS
- formal lint — PASS
- axiom audit on five capstones — only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import wired; no umbrella build run

Main declarations:

- `sourceHorizontalWoldPrimeClockCompletedFinitePrimitive_eq_primeSum`
- `tendsto_sourceHorizontalWoldPrimeClockCompletedFinitePrimitive`
- `tendsto_sourceHorizontalWoldPrimeClockCompletedFiniteResponse`
- `sourceHorizontalWoldEulerGreenProfile_mul_pos_iff`
- `sourceHorizontalWoldPrimeClockPolarRateWork_add_eulerGreenReserve`
- `sourceHorizontalWoldPrimeClockPolarRateWork_lt_eulerGreenVirial_iff`
- `gaussHodgeMassCurrent_eq_woldEulerGreenResponse`
- `gaussReciprocalCharacterWeight_one_eq_wold_gauge`
- `gaussWoldDepthOneCoefficientGauge_linear_lower`
- `tendsto_gaussWoldDepthOneCoefficientGauge_nthPrime`
- `tendsto_gaussWoldFiniteSourceVirialResponse`
- `gaussWoldFiniteSourceVirialResponse_one_eq_gaugedWold`

## No-go closure

- **Exact killing mechanism:** completion restores a strict positive Green reserve; coefficient
  comparison then introduces a cofinally divergent gauge.
- **Strongest positive survivor:** literal finite two-scale Wold–Gauss response converging
  labelwise to Hodge mass, with exact coefficient gauge and quantitative divergence.
- **New insight:** missing producer is a gauge-covariant boundary law before the Hodge fold, not a
  new positivity cone, trace reader, or bounded completion.
- **Status:** paper proof dependency-closed; Lean module direct-check green. RH producer remains
  open and explicitly named.

## Log

- 2026-08-12 — Singular-trace, mean-square, and cheap `m=3` pivots rejected.
- 2026-08-12 — Wold completion identified with existing inverse-Euler Green profile; no duplicate
  carrier introduced.
- 2026-08-12 — Exact Gauss Hodge Euler bridge, strict Green reserve, and depth-one coefficient
  gauge proved in Lean.
- 2026-08-12 — Gauge linear lower bound/divergence and finite two-scale source-to-Hodge convergence
  proved in Lean; gauge-covariant Ward law isolated as next producer.
