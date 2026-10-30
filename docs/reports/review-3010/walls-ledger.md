# Walls ledger

Status: 30 October 2026, corpus `4089dad808` plus working tree. **No core wall is crossed.**

**Three families of walls**, one for each property a crossing input must supply:

- **Σ — the critical sign.** A positivity statement that must hold with zero margin.
- **Π — square-root precision.** A count or cancellation that must be exact at x^{1/2}.
- **Γ — selection.** The statement must hold for ζ and fail for its gauge twins, at the trivial gauge point.

Each family is forced by theorems (§1). The three are read off one object in §5.

**Solved faces:** sub-spacing Hodge index; complete Weil positivity at every fixed overlap with its full conductor spectrum; twin resolution at bounded overlap; the rank-eight theta Hankel section; fixed conductor packets to (log N)^{1/40} ([S] to (log N)^{1/19}).

**Sharpest open faces:**

- **Σ1b** — signed payment of the successor shells jointly with the pole.
- **Σ7** — a same-point identity.
- **Σ5** — finite Krein index.

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-gos](../rh-killed-routes.md) · [working log](../../../logs/review-3010-rev4-research-2026-10-30.md). No builds were run. Evidence labels [L]/[K]/[S]/[P] as in the frontier map; (inference) marks this review's interpretation.

| Strength tag | Meaning |
|---|---|
| [RH] | Equivalent to RH |
| [FS] | Finitely many off-line zeros; implies LH |
| [LH] / [QRH] | Lindelöf; zero-free strip |
| [C%] | Critical-line proportion |
| [sub] | Open, implies no classical conjecture by itself |

## 1. Why there are exactly three families

| Family | Forcing theorems | What any crossing input must do |
|---|---|---|
| **Σ** | Extension no-go (`extension_forces_positivity`); odd Markov form never subcritical; E₁(c) → 0; Hecke state PD exactly from s = 1/2 | Hold at the boundary of a positivity cone, with no gap to spend and no monotone continuation from a positive range. |
| **Π** | `deciding_input_necessary_properties`; producers precision-blind; κ = 0 ⟺ one-sided √x log²x count | Separate a from a + εn^{−η} for every η < 1/2; no known producer law does. |
| **Γ** | `threeQuarters_le_of_gaugeInvariant_bound`; locality and pointwise-closed statements twin-blind; sub-spacing positivity holds for every sign twin; Λ ≥ 0 + FE + entire completion allows off-line zeros | Break the gauge symmetry at the trivial point using discreteness of the prime support and the simple pole. |

(inference) The three are independent away from the endpoint:

- Bounded-overlap complete positivity is selective and fixed-resolution, but not critical.
- The Krein index is critical and precise by construction, but has no producer.
- Integrality producers are selective through Λ∗1 = log, but reach only Chebyshev precision.

## 2. Family Σ — the critical sign

| Wall | Content | Status |
|---|---|---|
| **Σ1 Growing-overlap complete positivity** | Positive at every fixed c, low spectrum = conductor modes with energies E_m(c) ≥ 0 [K/L]. Fixed packets positive to (log N)^{1/48} uniformly, 1/40 along schedules [L], 1/19 [S]. RH ⟺ positivity whenever c⁴/log N → ∞, any C² profile with ∫φ ≠ 0 [L]. Floor E_m(c) ≍ c⁻⁷ for m ≤ c, constant above the overlap scale [L]. | Fixed c: **solved**. c ≫ (log N)^{1/4}: **open [RH]**. In between: open, strength unknown (inference). |
| **Σ1a Defect-only confinement** | Unit vectors with defect ≤ γ + (k+1)log2 + log4 + 5 escape every conductor set below 2^k (`eventually_exists_unit_vector_escaping_conductors`) [L]. | **Exact boundary:** capture from the defect alone needs exponential conductor cutoffs. |
| **Σ1b Shell payment** | Reserve W ≥ ac⁻⁷D − Cc⁹‖x‖², negative vectors D ≤ C′c¹⁶ [L]. Any separate one-sided payment of the shells costs ≥ κc²/ε, hence c⁹ at the reserve fraction [S, in progress]. On conductor modes the shells repay log(2πc) exactly; continuum shells are only the pole charge [S]. | Separate payment: **exact boundary**. Joint signed payment off the conductor span with log c loss: **open [sub]**. |
| **Σ2 Extension** | A nondecreasing minorant of λ(L) nonnegative once forces λ ≥ 0 everywhere; soft tools move positivity only downward in L. | **Exact no-go.** |
| **Σ3 Criticality of the arithmetic Markov form** | Odd form never subcritical; folded supersolutions excluded; archimedean place is Z-type, every obstruction is prime. μ(A) ≤ K exp((11/2)A − πe^{2(A−2)}) [L]. | **Open [RH]:** a positive supersolution of the full nonlocal generator. |
| **Σ4 Rank and order uniformity** | Rank-eight theta Hankel PSD for 0 < a < 1/2 [L]. Finite native tail = 2·(Gram-square mass) − 2·(local flux) [L]. No rank-uniform fraction of the new diagonal [K]. Heated orthant signs at all ranks; all-rank sign ⟺ RH. | Each finite rank: **A**. All ranks: **open [RH]**. |
| **Σ5 Infinite genus / finite index** | κ = 2·#sector zeros; κ < ∞ ⟺ finite off-line support ⟺ bounded heat counts ⟺ eventual criticality [L]; κ < ∞ ⇒ LH. Finite ζ index forces infinite index for every single-prime flip [L]. Weil's form has finitely many negative directions at each aperture. | **Open [FS].** |
| **Σ6 Realization** | Weil distribution = CCM operator trace; archimedean part = Sonin + square − anticommutator. Complete Deninger carriers have bounded generators. Lossless and Ising realizations need zero indexing or have a unit gap. Commutative realization of ζ has no dynamics; the free one has the wrong entropy; integrality forbids super-conformal roofs [P]. | **Open [RH]**; a Hölder mixing realization would give [QRH] [P]. |
| **Σ7 Explicit image** | Every line-calibrated explicit statistic is the Weil form W; S = W + Δ, Δ = ½Σm abs(F(z) − F(z̄))² ≥ 0. Holomorphic clocks have Cesàro excess 0 or ∞. Strip-holomorphic carriers vanishing on critical configurations vanish on all reflection-invariant ones; three-lines law: no depth-uniform quantum near the line [L]. | **Exact boundary:** same-point information needs a non-holomorphic operation. **Open [RH]:** an arithmetic same-point identity. |
| **Σ8 Quantum** | Collision charge O ∈ 2ℕ; O = 0 ⟺ critical; N ≤ N₀ + O. Over 𝔽_q unitary ⟺ O < 2; the golden datum has O = 2 [L]. | RH has integer margin 2 here. **Open [RH]:** source bound O < 2. **Open [C%]:** O ≤ cN, c < 1/4. |

**Σ1 phase diagram (overlap axis).**

| Overlap c | State | Selective? |
|---|---|---|
| ≤ c★ (fraction of spacing) | Hodge index proved, every N [L] | No: holds for every sign twin |
| Fixed | Positive definite, attained bottom E₁(c) [K/L] | Yes for Liouville and cofinite flips; single flips need c₀(p) ≍ p^{1/7} |
| (log N)^α, packets | α < 1/48, 1/40 [L]; 1/19 [S] | Packets only, not all vectors |
| Reserve | Gamma survives while c⁸ = o(log N) [L] | — |
| ≫ (log N)^{1/4} | RH-equivalent [L] | — |

## 3. Family Π — square-root precision

| Wall | Content | Status |
|---|---|---|
| **Π1 Global law** | κ = 0 ⟺ ψ(x) − x ≤ C√x log²x ⟺ odd Liouville upper count [L/S]. | **Open [RH].** |
| **Π2 Deciding input** | A Count-sufficient criterion rejects Liouville, separates a from a + εn^{−η} (η < 1/2), uses unbounded aperture; Λ + εn^{−η} satisfies PNT and every short-interval law past 17/30 [S]. Count(a) ⟺ a − 1 ∈ 𝒬 [K]. | **Exact boundary.** |
| **Π3 Producer cost** | Adams mixed-jet multiplicity r on the q-torsion locus costs support 2^{qr}, sharp [L]. Balanced factorial ratios cost (2log2 − ε)mn [L]. Bézout/Riemann–Roch on 𝔾_m are linear; approximate integer vanishing is divisibility; twist towers collapse to proper prime powers [L]. Over 𝔽_q Stepanov reaches √q. | Boundaries **exact**; a square-root producer over ℤ: **open [RH]**. |
| **Π4 Gamma reach** | Gamma reserve pays Euler heads p ≤ Y while 32√Y log Y ≤ log A, so up to Y ≈ (log A)²; Euler costs are not summable, so no depth pays the first prime layer; the remainder needs prime cancellation [L]. Prime and square coefficient masses diverge; cubes and higher powers have one Gamma budget [K]. | **Exact boundary** (Σ → Π bridge). |
| **Π5 Dispersion / parity** | No Type-II dispersion below the quadratic horizon for coherent prime blocks; every short-window or balanced saving is a zero-free strip; 5/6 strip ⟺ R = O(N^{5/3+ε}) [K]. | **Open [QRH]** and up. |
| **Π6 Depth visibility** | Single-horizon pole charge is depth-blind; window modes see depth through N^{κ−Re z}M^{κ+Re z} [L]; orbit correlation ≤ Ke^{σt} ⟺ zero width ≤ σ [L]; refutation finite, confirmation not. | **Exact boundary**; the amplifier exists, a subexponential bound does not. |
| **Π7 Amplifier rank** | Orthogonal families on π(x) phases have ≥ binom(π(x)+k−1, k) members, cancelling the moment gain; fixed-loss amplification needs an identity, not counting [P]. | **Boundary [P]**; a non-envelope amplifier over ℤ: **open [RH]**. |
| **Π8 Classical density layer** | Guth–Maynard; density hypothesis on σ ≥ 5/6; VK; 0.6725; 3/4-or-near-line dichotomy; Λ_dBN < 1/8 [L]. | **Formalized.** LH, DH: open; LH follows from Σ5. |
| **Π9 Exceptional zeros** | Uniform Dirichlet zero-free region except real zeros of real characters [L]. | **Open [Siegel].** |

## 4. Family Γ — selection

| Wall | Content | Status |
|---|---|---|
| **Γ1 Trivial gauge point** | θ_μ(0) = Θ; typical exponent 1/2; RH ⟺ the trivial point is typical; gauge-invariant majorants ≥ 3/4; quadratic Dirichlet twins ≤ (2 + Θ)/6; a universal gauge floor 1/2 would force Θ = 1 [L]. | **Open [RH].** |
| **Γ2 Twin resolution** | Bounded overlap rejects Liouville and every cofinite flip [L]; single flips need c₀(p) ≍ p^{1/7} [L]; every nonempty finite flip set has ≥ r negative eigenvalues for c ≥ c₀(r) [S]; finite ζ index ⇒ every p-flip has infinite index; unconditionally ζ or the p-flip has infinite index [L]; ζ and Liouville atomic pole indices differ by one square in an explicit window [L]. | Bounded overlap: **solved**. Uniform in p at growing overlap: **open [RH]**. |
| **Γ3 Twin-blindness of soft structure** | Locality and pointwise-closed statements are twin-blind (twins are Bohr limits of vertical shifts); sub-spacing Hodge index holds for every sign twin; multiplicativity + polar matching + maximal gap 2log2 does not select ζ [L]. | **Exact boundary.** |
| **Γ4 Hecke invariance** | RH ⟺ collided form Hecke invariant ⟺ Hecke similitude ⟺ W = collided [L]. | **Open [RH].** |
| **Γ5 Source identification** | Λ ≥ 0, Euler product, exact FE and entire order-one completion admit off-line zeros, with a continuous Λ-measure and a triple pole at s = 1 [L]. Simple-pole class = ζ; a positive measure with the FE is Riemann's prime measure [L]. | **Exact boundary:** selection must use discreteness of the prime support and the simple pole. |

## 5. How the walls interlock

| Bridge | Joins | Consequence (inference) |
|---|---|---|
| κ = #right zeros = Hodge defect; κ = 0 ⟺ one-sided count | Σ5 = Π1 | At the endpoint a critical sign and a precise count are one statement. |
| κ < ∞ ⟺ bounded heat counts ⟺ eventual criticality ⇒ LH | Σ5 → Π8 | The weakest structural target that implies a first-rank conjecture. |
| Finite ζ index ⇒ every p-flip infinite index | Σ5 = Γ2 | Finite index is selective by itself. |
| Gamma reach (log A)² for Euler heads | Σ3 → Π4 | The archimedean reserve pays primes absolutely only to a square-logarithmic depth; beyond it, positivity needs square-root cancellation. |
| Hecke state PD ⟺ s ≥ 1/2; prime Poisson measure ≪ Haar ⟺ s > 1/2 | Σ = Γ = Π | The critical line is the Kakutani threshold of a product measure on the gauge torus. |
| RH ⟺ W = collided; collided read from theta prefixes | Σ7 = Γ4 | The multiplicative reading (primes) and the additive reading (theta) of one divisor must agree. |
| Separate shell payment costs c²/ε | Σ1b | Shells, where successor and dilation meet, must be paid with their sign. |
| Gauge-invariant data ≥ 3/4; typical 1/2 | Γ1 → Π | Precision must be spent at one point of the gauge torus, not on average. |

**The common object** (inference, from the bridges above). Weil's correlation lives on the dilation group ℚ^×_{>0}, whose dual is the prime (gauge) torus.

- **Σ** is its Bochner positivity.
- **Γ** is the location of the trivial character on that torus.
- **Π** is the Kakutani threshold s = 1/2 of the prime Poisson measure, where square-root precision sits.

The same divisor has an additive reading (theta, successor) and a multiplicative reading (primes, dilation), and every wall is a form of their comparison. Shells are the comparison inside the complete matrix. The collided form is the comparison in the polarization.

## 6. Status by face

"Solved" means the stated face is answered; it never means a route is closed.

| Face | Wall | Status |
|---|---|---|
| Sub-spacing Hodge index, ζ and twins | Σ1, Γ3 | **Solved [L]**, not selective |
| Complete positivity at fixed overlap, conductor spectrum | Σ1 | **Solved [K/L]** |
| Fixed packets at growing overlap | Σ1 | **Solved to (log N)^{1/40} [L]**, 1/19 [S] |
| Defect-only capture | Σ1a | **Exact boundary [L]** |
| Separate shell payment | Σ1b | **Exact boundary [S]** |
| Signed joint shell–pole payment | Σ1b | **Open [sub]** |
| Positivity at c ≫ (log N)^{1/4} | Σ1 | **Open [RH]** |
| Extension of positivity ranges | Σ2 | **Exact no-go** |
| Ground state of the full nonlocal generator | Σ3 | **Open [RH]** |
| Rank-eight theta section | Σ4 | **Solved [L]**; rank nine: A |
| All-rank flux domination | Σ4 | **Open [RH]** |
| Finite Krein index | Σ5 | **Open [FS]** |
| Realization without zero indexing | Σ6 | **Open [RH]** |
| Explicit image of same-point sums | Σ7 | **Exact boundary [L]** |
| Arithmetic same-point identity | Σ7 | **Open [RH]** |
| Collision quantum O < 2 | Σ8 | **Open [RH]**; O ≤ N/4 **open [C%]** |
| Producer cost (Adams, factorial, Bézout) | Π3 | **Exact boundary [L]** |
| Gamma reach for Euler heads | Π4 | **Exact boundary [L]** |
| Type-II horizon | Π5 | **Exact boundary**; strips open [QRH] |
| Amplifier rank | Π7 | **Boundary [P]** |
| Classical density layer | Π8 | **Formalized [L]** |
| Bounded-overlap twin resolution | Γ2 | **Solved [L]** |
| Uniform selection at growing resolution | Γ2 | **Open [RH]** |
| Exponent at the trivial gauge point | Γ1 | **Open [RH]** |
| Hecke invariance | Γ4 | **Open [RH]** |
| Source identification by Λ ≥ 0 + FE | Γ5 | **Exact boundary [L]** |
