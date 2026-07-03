# 26 — The Reversal: Outer Crossing as a Localization Transition of the Equilibrium Field

**Register: SEARCH** (identities (REV), (OSC), (ΞSUM) are [PROVED HERE] with full
derivations; measured verdicts pre-registered and archived in
`computations/AMP-RESULTS.md` runs 4–5). Task #138 — the attack on (AMP-mono)(iii),
the last open part of (SPUR-R) after doc 25. Entropy draw for this round: move =
*reverse*; collision domains = *ant-foraging*, *percolation*.

## 0. Setting

A_d = J^d_g hyperbolic of degree d with zeros 0 < α_1 < … < α_d (g ∈ LP₀, g(0) ≠ 0;
window recentering makes the relevant field one-sided), critical points c_i ∈ (α_i, α_{i+1});
τ = a + bi, b > 0. (AMP-mono)(iii): along the outer critical points, margin(c) =
q_d(c)/(c⁴ℰ(c)) crosses 1 exactly once. The *reverse* move: invert the field. Set

> y = 1/c,  β_k = 1/α_k,  Â(y) = y^d A_d(1/y)  (the reversed section, hyperbolic
> with zeros β_k),  F̂(y) = Σ_k (y−β_k)^{−1},  ℰ̂(y) = Σ_k (y−β_k)^{−2}.

Under x ↦ 1/x the polar-derivative chain (doc 23, pole 0) becomes the plain derivative
chain — the reversal swaps the lane's two chains.

## 1. The reversal identity [PROVED HERE]

At any critical point c of A_d (so Σ(c−α_k)^{−1} = 0):

1. (c−α)^{−1} = yβ/(β−y) = y − y²/(y−β); summing, 0 = dy − y²F̂(y), so the
   **transported equilibrium constraint** is F̂(y) = d/y.
2. (c−α)^{−2} = y²β²/(β−y)² and β²/(β−y)² = 1 + 2y/(β−y) + y²/(β−y)²; summing and
   using (1): **c⁴ℰ(c) = ℰ̂(y) − d/y²**.
3. q_d(c) = |τ|² − 2ad/y + d(d−1)/y², and d(d−1) + d = d², so

> **(REV)  margin(c) > 1 ⟺ ℰ̂(y) < |τ|² − 2ad/y + d²/y² = (d/y − a)² + b² = |F̂(y) − τ|².**

Copy/flip compares the **energy** of the reversed configuration with |field − τ|² at
the same point — an intrinsic statement about one charge configuration, with d, c, α
all absorbed. (Verified to 63–75 digits at every critical point, two carriers, three
degrees: P-C.)

## 2. The oscillator form and the theorem-m energy [PROVED HERE]

Let V(y) := Â(y)e^{−ay} (same zeros β_k). Then V′/V = F̂ − a and
(V′/V)′ = V″/V − (V′/V)², while F̂′ = −ℰ̂, so V″/V = (F̂−a)² − ℰ̂. By (REV):

> **(OSC)  copy at c ⟺ V″(y)/V(y) > −b² ⟺ (V″ + b²V)·V > 0 at y = 1/c.**

Copy = V locally sub-oscillatory at frequency b = Im τ; flip = super-oscillatory.
With the frequency-b oscillator energy E_b := b²V² + V′², one has
E_b′ = 2V′(V″ + b²V): **copy ⟺ E_b and V² co-move; flip ⟺ they anti-move** —
theorem-m's ODE energy monotonicity reappears verbatim in the reversed coordinates,
with the pair's height b as the frequency. No ODE is used or available (the carrier is
flowless); the oscillator is the comparison object, not an evolution law. (P-D: the
(OSC) verdict agrees with the margin verdict at every critical point, and the ordered
pattern shows exactly one copy→flip transition — both models, d = 16, 24, 40.)

## 3. The sum rule and the localization reading [PROVED HERE]

Define the **pole weights** ξ_k := y/(y − β_k) = (1 − β_k/y)^{−1} (scale-invariant:
functions of the ratios β_k/y only). Multiplying F̂(y) = d/y by y:

> **(ΞSUM)  Σ_k ξ_k = d at every transported equilibrium** — conserved along the
> whole critical-point sequence. Moreover S := Σ_k ξ_k² = y²ℰ̂(y), and (REV) reads
>
> **flip at c ⟺ S > (d − ay)² + b²y²  (≈ d², since ay ≪ d in the outer range).**

So the copy→flip crossing is a **delocalization → localization transition** of the
equilibrium field: with the ℓ¹-type budget Σξ = d fixed, copy holds while the weights
are spread (Σξ² < d²-dressing), flip when the near-neighbor weight dominates —
a participation-ratio criterion. The ant-foraging decomposition (trail = the dense
one-sided far field, all kernels decaying monotonically away from it; local = the gap
neighbors) and the percolation frame (the flip event as a monotone event of the
configuration) both point at the same mechanism: the constraint Σξ = d recycles weight
into the dominant pole as the equilibria march outward.

## 4. Measured verdicts (pre-registered; AMP-RESULTS runs 4–5)

- **P-C PASS** — (REV) exact to working precision everywhere.
- **P-D PASS** — (OSC) ≡ margin verdict pointwise; exactly one transition.
- **P-E REFUTED, load-bearing** — the log-gap sequence of the section zeros is NOT
  monotone on the outer half (violations ≈ 0.15d) although the crossing stays single:
  gap monotonicity is the WRONG mechanism; the smoothing comes from the equilibrium
  constraint, not from the zero spacing.
- **P-F** — the race is O(1): d·(log-gap) at the crossing ≈ 3.5–4.3 (equilibrium sits
  at ≈ 27% of its gap — the near-symmetrization made quantitative), far margin →
  ≈ 0.28: the margin does not decay to 0, it saturates below 1. Any proof must be
  constant-aware; asymptotics alone cannot separate the two sides.
- **P-H: full majorization REFUTED / dominant weight PASS** — the sorted weight
  vectors do NOT march up the majorization order (≈ half the outer pairs violate), so
  Schur-convexity in full strength is dead. But the **top weight ξ_max is strictly
  increasing along outer equilibria at ZERO violations**, and **S itself is strictly
  increasing at ZERO violations** (both models, d = 16, 24, 40).

## 5. The kernel, re-cut

> **(S-mono) [OPEN — replaces (AMP-mono)(iii)]:** along the outer transported
> equilibria, S_i = Σ_k (y_i/(y_i − β_k))² is strictly increasing. Since the dressing
> (d − ay)² + b²y² is monotone in y (elementary), (S-mono) ⟹ single crossing ⟹
> T = 1 ⟹ (SPUR-R) closes on one-sided-far carriers with doc 25.

Measured at zero violations; the measured mechanism is the dominant weight: ξ_max,i
increases monotonically (localization is monotone) while the lower spectrum
reshuffles. Proof shape suggested by the data:

1. **Dominant-weight lemma**: ξ_max = (1 − β_near/y)^{−1} is governed by the
   equilibrium's fractional position in its gap; the constraint F̂ = d/y +
   the one-sided far field force the position to drift monotonically toward the near
   pole (the θ ≈ 0.27 measurement). A local statement about one gap and the trail —
   attackable with the (TRAIL) monotonicity (sources one-sided ⟹ their kernel sum at
   the evaluation point decays outward, unconditionally).
2. **Remainder control**: with Σξ = d fixed and ξ_max split off, bound Σ_{k≠max}ξ_k²
   from below by the constraint (signed Cauchy–Schwarz; the right charges contribute
   ξ < 0, the trail contributes ξ ∈ (0,1) each — the budget d − ξ_max is spent on
   ≤ d−1 terms).
3. **Percolation coupling (wild route)**: show the flip event is monotone under
   adding charge density toward the accumulation point; then single crossing is a
   0–1-type threshold statement, constants-free.

Next experiment: chart ξ_max,i and the gap-position θ_i across carriers including the
u-plane #136 shape (one-sided-far, the theorem-track carrier of doc 24 §6 / DISC run
6), and probe the dominant-weight lemma's drift claim directly. Next object: the
θ-drift law — the equilibrium's fractional position as a function of the trail mass,
where the ant-trail kernel sum should give a closed-form monotone bound.

[ROUND 2 — doc 27: the θ-drift attack ran. PROVED: the weight flow η′ = −η(η−1)/c and
its power-sum hierarchy; the pole-removed smooth path S_{i+1} − S_i = ∫Φ̃′ with
Φ̃′ = −(2/c)Σw_k(η_k + p̃₁), w_k > 0; endpoint signs; the midpoint-push lemma θ < 1/2
under gap growth; the log-time Calogero representation. (S-mono) is reduced to (LEG),
one local leg-comparison integral. Measured: dip-then-rise + net positivity + gap
growth + θ-drift all at ZERO violations.]
