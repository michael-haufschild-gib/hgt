# Route-unification ledger

Status: 30 October 2026, corpus `4089dad808` plus working tree.

**The 32 live routes, 17 candidates, PW-B and the route-like theory programmes are faces of three core problems:**

- **U-Σ, critical positivity:** a positivity statement with zero margin.
- **U-Π, the square-root count:** a one-sided count exact at x^{1/2}.
- **U-Γ, selection at the trivial gauge point:** a statement true for ζ and false for its twins.

The corpus proves exact identifications between the three at their endpoints (§2). §3 shows that all three are readings of one object.

Links: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [summary and next questions](obstacles-summary.md) · [frontier map](../rh-current-frontier-map.md) · [working log](../../../logs/review-3010-rev4-research-2026-10-30.md). Evidence labels as in the frontier map; (inference) marks this review's interpretation.

## 1. The three core problems

### U-Σ — Critical positivity

**Canonical forms:**

- The complete atomic Weil matrix is positive along c_N with c_N⁴/log N → ∞ (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`) [L].
- The restricted ground minimum satisfies μ(A) ≥ 0 at every aperture.
- The odd Markov form of Riemann's kernel has a positive supersolution of the full nonlocal generator.
- Weil's form equals the collided form (`riemannHypothesis_iff_W_eq_collided`) [L].

**Why it is critical:**

- E₁(c) → 0, with floor c⁻⁷ on the conductors m ≤ c.
- μ(A) decays doubly exponentially; the odd form is never subcritical.
- The Hecke state is PD exactly from s = 1/2.
- Monotone minorants cannot extend positivity.

**Faces:** HF, SRT, AIP, ACS (atomic branch), SC, RW, EWU, OWU, ACT, CHMD, SZ, FU, CFC, RP, PA, TG, RN, LI, TH, TT, LA, WD, HCF, GTA, DR, EGC, MSC, PTR, W1C; programmes HEF, SSH, APD, APol/CDG, AES/RBG, CCM, Deninger.

### U-Π — The square-root count

**Canonical form:** κ(K_ζ) = 0 ⟺ ψ(x) − x ≤ C√x log²x eventually [L]; equivalently the odd Liouville upper count.

**Why it is a precision problem:**

- Any criterion implying the count separates a from a + εn^{−η}, η < 1/2; every producer law in the corpus holds for both.
- Integrality over ℤ produces Chebyshev precision: Adams jets cost 2^{qr}, factorial ratios 2log2.
- The Gamma reserve pays primes absolutely only up to (log A)².
- Orthogonal families over π(x) phases cancel their own gain [P].

**Faces:** WL, MC, PBM, RB, JAS, CTF, ACS (effectivity branch), SRT (tower branch), SC, APF, EWJ, FEL, WBF; programmes HKT/AKLT, ALG, AOG/SSIC, THIM/BVI, ART.

### U-Γ — Selection at the trivial gauge point

**Canonical forms:**

- The Möbius gauge exponent at 0 equals its typical value 1/2 [L].
- The collided polarization is Hecke invariant [L].

**Why it is a selection problem:**

- Gauge-invariant majorants are ≥ 3/4 at 0; the trivial point is never better than typical.
- Locality, pointwise closure and sub-spacing positivity are twin-blind.
- Λ ≥ 0 with the exact FE and an entire completion admits off-line zeros [L].

**Faces:** MC, PM/PW-B, BAG, XN, BSH, CDC, HJ, IRK, PCS, RFHM, SEC; programmes Hedenmalm, BGG.

**Solved part [L]:**

- At bounded overlap, selection is a theorem: Liouville and every cofinite flip are rejected.
- The simple-pole class is ζ; a positive measure with the FE is Riemann's prime measure.

**Open part:** uniformity. Single prime flips need overlap ≍ p^{1/7}, and the trivial point is one point of a torus on which averages say nothing.

## 2. Proved identifications between the core problems

| Identity [L] | Joins | Content |
|---|---|---|
| `negIndex_zetaKernel_eq_two_mul`; `riemannHypothesis_tfae_zetaKernel` | U-Σ = U-Π | The index of the Weil kernel counts the zeros in a sector; index zero is the one-sided count. |
| `zetaKernel_finiteIndex_tfae` | U-Σ = U-Π (weakened) | Finite index ⟺ finite off-line support ⟺ bounded heat counts ⟺ eventual criticality; implies LH. |
| `negIndex_flip_eq_top_of_finite`; `negIndex_zetaKernel_eq_top_or_flip` | U-Σ = U-Γ | Finite ζ index forces every single-prime flip to infinite index; ζ or the flip is infinite unconditionally. |
| `riemannHypothesis_iff_collided_hecke_invariant`; `riemannHypothesis_iff_W_eq_collided` | U-Γ = U-Σ | Hecke invariance, a symmetry, is the sign. |
| `heckeState_kakutani_wall`; `riemannHypothesis_iff_exists_affine_posDef` | U-Σ = U-Γ = U-Π | The critical line is the PD threshold of the integer successor on Aff(ℚ) and the Kakutani threshold of the prime Poisson measure on the gauge torus. |
| `threeQuarters_le_of_gaugeInvariant_bound`; `gaugeExponent_moebius_trivial` | U-Γ = U-Π | The square-root exponent must be certified at one specified gauge point. |
| `finiteEulerGamma_negative_dimension_le`; `not_summable_primeEulerMixedWeightTotal` | U-Σ → U-Π | Archimedean positivity pays primes up to (log A)²; the rest needs square-root cancellation. |
| `zeta_orbitCorr_rate_iff_zetaZeroWidth_le` | U-Σ ↔ U-Π | Any growth rate σ of the scaling orbit correlation reads the zero width: the amplifier exists. |

(inference) These are endpoint identities. Away from the endpoint the problems separate: a route can be selective without being critical, or critical without being precise. The identities do not transfer partial progress between faces.

## 3. The one object behind the three problems

(inference, assembled from the identities in §2)

**Reading 1: Weil's correlation on the dilation group.** Weil's correlation is a function on ℚ^×_{>0} ≅ ⊕_p ℤ; its dual is the prime (gauge) torus 𝕋^{primes}.

| Property | Reading on the gauge torus | Corpus anchor [L] |
|---|---|---|
| U-Σ | The Fourier transform of Weil's correlation is a positive measure (Bochner) | RH ⟺ PD on dilations, or on one two-prime lattice |
| U-Γ | Twins are translates by characters χ of ℚ^×; ζ is the trivial character | Hecke-extremal PD states are twisted Haar states (`heckeExtremal_iff`) |
| U-Π | s = 1/2 is where the prime Poisson measure turns from absolutely continuous to singular over Haar | `heckeState_kakutani_wall` |

**Reading 2: two readings of one divisor.**

- **Additive reading.** The same-point (collided) form S is the limit of integer theta-prefix readings; the theta function is the successor/Poisson side.
- **Multiplicative reading.** The Weil form W is the explicit formula over primes; it is all any line-calibrated explicit formula can compute (HEF).

RH ⟺ S = W. The gap S − W = Δ ≥ 0 lives on off-line zeros. Inside the complete matrix the same comparison sits in the successor shells n = km + h:

- **Integrality of the shift** repays the logarithm on conductor modes.
- **The continuum average of the shells** is only the pole charge.

| Core problem | Form of the additive/multiplicative comparison |
|---|---|
| U-Σ | W ≥ 0 ⟺ S − W vanishes; shells must be paid with their sign |
| U-Π | ψ(x) − x: multiplicative count against additive measure, at √x |
| U-Γ | The trivial point is the additively invariant point; successor- and dilation-invariant forms retain only pole and Haar |

## 4. Each route as a face

**Supplies** lists what the route has; **Lacks** what it must produce. "Selective (bounded)" means selection at bounded resolution only.

| Route | Core object | Supplies | Lacks | Endpoint identity |
|---|---|---|---|---|
| HF, SRT, AIP, ACS-atomic | Complete Weil matrix | Selective (bounded); full conductor spectrum at fixed c | Critical | c⁴/log N → ∞ receiver |
| SC | Cross-fibre Krein index | Critical and precise by construction | Producer (index ceiling) | κ = 0 |
| RW, EWU, OWU | Restricted ground minimum | Selective odd witnesses at fixed radii | Critical | μ(A) > 0 ∀A |
| ACT, CHMD | Markov / Doob form | Exact ground-state structure; obstructions are prime | Critical | Positive supersolution |
| SZ, FU, CFC, RP, PA, LI, TG, RN | Boundary currents, histories, operator traces | Exact receivers | Critical | One-sided current or history floor |
| TH, TT, LA, WD, HCF, GTA | Theta/heat Hankel and Jensen data | Moment structure; finite-rank certificates | Rank/time uniformity | All-rank sign; Λ_dBN = 0 |
| WL, PBM, RB, JAS, CTF | Prime/Möbius error | Selective (divisor collapse at 0) | Precise | One-sided count |
| MC | Möbius gauge exponent | Precise form of the target | Selective at 0 and precise | θ_μ(0) = 1/2 |
| ACS-effectivity | Scaling surface | Riemann–Roch, ampleness on a subsurface | Precise (infinite genus) | Hodge defect zero |
| PM/PW-B, BAG, XN | Escape states, recurrence, Newton discs | Analytic objects | Selective | Every escape state visible |
| HEF | Same-point vs explicit sums | Exact quantum O ∈ 2ℕ; calibration rigidity | A source for the same-point side | O < 2 |
| SSH | Successor shells | Lattice repayment on conductor modes | Signed payment off the conductor span | Reserve with log c loss |
| APD, APol/CDG | Aff(ℚ) states; polarization | Exact threshold at s = 1/2; theta-prefix readings | Critical (at threshold) | PD extension; Hecke invariance |
| HKT/AKLT, AOG/SSIC, ALG | Krein index; visibility; Lorentzian | Exact counting form; the amplifier | Producer | κ = 0; subexponential orbit bound |
| ART | Realizations and amplifiers | Obstructions to realizations [P] | Non-envelope amplifier | — |
| Candidates APF, EWJ, FEL, WBF | Exhaustion, admission, balance | Receivers | Precise | — |
| Candidates BSH, CDC, HJ, IRK, PCS, RFHM, SEC | Pre-divisor forcing | Receivers | Selective | — |
| Candidates DR, EGC, MSC, PTR, W1C | Roots, contours, transport, realization | Receivers | Critical | — |

## 5. How one object supplies all three over 𝔽_q

| Property | Over 𝔽_q | Over ℤ, per the corpus |
|---|---|---|
| **Critical** | The Rosati/Hodge index on C × C is exact; purity is the boundary case, so no margin is needed. Every circle-calibrated explicit formula is the Rosati pairing [L]. | The explicit formula computes the Krein form W; no involution makes it a Hilbert form without RH. |
| **Precise** | Finite genus: abs(N_m − q^m − 1) ≤ 2g q^{m/2}; any constant suffices, since eventual Hasse–Weil is Hasse–Weil. Stepanov reaches √q. | Infinite genus: no radical, no finite constant. The amplifier exists (rate = depth), but there is no constant to amplify. Integrality reaches Chebyshev precision. |
| **Selective** | Frobenius is one endomorphism; the collision charge of an impure datum is ≥ 2 and the golden datum attains 2. | No Frobenius among self-maps of ℕ; the trivial point is never better than typical. |

(inference) Over 𝔽_q one object, the Frobenius graph Γ_F ⊂ C × C, supplies all three: its intersection numbers carry the sign (Hodge index), the count (Γ_F·Δ = N₁) and the selection (F is this curve's Frobenius). Over ℤ the corpus has:

- the surface (scaling surface);
- the intersection form (Weil form);
- the Hecke correspondences (similitudes of the defect);
- the count (index = #right zeros).

It lacks a correspondence whose self-intersection is bounded by an independent invariant, i.e. a Rosati involution for the additive/multiplicative pair.

## 6. What a unified input must look like

(inference, constrained by the theorems above)

1. **Positivity by identity.** The sign must come from an identity (Hodge index, Plancherel density, Fourier tail), not from coercivity with margin. Σ1, Σ2 and Σ3 exclude every estimate that spends a margin.
2. **A same-point source.** It must reach S, not only W: through a non-holomorphic operation (mean square, modulus, Laplacian, conjugation of the divisor), or through an integer-valued carrier with quantum 2.
3. **Discreteness and the simple pole.** It must use that the prime support is discrete on log ℕ and that the pole is simple. The countermodel with a continuous Λ-measure and a triple pole satisfies everything else.
4. **An amplifier seed.** Any subexponential bound in the scaling or Hecke-translation parameter suffices (rate = depth); the seed must not come from orthogonal families, whose size cancels their gain.

**Partial matches in the corpus:**

| Object | Has | Lacks |
|---|---|---|
| Complete Weil matrix at fixed c | 1 (E_m(c) are Fourier tails), 3 | 2; uniformity in c |
| Krein index | 2 in counting form, 4 | 1; a producer |
| Collided form from theta prefixes | 2 | 1, 3 |
| Hecke-similitude scaling surface | 1 in form, 3 | 2 |
| Integrality producers | 3 | 1; precision |
