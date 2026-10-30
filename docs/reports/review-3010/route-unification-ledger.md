# Route-unification ledger

Status: 30 October 2026, corpus `12ba3d87c6` plus working tree.

**The 32 live routes, 17 candidates, PW-B and the route-like theory programmes are faces of three core problems:**

- **U-Σ, critical positivity:** a positivity statement with zero margin.
- **U-Π, the square-root count:** a one-sided count exact at x^{1/2}.
- **U-Γ, selection at the trivial gauge point:** a statement true for ζ and false for its twins.

The corpus proves exact identifications between the three at their endpoints (§2). §3 reads all three off one object. It also identifies the one channel every route has to use: the archimedean place, the only coupling between primes and between the additive and multiplicative structures.

Links: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [summary and next questions](obstacles-summary.md) · [frontier map](../rh-current-frontier-map.md) · [working log](../../../logs/review-3010-rev5-facts-2026-10-30.md). Evidence labels as in the walls ledger; (inference) marks this review's interpretation.

## 1. The three core problems

### U-Σ — Critical positivity

**Canonical forms:**

- The complete atomic Weil matrix is positive along every c_N with c_N⁴/log N → ∞ (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`) [L].
- For a logarithmic Denjoy–Carleman profile it is positive at every bounded multiple of c*_N ≍ L(log L)² (`riemannHypothesis_iff_forall_critical_multiple`) [S].
- The restricted ground minimum satisfies μ(A) ≥ 0 at every aperture.
- The odd Markov form of Riemann's kernel has a positive supersolution of the full nonlocal generator.
- The zero side of the explicit formula is a positive measure (`positive_duality_of_the_explicit_formula`) [S].
- Weil's form equals the collided form (`riemannHypothesis_iff_W_eq_collided`) [L].

**Why it is critical:**

- E₁(c) → 0, with floor c⁻⁷ on the conductors m ≤ c.
- At c*_N the margin and the synthesis error are the same tail energy, 1/log N.
- μ(A) decays doubly exponentially, and the odd form is never subcritical.
- The Hecke state is PD exactly from s = 1/2.
- Monotone minorants cannot extend positivity.

**Faces:** HF, SRT, AIP, ACS (atomic branch), SC, RW, EWU, OWU, ACT, CHMD, SZ, FU, CFC, RP, PA, TG, RN, LI, TH, TT, LA, WD, HCF, GTA, DR, EGC, MSC, PTR, W1C; programmes HEF, SSH, APD, APol/CDG, ALG, AES/AID, CCM, Deninger.

### U-Π — The square-root count

**Canonical forms:**

- κ(K_ζ) = 0 ⟺ ψ(x) − x ≤ C√x log²x eventually [L]; equivalently the odd Liouville upper count.
- Graded form through the heat flow: t-uniform high counts of H_t ⟺ the zeros approach the line (`zerosApproachLine_iff_highCount`) [S].

**Why it is a precision problem:**

- Any criterion implying the count separates a from a + εn^{−η}, η < 1/2, and every producer law in the corpus holds for both.
- Integrality over ℤ produces Chebyshev precision: Adams jets cost 2^{qr}, factorial ratios 2 log 2.
- The Gamma reserve pays Euler heads absolutely only to (log A)².
- Orthogonal families over π(x) phases cancel their own gain [L].
- At every fixed length, prime phases align syndetically, so no eventual single-height power saving exists [S].

**Faces:** WL, MC, PBM, RB, JAS, CTF, ACS (effectivity branch), SRT (tower branch), SC, WD/LA (heat counts), APF, EWJ, FEL, WBF; programmes HKT/AKLT, AOG/SSIC, THIM/BVI, ART, census (IGP/TTPC).

### U-Γ — Selection at the trivial gauge point

**Canonical forms:**

- The Möbius gauge exponent at 0 equals its typical value 1/2 [L].
- The collided polarization is Hecke invariant [L].

**Why it is a selection problem:**

- Gauge-invariant majorants are ≥ 3/4 at 0: the trivial point is never better than typical.
- Nonnegative statistics are maximal at 0 and reach the same size at the Liouville antipode; only the sign of the pole boundary term separates the two [S].
- Locality, pointwise closure and the sub-spacing Hodge index are twin-blind.
- Λ ≥ 0 with the exact FE and an entire completion admits off-line zeros [L].

**Faces:** MC, PM/PW-B, BAG, XN, BSH, CDC, HJ, IRK, PCS, RFHM, SEC; programmes AGT, ACountP/SMAP, Hedenmalm, BGG.

**Solved part:**

- At bounded overlap, selection is a theorem: Liouville and every cofinite flip are rejected [L].
- The simple-pole class is ζ; a positive measure with the FE is Riemann's prime measure [L].
- A twin's prime-form defect is exactly its successor-disagreement shells (`twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`) [S].

**Open part:** uniformity.

- A single prime flip needs overlap ≍ p^{1/7}, and every fixed overlap misses all large primes [L/S].
- The trivial point is one point of a torus on which averages say nothing.

## 2. Proved identifications between the core problems

| Identity | Joins | Content |
|---|---|---|
| `negIndex_zetaKernel_eq_two_mul`; `riemannHypothesis_tfae_zetaKernel` | U-Σ = U-Π | The index of the Weil kernel counts the zeros in a sector; index zero is the one-sided count. |
| `zetaKernel_finiteIndex_tfae` | U-Σ = U-Π (weakened) | Finite index ⟺ finite off-line support ⟺ bounded heat counts ⟺ eventual criticality; implies LH. |
| `zerosApproachLine_iff_highCount`; `exists_card_deep_le_mul_nonrealZeroCount` | U-Σ ↔ U-Π (graded) | The high heat count is the depth-counting function of Ξ up to rescaling; deep zeros are bounded by C log X·N(t). |
| `negIndex_flip_eq_top_of_finite`; `iSup_negIndex_weightKernel_finiteFlip_eq_top` | U-Σ = U-Γ | Finite ζ index forces every single-prime flip to infinite index; for every finite flip set the test-supremum of the index is ∞, for ζ it is κ(K_ζ). |
| `twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm` | U-Γ = U-Σ (shells) | The selection defect of a twin lives exactly on the successor shells, the same block whose payment is the open Σ-face. |
| `riemannHypothesis_iff_collided_hecke_invariant`; `riemannHypothesis_iff_W_eq_collided` | U-Γ = U-Σ | Hecke invariance, a symmetry, is the sign. |
| `heckeState_kakutani_wall`; `riemannHypothesis_iff_exists_affine_posDef` | U-Σ = U-Γ = U-Π | The critical line is the PD threshold of the integer successor on Aff(ℚ) and the Kakutani threshold of the prime Poisson measure on the gauge torus. |
| `threeQuarters_le_of_gaugeInvariant_bound`; `gaugeExponent_moebius_trivial` | U-Γ = U-Π | The square-root exponent must be certified at one specified gauge point. |
| `finiteEulerGamma_negative_dimension_le`; `tendsto_headCoupling` | U-Σ → U-Π | Archimedean positivity pays primes absolutely up to (log A)²; beyond, the head edge couples at √Y and needs cancellation. |
| `zeta_orbitCorr_rate_iff_zetaZeroWidth_le` | U-Σ ↔ U-Π | Any growth rate σ of the scaling orbit correlation reads the zero width: the amplifier exists. |

(inference) These are endpoint identities. Away from the endpoint the problems separate: a route can be selective without being critical, or critical without being precise. The identities do not transfer partial progress between faces.

## 3. The one object behind the three problems

(inference, assembled from the identities in §2)

**Reading 1: Weil's correlation on the dilation group.** Weil's correlation is a function on ℚ^×_{>0} ≅ ⊕_p ℤ; its dual is the prime (gauge) torus 𝕋^{primes}.

| Property | Reading on the gauge torus | Corpus anchor |
|---|---|---|
| U-Σ | The Fourier transform of Weil's correlation is a positive measure (Bochner) | RH ⟺ PD on dilations, or on one two-prime lattice (`negIndex_twoPrime_eq`) [S] |
| U-Γ | Twins are translates by characters of ℚ^×; ζ is the trivial character, and its coherent excess over the gauge mean is the pole | `heckeExtremal_iff` [L]; `primeSource_coherence` [S] |
| U-Π | s = 1/2 is where the prime Poisson measure turns from absolutely continuous to singular over Haar | `heckeState_kakutani_wall` [L] |

**Reading 2: two readings of one divisor.**

- **Additive reading.** The same-point (collided) form S is the limit of integer theta-prefix readings; the theta function is the successor/Poisson side.
- **Multiplicative reading.** The Weil form W is the explicit formula over primes; it is all any line-calibrated explicit formula can compute (HEF).
- **The comparison.** RH ⟺ S = W. On the Ξ divisor this is the agreement of the two reconstructed orientations of the resolvent, which lie in one closed source carrier [S].

| Core problem | Form of the additive/multiplicative comparison |
|---|---|
| U-Σ | W ≥ 0 ⟺ S − W vanishes; the shells must be paid with their sign |
| U-Π | ψ(x) − x: multiplicative count against additive measure, at √x |
| U-Γ | The trivial point is the additively invariant point (Λ∗1 = log); dilation- and successor-invariant forms retain only pole and Haar |

**Reading 3: the archimedean place is the only bridge.** The prime part of Weil's kernel is supported on the prime-power towers of ⊕_p ℤ. Every interaction off the towers passes through the archimedean kernel:

| Interaction | Theorem |
|---|---|
| Prime with prime | A positive assembly of local constituents on ℤ^S has index 0 or ∞; finite nonzero index needs the off-tower (archimedean) constituent (`negIndex_localAssembly_eq_top`) [S] |
| Successor with dilation | Consecutive integers have zero prime incidence and couple only through ω(log(1 + 1/k)) (`successor_localPair_bounds`) [S]; the archimedean kernel on successor edges carries the successor connection (`gaugedArch_succ_nonneg_iff`) [S] |
| Renormalization | A rank-one partner pays at most one prime direction (`finrank_primeSurvival_le_rank`) [S] |
| Selection | The archimedean pole term is the coherent excess at 0 and reverses sign at the Liouville antipode [S] |
| Over Aff(ℚ) | Weil's correlation is archimedean, the integer successor is Kronecker-null; they meet in no PD component (`eq_zero_of_archimedean_le_integer_successor`) [S] |

(inference) The three core problems are three aspects of one deficit: an infinite-rank prime debt has to be paid through a rank-one channel.

- **U-Σ:** the channel carries no margin.
- **U-Π:** the channel gives growth log T only at bounded aperture.
- **U-Γ:** the channel is twin-blind except for the pole sign.

**Reading 4: the obstructions sit at cutoff edges.** Every quantitative obstruction the corpus isolates inside the complete matrix lives at a truncation edge, and the pole (PNT) is what pays it:

| Edge | Statement |
|---|---|
| Horizon N | The zeros meet the pole mode only through the Euler–Maclaurin boundary B_N(ρ)B_N(1 − ρ) (`weilQuad_poleMode_eq_tsum`) [S] |
| Horizon N, Ramanujan modes | The quasimode residual is the upward prime defect (`tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm`) [S]; its budget is the Mertens remainder near n ≈ N [S] |
| Top band n > N e^{−w}/2 | The separate-payment witness lives there; its pole moments are computed exactly [S] |
| Euler head p ≤ Y | The sharp edge at m = Y couples details to far windows with strength √Y [S] |

## 4. Each route as a face

**Supplies** lists what the route has, **Lacks** what it must produce. "Selective (bounded)" means selection at bounded resolution only.

| Route | Core object | Supplies | Lacks | Endpoint identity |
|---|---|---|---|---|
| HF, SRT, AIP, ACS-atomic | Complete Weil matrix | Selective (bounded); full conductor spectrum at fixed c | Critical; edge payment | c⁴/log N → ∞ or Kc*_N receiver |
| SC | Cross-fibre Krein index | Critical and precise by construction | Producer (index ceiling) | κ = 0 |
| RW, EWU, OWU | Restricted ground minimum | Selective odd witnesses at fixed radii | Critical | μ(A) > 0 ∀A |
| ACT, CHMD | Markov / Doob form; Euler heads | Exact ground-state structure; obstructions are prime | Critical; head edge | Positive supersolution |
| SZ, FU, CFC, RP, PA, LI, TG, RN | Boundary currents, histories, operator traces | Exact receivers | Critical | One-sided current or history floor |
| TH, TT, LA, HCF, GTA | Theta/heat Hankel and Jensen data | Moment structure; finite-rank certificates | Rank/time uniformity | All-rank sign; Λ_dBN = 0 |
| WD, LA (heat counts) | de Bruijn–Newman flow | Depth law; deep-zero counting by N(t) | Uniform or polynomial N(t) | Bounded heat count |
| WL, PBM, RB, JAS, CTF | Prime/Möbius error | Selective (divisor collapse at 0) | Precise | One-sided count |
| MC | Möbius gauge exponent | Precise form of the target | Selective at 0 and precise | θ_μ(0) = 1/2 |
| ACS-effectivity | Scaling surface | Riemann–Roch, ampleness on a subsurface | Precise (infinite genus) | Hodge defect zero |
| PM/PW-B, BAG, XN | Escape states, recurrence, Newton discs | Analytic objects | Selective | Every escape state visible |
| HEF | Same-point vs explicit sums | Exact quantum O ∈ 2ℕ; calibration rigidity; Ξ orientation receiver | A source law for the same-point side | O < 2 |
| SSH | Successor shells | Lattice repayment on conductor modes; twin defect = disagreement shells | Signed payment off the conductor span | Reserve with log c loss |
| AGT | Gauge torus | Coherence, divisor collapse, antipode, Adams operations | Point-specific cancellation | θ_μ(0) = 1/2 |
| APD, APol/CDG | Aff(ℚ) states; polarization | Exact threshold at s = 1/2; theta-prefix readings | Critical; a successor-compatible carrier | PD extension; Hecke invariance |
| ALG | Lorentzian / Metzler signature | Window-test positivity; Metzler selection | Critical; a conformal symmetry | Weighted trickle-down |
| HKT/AKLT, AOG/SSIC | Krein index; visibility | Exact counting form; the amplifier; two-prime decision | Producer | κ = 0; subexponential orbit bound |
| AES/AID | Transverse energy, source work | RH ⟺ 𝓔 < 1; logarithmic work ceiling | Subquantum work bound | 𝓔 < 1 |
| ART | Realizations and amplifiers | Realization obstructions [L] | Non-envelope amplifier | — |
| Census (IGP, TTPC) | Zero-ordinate Grams | 0.6725 simple critical; 3/4-or-near-line | Signed coalescent prime pairs past bandwidth 1 | — |
| Candidates APF, EWJ, FEL, WBF | Exhaustion, admission, balance | Receivers | Precise | — |
| Candidates BSH, CDC, HJ, IRK, PCS, RFHM, SEC | Pre-divisor forcing | Receivers | Selective | — |
| Candidates DR, EGC, MSC, PTR, W1C | Roots, contours, transport, realization | Receivers | Critical | — |

## 5. How one object supplies all three over 𝔽_q

| Property | Over 𝔽_q | Over ℤ, per the corpus |
|---|---|---|
| **Critical** | The Rosati/Hodge index on C × C is exact; purity is the boundary case, so no margin is needed. Every circle-calibrated explicit formula is the Rosati pairing [L]. Frobenius acts conformally with factor q (`frobeniusPullback_conformal`) [S]. | The explicit formula computes the Krein form W. Hecke dilations are isometric boosts (`boost_isometry`) [S]; power maps and the successor are not conformal [S]. |
| **Precise** | Finite genus: \|N_m − q^m − 1\| ≤ 2g q^{m/2}; any constant suffices, since eventual Hasse–Weil is Hasse–Weil. Stepanov reaches √q. | Infinite genus: no finite constant. The amplifier exists (rate = depth) but there is no constant to amplify. Integrality reaches Chebyshev precision. |
| **Selective** | Frobenius is one endomorphism; all data live on one tower, where a kernel with one hyperbolic pair has index one. | ℤ has no nontrivial endomorphism. The gauge torus has Adams operations, which act on characters. Several towers force the archimedean glue (§3, Reading 3). |

(inference) Over 𝔽_q one object, the Frobenius graph Γ_F ⊂ C × C, supplies all three: its intersection numbers carry the sign (Hodge index), the count (Γ_F·Δ = N₁) and the selection (F is this curve's Frobenius). Over ℤ the corpus has:

- the surface (scaling surface);
- the intersection form (Weil form);
- the Hecke correspondences (isometric boosts, similitudes of the defect);
- the count (index = #right zeros);
- one matched local Hodge index per prime.

It lacks a correspondence with conformal factor ≠ 1 whose self-intersection is bounded by an independent invariant, i.e. a Rosati involution for the additive/multiplicative pair. It also lacks a second bridge between the towers besides the archimedean place.

## 6. What a unified input must look like

(inference, constrained by the theorems above)

1. **Positivity by identity.** The sign must come from an identity (Hodge index, Plancherel density, Fourier tail, sum of squares), not from coercivity with margin. Σ1, Σ2 and Σ3 exclude every estimate that spends a margin. A uniform margin cannot even reach a fixed overlap ratio [S].
2. **Signed edge payment.** It must pay the shells, the Euler heads and the pole jointly at the cutoff edges. Separate payment is excluded at c²/ε, and absolute Euler-head payment ends at (log A)².
3. **A same-point source.** It must reach S, not only W. Possible routes are a non-holomorphic operation (mean square, modulus, Laplacian, conjugation of the divisor) or an integer-valued carrier with quantum 2.
4. **Discreteness, the simple pole and the boundary sign.** It must use that the prime support is discrete on log ℕ, that the pole is simple, and the sign of the pole boundary term. Size statements are equal at the trivial point and its antipode.
5. **A carrier beyond Aff(ℚ).** A successor-carrying positive state with Weil's dilation part does not exist on Aff(ℚ). The carrier must be adelic, or indefinite (Krein/Pontryagin) with finite index.
6. **An amplifier seed.** Any subexponential bound in the scaling or Hecke-translation parameter suffices (rate = depth). The seed must not come from orthogonal families, whose size cancels their gain.

**Partial matches in the corpus:**

| Object | Has | Lacks |
|---|---|---|
| Complete Weil matrix at fixed c | 1 (E_m(c) are Fourier tails), 4 | 2, 3; uniformity in c |
| Successor-shell calculus | 2 on conductor modes and on the top-band witness's pole moments, 4 (twin defect) | 2 off the conductor span; 1 |
| Krein index | 3 in counting form, 6 | 1; a producer |
| Collided form from theta prefixes | 3 | 1, 4 |
| Matched local Hodge index | 1 at one prime | assembly over primes (needs the archimedean glue) |
| Hecke-similitude scaling surface | 1 in form, 4 | 3, 5 |
| Bost–Connes / Hecke states | PD for β > 1 with Hecke exponent β/2 (`isPosDefOnGroup_bcState`) [S]; at s = 1/2 the Hecke state is the Haar state [L] | Weil's dilation part; 5 |
| Integrality producers | 4 | 1; precision |
