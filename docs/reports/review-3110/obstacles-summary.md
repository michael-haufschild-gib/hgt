# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`, wall labels to `walls-ledger.md`. `[L]` Lean statement read; `[S]` Lean source
unfinished or outside its umbrella; `[D]` derived here from `[L]` statements, not formalized.
Corpus state: `5c51362a92` plus working tree.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = κ(K_ζ) = #` zeros right of the
   line, an even number. Glued at `∞` or at any prime it becomes `κ + 1`, odd or infinite. The
   boost, Markov and harmonic hyperplanes coincide with `v₁^⊥`. The same integer counts the band
   poles of the loop-Eisenstein factor `Λ(s)/Λ(s+1)` [L].
2. **The index is a two-prime invariant carried by the coupling.** For every prime set with
   `|S| ≥ 2`, the coupled assembly `K ∘ proj_S` has glued index exactly `κ + 1`. On any window of
   log-height `L` the explicit formula with the primes `≤ e^{2L+8}` is exactly `ratCorr`, and the
   supremum over windows is `κ + 1` [L]. Every coupled assembly splits uniquely into an axial
   (separable) part and an inter-tower coupling, which vanishes on all axes and equals the coprime
   cross-difference `K(uv) − K(u) − K(v) + K(1)` off them [L]. The coupling is the zero carrier.
   Separable assemblies annihilate it, cannot approximate `ratCorr`, and are zero-blind when truncated
   (`κ ∈ {r+1, r+2, ∞}`) [S]. Untruncated, on the finite non-RH stratum, they overcount `κ` at every
   non-blind prime and diverge [L]. A continuous profile with vanishing coupling is affine, `κ ≤ 2`
   [L]. Consequence [D]: **RH ⇔ the inter-tower coupling of `ratCorr` on `⟨2,3⟩ × ⟨5,7⟩` is
   bounded** (density, continuity, Hyers–Ulam stability, and "bounded Weil kernel ⇒ RH").
3. **Reformulations do not soften.** Castelnuovo–Severi at rational scales, bounded `K_ζ`, Hadamard
   powers, the Künneth square, glued index one, quadratic Riemann–Roch on the scaling surface: each is
   RH [L]. A crossing-free deformation to a positive model exists iff the form is positive [L].
4. **The edge is a defined invariant.** RH ⇔ the complete Weil family of any admissible profile has
   no edge; without RH the edge is `≤ 2(log N)^β` infinitely often for every `β > ¼` [L] (for the
   tilted spline every `β > 1/8` [L]). The tilted-spline edge is `≥ (log N)^{α}` for every
   `α < 1/9` and tends to `∞` unconditionally [L].
   The edge is a threshold curve in the plane of resolutions; over a curve it is `≤ 2g` [S].
5. **Above polylogarithmic conductors the complete form is coercive mode by mode.** For
   `(log N)^A ≤ m ≤ N^θ`, `θ < ½`, `α < ¼`, `A > 8α`, every Ramanujan mode has energy
   `≥ ((1−2θ)/4) log m`; no exceptional single conductor exists there, for every C² profile [L]. The
   pole defect of a packet is `≥ (log N − 3 log Q − 1)` times its adjunction energy [L]. Whatever
   blocks positivity sits in the low conductors `m ≲ (log N)^A`, in spans rather than single modes,
   and above `N^θ`.
6. **The prime part carries one coherent, uncancellable excitation.** In prime-incidence coordinates
   (`√(p−1)/p` times a prime mode is `1_{p|n} − 1/p`) the generator, its dilation jumps and its
   complementary tail are nonnegative arithmetic counts [L]. The pole response costs exactly
   `S_Q = log Q + O(1)` against adjunction energy, on every pole hyperplane too [S]. The coherent
   prime residual has a matching lower bound `≍ log P · (pole mass)²`, which the scalar Mertens row
   cannot cancel [L]. Successor and dyadic dilation see every nonconstant conductor with the sharp
   constant `3/4`, kernel = constants [L].
7. **Collisions are bounded by the Hecke defect.** The horizontal fibre multiplicity obeys
   `H(γ) ≤ C(1 + log|γ|/L) − Re Π_{F_L}(e^{2L}, −γ/2π) + 4E_γ(L)` for `1 ≤ L ≤ 4 log|γ|`, with
   `E_γ` the Hecke defect. At `L = ¼ log log|γ|` the prime polynomial is free:
   `H(γ) ≪ log|γ|/log log|γ| + E_γ(¼ log log|γ|)` [L]. Collision increments satisfy
   `ΔO ≤ 2·max H·n_off`; the stopping prefix is source-certified [L].
8. **Selection is partial and sharp.** Separated: every finite flip (glued index, bounded edge); every
   prime-set flip of greatest gap `< 2 log 2`, including thin, co-thin, cofinite flips and every flip
   of relative logarithmic density `κ > ¼` (Wirsing) [L]. Unselected: flip sets of relative density
   `0 < κ ≤ ¼`, sets of density zero with divergent `Σ1/p`, irregular densities, and general
   maximal-margin gauges.
9. **Falsification certificates multiply; no converse.** RH ⇒ the Donoghue map of `Ξ` has `i` as its
   only upper periodic point; RH ⇒ every Jensen section of every real translate of
   `∏(1−c_iD) D^k Ξ` splits; RH ⇒ every Ritz branch of the Xi heat-moment form moves strictly left
   [L]. Each yields a finite falsification test and no RH mechanism.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit horizon `N₀` for the `1/9` theorem | HF, SRT, AIP, ACS, SC | proved mechanism; constants |
| A2 | Exact complete Weil energy on prime-incidence packets (incidence coordinates make generator, jumps and tails explicit nonnegative counts) | HF, SRT, AIP, ACS | finite arithmetic computation with Gamma and poles retained |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` | SRT, HF | synthesis error at one explicit scale |
| A4 | Compare CSAR rigidity and relative residual energies with the complete Weil energy on fixed and slowly growing packets | HF, SRT, AIP, ACS | fixed-dimensional comparison |
| A5 | Gamma/polar head-pole cancellation for packets up to `exp(c√log Y)` | CHMD, HF, AIP | window PNT with classical error |
| A6 | Edge exponent of a finite model configuration (one off-line pair) | HF, SRT, AIP, SC, EHT | analysis of an explicit model kernel |
| A7 | Explicit capture stage for complete-cell indices | AID, HF, CHMD | compactness transfer |
| A8 | Stronger subconvexity exponent for the heat floor `2/3` | WD, LA | known exponents |
| A9 | Certified de Bruijn–Newman bound below `1/8` as an index-one time | SC-heat, WD | barrier method + certified numerics |
| A10 | One Lean statement: `ΔO = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf | WD, SRT | composition of `CollisionChargeIncrements` and `BacklundLindelofConverse` |
| A11 | Computable stopping prefix (certified interval bounds instead of compact minima) | WD | interval arithmetic |
| A12 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A13 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | Farkas / rounding |
| A14 | Canonical relative split for general nonzero proper rational subgroup successors | SC, AKG | classification and index preservation proved |
| A15 | `𝔽_q(X)` calibration: higher-degree local walls, global Hecke product formula, archimedean Weil state of a curve | SC, ACS, RIT | local wall at `∞`, quantized exponents and the curve edge proved |
| A16 | Formalize RH ⇔ bounded inter-tower coupling: Hyers–Ulam on `ℝ`, density of two-prime log-lattices, continuity of the spline series, `riemannHypothesis_of_norm_zetaKernel_le` | SC, AKG | classical stability theorem; every other ingredient is in Lean |
| A17 | `𝔽₃` loop chain: Bruhat unfolding and constant-term evaluation | ACS | loop-group foundations in Lean |
| A18 | Certified Weil positivity past the two-prime aperture `r ≥ ½ log 3` | RW, EWU, OWU, CHMD | certified numerics |
| A19 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A20 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF | effectivise eventual statements |
| A21 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A22 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A23 | Transfer of the universal regime to the glued state on atomic test families through the threshold curve | SC | identification of the fixed-width horizon Gram with the complete Weil matrix |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (Lindelöf + zero-free half-plane); **LH** (Lindelöf); **sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Positivity on `v₁^⊥` across the detection edge | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| Σ-2 | Signed estimate on the subthreshold block beating the residual-versus-floor exponent: closed by bilinear 8-channel residuals, packets `α < 1/8` [L]. Remaining: inverse-energy residual sum `≪ c⁹/log N` → `c⁸` | sub | same |
| Σ-3 | Defect bound below `c¹⁶`: bypassed by four-band split `Q₁ < exp((log N)^½) < N^θ₁`, all-vector positivity `α < 1/9` [L]. Remaining: two-region reserve gap `K c⁹ ≤ θ₁ log N` and band–terminal cross `c⁹/log N` → `c⁸` | sub; RH at RH-complete overlap | same |
| Σ-4 | Mertens cancellation of the coherent prime pole by the pole/Gamma/counterterm part of the complete form | sub | HF, SRT, AIP, ACS |
| Σ-5 | Localization of near-edge negative directions in the coherent prime sector | sub | same |
| Σ-6 | Bounded inter-tower coupling of `ratCorr` | RH [D] | SC, AKG |
| Σ-7 | Quantitative coupling transfer (local Hyers–Ulam with Baker-type density control) | sub | SC, AKG, HCF |
| Σ-8 | Exact sum-of-squares identity for Weil's dilation form on the boost hyperplane | RH | SC, HF, RIT |
| Σ-9 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| Σ-10 | All-rank / all-degree theta, heat and Jensen signs | RH | TH, LA, HCF, PA, GTA |
| Σ-11 | Arithmetic index ceiling uniform in resolution | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | CHMD, SRT, WD, AID, SC |
| Σ-12 | Collision charge `< 2` per window; no heat-index jump; `Λ_X = 0` | RH | WD, TG, SC-heat |
| Σ-13 | `ΔO = o(log T)` | LH | WD, census |
| Σ-14 | Cumulative charge `O(T) = o(N(T))` | sub | WD, census |
| Σ-15 | Hecke defect at doubly-logarithmic scale `E_γ(¼ log log|γ|) = o(log|γ|)` | sub | WD, HEF |
| Σ-16 | Subcritical heat count `a < 1` | sub | WD, SC-heat |
| Σ-17 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL |
| Σ-18 | Spectral reality of a realized operator | RH | RN, PTR, W1C, PM |
| Σ-19 | Joint payment of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles | unknown | CHMD, AID, HF |
| Σ-20 | A source-defined noncrossing path to an index-one model | RH | SC, TG, WD |
| Σ-21 | Emptiness of the loop-Eisenstein band poles by a noncancellation theorem | RH | HF, ACS, SC |

### Π — square-root precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | ε-uniform producer | sub / RH | WL |
| Π-3 | Moving-scale half-power Möbius cancellation; near-band cyclotomic energy | RH; ≥qRH | MC |
| Π-4 | An unconditional Serre-dual `h⁰` with quadratic RR | RH | ACS, RIT |
| Π-5 | Low-conductor and exceptional spans: nonpositive span dimension below `(log N)^A` | sub | HF, MC, CAF |
| Π-6 | Conductors `N^{½} < m ≤ N` | sub | HF, SRT, AIP, SC |
| Π-7 | 100% census; pointwise local count | sub | ACS, SRT, IGP, LA, WD |
| Π-8 | Gap-independent detection scale for collision readings | sub | WD |
| Π-9 | Pointwise heat horizon constant `< ½` | ≥qRH | WD, LA |
| Π-10 | Window-uniform coupling: the window explicit formula needs the primes `≤ e^{2L+8}`; uniformity over `L` | RH | SC, AKG |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point | RH | MC, BAG, XN, PM |
| Γ-2 | Hecke invariance of the collided form; Frobenius at infinity | RH | HF, AP, CDG, WD |
| Γ-3 | Pre-divisor sections / potentials coupled to Ξ | RH | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF |
| Γ-4 | A conformal correspondence over ℤ with factor `≠ 1` | RH | ACS |
| Γ-5 | Separation of flip sets with relative density `0 < κ ≤ ¼`, of zero-density sets with divergent `Σ1/p`, and of irregular densities | sub | HF, ACS, AIP, SRT, SC |
| Γ-6 | Half-parameter cusp selection | RH | PM |

## 2.3 The three questions to answer next

**Q1. Does the complete Weil form absorb the coherent prime pole by Mertens cancellation, and do its
near-edge negative directions live in the coherent prime sector?** Several statements are proved.
In prime-incidence coordinates the prime generator, its dilation jumps and its complementary tail
are nonnegative arithmetic counts [L]. The pole response of prime packets costs exactly
`S_Q = Σ_{p≤Q} log p/p = log Q + O(1)` against adjunction energy, on every pole hyperplane [S]. The
coherent prime residual is bounded below by `≍ log P · (pole mass)²`, so the prime side alone
cannot cancel it [L]. Above `(log N)^A` every single conductor is coercive [L]. The complete form
contains exactly two terms that can absorb a logarithmic coherent excitation: the pole term with its
running counterterm `log N − γ`, and Mertens' constant. Two parts. (a) Mertens cancellation:
on prime-incidence packets, is the complete Weil energy equal to an adjunction-weighted incidence
energy plus a remainder `O(1)·L_Q`, uniformly in `Q ≤ N^θ`, the `log Q` being cancelled by
`Σ_{p≤Q} log p/p − log Q → E`? (b) Localization: is every nonpositive vector of `W_{φ,c,N}` near the
edge concentrated, up to an error below the floor, on the coherent sector (the span of the
prime-incidence packets with the pole-witness profile)? Why this question: (a) is the precise
interface between the CSAR arithmetic and the CACT positivity proof, and it decides whether the
conductor loss in the residual-versus-floor barrier is real. (b) would reduce the edge problem to a
sector of dimension `π(Q)` with an explicit positive incidence calculus. A negative answer to (a)
identifies the coherent prime packet as a concrete obstruction to every estimate route. Starting
points: CSAR `PrimeCoherenceCalculus`, `CoherentPrimeTailLowerBound`, `PrimePoleNorm`,
`HarmonicPoleCentering`, `RelativePrimeResidual`; RAPT `Conductor/PrimePacketDefect`; CAF
`ExceptionalConductorsVanishAbovePolylog`, `PrimePacketCoercivity`; CACT
`TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap`.

**Q2. How large is the inter-tower coupling of `ratCorr`, and can its size be transferred to the
whole correlation quantitatively?** The coupling is the coprime cross-difference
`C(u, v) = K(uv) − K(u) − K(v) + K(1)` between two disjoint two-prime lattices. It is the only part
of the correlation that separable structures miss, it is nonzero unconditionally, and its vanishing
forces an affine profile [L]. Writing `K(u) = W(f, T_u f)`, it is the Weil pairing
`W((T_{u^{-1}} − 1)f, (T_v − 1)f)` of difference tests in coprime directions. Qualitatively,
bounded coupling is RH [D]. Two parts. (a) *Transfer*: a local Hyers–Ulam inequality
`sup_{|log u| ≤ L} |K(u) − K(1)| ≤ C(L) · sup_{box of log-height L} |C|`, with `C(L)` polynomial in `L`,
using Baker-type lower bounds for `|a log 2 + b log 3 − x|` to control the density of the lattices
(the two-prime phase separation of HCF is the template). (b) *Size*: the explicit formula writes
`C(u, v)` as a four-window prime sum at heights `uv, u, v, 1`; which cancellation in that combination
is forced by the coprimality of the windows? Why this question: it gives SC a target in which the
axial data, single-tower and separable, are irrelevant by theorem. It ties SC to the Π wall at its
sharpest point: four coupled windows of the prime count instead of one. Part (a) is an inequality
between two functionals of `K`, below RH, and makes every growth estimate on the coupling a growth
estimate on `K_ζ`. Starting points: AKG `TowerCoupling/InterTowerCouplingRigidity`,
`TowerCoupling/CoupledTowerSignatureFormula`; RIT `TheKunnethSquareOfWeilsKernelIsRH`
(`riemannHypothesis_of_norm_zetaKernel_le`); ASRP `TwoPrimeTowersSeeEveryOrdinateDifference`.

**Q3. Can the Hecke defect at doubly-logarithmic scale be bounded by `o(log|γ|)`?** At
`L = ¼ log log|γ|` the master inequality gives `H(γ) ≪ log|γ|/log log|γ| + E_γ(¼ log log|γ|)`, with no
prime cancellation needed [L]. `E_γ(L) = Σ_ρ w_ρ(2 cosh(2δ_ρ L) − 2)` is a positive depth functional
localized at height `γ`. It is zero under RH. Dyadic amplification `E(2L) ≥ 4E(L) + E(L)²/D` gives a
lossless transfer from one larger scale down to all smaller ones [L]. A bound
`E_γ(¼ log log|γ|) = o(log|γ|)` for every `γ` gives `H(γ) = o(log|γ|)`: every horizontal fibre, and so
every zero, has multiplicity `o(log|γ|)`. The best unconditional bound is `O(log|γ|)`; the
`log|γ|/log log|γ|` bound of Littlewood–Titchmarsh needs RH. At `L = ¼ log log|γ|` the depth weight
`2cosh(2δL) − 2` is `≈ (log|γ|)^{δ/2}` for a zero of fixed depth `δ` and `≈ δ²(log log|γ|)²/4` for a
shallow one. The question is therefore a pointwise zero-density statement near one height, weighted
by depth, at a scale where density estimates are almost strong enough. Why this question: it is the first point where the
Frobenius-at-infinity object (the Hecke defect) controls the collision object (fibre multiplicity,
`ΔO`) with an explicit payoff below Lindelöf. It joins WD, HEF and the census through one
inequality. Starting points: CDG `HeckeDefectHorizontalMultiplicity`, `CollisionChargeIncrements`,
`ZetaDepthDistribution`, `TwoScaleDepthRigidity`; RBG `TheDyadicAmplificationOfTheHeckeDefect`.

## 2.4 A wildly different route

**The rigidity route: RH from higher-rank rigidity of the joint action of two primes.**

All routes in the map are either quantitative (a sign estimate on a growing family, a count at
square-root precision) or index computations on the affine group of ℚ. The rigidity route asks for
a qualitative conclusion from the multiplicative action where it has higher rank. Precedent:
arithmetic quantum unique ergodicity was proved by measure rigidity (Lindenstrauss), where the
L-function route needs an unavailable subconvexity bound.

The coupled tower results put this route on a definite footing. A two-prime test lattice
`⟨p, q⟩ ≅ ℤ²` carries the full index: `κ(K_ζ ∘ proj_{p,q}) = κ_ζ` [L]. On the finite stratum the
Krein–Langer decomposition writes the kernel as a positive part plus the joint exponential
characters `(a, b) ↦ p^{a(ρ−½)} q^{b(ρ−½)}` of the right zeros. These are joint eigenfunctions of the
rank-two lattice action whose eigenvalues `(p^{ρ−½}, q^{ρ−½})` are off the torus. They are exactly the
non-unitary joint eigen-objects that higher-rank rigidity excludes on compact phase spaces. The
coupling is what makes the system genuinely rank two: separable kernels have zero coupling, and a
continuous separable profile is affine [L].

Route. (i) Transfer the kernel `K_ζ ∘ proj_{p,q}`, which lives on the acting group `ℤ²`, to a
`(×p, ×q)`-equivariant positive object on the `S`-arithmetic solenoid `X_{p,q}`. Candidates are a
measure, a positive distribution, or a cocycle, with the zero characters becoming eigendistributions.
(ii) Apply higher-rank rigidity: positive-entropy `×p, ×q`-invariant measures are Haar (Rudolph,
Johnson), and higher-rank cocycles are cohomologous to constants (Katok–Spatzier). (iii) Conclude that
the non-unitary characters are absent.

How it avoids the walls. **Σ**: no estimate against a ground energy, so the edge obstruction does not
apply. **Π**: the conclusion is qualitative. **Γ**: dense exponents for two primes are specific to ℤ;
over `𝔽_q[T]` the action is rank one in the relevant sense. Unitary twists change eigenvalues by
unitary characters and do not create non-unitary ones.

Its wall: **from the acting group to the phase space.** The zeros appear as characters of `ℤ²`, not
as distributions on `X_{p,q}`. Positive-definiteness transfers through Bochner only for the unitary
part. The off-torus characters need a positive phase-space object, and none is known. In the
coupling language, (i) asks for a positive realization of the cross-difference kernel
`W((T_u − 1)f, (T_v − 1)f)` as a correlation of a `(×p, ×q)`-system. First question: is there a
measure-preserving `(×p, ×q)`-system on `X_{p,q}` and an observable `F` whose correlation
`⟨F ∘ (×u), F ∘ (×v)⟩` reproduces the inter-tower coupling of `ratCorr`? If the system has positive
entropy, rigidity makes it Haar. Haar correlations are bounded, so RH would follow from the coupling
criterion [D].

No second route was found that avoids all three walls. Any candidate is constrained by the edge
principle (statements proved without zero information hold only where zeros are invisible) and by
coupling rigidity (statements built from separable data cannot see the zeros). A distant route
therefore has to be qualitative and genuinely coupled across primes. The rigidity route is the only
one of that shape.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the coherent sector carries the edge
**Question.** Prove that, at every overlap `c ≤ (log N)^{¼}`, every unit vector with nonpositive
complete Weil energy lies within squared distance `o(1)` of the coherent prime sector: the span of
the conductor packets `Σ_{p≤Q} b_p (1_{p|n} − 1/p)` with `Q ≤ (log N)^A`.
- **Below RH / quasi-RH**: a localization statement about where negative directions could be; it
  excludes no zero.
- **Advance**: above `(log N)^A` every single conductor is coercive [L], and the coherent sector is the
  one place where the prime part has an uncancellable logarithmic excitation [L]. Localization would
  shrink the RH problem from all of `ℓ²(1..N)` to a sector of dimension `≈ π((log N)^A)` with an
  explicit nonnegative incidence calculus. Positivity on that sector, Q1(a), would then be a
  finite-sector computation at every resolution. It also locates the detection edge structurally:
  the edge is the overlap at which the coherent sector's energy crosses zero.

### 2.5.2 Route SC — a quantitative coupling transfer
**Question.** Prove a local Hyers–Ulam inequality for the Weil correlation:
`sup_{|log u| ≤ L} |K_ζ(u) − K_ζ(1)| ≤ C L^k · sup |K_ζ(uv) − K_ζ(u) − K_ζ(v) + K_ζ(1)|`, the supremum
over `u ∈ ⟨2,3⟩`, `v ∈ ⟨5,7⟩` of log-height `≤ L + O(log L)`, with explicit `k` from Baker's theorem.
- **Below RH**: an inequality between two functionals of `K_ζ`; it fixes no zero.
- **Advance**: it makes the inter-tower coupling the complete invariant of SC in quantitative form.
  Every growth bound on the coupling becomes a growth bound on `K_ζ`, i.e. a zero-free statement
  of matching depth: growth `≤ e^{σL}` excludes zeros deeper than `σ`. SC's target becomes a
  four-window coupled prime sum, with the separable data provably irrelevant. It is the quantitative
  counterpart of coupling rigidity, and over `𝔽_q[T]`, where log-lattices are discrete, it fails in
  the right way.

### 2.5.3 Route WD — sublogarithmic multiplicity of zeros
**Question.** Prove `E_γ(¼ log log|γ|) = o(log|γ|)` uniformly in `γ`, and hence that every zero of ζ
has multiplicity `o(log|γ|)`.
- **Below RH / quasi-RH**: a pointwise multiplicity statement. It implies no Lindelöf statement and
  no zero-free region.
- **Advance**: it improves the classical unconditional bound `m(ρ) ≪ log|γ|`, which has resisted
  improvement without RH, through the master inequality [L]. It would be the first unconditional
  output of the Hecke defect, the collided-side object that Frobenius at infinity has to control.
  It also gives `ΔO(T) ≤ 2·o(log T)·n_off(T)`, the first improvement on the unconditional
  `ΔO ≪ log²T`.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — positivity of the coherent sector by an incidence identity
**Question.** On the coherent prime sector, is the complete Weil form an exact sum of squares of
incidence events (dilation jumps `[p|k ∧ p∤n]`, nondivisibility counts) minus a Mertens term that
equals the pole-plus-counterterm contribution exactly?
- **Why it opens the path**: the incidence calculus already writes every prime-side ingredient on
  that sector as a nonnegative count [L]. An identity there would make positivity on the sector
  structural, valid at the edge, with no estimate against the ground energy. Together with
  localization (2.5.1) this is RH. It is the arithmetic form of the Castelnuovo–Severi inequality:
  on `𝔽_q` the Frobenius graph's self-intersection is a count; over ℤ the coherent sector is where the
  count is visible.

### 2.6.2 Route SC — a kernel-rigid homotopy
**Question.** Is there a source-defined continuous path of Hermitian forms from the glued Weil state
`φ_c` to an index-one model along which every null vector is forced, by an arithmetic rigidity
theorem, to be the pole mode? An example of such a theorem: a vector neutral under successor and prime
dilations is constant.
- **Why it opens the path**: along a nondegenerate path the negative index is constant, and at a
  crossing it changes only through a null vector [L]. A crossing-free deformation to a positive model
  is the sign itself [L], so the sign cannot be avoided, but it can be converted into a kernel
  statement. Kernel statements are qualitative rigidity theorems, and the joint successor/dyadic kernel
  being the constant packet [L] is a corpus instance. The heat homotopy is a source path whose crossings
  are exactly the collisions [L]; the question asks for a path whose crossings are excluded by
  rigidity. The coupled assembly gives a natural parameter: interpolating between the axial assembly
  (index known) and the full coupling.

### 2.6.3 Route WD — a single-scale prime bound for the Hecke defect
**Question.** At `L = c log T`, is the Hecke defect `E_γ(L)` bounded by the prime polynomial
`Π_{F_L}` of length `T^{2c}` and a constant, uniformly over `γ ∈ [T, T+1)`?
- **Why it opens the path**: RH is equivalent to subexponential growth of the dyadic Hecke defects,
  and a bound at one large dyadic scale transfers losslessly to every smaller scale [L]. The master
  inequality turns a bounded `E` at `L = c log T` into bounded fibre multiplicity and `ΔO ≪ log T` [L].
  A prime-side bound on `E` at that single scale closes a loop. The prime polynomial controls `E`;
  `E` controls the collisions; dyadic amplification forces `E` to be either exponentially large or
  zero. This is the analytic face of Frobenius at infinity, with the scale and the prime length made
  explicit.

## 2.7 Does closing RH need a new field?

**Assessment: yes. Edge Hodge theory is necessary and is being built, but its results show it is not
the field that closes RH.** EHT does what the analogy with degenerations promised descriptively. The
edge is a defined invariant, RH is its nonexistence, the edge diverges unconditionally over ℤ and is
bounded by `2g` over a curve, and at fixed width the Hodge defect is a monotone integer converging to
the seen zeros. It has also closed two of its own hoped-for mechanisms. Integer invariance along
paths is equivalent to the sign [L], so homotopy needs noncrossing proved from elsewhere. The
edge, being an invariant, is located only by the same estimates that stop at it. EHT measures where
positivity fails; it does not produce positivity.

The results of the coupling and arithmetic layers point to what is missing.
- The index is carried entirely by the inter-tower coupling `K(uv) − K(u) − K(v) + K(1)`. Separable
  data are blind, a continuous profile without coupling is affine, and bounded coupling is RH [L/D].
- The prime part of the complete form is an explicit nonnegative incidence calculus with one sharp,
  uncancellable logarithmic coherent excitation [L/S].
- Additive shift and multiplicative dilation are jointly rigid on conductor packets with the sharp
  constant `3/4` [L].

All three are statements about how the additive structure of ℤ (successor, divisibility, the
four-window prime sum) couples its multiplicative towers. Over `𝔽_q` this coupling is geometric:
the Frobenius graph couples the two factors of `C × C`, and its self-intersection is a count. Over ℤ
there is no theory of this coupling at the level of positive forms. That theory is the missing
field.

**Working name: arithmetic coupling theory** (the sum–product Hodge theory of the scaling surface).

*What it is about.* Hermitian kernels and forms on `ℚ_{>0}` and its two-prime lattices, studied
through their coupling: mixed differences across coprime directions, approximate additivity in
`log`, and the interaction of successor with dilation. Its central object is the coupling kernel of
the Weil correlation and its arithmetic expression as coupled prime windows. Its central phenomenon
is stability: how far a form that is nearly separable or nearly additive can be from separable or
additive, with the defect measured arithmetically.

*What it would be like.* A merger of three existing theories, none of which has been used on Weil's
form. (1) Stability theory of functional equations (Hyers–Ulam, approximate homomorphisms), where
"approximately additive ⇒ near additive" is a theorem with explicit constants. (2) Sum–product and
incidence theory of additive combinatorics, where the interaction of `+` and `×` is controlled by
counts and rigidity, e.g. the incidence and energy bounds behind Bourgain–Katz–Tao. (3)
Diophantine approximation of logarithms (Baker), which turns density of `log⟨p, q⟩` into explicit
constants. Over ℤ its statements would be inequalities of Hyers–Ulam type whose defects are prime
sums, and identities in which divisibility events are the squares.

*Criteria it must meet.*
1. Coupling-completeness: its invariants see exactly the coupling. They vanish on separable data
   and determine the index of every coupled assembly.
2. Stability with explicit constants: approximate additivity of a profile across two coprime
   lattices implies near-additivity on boxes, with constants from Baker-type bounds.
3. Incidence positivity: on coherent prime packets every prime-side quantity is a nonnegative count,
   and the pole enters only through Mertens' constant and the running counterterm.
4. Edge validity: its positivity statements are identities or stability theorems, never estimates
   against the ground energy.
5. Calibration: over `𝔽_q[T]` the log-lattices are discrete, the coupling of two prime towers is
   governed by the Frobenius graph, and the theory reproduces Weil's Castelnuovo–Severi inequality;
   on the golden datum it fails.
6. Rigidity output: its kernel theorems (vectors neutral under successor and dilation are constant)
   are strong enough to force noncrossing along source paths.
7. Selectivity: it distinguishes ζ from flip twins of every relative density, because flipping
   primes changes the coupling of the towers it touches.

*Questions it must answer.*
- What is the size of the inter-tower coupling of `ratCorr`, as a four-window prime sum, and which
  cancellations does coprimality force?
- Is there a local Hyers–Ulam inequality for kernels on `ℚ_{>0}` with polynomial constants?
- Is the complete Weil form on the coherent prime sector a sum of incidence squares minus an exact
  Mertens term?
- Do near-edge negative directions localize in the coherent sector?
- Which arithmetic rigidity theorems make source paths crossing-free?
- What is the arithmetic analogue of the self-intersection of the Frobenius graph: a count attached
  to the coupling of two prime towers?

*Tools it aims to develop.* Local Hyers–Ulam inequalities on dense subgroups of `ℝ` with Diophantine
constants. Mixed-difference (coupling) calculus on `ℤ^S` and its polar identities. Prime-incidence
coordinates and incidence-square certificates. Sum–product energy bounds for divisibility events.
Rigidity-to-noncrossing transfers for Hermitian paths. Interfaces to EHT (edge, threshold curve) and
CSAR (packet rigidity, coherent sector).

*Objects, language, mechanisms.* Coupled and axial assemblies; the inter-tower coupling kernel;
coprime cross-differences; two-prime log-lattices and their Diophantine density; coherent prime
sector, incidence events, nondivisibility counts; successor–dilation rigidity; Mertens cancellation.
Mechanisms: stability (approximately additive ⇒ near additive), incidence identities (positivity as
a count), and rigidity-forced noncrossing.
