# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `2b57d8735a` (2026-11-08). Working log: `logs/review-0811-statusquo-facts.md`.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished or unintegrated; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized. Sections 2.3–2.13 and 3 are interpretation and ideation; every statement there that is not tagged is a proposal, not a result.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

Notation: `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **LinAt C** `Θ−½≤C(Θ∞−½)`; `Φ(L)=e^{−L/2}primeDeviation(e^L)`; `c_B` the cubic-spline orbit correlation; `Γ_n` the smoothed Frobenius graph of degree `n`; `G_s(d)=e^{−(s−1)d}/(4π sinh d)` on `ℍ³`; `H_t` the heat deformation of Ξ.

## 1. Big picture

### 1.1 RH is ZAL plus AAL, with a strict dial between them
For every zero configuration, purity ⇔ ZAL ∧ AAL [L]. Between the two halves sits a strict linear hierarchy [L]:

  `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13`  (`1<C₁<C₂`),

with `LinAt C ⇔` "finitely many zeros right of `½+h` ⇒ none right of `½+Ch`"; `AAL ⇔ ∀C>1 LinAt C`; `Pure ⇔ ZAL ∧ LinAt C` for every real `C`; and the **quantifier collapse** `∃C LinAt ⇔ (ZAL ⇒ Pure)`. Every level is separated by an explicit configuration; harmonic-depth configurations (ZAL, infinitely many off-line zeros, no linear law) separate `ZAL⇒RH` from B13 [L]. For ζ: existential linear AAL is exactly `ZAL ⇒ RH`; at slope `C≥1`, `LinAt C` ⇔ finite-rank Chebyshev self-improvement at factor `C` ⇔ all-scale lag `‖Φ(L)‖≤Me^{C(Θ∞−½)L}` ⇔ a thick tower lag bound at exponent `C(Θ∞−½)+ε` ⇔ a thick prime deviation `O(X^{½+C(Θ∞−½)+ε})` [L]. And `Θ∞` itself is the **finite-rank Chebyshev exponent**: the infimum exponent of `ψ(x)−x` modulo finite exponential sums [L].

### 1.2 AAL is transport; approximate events are abundant, exact ones are the content
AAL ⇔ zero transport ⇔ tail transport: every right zero transports to arbitrarily high points where every Euler tail vanishes and cancels the head with full amplitude [L]. Near-full cancellation `|ζ−E_y|≥(1−η)|E_y|` occurs on a set of heights of positive lower density at every strip point, for every cut and every `η>0` (Voronin universality) [L]; returns at right zeros are tail-bad and rare [L]. AAL asks for `η=0` near right zeros. ¬AAL is one rigid object: an isolated top over an infinite remainder, a finite oscillation `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, syndetic lag excursions at every base [L].

### 1.3 What decides AAL and the finite stratum, and what cannot
Five proved boundaries fix the input type.
- **Two scales.** Properties depending only on zeros above a height, or only below a fixed height, decide neither B13, nor any linear law, nor AAL [L].
- **Analytic shape.** FE, order one and reality admit every finite top layer, also over a remainder of positive asymptotic abscissa (two-scale `cosh` models defeat every prescribed slope) [L]. The input must use the Dirichlet series.
- **Family uniformity.** Every heat deformation `H_t` (`t>0`) has finitely many non-real zeros, the FE, reality and Pólya positivity; any property holding for all `H_t` and implying "finitely many non-real zeros ⇒ none" gives RH [L]. A B13 mechanism must use what `H_t` lacks: the Euler product.
- **Firewall.** Positive Euler products with linear counting (integer norms, rational-prime labels), continuous Beurling systems and one reflection pair carry finite top layers; positive two-prime and Hecke polynomials annihilate any finite zero set; the integer-norm one-off satisfies ZAL and violates every finite slope [L]. The input must use the FE.
- **Well-foundedness.** Wolff towers (positive weights, every mode off the circle, all nonzero level sums zero) defeat elimination without ZAL [L].

The only proved calibration where Euler product + FE succeed is finite rank: a finite Euler product with an FE of conductor `ΠP` has `a_p²=p` and every zero on `Re s=½` [L]; in the Beurling class an exact FE (or FE defect `≤1/6400`) forces the rational primes [L].

### 1.4 The finite stratum
Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height ⇔ eventual slice positivity; in the stratum Lindelöf holds and RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set [L/K]. The finite stratum is the bottom of the dial. Its heat-family extension is RH [L]; B13 for ζ alone is below quasi-RH and below AAL. Heat energy carries its initial trace: `E(t)=Σ (Im z)²` tends to the sum of squared upper depths of the ξ divisor as `t→0⁺`, and a finite initial mass forces `t·N(t)→0` for the non-real heat count `N(t)` [L].

### 1.5 The curve proof over ℤ: elimination is free, the crude step is open
Finite rank: unit circle ⇔ bounded traces at every level ⇔ bounded on one thick set ⇔ point counts within `Cq^{n/2}` on one thick set [L]. Infinite rank: RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ bounded lag on a thick set of one tower ⇔ ZAL ∧ a positive (Toeplitz) count of one tower ⇔ ZAL ∧ thick `O(X^{½})` prime deviation [L]. A thick prime deviation `O(X^{½+a})` for every `a>0` gives AAL [L]. On continuous levels there is no rank barrier: `|Φ(L)|≤Me^{aL}` for all `L` ⇔ every zero `Re ρ≤½+a` [L] — the crude regime is the thick discrete one. In Frobenius-graph coordinates the self-improvement is free: `|c_B(log n)|≤Kn^σ` at every integer degree ⇔ width `≤σ`; any constant `K` ⇔ RH; degree sets with gaps `O(√x)` (the squares) suffice; prime planes give width `≤θ−½` from prime gaps `x^θ` (`≤1/12`, Huxley [S]) [L].

### 1.6 The archimedean Frobenius exists only approximately, and its precision is capped
At a `δ`-return of a set `P` of primes every `P`-smooth `n` has `|n^{−it}−1|≤Ω(n)δ`; Dirichlet polynomials on smooth integers freeze; `J` moment conditions force approximate vanishing to order `J` [L]. A Rouché copy of the forced zero at the return needs `δJ!<(r log N)^JN^{2r}`, so `J≤e²r log N+log(1/δ)`; the resulting Stepanov count of `r`-separated returns is the trivial separation bound [L/D]. Two distinct primes have no common exact return [L]. Over `𝔽_q` the Frobenius makes the order of vanishing as large as the degree allows; over ℤ the order is capped by the precision.

### 1.7 The window sign is one scalar flow; the critical curve is the window plus one inequality
RH ⇔ `Ψ=½log H₁` locally bounded ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` [L]. At the critical overlap `R=c⁸/log N`: `R_c=R_c^{PSD}=R_polar≤R_prim=R_high=W=⨅_A windowThreshold(A)`; every threshold `=⊤` ⇔ RH; `R_c≥c₁e^{c₂a}` and `R_high≥c₀e^{6a}` for `a≤a*(ζ)` [L]. Nonpositive whole-space sequences have normalized charged limits (collar profile + pole coordinate), polar rows converge to their sampled profiles, fixed windows keep their physical pairings, and payment at a larger ratio contradicts the limit [L]: the compactness passage is closed. What remains of the critical curve is polar payment at every `R<W` (B104).

### 1.8 The theta wall is ζ on the critical line
All ranks reduce to the adaptive head `M(b)=⌈|b|/2+B⌉`; its leading term is `|ζ(½+ib)|²+O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` [L]. The sign is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms near the critical zeros.

### 1.9 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)`; an Euler mollifier reaching them uses every prime up to `≍log²T` [L]; conditional tail laws stop at the Kronecker scale [L]. Past the height the Fejér mean value of the prime polynomial is a count of prime pairs at multiplicative distance `≲1/T`, of exact order `X²` (between `X²/log X` and `X²log²X`), dominating the diagonal once `X≫T log³X`; its constant is the Hardy–Littlewood pair constant [L].

### 1.10 The surface of Spec ℤ: the off-diagonal is two positive dampings and a rank-two pole; the diagonal is the sign
Off the diagonal, Weil's kernel `√(mn)W(m,n)=(m+n)−Γ_m·Γ_n` with `Γ_m·Γ_n` = archimedean + torsion [L]:
- the **archimedean Frobenius is a Green function of hyperbolic three-space**: on coprime orders `archKernel(m,n)/√(mn)=Σ_{k≥0}e^{−(2k+½)d}=2πG_{1/2}(d)`, `d=|log(n/m)|` the hyperbolic distance of `(0,0,m)` and `(0,0,n)` in upper half-space, the dilation `x↦nx` being translation along the vertical geodesic; `k=0` is the 𝔽₁-cusp, `k≥1` the jets of the trivial zeros [L];
- in Euclidean AdS₃ language `G_{1/2}` is the bulk propagator of a scalar of mass `m²=−¾` in the quantization `Δ=½`; `2πG_{1/2}=2πG_{3/2}+1/(2cosh(d/2))` [L]; Weil's archimedean + pole weight is `4πG_{1/2}(u)−4cosh(u/2)` [L];
- damped kernels `√(mn)e^{−d/2}/(1−r²e^{−2d})` are PSD and converge off the diagonal; the diagonal `n/(1−r²)` diverges like the Newtonian self-energy of a point of `ℍ³` [L];
- torsion is the Abel limit of positive twisted torsion energies on `ℙ¹_ℤ` [L]; the pole `m+n` has rank two [L];
- the archimedean kernel has infinite rank on coprime orders, and the compensation `C_∞(m,n)` changes sign exactly at the plastic ratio `n/m=ρ`, `ρ³=ρ+1`, the same number that bounds the Markov range of the even band [S/L];
- atomic Frobenius graphs need genus `≍N log N` on all degrees `≤N`, unconditionally, and this genus is carried by the jets (harmonic row sum `2N(1+log N)`); the primes contribute row sums `≤2N` [L].

So the sign sits in the diagonal: renormalized self-energies against a positive interaction energy plus a rank-two term. Renormalization carries no sign; damping is lossless [L].

### 1.11 The count
A count law has a quadratic half (a nondegenerate Born rule, the FE) and a count half (positivity, damping) [L]. Over ℤ the quadratic half holds (Hecke at `p` is an isometry of `Q`), RH ⇔ `Q` is the Tate limit of an `ℕ`-count, and `Q` itself is not integer-valued: integer Krein squares would make the spline series constant, hence RH, while under RH it is a nonconstant Bohr series [L]. Plane by plane: RH ⇔ every integer plane `⟨Γ₁,Γ_n⟩` carries a binary `ℕ`-count with Tate limit `c_B(0)x²+2c_B(log n)xy+c_B(0)y²` [L]. Over finite fields the corpus has counts defined before any form: resultant rings, radial cyclotomic counts converging to the discriminant height, Frobenius-stable orbit counts `q^{|I|}` of any permutation action, and an orientation cover whose point defect is the Möbius sum [L].

### 1.12 Production, Farey, the nerve, the core and the prime vertices are the Mertens level
Producer rates equal the Mertens level; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the prime-star nerve; the prime-vertex local indices are relative singular Euler characteristics of block/exit pairs, the exits are sphere bouquets, and `Σ_p index=1−M(N)`, with indices unbounded below [L]. Over `𝔽_q[T]` the Möbius sum is the point defect of the factor-trace orientation cover (Stickelberger), whose total count is exactly `qⁿ` for `n≥2` [L]; over `ℤ[ω]` Möbius is a cubic Gauss coefficient (composite cubic Gauss sums cube to `μ(I)p/|p|`) [L]. No ℤ-analogue of either structure is constructed.

### 1.13 Physics: every horizon observable is the width axis; internal, vacuum-fixing and half-sided realizations fail
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; its mirror-odd sector is a cavity of cusp forms and the zeros live in the mirror-even (Eisenstein) half [L]. Zero-free width `2δ` ⇔ ringdown `e^{−(δ−ε)τ}` ⇔ horocycle rate `y^{½+δ−ε}`; RH ⇔ `y^{¾−ε}` ⇔ universal decay `e^{−t/4}` [L]. Smooth profiles thermalize at `y^{½}exp(−√(−log y))`; the Narain AdS₃ remainder carries the VK saving; `¾` ⇒ RH [L]. On the operator side: internal partner unitaries are central and realize `Q` iff RH; vacuum-fixing partner unitaries make cross-horizon correlations multiplicative Hankel kernels, Hecke-invariant ones factor through the squarefree core, continuous profiles are constant; Borchers half-sided modular inclusions have no eigenvalues, are trivial on every graph black hole and kill alternating Cesàro averages, so neither their natural-cone forms nor their GNS norms have Tate limit `Q` [L]. In a GNS realization of `Q` the Hecke clock has pure point spectrum at the critical ordinates; the horizon's own translations have none.

### 1.14 Hull
Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH [L].

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms | [L] |
| Physical tearing at the collar boundary | Schur ratio `4/13` | [L] |
| The critical ratio as an independent sub-RH problem | `R_c=R_polar≤W`; only polar payment below `W` remains | [L] |
| Uniform logarithmic Gamma reserve in coefficient norm | resonant two-copy profiles | [L] |
| Fixed theta heads; summable absolute pair majorants; compact cores | no margin; harmonic diagonal; geometric growth | [L/S] |
| Positive Laplace representations of the theta amplitude | excluded | [L] |
| Fixed or limiting amplitude locking | adds nothing | [L] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0`; family-uniform finite-stratum laws | blind; RH-strength | [L] |
| Barriers, short detectors and weights | blind to purity | [L] |
| Moment data for the log-mean; outer mollifiers for the inner mass | blind | [L] |
| Asymptotic or local-below zero statistics as inputs to any level of the dial | cannot decide | [L] |
| FE, order one and reality as exclusion of a finite layer | `cosh` and two-scale `cosh` models | [L] |
| Positivity, Euler products, integer norms, linear counting, continuation, reflection symmetry, positive Hecke combinations as AAL | finite layers exist | [L] |
| Density statements on levels of a tower | rank barrier | [L] |
| Elimination without well-foundedness | Wolff towers | [L] |
| Exact returns as a Frobenius; norm-majorant Rouché copies at returns | one fixed point; trivial separation bound | [L] |
| Diagonal moments, group closure, early orbit against a return | blind | [L] |
| Slow-return bounds on discs crossing `Re s=½` | the premise is RH | [L] |
| Schur, `C*`, KMS, reflection positivity, internal modular conjugation, vacuum-fixing partners, Borchers half-sided inclusions as zero locators or carriers of `Q` | blind; central collapse; square-class collapse; no eigenvalues | [L] |
| Positive Poisson measure of the Hecke algebra; positive Hecke polynomials | hold off the line; annihilate finite resonance sets | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping | fakes carry all | [L] |
| Linear counts as count laws; Hecke at a second place; `Q` as its own count | degenerate; conservation only; not integer-valued | [L] |
| Narain remainder past `¾`; sharp sources at the RH rate | impossible; need Möbius × circle cancellation | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level | [L] |
| Polynomial ledgers as parity input at zeros | twin shares every leading pole | [L] |
| Bounded count error as a selector | new zero with signed generators | [L] |
| Mean spectra as detectors of zero relocation | relocation invisible | [L] |
| Discrete Morse matchings; fixed-point localization in cardinality; persistence | Betti `≍N`; primes fixed with unbounded indices; `s`-independent | [L/D] |
| Renormalized torsion forms under finite constraints | both signs survive | [L] |
| Renormalization as a source of sign | any form arises | [L] |
| Metrics on `ℙ¹_ℤ`, toric pairings, continuous Hecke kernels, finite-rank kernels as carriers of the archimedean place | excluded; the carrier is `ℍ³` | [L/S] |
| Finite-genus atomic Frobenius graphs | genus `≍N log N` | [L] |
| Thermal averaging (primon gas) as a strip input | Euler factors at real points `>1` | [L] |
| Extremal-angle position alone; rotated relations of small growth | polynomial model; trivial | [L] |
| Shrinking-mesh pure Euler approximants | Euler abscissa escapes | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with zero location (Turing count), first `T≈10²–10³` | all rungs | `hardySEM` sign chains; Fejér budget |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2 or rigorous Galerkin |
| A4 | Theta rank 15 and beyond at every `0<a≤½`, one rank at a time (unverified past 14) | TH | radius-12 power core, height 67, coupled current tail |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` (unverified; statement unsettled) | ACT | finite case analysis |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | SOSZ, HF, ACS | window rungs (A1) |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | AIP, HF | gcd-defect coercivity through `M₀(N)` |

### Exceptional coordinate, flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | BAG, ZCG, PTT | fixed-resonator limit, arithmetic mean values |
| A47 | The one-quartet world: explicit window constants of the tower theorems for one top quartet `Θ±iγ` at base `π/γ` (size of `ε`, onset level, dependence on `γ` and `Θ−½`) and the constraint each finite-stratum receiver imposes on `(Θ,γ)` (unverified) | ZCG, WL, IWT | `eventually_lag_large_of_single_top_pair`, finite-stratum TFAE [L] |
| A49 | Assemble "thick crude Hasse–Weil for smoothed Frobenius graphs ⇒ AAL": the spline zero sum `c_B(t)=Re ΣF(z)e^{zt}` with `Σ‖F(z)‖‖z‖<∞` and every off-line zero visible is a Weil tower at every base; apply the window theorem | ACS, SOSZ, WL, IWT | `TheTowersOfZeta`, `HasseWeilAtTheIntegerDegrees` [L] |
| A50 | Finite-stratum laws on other positive deformation families (cosine shifts `A_h`, shifted Jensen families) imply RH, as for the heat family (unverified) | ZCG, PTR, LA | `TheFiniteStratumLawOnTheHeatFamilyIsRH` [L] |

### Theta, horizon, counts, production, descent, topology
| # | Task | Routes | Basis |
|---|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` proved |
| A28 | Reciprocal quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | exact projective quadric counts |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale, three-quarter floor |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue, continued Fourier modes |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | ACS, PM, CTH | crude-bound self-improvement on thick sets [L] |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to `M=M(b)≈\|b\|/2` with effective error (unverified) | TH | fixed-`M` asymptotic [L]; adaptive partial sum `=ζ(½+ib)+O(\|b\|^{−½})` [L] |
| A43 | Identify the continued `Λ_g` with a Gamma factor times `L(g×ḡ,s)` on ℂ | PM, BHR | eigenform RS Euler product on `Re s>2` [L]; continuation and FE [L]; uniqueness of continuation |
| A46 | Local singular indices of prime vertices beyond the cubic cutoff `N>p³` (unverified) | MC, RIAC | discrete-exit computation [L] |
| A51 | Prime-plane width bound with the prime-gap exponent `0.525` (width `≤0.025`) [C] | ACS, SOSZ | gap-exponent transfer [S] |
| A52 | Integrate the unfinished pieces: infinite rank and plastic sign of the archimedean Frobenius, prime-plane width bound, logarithmic torsion bound | SOSZ, RIAC | proved source [S] |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Variation of `r` free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH | RW, GWZ, WTZ, HF |
| B6 | Full-space sign eventually at every `K`; every critical threshold `=⊤` | RH | HF, SRT, AIP |
| B8 | Head thresholds for every `d` | RH | HF, AHD |
| B9 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B10 | Top coprime stratum | RH | HF, ACS, ADT |
| B11 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B13 | Finitely many off-line zeros of ζ ⇒ none (bottom of the dial); its heat-family extension is RH | sub | whole programme (§3) |
| B14 | Any interior width value (window negativity exponent `<½`; horocycle, Farey, pulse, Narain, spline-orbit or integer-degree exponent past the trivial one) | ≥qRH | width axis |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16 | Decay law of `λ*(c)` | sub | CHT, RW |
| B17 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW, PBAP |
| B19 | Exact torus law for `S*(a,b)`; `{2,3}` cross-chain positivity | model | TH |
| B20 | Oscillation of the actual amplitude with the height | RH (all primes) | TH |
| B21 | All theta ranks at every `a` | RH | TH |
| B22 | Outer-root control of `R_d(Ξ)` | RH | LA |
| B23 | `N_d` bounded | ≥qRH | LA, FFP |
| B24 | Collision exclusion at small time, every height | RH | ZCG |
| B25 | Frequency `<1` at every collision | RH | ZCG |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method | ZCG, TH |
| B27 | Runs of `k` simple critical zeros, every `k` | sub | ZCG, census |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub | RW, ZCG, WD, ACS |
| B29 | Cosine Laguerre sign below VK | RH | PTR |
| B30 | Heat grids at every degree; Gaussian prime ceiling at every rational height | RH | HCF |
| B31 | Hausdorff signs below the explicit shift | RH | PA |
| B32 | Self-map discs covering every zero | RH | XN |
| B33 | Cofinally small quartic charge | RH | GTA |
| B34 | `C_t` at every fixed `0<t<½` | RH | TT |
| B35 | Unnormalized prime wave bound; complete odd sign | RH | CHMD |
| B36 | Joint-node exclusion | RH | RN |
| B37 | Bounded `A_N` | RH | SZ |
| B38 | Cubic trace norm `<1` | RH | TG |
| B39 | Damped coupling bound; sublinear tensor loss | RH | SC |
| B40 | Source-energy sign | RH | ACS |
| B41 | Source-work ceiling `≤2` | RH | HF |
| B42 | Complete-history floors | RH | FU, CFC, RP |
| B43 | Li budget or response floor | RH | LI |
| B44 | Retained-variance payment; one shift uniform in profile | RH | ACT, OWU, EWU |
| B45 | `C_σe^{2σr}` signed cost bound | RH | AIP |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights; no early heavy return | sub (up to shielding) | RW, all rungs, PTT |
| B47 | Multiplicity `o(log X)` by an input not reducible to size | sub | ZCG |
| B101 | Polar payment at every ratio on growing windows | RH | HF, AIP, SRT |
| B102 | Sign of the adaptive theta head at every degree; leading term `\|ζ(½+ib)\|²`, decided near the critical zeros | RH (all ranks) | TH |
| B104 | Polar payment at every ratio below `W`, equivalently `R_polar=W` | method | HF, SRT, AIP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision; a crude zero-localized prime count at every level | RH | WL, MC, PBM, RB, JAS, CTF, HCF |
| B49 | Bounded endpoint energy; integer lag ceiling | RH | WL |
| B50 | Trivial-gauge half power; zero exclusion for `M_X` | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Depth density `o(T)`, equivalently log-mean `→0` | sub | WD, census, MC, RW, ZCG, CTF, PM |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall | sub | WD, ZCG |
| B60 | Exponential moments of the Green potential at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |
| B66 | Near-unit holomorphic budgets; zero dilation surplus | RH | CTF, WD, AIF |
| B67 | Parity at power saving | ≥qRH | WL, MC |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH | RAC, CTF |
| B94 | Identification of the cubic Gauss coefficients with an automorphic theta expansion; transfer to rational-integer Möbius | past VK at least | MC, MMD |
| B96 | Conditional law of the Euler tail at the Kronecker scale; lower bounds for exact tail events | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of every heavy subset: `log R(y,δ)≥y^c` for fixed `δ` | sub | PTT, TAPO, BAG |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural relative pair with `χ=M(N)`, or a natural self-map or action whose signed fixed-point indices localize `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) | MC, HF, ESG, HHAC, RIAC |
| B110 | **Thick crude count**: `primeDeviation(X)=O_a(X^{½+a})` along a thick set of geometric scales of one base, for every `a>0` | AAL (with ZAL at `a=0`: RH) | WL, ZCG, ACS, IWT |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH | PM (sharp shells) |
| B119 | Prime gaps `O(x^{½+ε})` (the prime planes decide RH through the gap transfer iff) | sub [C open] | ACS, SOSZ |
| B120 | An orientation cover over the integers: a natural double cover whose point defect over `n` is `μ(n)` and whose total count obeys a trace formula | producer | MC, RIAC, ESG |
| B121 | Freezing control beyond the precision cap: a Stepanov count at returns through signed freezing or integrality | sub | BAG, ACS, PTT, IWT |

### Γ — selection, reflection and transport
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH | PM |
| B69 | Positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Lower bound for `V_p` from the carrier | sub | PM |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey or Narain rate `y^{¾−ε}` | RH | PM, BHR, CTH |
| B72 | Cutoff-uniform target mass | RH | BAG |
| B73 | Factorial-Fock bound at actual zeros | RH | SEC |
| B74 | Proof-erasure equality at actual zeros | RH | CDC |
| B75 | Reflection-odd class vanishes at actual zeros | RH | PCS |
| B76 | FE-pair reality with coverage | RH | ZCG, ADO |
| B77 | `0∉E` | indep. | ADO |
| B78 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, PM |
| B79 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B80 | FE twins with off-line zeros in the full class | sub | SEL |
| B81 | Candidate landings | producer | candidates |
| B82 | Inner-field decay `I(½+h+it)→0` | ≥qRH | BAG, AIF |
| B83 | AAL | sub | BAG, JAS, SC, ZCG, WL, IWT |
| B84 | Smallest FE defect of a discrete Euler product carrying a finite off-line layer (§2.5) | method | BAG, ACS, APD |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank | RH | ACS |
| B87 | A nonnegative count on integer probes, defined without `Q`, with Tate limit `Q` (a genuine limit: `Q` is not integer-valued) | RH | ACS, HF, PM, RW, AE, CTH, SOSZ |
| B88 | A counterterm-free damping presentation of the diagonal of Weil's form (off the diagonal: rank-two pole − `ℍ³` Green function − torsion energy, all known) | RH | AE, HHAC, SOSZ, RIAC, HF |
| B89 | A bounded aligned return at each right zero on a right disc | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B95 | Abelian group with Hecke endomorphisms whose trace form is `Q` | producer | ACS, AE |
| B103 | Positive discrete Euler products with linear counting, continuation across `Re s=½` and an FE: AAL? | method / sub | BAG, APD, ZCG |
| B109 | Rankin–Selberg noncancellation: some cusp form `g` with `Λ_g(ρ/2)≠0` at every off-line zero | indep. | PM, BHR |
| B111 | **`ZAL ⇒ RH`** (existential linear AAL): `Θ∞=½ ⇒ Θ=½` | sub | BAG, ZCG, IWT, WL |
| B112 | A mechanism converting the FE (a height reflection) into vertical transport of zeros, using the Euler product and coupling both scales | sub | BAG, ZCG, APD |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer | PM, CTH |
| B116 | Linear AAL at one fixed slope `C≥1` (⇔ thick relative crude count at exponent `½+C(Θ∞−½)+ε`) | sub | ZCG, IWT, WL |
| B117 | A confined companion of the modular horizon (§2.7) | producer | PM, BHR, ASH, CTH |
| B118 | A hyperbolic-three-orbifold Arakelov theory in which Weil's kernel is an automorphic Green function at `s=½` and the diagonal counterterm a Robin constant (§2.8) | producer | SOSZ, ACS, HF |
| — | ZAL | ≥qRH | whole programme |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has at least one open input. The assemblies whose output is RH (F1, F22, F15) need inputs of RH, AAL or ≥qRH strength. The others collapse independent problems into one or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (incl. thick lag, thick prime deviation, positive count of one tower) with any ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, LH with every cosine-shift level eventually real, high-collision counts) | RH [L] | one AAL input (B83) and one ZAL input (≥qRH) | the two-input assembly with output RH |
| F2 | **Critical curve = window + polar payment.** Threshold identities, charged compactness, conductor resolution, low packet at every ratio | `R_c=R_polar≤W`; HF, SRT, AIP critical branches are the window problem of RW plus one inequality [L] | B104 | the critical curve carries no further sub-RH content |
| F3 | CSTW traces and flow, AIF restoring bound | RH ⇔ `Ψ` locally bounded [L] | B2 | the tower is one local boundedness statement |
| F4 | ACS typical sign, AIF onset field, frequency packets, WVL visibility, ZCG sharp location | negativity at aperture `K log log T` on heights of measure `≤T^{1−1/(64K)}` [L] | B28, B46 | first sign past bounded aperture on typical heights; cannot reach the dial |
| F5 | Log-mean equivalences, Selberg `O(T)` depth, Carleson measure, Euler mollifier length `log²T` | typical-height layer = depth density `o(T)`; any Euler mollifier reaching it uses the primes `≤c log²T` [L] | B57 | one target for RW, ZCG, WD, CTF, PM |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets | deep zeros obey rate 2 or carry a large Green potential [L] | B60 | density exponent near `½` |
| F7 | **One edge.** Pronic domination, flux, FFP drift, Euler coordinates, Hecke Poisson measure, positive Hecke annihilators, primon means, Hecke state on `Aff(ℚ)` | positivity reaches `Re s=1`, and `Re s=½` only as a threshold [L/D] | B68, B70 | marks what positivity reaches |
| F8 | **Theta wall.** Column calculus, carrier horizon, Ξ-current lift, adaptive head, Gamma reserve, partial sum `=ζ(½+ib)` | all ranks reduce to `\|ζ(½+ib)\|²` plus second-order terms near the zeros [L] | A42, B102 | merges TH with the size of ζ on the line |
| F9 | Rate law, producers, three-quarter floor, quarter rate, twin floor, cut kernel, parity identity, Frobenius = factorial stencil | stencils, parity, twin pairs and strips are one axis [L] | B15 | closes production and parity as independent routes |
| F10 | One verified height, all rungs, cone PNT | all finite rungs [L] | nothing finite | decides no all-rank statement and no level of the dial |
| F11 | VK savings of all routes incl. Narain, horocycle, integer-degree crude bounds | one width axis [L] | B15 | they share one input |
| F12 | **Rigid ¬AAL world.** Finite oscillation, dilation annihilation, jets with long-shift `m²`, tower excursions at every base, single top pair seen at every level of its resonant tower, tail-bad returns, qRH, FE pairing top and bottom layers, annihilator inverse oscillation | a contradiction search on one rigid world [L] | any contradiction; it must use the Euler product and the FE together and couple scales | decides B83 if it succeeds |
| F13 | **Isolation.** FE-defect rigidity `1/6400`, count distance, parity identity, Selberg degree one, relocation first-gap obstruction | ζ is a singleton in three metrics [L] | B84, B98 | every stable argument in these metrics is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Szegő-ratio dilation | over a curve Castelnuovo ⇔ budgets reach 1; over ℤ every piece except the bound [L] | B66 | states what a Castelnuovo over ℤ must assert |
| F15 | **Count skeleton.** Hecke isometry of `Q`, Tate principle both ways, point-count defect on curves, half-products, `ℍ³` archimedean fibre, positive torsion energy, critical weight, plane counts, `Q` not integer-valued | every ingredient of the curve count proof except a count over ℤ; the off-diagonal as positive dampings; the diagonal the missing positive damping [L] | B87, B88 | output RH; names the missing object exactly |
| F16 | **Horizon.** AdS₄ quotient, fakes, Hecke rigidity, Krein law, KMS, throats, genus-two graph, Born rules, boundary algebra, standard-form trichotomy, half-sided exclusion, odd cavity, all horizon receivers | physics reduced to one positivity for one involution; internal, vacuum-fixing and half-sided realizations excluded [L] | B68, B71, B87, B114, B117 | closes waves, Hecke, KMS, reflection, modular conjugation and half-sided inclusions as sources |
| F17 | **Dark range.** Savings, precision law, heavy-return dictionary, almost-every-height cancellation, collision counts of order `X²`, precision cap of forced vanishing | the short-sum barrier is one first-return statement; phase-freezing producers are capped [L] | B97, B121 | gap: precision `y^{−9/2}` against constant precision |
| F18 | **AAL tail form.** Tail transport, near-full tail events of positive density, partial returns, short-arc prime mass, recurrence dichotomy, conditional moments | AAL ⇔ exact rare tail events at every right zero; approximate events abundant; proved results bound exact events from above [L] | B89, B96 lower bounds | one tail statement: `η→0` at right zeros |
| F19 | Agler wall, Euler coordinates, head–tail certificate, Ξ-current lift | certificates exist exactly at tail-good heights [L/D] | B96 | one tail law for TH, PTT and BAG |
| F20 | **Mertens in seven geometries.** Franel–Landau, Farey law, nerve, core, barcode, prime-vertex indices (`Σ=1−M(N)`), Zagier horocycle law | one exponent [L] | B14, B15, B50, B106 | topological and dynamical tools act on the Mertens level |
| F21 | **Firewall + two-scale law + `cosh` models + heat family** | every input using only positivity, Euler products, linear counting, continuation, reflection symmetry, FE with analytic shape, family-uniform laws, or scale-separated statistics is refuted [L] | B112 | names the ingredient left: a two-scale Dirichlet-series statement using Euler product and FE together, with the FE as transport |
| F22 | **Curve template over ℤ.** Elimination at infinite rank, towers of ζ, crude step as Toeplitz count, thick crude count ⇒ AAL, ZAL = well-foundedness, FE = Born rule, count = Tate limit, linear six-way TFAE | RH = ZAL + thick `√X` count; AAL = thick crude count at every `a>0`; each slope `C` = a relative thick count [L] | B110 and ZAL | the elimination step exists over ℤ; the two missing inputs are a thick crude count and well-foundedness |
| F23 | **Theta at the zeros.** Adaptive head `=\|ζ(½+ib)\|²`, FE-pair flatness, negative moments | the theta sign is decided where `\|ζ(½+ib)\|` is small [L/D] | A42, B102, Π54 | joins TH (Σ) to the negative-moment wall (Π) |
| F24 | **Topology meets the horizon.** Core Euler characteristic, prime-vertex indices, square-root Farey law, `SL₂(ℤ)` on Farey fractions | the only arithmetic action carrying `M(N)` as a deviation acts on the Farey model [L/D] | B106 | turns B106 into one construction |
| F25 | **Count through `ℍ³`, torsion and the pole.** `ℍ³` Green function at `s=½`, positive torsion energies, rank-two pole, critical weight, compensation exponent 2, atomic genus `N log N` | off the diagonal Weil's kernel is pole − two positive dampings; the atomic diagonal is the archimedean self-energy; the arithmetic is lower order [L] | B88 | the count must renormalize a Newtonian self-energy in `ℍ³` by a damping, not a counterterm |
| F26 | **Two-scale tower input.** Towers of ζ at every base, exceptional rank, thick sets, Fejér collision counts, Euler mollifier length, partial returns | a thick crude count is a statement about the prime deviation on long runs of geometric scales, i.e. about long mean values past the height, which are binary collision counts [L/D] | B110 | joins the IWT door to the dark range |
| F27 | **Standard-form physics.** Tomita collapse, vacuum-fixing square-class collapse, Borchers exclusion, graph standard forms iff damped, odd cavity | a realization of `Q` must give the Hecke clock point spectrum without fixing the vacuum and without a Borchers scaling; the horizon carries the zeros as resonances [L/D] | B114, B117 | turns the physical sign into a resonance-to-normal-mode question (§2.7) |
| F28 | **Frobenius graphs + towers.** Integer-degree Hasse–Weil, crude bound = width, sparse and prime degrees, spline zero sum, IWT window theorem | Hasse–Weil at every integer degree with any constant = RH; on a thick set of geometric degrees = AAL [L/D, A49] | B110 in graph form | one geometric statement for SOSZ, ACS, IWT and WL |
| F29 | **Euler + FE calibration ladder.** Finite-rank local squares, Beurling FE rigidity, Selberg degree one, heat family, one-offs, `cosh` models | Euler product + FE force purity at finite rank and identify ζ in the Beurling class; every model with a finite layer lacks one of the two [L] | B112, B13 | fixes the B13 input as the infinite-rank form of an Euler–FE rigidity |
| F30 | **Finite-field counts.** Resultant rings, radial cyclotomic counts, Frobenius orbit counts, orientation cover, cubic Gauss conversion | Möbius as point defect over `𝔽_q[T]`, as cubic Gauss coefficient over `ℤ[ω]`; counts before the form [L] | B87, B94, B120 | names the ℤ-object a count must be (§2.8) |

**Closest to the open core: F22, F21, F29, F25, F28.** F22 names the two missing inputs of the curve template over ℤ. F21 and F29 fix what the dial input must contain. F25 locates the sign in the self-energy of a point of `ℍ³`. F28 puts the crude step in Frobenius-graph form.

### The rigid ¬AAL world: what a contradiction search may assume (F12)
| In the world ¬AAL | Evidence |
|---|---|
| Isolated top `Θ`, rest left of `Θ₂<Θ`, bottom layer reflected at the same heights, higher zeros in `\|Re z−½\|≤Θ−½` | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, sign changes at bounded log gap | [L] |
| `Θ∞<Θ`: `ψ(x)−x` is `O(x^{Θ∞+ε})` after removing finitely many exponential terms, and not before | [L] |
| Two-prime dilation annihilation of `ψ`; a positive annihilator of the top whose inverse oscillates at every exponent `<Θ` | [L] |
| At every base, syndetic lag excursions `\|Φ(νℓ)\|>Ce^{aνℓ}`; single top pair: every level at base `π/γ` | [L] |
| Polar ground energy `≤−c′e^{2(Θ−½)B}/B³`; lag excursions of positive lower Abel density | [L] |
| `Λ`-moments: diagonal `→0`, long-shift correlation `→m²` | [L] |
| Every return at a top zero tail-bad; transport events rare; near-full tail events abundant | [L] |
| Zero-free strip `(Θ₂,Θ)` above the layer's heights; qRH | [L] |
| The layer is not a rational relocation of critical zeros of ζ with positive coefficients | [L] |

No contradiction comes from exact identities, from positivity, Euler products, counting or positive Hecke combinations alone, from the FE with order one and reality, from a property shared by the heat family, or from statistics at one scale [L].

## 2.4 Breakthrough question below RH and quasi-RH: the thick crude count

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

**Question.** *Is the prime deviation square-root small along arbitrarily long runs of geometric scales?* Precisely (B110): is there a base `ℓ>0` and a thick set `G` of levels (arbitrarily long runs arbitrarily far out) such that for every `a>0`

  `|(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)| ≤ C_a X^{½+a}`  for `X=e^{νℓ}`, `ν∈G`?

**Four faces of one statement.**
| Coordinate | Form | Evidence |
|---|---|---|
| Prime side | the inequality above | [L] |
| Weil tower | `\|Φ(νℓ)\|≤C_ae^{aνℓ}` on a thick set of levels of one tower | [L] |
| Count | at `a=0`: the lag kernel `k_ℓ(ν)=Φ(νℓ)` of one tower is Toeplitz positive (a positive count) | [L] |
| Frobenius graphs | crude Hasse–Weil `\|c_B(νℓ)\|≤C_ae^{aνℓ}` on a thick set of geometric degrees | [D, A49] |

**What it gives [L].** AAL (`asymptoticAbscissaLaw_of_thick_primeDeviation_bound`). With ZAL at `a=0`, RH. At a fixed `a` it excludes every isolated top above `½+a`. In relative form — exponent `½+C(Θ∞−½)+ε` — it is exactly the linear law `LinAt C` (six-way TFAE).

**Why this question.**
- **It is the crude step of the curve proof over ℤ.** Elimination is proved at infinite rank on thick sets; the self-improvement at the integer degrees is free; what is missing is exactly a crude bound on a thick set of levels. On curves Stepanov supplies it.
- **It sits exactly between two proved boundaries.** On continuous levels a crude bound at exponent `a` is a zero-free half-plane (quasi-RH); on sets of levels of density `1−1/k` no bound self-improves (rank barrier). The thick discrete set is the one regime where a crude bound is sub-RH and still decisive.
- **It has the shape the five boundaries demand.** A bound on the prime side at scale `X` sees every zero through the explicit formula, low and high together, so it is neither asymptotic nor local-below; it is a statement about `ψ`, so it uses the Dirichlet series and the Euler product; it is not shared by the heat family, the `cosh` models or the one-offs.
- **It is false on every fake that matters.** Beurling one-offs: the deviation is `≍X^{3/5}` at every level of the resonant tower. The golden fake: unbounded on every thick set. Wolff towers: bounded but not well-founded, and not prime sides. `cosh` models: no prime side.
- **It lies on the dark range, with its producer named.** On a run `[Y,Ye^{kℓ}]` the deviation is governed by Dirichlet polynomials longer than the height, whose mean values are counts of prime pairs at multiplicative distance `≲1/T` of exact order `X²` (Π122). Phase-freezing producers are capped at the trivial bound (Π121); integrality producers stop at Chebyshev (Π66). An answer needs cancellation in prime-pair collision counts on long runs of scales, or a freezing control beyond the cap.

**Tests.** T1: RH gives `O(X^{½}log²X)` everywhere; B110 implies AAL, which does not imply quasi-RH. T2: a stated inequality. T3: AAL; RH with ZAL; each slope `C` [L]. T4: a finite rung cannot produce arbitrarily long runs arbitrarily far out. T5: fails on Beurling one-offs and the golden fake [L]. T6: inputs are prime-side counts on thick sets; none is refuted. T7: moves Γ68, Γ69, Π114, Γ155, B83.

**Limits.** It does not give ZAL. It is at least AAL-hard. A world with AAL and infinitely many off-line zeros accumulating to some `Θ>½` is not excluded by it.

### Alternatives
| Question | Why it matters | Tests | Limit |
|---|---|---|---|
| Polar payment below `W` (B104) | collapses the whole critical curve to the window threshold | T1–T4, T7 pass; T5 vacuous | method strength: moves no wall of Π or Γ |
| Depth density `o(T)` (B57) | closes the typical-height layer for RW, ZCG, WD, CTF, PM | T1–T7 pass | asymptotic: cannot touch any level of the dial |
| Constant-precision first return (B97) | sign-free crude step on the dark range (§2.6) | T1 [L, RH bracket] | past VK |
| Rankin–Selberg noncancellation (B109) | turns the cusp-energy rate into a full receiver | T1 vacuous | adds a receiver |
| Prime gaps `O(x^{½+ε})` (B119) | the prime planes then decide RH | T1 pass, T5 n/a | classical problem; strength above qRH through the transfer |

## 2.5 Breakthrough question below AAL, RH and quasi-RH: how much functional equation does a finite layer cost?

**Why not a zero law.** On configurations the dial is strict, `AAL ⊊ LinAt C ⊊ (ZAL⇒RH) ⊊ B13`, and B13 is its bottom [L]. Every statement below AAL that constrains the zeros of ζ contains B13: every transport law (a right zero forces off-line zeros at larger heights, at any depth), every linear slope, and `ZAL⇒RH` [L/D]. B13 is an exceptional-zero problem of Landau–Siegel type. A tractable question below AAL therefore cannot be a law for the zeros of ζ; it has to be a question about the mechanism an AAL proof must use.

**The mechanism.** Five theorems leave one ingredient: the Euler product and the FE used together (§1.3). Two proved facts bracket it. At finite rank the two force purity: a finite Euler product with an FE of conductor `ΠP` has `a_p²=p` and every zero on `Re s=½` [L]. In the Beurling class an FE with defect `≤1/6400` forces the rational primes [L]. What no theorem decides is whether the FE excludes finite layers **stably** — at positive defect, for systems other than ζ — or **only through rigidity**, by forcing the system to be ζ.

**The question (B84).** *What is the smallest functional-equation defect of a discrete Euler product that carries a finite off-line layer?* Precisely: among discrete Beurling systems (prime atoms `p_k>1`) whose zeta continues to a neighbourhood of `Re s=½` with the regularity required by the rigidity theorem, let `D_layer` be the infimum of the FE defect over systems with a finite nonempty off-line layer. Rigidity gives defect `≥1/6400` for every system other than the rational primes. Is `D_layer` finite, and how close to `1/6400` is it?

**First step: construct a discrete one-off with finite FE defect.** The corpus discrete one-off follows the continuous one-off's prime count to within one, `|N−W|≤1`, and therefore blows up at `s=½`: its prime squares give `R(σ)≥½Σ_kp_k^{−2σ}→∞` as `σ→½⁺` [L, `ADiscreteBeurlingOneOff`]. The blow-up comes from matching the count of primes alone. Matching instead the full prime-power count `Π_P(x)=Σ_{p_k^m≤x}1/m` to the continuous `Π_c` within `O(1)` (a greedy choice of atoms does this, since the prime-power jumps are `≤½` and of total size `O(√x)`) gives `ζ_P=ζ_c·exp(s∫x^{−s−1}(Π_P−Π_c)dx)`, a nonvanishing factor on `Re s>0` times the continuous one-off, which continues across `½` with exactly the finite layer `(1−μ)±iγ` [L for `ζ_c`; D for the factor]. What remains is the concrete analytic obstacle: the factor must have finite order on the critical line, which needs the atoms' Dirichlet series `Σp_k^{−s}` to grow at most logarithmically in `|t|` — a choice of atoms with controlled exponential sums (near-integer atoms, or atoms from an auxiliary Beurling system with known Weyl sums). Then the FE defect is an explicit integral of `ζ_P` against its reflection and can be computed.

**What either answer gives.**
| Answer | Effect on AAL research |
|---|---|
| A discrete one-off with finite FE defect `D` exists | the FE has no stable exclusion power at defect `D`; with the rigidity window `[0,1/6400)` this says the FE excludes finite layers only by pinning the system to the rational primes. Every B13 or AAL argument must use the exact FE of ζ; deformation, compactness and stability arguments in spaces of Euler products are dead; the toolkit is exact identities (local squares, Hamburger-type rigidity). The value of `D_layer` measures how close a fake can come to ζ. |
| Every construction is forced to infinite defect (blow-up at `½` or infinite order) | evidence, and a target theorem, that continuation across the line with finite FE defect is incompatible with a finite layer for discrete Euler products other than ζ: a stable Euler–FE exclusion mechanism exists. Its proof in the class of non-ζ systems is the first theorem of the type B112 asks for, and the template for B13. |

**Why this question.**
- **It is about the only unrefuted ingredient.** Positivity, Euler products alone, linear counting, continuation alone, FE alone, family-uniform laws and scale-separated statistics are refuted as AAL inputs [L]; the Euler product together with the FE is what remains, and this question decides in which form it can work.
- **It is not a famous problem in disguise.** It asks for a construction in a class the corpus already builds (continuous, discrete, integer-norm and rational-prime one-offs) plus a computation of a defect; neither answer implies B13 for ζ.
- **It has a definite first step and a named obstacle.** The blow-up mechanism of the existing discrete one-off is identified in Lean; the replacement (prime-power matching) is explicit; the remaining difficulty is growth of one auxiliary Dirichlet series on one line.
- **It sharpens two walls at once.** B103 (positive discrete Euler products with continuation and an FE: AAL?) and B84 (smallest FE defect carrying a one-off) become one quantitative question.

**Tests.** T1: not applicable (a method question, implied by nothing about ζ's zeros). T2: a stated quantity `D_layer`. T3: the effects table. T4: not a finite rung. T5: calibrated on the corpus fakes by construction. T6: prime-power matching and controlled atom sums; neither refuted. T7: moves Γ73, Γ124, Γ145, Γ161, B84, B103. T8 (tractability): not itself a long-standing open problem; its first step is a construction with one named analytic obstacle.

**Limit.** It decides the form of the mechanism, not AAL. If the FE works only through rigidity, the remaining AAL problem is a statement about the exact arithmetic of ζ, of Landau–Siegel type.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalues, spectral decompositions, Hilbert–Pólya realizations, trace formulas, spectral gaps, Lax–Phillips semigroups, standard forms. Counts used through their nonnegativity, Hodge index and Tate limits fall under positivity. Kept: Fourier analysis, mean values used as bounds, exponential sums, power sums, Vandermonde and Turán, Dirichlet polynomials, integrality, Diophantine approximation and transcendence, reciprocity, recurrence, almost periodicity, Jensen and Rouché.

**What survives [L].** The curve proof for every hyperelliptic curve is Stepanov's auxiliary polynomial, power-sum elimination and the FE. Over ℤ three of its steps are proved and sign-free: elimination at the exceptional rank on thick sets (Vandermonde), the free self-improvement at the integer degrees (Lipschitz propagation), and the finite-rank Euler–FE purity theorem (an identity of Dirichlet polynomials). Three sign-free producers are proved and capped: integrality reaches Chebyshev (Π66), phase-freezing Rouché copies reach the trivial separation bound (Π121), exponential sums reach VK (Π51). What falls: all of Σ, the PM Krein, Lax–Phillips, cusp-energy and standard-form branches, the index routes, the count door.

**The question.** *Are the logarithms of the primes quantitatively independent at constant precision?* Precisely (B97): for a fixed precision `δ∈(0,1)`, is the first `t>0` at which all phases `t log p`, `p≤y`, lie within `δ` of `2πℤ` at least `exp(y^c)` for some `c>0` — and does the same hold for every heavy subset of the primes below `y`?

**Why it opens the path.**
- **It is the producer gap of the sign-free curve proof.** The crude count over ℤ fails exactly where the prime orbit returns: at a heavy early return a long prime polynomial is large, and a zero can hide under it (proportional saving ⇔ no early heavy return, Π95). The Frobenius over `𝔽_q` has no returns to fear, because the auxiliary polynomial vanishes exactly at every point; over ℤ the returns are the obstruction.
- **It is a Diophantine statement, not a sign.** Returns are simultaneous approximations to `2πℤ` by multiples of `(log p)_{p≤y}`. Transcendence methods (auxiliary functions with integer coefficients, extrapolation, zero estimates) are the sign-free tools for such lower bounds, and integrality — `|n|≥1` for a nonzero integer — is the one sign-free mechanism that turns approximate vanishing into exact vanishing, which is exactly what the precision cap says Rouché cannot do (EAHT: small integer auxiliaries are divisible).
- **Its consequences are proved receivers.** Constant-precision returns at `exp(y^c)` give proportional saving at length `(log X)^{2K}` at all heights (B46), the all-height sign past the size curve, and the exclusion of isolated zeros of depth beyond the visibility threshold [L/D]; with the sign-free elimination on thick sets, they feed a thick crude count.
- **It is bracketed.** Unconditionally `log R(y,δ)` lies between `(log y)^{3/2−o(1)}` (VK) and `y/log y` (Dirichlet); under RH it is `≥c√(y/log y)` [L]. The question asks for any power of `y`.

**First rungs.** (i) Two primes: continued fractions of `log 3/log 2` give polynomial return bounds [L]. (ii) A fixed number `k` of primes: Baker–Wüstholz bounds each linear form in `k` logarithms [C]; the question is the passage from `k` to `π(y)`. (iii) `𝔽_q[T]`: the Frobenius is exact and there are no returns to bound [L].

**Tests.** T1: implied by RH [L, RH bracket]. T2: an inequality. T3: B46, the all-height sign, isolated-zero exclusion [L/D]. T4: no finite rung. T5: fails for impure columns and for rounded orbits [L]. T6: transcendence with integrality; not refuted. T7: moves Π94, Π95, Π121.

**Limit.** It speaks about large heights; a finite layer at a fixed height is invisible to it. The finite stratum then needs the FE as a reciprocity acting on heights (Poisson, theta, Farey and Dedekind reciprocity), the one sign-free ingredient left unused.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** See 1.10 and 1.13. In particular: the archimedean place is a field in Euclidean AdS₃ — the archimedean Frobenius is `2π√(mn)` times the bulk propagator `G_{1/2}` of a scalar of `m²=−¾` in the quantization `Δ=½`, evaluated between points of one geodesic at distance `|log(n/m)|`, i.e. along a static worldline whose normal-mode energies are `½+2k` (the trivial zeros) [L]; the zeros of ζ live in the modular horizon as resonances of the mirror-even channel, with decay rate equal to the zero width; universal decay `e^{−t/4}` is RH [L]; in a Hilbert-space realization of `Q` the Hecke clock must have pure point spectrum at the critical ordinates, while internal clocks collapse to the centre, vacuum-fixing clocks collapse to square classes, and half-sided Borchers clocks have no eigenvalues at all [L].

**The law, read physically [D].** The same zeros appear twice: as complex quasinormal frequencies of a horizon (decay = width) and, under RH, as real normal-mode frequencies of the clock in a realization of `Q`. A black hole has quasinormal modes; a confined geometry has normal modes. In AdS₃ the two are exchanged by a modular transformation: the BTZ black hole and thermal AdS₃ are S-dual images of each other, the BTZ quasinormal spectrum is the image of the thermal-AdS normal-mode spectrum, and the decay rates of the lowest BTZ tower are fixed by the conformal weight alone — universal damping as kinematics of a real spectrum [C]. The archimedean place already shows this structure in the corpus: its modes are the normal modes `½+2k` of global AdS₃ and, in the explicit formula, the Gamma poles at the trivial zeros, a lattice of universally damped modes [L].

**The question.** *Is the modular horizon the modular image of a confined system whose normal modes are real?* Precisely (B117): is there a unitary, horizonless (normal-mode) system — a Hilbert space and a self-adjoint Hamiltonian defined without reference to the zeros, with the archimedean place as its free part (the AdS₃ worldline with `Δ=½`) and the primes as interactions at the times `log n` — together with a modular transformation that maps its Euclidean correlators to the mirror-even response of the modular horizon, so that every horizon resonance `ρ/2` is the image of a real normal-mode frequency?

**Why it opens the path.**
- **It turns universal damping into kinematics.** If the resonances are images of real frequencies under a fixed modular map, their decay rates are fixed by the map, as in BTZ; RH is then the statement that the arithmetic modes lie in the lowest tower.
- **It is exactly what the operator no-gos leave.** A realization of `Q` needs point spectrum (normal modes) and cannot be the horizon's own vacuum-fixing or half-sided clock [L]. A confined companion supplies point spectrum without fixing the horizon vacuum; the modular map supplies the horizon. It also explains why internal modular conjugation fails: the partner involution would be the modular map between two phases, not an involution inside one algebra.
- **It has rungs.** (i) The archimedean sector: Gamma poles = universally damped lattice; global AdS₃ normal modes `½+2k` [L]. (ii) Graph black holes: partner standard forms exist iff the hole is damped [L]; test whether each damped graph hole is the modular image of a finite oscillator bank with real frequencies (oscillator-bank positivity holds iff every block is strictly stable [L]). (iii) The Narain AdS₃ partition function: modular invariant, with an Eisenstein/cusp spectral decomposition in which the arithmetic poles survive [L]; the confined seed and its Poincaré sum over `SL₂(ℤ)` are the natural first instance — the Eisenstein series is the Poincaré sum of `y^s`.
- **A negative answer is informative.** If no confined companion of the mirror-even channel exists for which the modular map preserves reality, the physical reading reduces to the width axis.

**Calibration and risks.** The theta reflected squared product has no finite positive or signed Laplace representation [L]: the confined Euclidean correlator cannot be the theta carrier. Fakes (graph black holes with `t²>4q`) must fail through the companion, not through the dynamics. A companion with the critical ordinates as eigenvalues is a Hilbert–Pólya operator; the question is useful only if the confined system and the modular map are defined from the archimedean place and the primes alone.

**Second physical question (sub-RH).** *Does some cavity mode see every zero?* (B109): is there a Maass cusp form `g` with `Λ_g(ρ/2)≠0` at every off-line zero `ρ`? With it, the cusp-energy horocycle rate becomes a complete receiver: rate `y^α` ⇒ every zero has `Re ρ≤2−2α` [L]. Its strength is independent of RH.

## 2.8 If RH is a problem of topology or geometry

**What is proved.** See 1.10–1.12. The off-diagonal of Weil's form is a rank-two pole minus two positive dampings — the Green function of `ℍ³` at `s=½` between points of a vertical geodesic, and the torsion energy of cyclotomic orbits on `ℙ¹_ℤ` [L]; the atomic diagonal is the Newtonian self-energy of a point of `ℍ³`, renormalized at order `N log N` [L]; the compensation changes sign at the plastic ratio [S]; RH ⇔ Hasse–Weil at every integer degree of the smoothed Frobenius graphs, and a crude bound there is the width [L]. In topology, the prime-vertex local indices are relative singular Euler characteristics with sum `1−M(N)`, unbounded below [L]; over `𝔽_q[T]` the Möbius sum is the point defect of an orientation cover with exact count `qⁿ` [L].

**Geometric question.** *Is Weil's form the energy of an arithmetic charge configuration on a hyperbolic 3-orbifold?* Precisely (B118): is there a finite-volume arithmetic quotient `Γ\ℍ³` (a Bianchi orbifold; the cubic quotient `SL₂(ℤ[ω])\ℍ³` of the Möbius descent is the first candidate) such that
1. the vertical geodesic points `z_n=(0,0,n)` and their `Γ`-images realize the archimedean Frobenius and the torsion energy together as one automorphic Green function at `s=½`, off the diagonal;
2. the arithmetic diagonal counterterm (`log N−γ` and its archimedean part) is the Robin constant — the regularized self-energy — of the points `z_n` in the quotient;

so that the sign of Weil's form becomes a Hodge-index statement for a Green operator of the quotient: one negative direction from the constant eigenfunction (the pole, which has rank two in Weil's form) and positivity on its complement as long as no Laplace eigenvalue lies below `¾`?

**Why it opens the path.**
- **It removes the renormalization problem.** Renormalization carries no sign [L]; a Robin constant on a finite-volume quotient is not a counterterm but the finite part of an honest Green function, and the energy of a signed configuration is then a quadratic form of a resolvent, whose signature is read off the spectrum below the spectral parameter.
- **It uses the carrier the corpus found.** The archimedean place is not carried by any metric on `ℙ¹_ℤ`, any toric pairing, any continuous Hecke kernel or any finite-rank kernel [L/S]; it is carried by `ℍ³` [L]. The jets are the radial modes `½+2k` of `G_{1/2}`; the decomposition `2πG_{1/2}=2πG_{3/2}+1/(2cosh(d/2))` separates the honest resolvent from a complementary-series spherical function, the two pieces a Hodge index would have to account for [L].
- **It explains the shape of the atomic genus.** The genus `N log N` is the harmonic divergence of the archimedean kernel at spacing `1/N`, with the arithmetic below it [L]: exactly what a Green function on a 3-manifold does near its diagonal.
- **It has rungs.** (i) The free `ℍ³` kernel: positive damping off the diagonal [L]. (ii) Hasse–Weil at the integer degrees: plane by plane, a binary genus form [L]. (iii) The cubic quotient: Möbius over `ℤ[ω]` is a cubic Gauss coefficient and the cubic spectral pencil is Fredholm below the cusp threshold [L]. (iv) Function fields: Castelnuovo–Severi on `C×C` [L].
- **The risk is named.** On a quotient, the scattering matrix of the cusp carries the zeros of a Dedekind zeta as poles; the required positivity at `s=½` may itself be the absence of resonances, i.e. a Riemann hypothesis for the quotient. The question is decisive in both directions: a positive answer reduces RH to a spectral statement about one arithmetic 3-orbifold; a negative answer shows that the `ℍ³` fibre of Spec ℤ is not an Arakelov fibre.

**Topological question.** *Is there an orientation cover over the integers?* Precisely (B120): is there a natural double cover — of the prime complex, or of a model of `{1,…,N}` — whose fibre over a squarefree `n` has `1+μ(n)` points (or `1+λ(n)` over every `n`), defined by a trace discriminant attached to `n`, and a self-map of the cover with bounded local indices whose Lefschetz number is the total count? Over `𝔽_q[T]` the factor-trace orientation cover exists (Stickelberger), and its total count is `qⁿ` exactly: Möbius cancellation is the statement that the cover has no middle cohomology [L]. Over ℤ the prime-vertex indices already localize `1−M(N)` with unbounded indices [L]; an orientation cover would replace unbounded indices by a trace on a cohomology of weight `½`, giving `|M(N)|≪N^{½+ε}`. First rungs: `𝔽_q[T]` [L]; `ℤ[ω]`, where the cubic Gauss coefficient is a cubic orientation [L]; Jacobi symbols, which are signs of multiplication permutations (Zolotarev) [C].

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Heights over number fields give central-value signs, not off-line zeros [D].

## 2.9 Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason, the curve proof's freebies — finite rank and periodicity — are both absent over ℤ, and the one calibration where Euler product + FE succeed is finite rank.

| Tool | Why it stops |
|---|---|
| Size estimates | before half-width `21/40`; all heights only to `a≈log log X` |
| Markov, Perron | frustration past `log ρ` |
| Type I/II sieve data | parity-blind |
| Linear floor identities, ledgers | blind to every zero |
| Barriers, short detectors | blind to purity; last-scale floor |
| Mollifiers | outer; near-unit moments need the primes up to `log²T` |
| Conditional laws, mean values | stop at the Kronecker scale; past the height collision counts of order `X²` with a binary constant |
| Euler and prime coordinates | stop at `Re s=1` |
| Concentration-compactness at the critical curve | returns the window threshold plus polar payment |
| Finite computation | decides no level of the dial |
| Zero statistics at one scale | cannot decide any level of the dial |
| FE with analytic shape | admits every finite layer |
| Laws uniform on the heat family | already RH |
| Positivity, Euler products, counting, continuation | carry finite layers |
| Density statements on tower levels | rank barrier |
| Exact Frobenius; Rouché copies at returns | no exact returns; capped by precision |
| Integrality | Chebyshev |
| Renormalization | carries no sign |
| Metrics, toric, continuous and finite-rank kernels | cannot carry the archimedean place |
| Unitarity, Schur, `C*`, KMS, internal, vacuum-fixing and half-sided modular structures | wrong involution; central, square-class or eigenvalue collapse |
| Horizon observables | width axis; VK saving |
| Homotopy, persistence, identity-homotopic fixed points | `s`-blind; primes fixed with unbounded indices |

**What is built, and where it stops.**
| Field | Object | Stops at |
|---|---|---|
| Infinite-rank Weil theory | towers, exceptional rank, thick sets, elimination, Toeplitz counts, linear dial, critical weight, Frobenius substitute and its precision cost | the thick crude count for ζ; ZAL |
| Zero-configuration geometry | abscissa laws, transport, two-scale law, curve split, strict linear hierarchy, finite-rank Chebyshev exponent, heat family | a two-scale Euler–FE input |
| Surface of Spec ℤ | half-products, zonotope, `ℍ³` archimedean fibre, point count, Frobenius graphs at integer degrees, atomic genus | the diagonal |
| Arithmetic inner functions | half-plane, causal order, inner mass | size, not vanishing |
| Prime torus and tail arithmetic | `(t,ω_t)`, first return, Euler tail, tail transport | the Kronecker scale; exact events |
| Rigid arithmetic of cuts | cut system, ledgers, kernel | parity is the strip |
| Holography, ringdown, counting holography | waves, Born rules, count laws, standard forms, half-sided exclusion | the count over ℤ; a carrier with point spectrum |
| Effective and renormalized geometry | polar surfaces, torsion forms, compensation, prime boundary, vertex dynamics, finite-field counts | sign at the critical weight; `s`-blind topology |
| Arithmetic positive duality | Beurling systems, firewall, annihilators, relocation | the critical line |

**The proposal: infinite-rank Weil theory of Euler products with a functional equation.** A field that proves RH must build, at infinite rank, what the curve proof gets from finite rank and periodicity, plus the count, and the corpus fixes where each must act: a crude step on thick sets, well-foundedness, an Euler–FE rigidity that at finite rank is the local-squares theorem, and a damping of the diagonal whose archimedean part lives on `ℍ³`.

| Aspect | Content |
|---|---|
| What it is about | zeta-like objects with infinitely many modes, an Euler product and a functional equation, studied in the exceptional coordinate (modes beyond each depth, the linear dial) rather than the size coordinate; the coupling between low and high zeros that the Euler product and the FE impose together; counts at the critical weight with an archimedean fibre |
| Objects | zero configurations and their dial `(Θ,Θ∞)`; finite-rank Chebyshev expansions of `ψ`; Weil towers at every base and their level sums and Toeplitz counts; isolated tops and their reflected bottom layers; thick sets of levels; Euler heads and tails; returns of prime subsets and frozen polynomials; half-products (𝔽₁-zonotope, `ℙ¹_ℤ` torsion) and the `ℍ³` fibre; Frobenius graphs at integer degrees; damping families of positive kernels; deformation families (heat, shifts) as calibration |
| Language | exceptional rank, thick set, well-founded tower, isolated top, slope, eventual-to-global, zero transport, tail event, two-scale property, family-uniform property, critical weight, damping versus renormalization, half-product, archimedean fibre, self-energy, partner involution |
| Mechanisms | Turán–Vandermonde elimination at the exceptional rank; the Dirichlet series as the coupling between scales; Euler product + FE rigidity (local squares at finite rank, Beurling rigidity at infinite rank); the FE converted into vertical transport; damping limits of positive intersection pairings; Green functions of `ℍ³` |
| Tools to build | a thick crude-count theorem (B110); `ZAL⇒RH` (B111); a well-foundedness (ZAL) mechanism; an FE-to-transport principle (B112); an infinite-rank Euler–FE rigidity excluding finite layers (B13); a damping presentation of the diagonal (B88) with the `ℍ³` self-energy as its archimedean part |
| Questions it must answer | Which Euler-product property of ζ couples the zeros below a height to those above it? How does the FE, a height reflection, become transport in height? Which prime-side bound holds on long runs of scales? What makes the towers of ζ well-founded? What positive object damps to the diagonal of Weil's form, and what is the self-energy of the point `z_n`? |
| Criteria | reduce to the Lean curve proof at finite rank and to the local-squares theorem for finite Euler products; reproduce AAL for periodic, recurrent and almost periodic configurations; fail on `cosh` models through the Dirichlet series, on the heat family through the Euler product, on Beurling one-offs through the FE, on relocations through positivity, on Wolff towers through well-foundedness, on harmonic-depth configurations through the dial; be invariant under symmetric shifts where AAL is, and not where linear laws are not; respect the rank barrier; produce signs only by damping |
| Calibration | curves (finite rank, periodic, complete proof [L]); finite Euler products with FE (local squares [L]); graph black holes (FE without damping [L]); Beurling one-offs (Euler product without FE [L]); `cosh` models (FE without Dirichlet series [L]); heat family (FE and Pólya positivity without Euler product [L]); shifted products (FE, AAL ⇔ AAL(ξ), trivial linear slope [L]); Wolff towers (non-well-founded [L]); the zonotope surface (a count [L]) |

**Limits.** Binary problems at the Kronecker scale are parity problems [C]. Excluding a finite layer is an exceptional-zero problem of Landau–Siegel type [D]. ZAL is quasi-RH.

## 2.10 Does an AAL proof or falsification need a new field?

**Why the existing tools stop [L].** AAL is vertical transport of zeros. Tools that see one scale decide no level of the dial. The FE as a zero symmetry keeps heights. Positivity, Euler products, linear counting and continuation carry finite layers. Laws uniform along the heat flow or the shift family are RH or diverge. Uniform almost periodicity would give AAL, and ζ is not uniformly almost periodic in the strip; almost periodicity at large height is not enough. Near-full tail cancellation is abundant at every point (Voronin), but AAL needs exact cancellation at heights transported from a right zero; returns at zeros are tail-bad and rare, so every density statement bounds the needed events from above. A moving functional equation (Riemann–Siegel at height `t`) does not transport a zero by a head return: freezing its head needs every prime phase up to `√(t/2π)` within a small precision, which at bounded harmonic defect first happens at heights `≥exp(c(log t)^{3/2}/log log t)` [L, bracket], where the head is longer and no longer determines ζ [D]. Phase-freezing Rouché copies are capped by precision [L].

**The field: exact-event theory of Euler products.** Its subject is the existence, not the frequency, of exact exceptional events of Dirichlet series with an Euler product and a functional equation — zeros, exact tail cancellations — and the rigidity of finite exceptional sets over approaching remainders.

| Aspect | Content |
|---|---|
| What it is about | when a single exceptional event (a zero right of the line) forces infinitely many at larger heights; the passage from approximate events of positive density (`η>0`) to exact events (`η=0`); finite exceptional layers and their dial `(Θ,Θ∞)` as rigid objects |
| Objects | zero configurations and the transport relation; the linear dial and its separating configurations; the vertical shift group and the Bohr/prime torus; Euler heads and tails at every cut; partial returns with omitted arcs; isolated tops; towers and exceptional ranks; positive annihilators and their oscillating inverses; `cosh` models, two-scale `cosh` models, heat and shift families, Beurling one-offs, Wolff towers, relocations as calibration |
| Language | transport, exact event, tail event, tail-good/bad height, isolated top, exceptional rank, slope, two-scale property, family-uniform property, relative thick count, conditional recurrence |
| Mechanisms | Rouché and Jensen under partial approximation; universality upgraded from nonvanishing to vanishing targets in the presence of a zero; Turán–Vandermonde at the exceptional rank; the FE as a height reflection composed with vertical twists; Deuring–Heilbronn-type interaction between one exceptional zero and the rest [C], read as attraction rather than repulsion |
| Tools to build | zero transport from weak almost periodicity with zero-disc control and the Euler product; lower bounds for exact tail events (B96); relative thick crude counts (B116); `ZAL⇒RH` (B111); an FE-to-transport principle (B112); a classification of Dirichlet series with Euler product and FE carrying a finite layer (B103, B84) |
| Questions it must answer | Which weak almost periodicity, together with the Euler product, transports zeros? Does an isolated top force, through the Euler product and the FE together, a zero of the tail at larger heights? Is there any Dirichlet series with an Euler product and an FE and a finite layer? Can the rigid ¬AAL world coexist with the FE of ξ? Does the trivial linear slope of the shift family stay bounded as the shift tends to zero? |
| Criteria | reproduce Bohr's recurrence on the half-plane of absolute convergence and AAL on curves and exponential polynomials; fail on `cosh` models (no Dirichlet series), the heat family (no Euler product), Beurling one-offs (no FE), harmonic-depth configurations and one-pair configurations; be shift invariant for AAL; never use the position of the line beyond the FE involution and Hardy's zeros; couple scales |
| Falsification side | a ζ-specific finite layer cannot be produced by rational surgery with positive coefficients (first-gap negativity) [L]; a falsification needs an intrinsic construction — a Dirichlet series with Euler product, FE and a finite layer — of which no example exists, and in degree one none can exist other than ζ and its twists (Beurling and Selberg rigidity) [L] |

**Limits.** AAL is not implied by any density statement; its finite case is an exceptional-zero problem [D].

## 2.11 Without positivity, Weil positivity and spectral methods: which field?

Inner-function theory, holography's flux and Lax–Phillips, standard forms, Hodge index and the count door lose their core. What remains is the toolkit of the curve proof — auxiliary functions, power sums and the FE as an identity — and its infinite-rank versions in the corpus: elimination at the exceptional rank on thick sets, the free self-improvement at the integer degrees, the finite-rank Euler–FE purity, tail transport, frozen polynomials at returns, collision counts, finite-field orientation and orbit counts used as identities.

**The field: Diophantine Weil theory over ℤ — transcendence at the archimedean place, Turán at infinite rank, reciprocity as transport.**

| Aspect | Content |
|---|---|
| What it is about | proving the crude count and the transport law by Diophantine approximation, cancellation and elimination: quantitative independence of the logarithms of the primes, auxiliary functions with integer coefficients forced to vanish exactly by integrality, power sums of zeros on windows of levels, reciprocity laws acting on heights |
| Objects | the prime orbit `(t log p)_{p≤y}` and its returns as simultaneous approximations; auxiliary Dirichlet polynomials on smooth integers with integer coefficients; linear forms in logarithms; level sums of towers; thick sets of scales; smooth × prime products and their gcd collision classes; Farey fractions, Dedekind and cotangent sums; the prime deviation along geometric scales; orientation covers and cubic Gauss coefficients over function fields and `ℤ[ω]` |
| Language | Frobenius substitute, frozen polynomial, forced vanishing, precision cap, return, heavy subset, linear form, height, zero estimate, exceptional rank, thick set, reciprocity, transport |
| Mechanisms | transcendence method: auxiliary function, integrality (`|n|≥1`), extrapolation, zero estimate; Baker-type lower bounds for linear forms in logarithms; Vandermonde/Turán lower bounds at the exceptional rank; sum-product and incidence bounds for hyperbolas `xy=c`; reciprocity along the Euclidean algorithm as a height-moving identity; Stickelberger-type identities turning Möbius into a character of a discriminant |
| Tools to build | a constant-precision first-return bound (B97, §2.6); a freezing control beyond the precision cap through integrality (B121); a thick crude count from collision counting past the height (B110); incidence bounds with a prime-density saving for smooth × prime near-collisions; a sign-free FE-to-transport principle through Poisson, theta and Farey reciprocity; an orientation cover over ℤ used as an identity (B120) |
| Criteria | no quadratic form with a sign, no operator spectrum, no use of nonnegativity of counts; prove Hasse–Weil over `𝔽_q` in the same language (the corpus does for hyperelliptic curves [L]); reproduce the finite-rank Euler–FE purity; separate rational primes from Beurling one-offs through count distance or reciprocity; any parity output at power saving is a strip [L]; respect the rank barrier and the precision cap |
| Questions it must answer | How early can the primes below `y` return simultaneously? Can integrality replace the exactness of the Frobenius? Is the fine multiplicative energy of smooth × prime products at scale `1/T` at its random value? Do long runs of scales carry square-root prime deviations? Does reciprocity, iterated along the Euclidean algorithm, move zeros in height? |

**Limits.** No source produces parity at power saving other than a strip [L]. No named mechanism above VK. Baker-type bounds lose a factor exponential in the number of logarithms [C].

## 2.12 If RH is a physical phenomenon in AdS with a modular horizon: which field?

Holography, ringdown and counting holography are formalized; their positive results are exact solutions, width-axis receivers, Born rules and standard-form criteria; their negative results are that wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation, vacuum-fixing partners, half-sided inclusions, the FE, integrality, linear counts and Hecke at a second place do not carry universal damping or `Q` [L]. The archimedean place itself is a field in Euclidean AdS₃ [L].

**The field: arithmetic holography of phases — modular duality between confined normal modes and horizon resonances.**

| Aspect | Content |
|---|---|
| What it is about | two descriptions of one arithmetic system: a confined phase (a static worldline in AdS₃, normal modes, a unitary Hamiltonian with point spectrum) and a deconfined phase (the modular horizon, quasinormal modes, decay rates on the width axis), related by a modular transformation; RH as the statement that the arithmetic resonances are modular images of real frequencies |
| Objects | `ℍ³` = Euclidean AdS₃ with the worldline `{(0,0,y)}` and the scalar of `m²=−¾` in the quantizations `Δ=½` and `Δ=3/2`; the modular horizon `SL₂(ℤ)\`(Rindler wedge of AdS₄) with its mirror-even channel and odd cavity; the Narain AdS₃ partition function and its Poincaré structure; graph black holes and oscillator banks; Eisenstein series as Poincaré sums of a confined seed; the Hecke clock `U(log n)` |
| Language | confined and deconfined phase, normal mode, quasinormal mode, Poincaré sum, modular image, conformal weight, lowest tower, alternate quantization, double-trace flow, cavity, partner involution, width |
| Mechanisms | S-duality of thermal AdS₃ and BTZ (quasinormal = image of normal) [C]; Poincaré sums over `SL₂(ℤ)` (Eisenstein series, Maloney–Witten-type sums) [C]; the Gamma-function lattice of the archimedean place [L]; Bochner realization of `Q` with point spectrum; Rankin–Selberg unfolding between cavity and scattering channels [L] |
| Tools to build | a confined companion of the mirror-even channel (B117); the modular map from its Euclidean correlators to the horizon response; a dictionary between the quantizations `Δ=½,3/2` and the pole of ζ (the spherical function `½sech(d/2)` that separates them); Rankin–Selberg noncancellation for one cavity mode (B109) |
| Criteria | recover the universally damped lattice of the trivial zeros from the archimedean worldline; recover damped graph black holes from strictly stable oscillator banks and fail on undamped ones; avoid the central, square-class and Borchers collapses; use only smooth sources (sharp ones need more than RH); define the confined system without the zeros |
| Questions it must answer | Is the mirror-even channel of the modular horizon the modular image of a confined system? Which conformal weight fixes the lowest tower at rate `¼`? Why does arithmeticity (no second place) make the companion unitary? Is the Narain average the first confined–deconfined pair in which the arithmetic poles survive? |

**Limits.** A companion with the critical ordinates as eigenvalues is a Hilbert–Pólya operator; every proved physical statement is a restatement, an edge theorem, a width-axis receiver or the absence of a law. The geometry is locally pure AdS.

## 2.13 If RH is a problem of topology or geometry: which field?

**The field: Arakelov geometry of Spec ℤ with a hyperbolic archimedean fibre.** Counts are intersection numbers; signs come from Green functions of finite-volume hyperbolic 3-orbifolds, never from counterterms; the archimedean place is the dilation geodesic of `ℍ³` with its Green function at `s=½`; topology enters through orientation covers and signed localization.

| Aspect | Content |
|---|---|
| What it is about | building the missing surface "Spec ℤ × Spec ℤ" only as far as needed: Frobenius graphs at the integer degrees, an archimedean fibre in which the jets are radial modes of `ℍ³`, a finite part on `ℙ¹_ℤ`, and a diagonal whose self-intersection is a Robin constant rather than a counterterm; Möbius cancellation as the vanishing of a middle cohomology |
| Objects | 𝔽₁-zonotope surface; `ℙ¹_ℤ` with torsion orbits and radial cyclotomic counts; `ℍ³` with the points `z_n=(0,0,n)` and the Green functions `G_{1/2}`, `G_{3/2}`; Bianchi orbifolds (the cubic quotient of the Möbius descent); smoothed Frobenius graphs and their integer-degree planes; the prime-product complex with its prime-vertex dynamics and exits; orientation covers over `𝔽_q[T]`, `ℤ[ω]`, ℤ |
| Language | half-product, Frobenius graph, integer-degree plane, genus of a smoothing, archimedean fibre, Robin constant, self-energy, damping, critical weight, Hodge index, spectral gap, orientation cover, local index, Lefschetz localization |
| Mechanisms | Hodge index by counting (zonotope); damping limits of positive kernels; Green functions and their signatures on finite-volume quotients; Robin constants as finite parts; Lefschetz–Hopf localization; Stickelberger orientation; Riemann–Roch on surfaces; Hecke equivariance |
| Tools to build | an automorphic Green function at `s=½` reproducing pole − archimedean − torsion off the diagonal (B118); the identification of the arithmetic counterterm with a Robin constant; a damping presentation of the diagonal (B88); an orientation cover over ℤ (B120); a self-map of Lefschetz number `M(N)` with bounded local indices (B106) |
| Criteria | reduce to the zonotope Hodge index and the curve count laws; reproduce the `ℍ³` identity of the archimedean Frobenius, the plastic sign change, the atomic genus `N log N` and the genus `c_B(0)/2` of smoothed pairs under RH; never use a counterterm as the source of sign; reproduce `Σ index=1−M(N)` and the orientation-cover count over `𝔽_q[T]` |
| Questions it must answer | Which arithmetic 3-orbifold, if any, carries Weil's kernel as a Green function? What is the self-energy of the point `z_n`, and is it the arithmetic counterterm? Which eigenvalues of that orbifold lie below `¾`? Is there an orientation cover over the integers, and what is its cohomology? |

**Limits.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. On a quotient the cusp's scattering matrix carries zeros of a Dedekind zeta; the positivity needed at `s=½` may be a Riemann hypothesis for the quotient [D].

## 3. The one big question

**Can ζ have finitely many, but not zero, zeros off the critical line?** (B13) It is AAL at depth `h=0`: the bottom of the strict dial `AAL ⊊ LinAt C ⊊ (ZAL⇒RH) ⊊ B13`, strictly below `ZAL⇒RH` (B111), below AAL and below quasi-RH.

| Form | Statement | Evidence |
|---|---|---|
| Configuration | `Θ∞=½` with finitely many right zeros ⇒ none | `ConfigAbscissa.AbscissaLawAt`, `zetaZeroConfig_abscissaLaw_iff` [L] |
| Chebyshev | if `ψ(x)−x` equals a finite exponential sum `Σ_{z∈S}d(z)x^z` up to `O(x^{½+ε})`, then `S` carries no zero off the line | `zetaAsymptoticAbscissa_eq_sInf_chebyshevFiniteRank` [L] |
| Index | the negative index of Weil's kernel is `0` or `∞`; equivalently on one two-prime lattice | `zetaKernel_finiteIndex_tfae` [L] |
| Heat | a bounded number of non-real heat zeros for `t>0` forces none at `t=0` | `zetaKernel_finiteIndex_tfae` [L] |
| Jensen | `N_d` bounded forces `N_d=0` | FFP [L] |
| Slice | eventual slice positivity forces positivity | `eventualSlicePositivity_iff_finiteOffLine` [L] |
| Prime tower | in the finite stratum, one non-blind prime tower is PD | `FiniteSupportMakesAlmostEveryPrimeDecideZeta` [K] |
| Weil tower | in the finite stratum, one Weil tower is Toeplitz positive; equivalently bounded on a thick set | `b13_iff_toeplitzPositive`, `b13_iff_thick_lag_bounded` [L] |
| Resonant tower | a single top pair `Θ±iγ` makes the lag large at every level at base `π/γ` | `eventually_lag_large_of_single_top_pair` [L] |

### Why this one
- **It is the finite-rank piece of the whole problem.** The finite stratum is a finite-rank Weil datum over a critical remainder — the regime in which the curve proof self-improves and in which Euler product + FE are known to force purity (finite Euler products with FE: local squares [L]). The step to prove is that finitely many exceptional modes force none.
- **Its negative world is the most rigid and best-equipped one.** Lindelöf; a zero-free half-plane; 100% critical zeros; Weil's form PSD on a subspace of finite codimension; boundedly many non-real heat zeros; bounded `N_d`; the explicit formula exact up to finitely many oscillating terms over an RH-size remainder; positive annihilators remove the off-line set at an exponential cost in the multiplicity, with an oscillating inverse; the lag at the resonant base is large at every level [L/K].
- **Its input type is fixed by five theorems.** By the two-scale law it cannot be a statistic of the zeros at large height or a finite verification; by the `cosh` models it must use the Dirichlet series; by the heat-family theorem it must use the Euler product, and it cannot be a law that also holds along `H_t`; by the firewall it must use the FE; by the finite-rank calibration it is the infinite-rank form of an Euler–FE rigidity [L]. No other question in the corpus has its required input so tightly constrained.
- **It is false on every corpus fake.** Every one-off has finitely many off-line zeros; `cosh` models and one-pair configurations violate it; tempered finite-support models defeat fixed-ratio positivity [L/K].
- **It has a first rung.** `k=1`: one quartet `{ρ,ρ̄,1−ρ,1−ρ̄}`, `ρ` simple — "ζ is not a one-off" — with its resonant tower at base `π/γ`.

| Kind | Best form | Why it ranks lower as the one big question | Evidence |
|---|---|---|---|
| Configuration law, full | AAL (B83) | no mechanism has moved it | [L] |
| Configuration law, existential | `ZAL⇒RH` (B111) | contains B13 and the harmonic-depth worlds | [L] |
| Configuration law, fixed slope | `LinAt C` (B116) | contains `ZAL⇒RH` | [L] |
| Tower crude count | thick crude count (B110) | at least AAL-hard | [L] |
| Critical ratio | polar payment below `W` (B104) | method strength | [L] |
| 100% near the line | depth density `o(T)` (B57) | asymptotic: cannot touch the dial | [L] |
| All-height sign | constant-precision first return (B97) | past VK | [L/D] |
| Kronecker-scale law | lower bounds for exact tail events (B96) | binary prime problems | [D]; [C] |
| Topology | localization of `M(N)` (B106); orientation cover (B120) | RH-strength at `√N`; producer | [L] |
| Horizon | any exponent past `½` (B14, B71); confined companion (B117) | interior exponent is a strip; producer | [L] |
| Count | Tate limit / damping of the diagonal (B87, B88) | RH-strength | [L] |
| Theta | adaptive head near critical zeros (B102) | RH-strength | [L] |
| **Finite stratum** | **B13** | **bottom of the dial; decisive for many receivers; most structure; false on every fake; rung `k=1`; input type fixed by five theorems** | **[L/K/D]** |

### What an answer does
| Answer | Effect |
|---|---|
| **B13 proved** | Finite index of Weil's kernel ⇒ RH; finite index on one two-prime lattice ⇒ RH; bounded heat count ⇒ RH; bounded `N_d` ⇒ RH; eventual slice positivity ⇒ RH; RH above some height ⇒ RH; one Toeplitz-positive tower in the stratum ⇒ RH [L]. HF, HKT, AKLT, CWS, SC, ZCG heat count, WD heat charge, LA, FFP lose the obstacle "finite exceptions remain" and need only a finiteness producer (B12, B23). |
| **B13 proved** | The first theorem in which the Euler product and the FE together exclude off-line zeros at infinite rank; it names the two-scale coupling that separates ζ from every `cosh` model, every heat deformation and every one-off. |
| **B13 proved** | The dial reduces to worlds with infinitely many off-line zeros; F1 and F22 reduce to ZAL plus "an infinite remainder approaching the line cannot carry a finite top" (`ZAL⇒RH`), then `C↓1`. |
| **B13 refuted** | RH is false with finitely many off-line zeros, all above the verified height; ζ is a one-off; the explicit formula is RH up to finitely many terms. |

### What is proved around it
| Channel | Status | Module |
|---|---|---|
| Finite stratum | TFAE: finite index, lattice index, finite off-line set, heat count, eventual RH | `HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] |
| Towers decide | under finite support RH ⇔ one non-blind prime tower PD | `ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta` [K] |
| Weil-tower forms | B13 ⇔ one Toeplitz-positive tower in the stratum ⇔ one thick-bounded tower | `InfiniteRankWeilTheory/TheCrudeStepAndTheCount` [L] |
| Lindelöf | finite off-line support ⇒ zeros approach the line ⇒ LH | `RHTower/LindelofCosineFiniteDefectDepth` [L] |
| Jensen count | `N_d` nondecreasing, `sup_dN_d` = off-line multiplicity | `FiniteFreeProbability/{JensenCountsOffLineZeros,NonRealJensenCountBound}` [L] |
| Dial | strict hierarchy, quantifier collapse, finite-rank Chebyshev exponent | `ZeroConfigurationGeometry/AbscissaLaws/TheLinearAbscissaLawAndItsHierarchy`, `InfiniteRankWeilTheory/TheLinearAbscissaLawInWeilTowers` [L] |
| Two-scale law | asymptotic and local-below properties do not decide B13 | `ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawIsNotAsymptotic` [L] |
| Heat family | a finite-stratum law valid on all `H_t` is RH | `ZeroConfigurationGeometry/AbscissaLaws/TheFiniteStratumLawOnTheHeatFamilyIsRH` [L] |
| FE models | `cosh` models carry every finite layer | `InfiniteRankWeilTheory/TheFunctionalEquationAdmitsEveryFiniteLayer` [L] |
| Firewall | positive classes, continuation, reflection symmetry carry finite layers | `ArithmeticPositiveDuality/TheCriticalLineFirewall` [L] |
| Finite-rank calibration | finite Euler product + FE ⇒ local squares ⇒ purity | `RHTower/FiniteSquarefreeEulerFunctionalEquation` [L] |
| Tower form | syndetic excursions; single top pair at every level of its resonant tower | `InfiniteRankWeilTheory/TheTowersOfZeta` [L] |
| Elimination | exceptional rank, price of hiding, rank barrier | `InfiniteRankWeilTheory/{TheExceptionalRankDecidesTheWindow,TheRankBarrier}` [L] |
| Annihilators | finite sets at any multiplicity; harmonic packets cost `≥m`; Chebyshev, hyperbolic, fixed-height and divisor costs; oscillating inverses | `ArithmeticPositiveDuality/{PositiveTwoPrimeAnnihilators,TheChebyshevCostOfAnnihilatorMultiplicity,TheHyperbolicCostOfReflectedZeroPairs,FixedHeightAnnihilatorsHaveAMassGap,TheZeroDivisorConsumesAnnihilatorMass,AnnihilatorDivisionForcesCoefficientOscillation}` [L] |
| Rigid oscillation | finite oscillation of `ψ`, dilation annihilation | `ZeroConfigurationGeometry/{TheOneOffsAreFiniteOscillationsOfThePrimeError,MultiplicativeDilationAnnihilationOfPrimeError}` [L] |
| Surgery | rational relocation fails at the first integer gap | `ArithmeticPositiveDuality/TheFirstIntegerGapDetectsRelocation` [L] |
| Heat energy | initial trace `Σ (Im z)²` of the ξ divisor; no loss at time zero | `ArithmeticElectrostatics/TheInitialTraceOfHeatDepthEnergy` [L] |

### The forms of the missing input
1. **Euler product + FE on a finite set.** In the stratum `N(T)−N₀(T)=2k` is eventually constant and the explicit formula is exact up to `2k` oscillating terms. The input is a statement about ζ that sees both the finitely many off-line zeros and the critical zeros above them, uses the Euler product (so that it fails along `H_t`) and the FE (so that it fails on the one-offs) — the infinite-rank form of the local-squares rigidity.
2. **Index form.** A zero-or-infinity law for the actual two-prime lattice kernel; proved under escape, mixing or slope-height decay [L]; the input is the arithmetic mixing property of the kernel in the stratum, where Lindelöf supplies growth control.
3. **Tower form [K/L].** One non-blind prime tower decides; one Weil tower is a one-dimensional Toeplitz problem whose positivity is the bound `|Φ(νℓ)|≤Φ(0)` at every level.
4. **Annihilator form.** A positive two-prime annihilator of the off-line set that is `ε`-accurate on `Re s≥1` must grow like `ε^{−(β−½)/(1−β)}` on the line and costs `base(σ,ρ)^n` per multiplicity; its inverse oscillates at every exponent below `β` [L]; compare with what Lindelöf and the index structure allow.
5. **Resonant-tower form.** At base `π/γ` the lag is `≥ce^{(β−½)L}` at every level [L]; one thick-set bound at that base with any exponent below `β−½` excludes the quartet. The tower at base `π/γ` folds every ordinate modulo `2γ`, so it couples the quartet at height `γ` to the zeros near the odd multiples of `γ`: the two-scale input in its smallest instance [D].

### First steps
1. Rung `k=1`: write the one-quartet world explicitly and apply every proved receiver of the stratum — window, tower, Toeplitz count, heat, Jensen, annihilator, resonant tower at `π/γ` — recording the constraint each imposes on `(β,γ)` (A47).
2. Test the escape and mixing hypotheses of the dichotomy theorems on the kernel of the lattice `⟨2,3⟩` in the stratum, using Lindelöf.
3. For one quartet, compute the blind primes and the explicit negative direction on a non-blind tower; test it against the FE mirror `1−ρ̄`.
4. Compare the cheapest positive annihilator of one quartet, and its oscillating inverse, with Lindelöf-size bounds on `Re s=½`.
5. Determine which Dirichlet-series identity at the resonant base `π/γ` couples the quartet to the critical zeros near `(2k+1)γ`, and check that it fails along `H_t`, on the `cosh` models and on the one-offs.

### Validation
| Test | Verdict |
|---|---|
| T1 | Pass. RH implies it; it does not imply quasi-RH [D]. |
| T2 | Pass. A stated implication in each form. |
| T3 | Pass. The effects table. |
| T4 | Pass. No finite verification decides it [L]. |
| T5 | Pass. False on every one-off, `cosh` model and one-pair configuration [L]. |
| T6 | Pass. Each form names an unrefuted input. |
| T7 | Pass. Moves Σ4, Γ67, Γ68, Γ136, Γ140, Γ146, Γ155, Γ156 and block S8. |

### Limits
- B13 leaves every world with infinitely many off-line zeros; `ZAL⇒RH`, the fixed slopes, AAL and ZAL remain for RH.
- Its receivers become RH receivers, but their producers (finite index, bounded heat count, bounded `N_d`) are at least quasi-RH (B12, B23).
- Positivity, Euler products, counting, continuation, positive Hecke combinations, rational surgery, the FE with analytic shape, family-uniform laws and scale-separated statistics cannot exclude a finite set [L].
- Excluding finitely many zeros is an exceptional-zero problem; classical exceptional-zero repulsion is consistent with the finite stratum [D].
