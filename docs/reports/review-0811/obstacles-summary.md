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
- atomic Frobenius graphs need genus `≍N log N` on all degrees `≤N`, unconditionally, and this genus is carried by the jets (harmonic row sum `2N(1+log N)`); the primes contribute row sums `≤2N` [L], and the prime channel has spectral radius between `(log N)/4−O(1)` and `log N+O(1)` [S];
- only the rotations about the degree geodesic preserve the archimedean profile; the free-space Robin constant is `¼` at `s=½` while the prime self-intersection grows like `log p`; finite-volume quotients fold pairs of unbounded ratio or diverge at cusps; the pure jets have infinite rank on coprime primes; causal waves `√(4k+1)1_{(0,a]}(x/a)^{2k}` on `L²(0,∞)` realize the damped Frobenius as a Gram kernel [S];
- a PSD limit matching the atomic off-diagonal needs a diagonal `≥N(log N−17)/8` in every dyadic block; adding the twisted torsion energy to any PSD family diverges; any Hilbert difference presentation with a divergent part locks its two parts; on spline Frobenius graphs RH ⇔ `c_B` is a counterterm-free limit of PSD kernels, and neither the smoothed prime channel nor the smoothed archimedean-plus-pole channel alone is one [S].

So the sign sits in the diagonal: renormalized self-energies against a positive interaction energy plus a rank-two term. Renormalization carries no sign; damping is lossless [L]; a damping must couple the prime and archimedean channels and lock them [S].

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
| Finite-volume hyperbolic 3-orbifolds as carriers; a constant Robin constant as the counterterm | folding or cusp divergence; `¼` vs `log p` | [S] |
| Logarithmic diagonals, additive channel decoupling, single channels as damping presentations | diagonal `≥N(log N−17)/8`; divergence; neither channel PSD | [S] |
| Beurling one-offs as approximate-FE fakes | defect not integrable | [D] |
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
| B13 | Finitely many off-line zeros of ζ ⇒ none (bottom of the dial); its heat-family extension is RH | sub | whole programme |
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
| B104 | Polar payment at every ratio below `W`, equivalently `R_polar=W` (§2.4) | method | HF, SRT, AIP |

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
| B88 | A counterterm-free PSD damping of `c_B` on `log ℕ₊` (⇔ RH [S]); it must couple and lock the prime and archimedean-plus-pole channels [S] | RH | AE, HHAC, SOSZ, RIAC, HF |
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
| B118′ | Hyperbolic carriers beyond the thin–thick obstruction: every finite-volume embedding excluded? a twisted infinite-volume Green function carrying the torsion? (§2.8) | producer | SOSZ, ACS, HF |
| B122 | Complete rigidity of Riemann's FE: integrable defect forces the rational primes (§3) | method | APD, BAG, ZCG, SEL, ACS |
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

## 2.4 Breakthrough question below RH and quasi-RH: can the pole always be paid below the window threshold?

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH (or a method question implied by nothing about ζ's zeros) |
| T2 | Answered by proving or refuting a stated inequality or identity |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake, or calibrated on the fakes |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |
| T8 | Tractable: not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK); its first step uses corpus objects and has one named obstacle |

Every statement below AAL that constrains the zeros of ζ contains B13, an exceptional-zero problem of Landau–Siegel type [L/D]; every crude step on thick sets contains AAL [L]. Under T8 the questions of 2.4, 2.5 and 3 are therefore questions about mechanisms, not zero laws for ζ.

**Question (B104).** *Is positivity along the critical curve decided on windows?* Precisely: is `R_polar=W`, i.e. for every ratio `R<W=⨅_A windowThreshold(A)` and every window `[−A,0]`, does the polar payment

  `S(h)²/D(R) ≤ a_φQ(H)+(7J(1)/R)M₈(H)`  (`H=e^{y/2}h`, every window test `h`)

hold?

**What is proved [L].** `R_c=R_c^{PSD}=R_polar≤R_prim=R_high=W`; every threshold `=⊤` ⇔ RH. The window threshold is the pencil threshold `windowThreshold(A)=inf R*(H)`, `R*(H)=7J(1)M₈(H)/(a_φ(−Q(H)))`, `=⊤` for `A≤181/250`. Payment at `R` on `[−A,0]` gives `R≤windowThreshold(A)`; payment at `R` leaves explicit reserves `(1/R′−1/R)(7J̃(1)M₈+J(1)t²)` at every `R′<R` (strict interior margin); below `(2K)⁸` payment holds on every window; nonpositive sequences have charged limits and payment at a larger ratio excludes them. Below `W` the complete matrix is PD iff its pole channel is (Σ135).

**The exact content.** Below `windowThreshold(A)` the pencil is positive; payment asks that it also dominate the rank-one pole charge `S(h)²/D(R)`. So B104 ⇔ the near-extremal tests of every window pencil carry asymptotically no pole charge: if `H_k` with `R*(H_k)→windowThreshold(A)` have `S(h_k)²/D ≥c‖h_k‖²`, payment fails just below the window threshold and `R_polar<W` [D].

**What either answer gives.**
| Answer | Effect |
|---|---|
| `R_polar=W` | the critical curve is one scalar per aperture: every window result (two-weight membership, plastic windows, Markov range, window growth `≥c₀e^{6a}`) is a critical-curve result; HF, SRT, AIP, AHD, CHT reduce to window positivity at every aperture; the pole needs no separate treatment |
| `R_polar<W` | a pole defect exists: an explicit window test whose pole charge is not paid below its own threshold; window routes cannot reach the critical curve without a pole mechanism, and the defect is a new invariant of Σ |

**Why this question.** It is the last method gap of the Σ core after the compactness passage closed; it is an identity between two internal thresholds, both `⊤` under RH, implying nothing about the zeros at finite values; its first step is a variational problem on explicit quadratic forms (window pencil, pole source `S`, cost `D(R)`) with the charged-limit machinery already in Lean; its obstacle is uniformity of the pole charge of near-extremal tests in the window length `A`.

**Tests.** T1: RH gives both `=⊤`; neither value implies quasi-RH. T2: an identity of thresholds. T3: the table. T4: the certified band is finite; the question is at every ratio below `W`. T5: n/a (identity). T6: variational, unrefuted. T7: moves Σ135, B101, B104, B6. T8: internal identity; first step and obstacle named.

**Limit.** It decides the shape of the Σ core, not its sign: RH remains `W=⊤`.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Thick crude count (B110) | the crude step of the curve proof over ℤ; gives AAL | fails: contains AAL | — |
| Depth density `o(T)` (B57) | typical-height layer of seven routes | fails: ≈ 100% of zeros near the line | asymptotic |
| Constant-precision first return (B97) | sign-free producer (§2.6) | fails: past VK | large heights only |
| Rankin–Selberg noncancellation (B109) | completes the cusp-energy receiver | open as to difficulty | adds a receiver |
| Carriers beyond finite volume (B118′, §2.8) | decides the geometric family | passes | geometry only |

## 2.5 Breakthrough question below AAL, RH and quasi-RH: how much functional equation does a finite layer cost?

**Why not a zero law.** On configurations the dial is strict, `AAL ⊊ LinAt C ⊊ (ZAL⇒RH) ⊊ B13` [L]; every transport law, linear slope and `ZAL⇒RH` contains B13. A T8 question below AAL is a question about the AAL mechanism. Five theorems leave one ingredient, Euler product and FE together (§1.3); §3 asks whether the FE is completely rigid on Euler products. This section is its finite-layer face.

**The question (B84).** *What is the smallest integrable FE defect of a countable Beurling system other than the rational primes that carries a finite nonempty off-line layer?* The defect is the corpus one: `E(s)−E(1−s)=−β(Γ_ℝ(s−1)−Γ_ℝ(−s))+Γ_ℝ(s)g(Im s/2)` on `Re s=½` with `Γ_ℝζ_B=E+βΓ_ℝ(s−1)` on `Re s=3/2`, and `D=∫‖g‖`. Defect `≤1/6400` forces the rational primes; defect `M` fixes the primes up to height `≍M^{−½}` [L]. So `D_layer≥1/6400`; is it finite?

**What a finite-defect fake must look like [D].** On the line, up to the pole term, `|g|=2|ζ_B(½+it)||sin(arg ζ_B(½+it)+θ(t))|` with `θ` the Riemann–Siegel phase. Integrability forces either phase-locking to `θ`, which by the argument principle gives about `(T/2π)log(T/2π)` zeros up to height `T`, or integrability of `ζ_B` on the line. Hence:
- the corpus one-offs (continuous, discrete, integer-norm) have infinite defect: `ζ_c→1` on vertical lines and they have no critical zeros; the discrete one-off even blows up at `s=½` [L];
- `ζ·R` with `R` an Euler-factor ratio absolutely convergent on the line has `|g|=2|ζ(½+it)|e^{Re D}|sin Im D|`, `D=log R(½+it)` almost periodic; integrability forces `D` real on the line, hence `R` constant (with an exact FE this is the subcritical Euler rigidity [L]).

A finite-layer fake with finite defect therefore needs Riemann–von Mangoldt-many critical zeros and an Euler discrepancy from the rational primes that is not absolutely convergent on the critical line.

**First step.** Construct, or exclude, a countable system whose primes agree with the rational primes up to height `M^{−½}` and differ beyond it at a positive proportion of primes in every dyadic range, with discrepancy conditionally convergent on the line and defect `O(M)`. Named obstacle: integrability of `ζ(½+it)·Im D(½+it)` for a conditionally convergent prime series `D`.

**What either answer gives.**
| Answer | Effect on AAL research |
|---|---|
| finite `D_layer` | the FE excludes finite layers only by pinning the system: every B13/AAL argument must use the exact FE of ζ; stability, deformation and compactness arguments in spaces of Euler products are dead; the first fake class with Euler product, near-FE and Riemann–von Mangoldt count exists for testing every receiver |
| `D_layer=∞` | finite defect and a finite layer are incompatible off ζ: a stable Euler–FE exclusion exists in the non-ζ class, the first theorem of the type B112 asks for |

**Tests.** T1: method question. T2: the quantity `D_layer`. T3: the table. T4: no finite rung. T5: calibrated on the fakes. T6: conditionally convergent discrepancies; unrefuted. T7: moves Γ73, Γ124, Γ145, B84, B103. T8: construction problem with one named obstacle.

**Limit.** It decides the form of the mechanism, not AAL.

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

**What the hyperbolic carrier cannot be [S].** Only the rotations `diag(a,a⁻¹)`, `|a|=1`, about the degree geodesic preserve the archimedean profile on integer degrees. The free-space Robin constant is `(1−s)/2` (`¼` at `s=½`), constant along the geodesic, while the prime self-intersection `((p−2)/(p−1))log p` is unbounded: no constant Robin shift is the arithmetic counterterm. A discrete group of finite covolume either drives infinitely many degrees into thin parts or folds pairs of unbounded ratio to arbitrarily small distance, where every invariant kernel with a Newtonian pole is unbounded on prime pairs although the archimedean profile tends to `0`; at a cusp the Poincaré series of `G_{1/2}` diverges and the continued zero mode is `−min^{½}max^{3/2}/Λ`, of order `n²` on the diagonal. On atoms no `O(log n)` diagonal completes Weil's off-diagonal (a diagonal `≥N(log N−17)/8` is forced in each dyadic block). The finite-volume Bianchi question (former B118) is answered negatively for the vertical embedding.

**Geometric question.** *Which hyperbolic carriers survive the thin–thick obstruction?* Precisely (B118′):
1. **Every finite-volume carrier.** For every lattice `Γ⊂SL₂(ℂ)` and every embedding `n↦w_n` of the degrees into `Γ\ℍ³`, does the automorphic Green function at `s=½` fail to reproduce archimedean Frobenius plus torsion off the diagonal? An infinite point set in finite volume enters a cusp or accumulates in the compact part, and a sparse convergent subsequence gives pairs of unbounded ratio at small distance [D]; the cusp needs the zero-mode growth for general embeddings.
2. **Twisted infinite-volume carriers.** Untwisted image sums `Σ_{γ≠1}G_{1/2}(z_m,γz_n)` are positive at every pair, while the torsion kernel vanishes off prime-power ratios, so no discrete group carries the torsion untwisted [D]. For a geometrically finite group of infinite covolume with critical exponent `δ<½` (so the Poincaré series of `G_{1/2}` converges) and a unitary character `χ`, can `Σ_{γ≠1}χ(γ)G_{1/2}(z_m,γz_n)` equal the torsion kernel `Λ(n/m)(n/m)^{−½}`?

**What either answer gives.** Negative in both: no hyperbolic 3-manifold carries Weil's form; the archimedean fibre is `ℍ³` with one marked geodesic and `U(1)` symmetry, the finite places are not geometric images, and the intersection routes (SOSZ, ACS, HF, AE, HHAC) must carry the primes on `ℙ¹_ℤ` with the sign in a coupled damping (B88). Positive in 2: Weil's form is the twisted Green energy of an infinite-volume hyperbolic 3-manifold, its sign a statement about the resonances of that manifold at `s=½` (Patterson–Sullivan theory): a scattering geometry, the geometric face of the horizon picture of §2.7.

**Tractability.** Part 1 is the corpus dichotomy for general embeddings. Part 2 is an identity test with explicit ingredients: the support of the torsion kernel, convergent Poincaré series at `s=½`, characters of Schottky groups. Neither part is a named problem.

**Topological question.** *Is there an orientation cover over the integers?* Precisely (B120): is there a natural double cover — of the prime complex, or of a model of `{1,…,N}` — whose fibre over a squarefree `n` has `1+μ(n)` points (or `1+λ(n)` over every `n`), defined by a trace discriminant attached to `n`, and a self-map of the cover with bounded local indices whose Lefschetz number is the total count? Over `𝔽_q[T]` the factor-trace orientation cover exists (Stickelberger), and its total count is `qⁿ` exactly: Möbius cancellation is the statement that the cover has no middle cohomology [L]. Over ℤ the prime-vertex indices already localize `1−M(N)` with unbounded indices [L]; an orientation cover would replace unbounded indices by a trace on a cohomology of weight `½`, giving `|M(N)|≪N^{½+ε}`. First rungs: `𝔽_q[T]` [L]; `ℤ[ω]`, where the cubic Gauss coefficient is a cubic orientation [L]; Jacobi symbols, which are signs of multiplication permutations (Zolotarev) [C].

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Heights over number fields give central-value signs, not off-line zeros [D].

## 2.9 New field for RH: arithmetic Lefschetz–Stepanov theory

**Goal.** RH, with ZAL and AAL together, by completing the curve proof over ℤ.

| Aspect | Content |
|---|---|
| What it is about | Making the integer degrees of Spec ℤ behave like the degrees `n` of `F^n` on a curve over `𝔽_q`. `c_B(log n)=Γ_1·Γ_n` becomes a fixed-point count of a degree-`n` Frobenius. Stepanov's auxiliary-polynomial bound is proved for that count, with integrality in the role of `x^q=x`. |
| What it would be like | Weil's proof on `C×C` run at infinite rank. An exact Lefschetz formula for each `Γ_n` comes first, then a crude bound from an auxiliary function, then the free self-improvement. It is analytic number theory organized as algebraic geometry: every estimate is an intersection number, every bound an auxiliary function. |
| Criteria it must meet | Reproduce Stepanov–Bombieri on curves over `𝔽_q` as its finite-rank case. Give the crude bound with a constant `K` at every integer degree, or on the squares. Use the Euler product and the FE (fail on one-offs, `cosh` models and the heat family). Beat the precision cap `J≤e²r log N+log(1/δ)` by exact vanishing, not by approximation. |
| Questions it must answer | What is the degree-`n` Frobenius of Spec ℤ as a correspondence, and what are its fixed points? What is the Lefschetz identity for `Γ_1·Γ_n` with its main term? Which auxiliary integer Dirichlet polynomials vanish at all fixed points, to what order, of what degree? When does integrality force a `δ`-small auxiliary to vanish exactly at a return of the prime orbit? |
| Tools it aims to develop | Siegel lemmas for Dirichlet polynomials on smooth numbers; zero estimates in many logarithms, uniform in their number; an integrality amplifier (small integer auxiliaries at returns are divisible); a Lefschetz fixed-point form of Frobenius-graph intersections; Stepanov counting `#fixed·J≤deg A`. |
| Objects | Smoothed Frobenius graphs `Γ_n` and their integer-degree planes; the scaling surface and its zonotope Hodge index; Weil towers and thick sets of levels; returns of the prime orbit; integer auxiliary Dirichlet polynomials; the genus `c_B(0)/2`. |
| Language | degree, Frobenius graph, fixed point, Lefschetz number, auxiliary polynomial, order of vanishing, height of an auxiliary, return, integrality amplifier, crude bound, self-improvement. |
| Mechanisms | Built on: Turán–Vandermonde elimination at the exceptional rank; Lipschitz self-improvement at integer degrees (`K` ⇒ genus); Hodge index by counting on the zonotope; EAHT divisibility. To discover: an exact Frobenius over ℤ (the corpus has only approximate returns and one exact fixed point per prime); exact vanishing through integrality at many-prime returns. |

**Main conjecture (arithmetic Stepanov bound).** `|c_B(log n)|≤K` for every integer `n≥1`, or for every square.

**Route.** (1) [L] Any constant `K` at every integer degree is RH; squares suffice. (2) Lefschetz identity for `Γ_1·Γ_n`. (3) Auxiliary `A_n` vanishing to order `J` at the fixed points. (4) Integrality amplifier lifting the precision cap. (2)+(3)+(4) ⇒ crude bound ⇒ RH.

**Milestones.** M1 Lefschetz identity on the smoothed graphs. M2 amplifier at returns of `k` fixed primes, order `J≫k log N`. M3 amplifier with `k→∞` at the rate the squares need. M4 `|c_B(log k²)|≤k^{2σ}` for one `σ<½` (zero-free strip). M5 constant `K` (RH).

## 2.10 New field for AAL: Euler–FE transport theory

**Goal.** Prove AAL (`Θ=Θ∞`), so that ZAL gives RH; or build the counterexample class that decides the falsification branch.

| Aspect | Content |
|---|---|
| What it is about | The functional equation as a dynamics on heights, coupled across scales by the Euler product: how a reflection `s↦1−s̄` and a positive prime measure together force an exceptional zero to recur at every larger height. |
| What it would be like | A rigidity theory of almost-periodic oscillations under a reflection and a positivity constraint. The rigid ¬AAL world (one isolated top, one finite oscillation of `ψ`) plays the role of a hypothetical counterexample, and theorems take it apart by transport. It resembles ergodic rigidity (measure classification) and Hamburger-type uniqueness more than estimates. |
| Criteria it must meet | Use the Euler product and the FE together and at two scales, so that it fails on the heat family, the `cosh` models, the one-offs and Wolff towers [L]. Act stably or by exact identity, as decided by B122 (§3). Reduce to the local-squares purity theorem at finite rank. Prove transport at the same depth (`η=0`), not near-full tail events. |
| Questions it must answer | How does theta modularity transform the oscillation `x^ΘT(log x)`? Why must a positive Euler product that continues to ℂ carry its atoms by zeros, and how does that couple the top to the critical zeros? What forces recurrence at larger heights: the resonant tower at `π/γ`, Poisson reciprocity, or the Euler factorization of the reflected side? What does a finite layer cost in FE defect? |
| Tools it aims to develop | An FE-to-transport operator (B112); quantitative almost periodicity of the rigid oscillation; resonant-tower identities coupling height `γ` to `(2k+1)γ`; a defect calculus for conditionally convergent prime discrepancies; replication theorems ("one top ⇒ infinitely many tops at the same depth"). |
| Objects | Zero configurations and the dial `(Θ,Θ∞)`; the rigid ¬AAL world; Euler heads and tails; returns; theta and its reflection; Beurling systems with integrable FE defect; resonant towers; one-offs as calibration. |
| Language | transport, replication, isolated top, rigid oscillation, reflection, two-scale coupling, FE defect, layer cost, depth, resonant base. |
| Mechanisms | Built on: AAL ⇔ zero transport ⇔ tail transport; the strict dial and quantifier collapse; FE rigidity at defect `1/6400` and stability up to height `M^{−½}`; subcritical Euler rigidity; local squares at finite rank. To discover: the replication law, i.e. how the FE turns a height reflection into vertical transport. |

**Main conjecture (replication law).** A positive Euler product satisfying Riemann's FE cannot carry an isolated almost-periodic oscillation of `ψ` at exponent `Θ>Θ∞`; any top zero recurs at every larger height at the same depth.

**Route.** (1) [L] AAL ⇔ transport; ¬AAL is rigid. (2) The theta reflection maps the top oscillation to exponent `1−Θ`. (3) Positivity between atoms forces the critical zeros to reproduce the reflected oscillation at every scale. (4) Coherent reproduction needs zeros at depth `Θ−½` above every height ⇒ AAL.

**Milestones.** M1 complete FE rigidity or the fake class (§3). M2 `D_layer=∞` in the finite-defect class (§2.5). M3 one quartet of ζ replicates (`k=1`). M4 `LinAt C` for one `C`. M5 AAL.

## 2.11 New field for RH without positivity: transcendence theory of the prime orbit

**Goal.** RH through ZAL and AAL using only Diophantine approximation, integrality, Turán power sums, Jensen and Rouché.

| Aspect | Content |
|---|---|
| What it is about | The prime orbit `t↦(t log p)_p` on the infinite torus as a Diophantine object. Quantitative independence of the logarithms of the primes is the engine; exact vanishing through integrality, where Rouché only approximates, is the output. |
| What it would be like | Baker theory carried to infinitely many logarithms and joined to the analytic theory of Dirichlet polynomials. Proofs are auxiliary-function arguments (construct, extrapolate, apply a zero estimate) whose conclusions are bounds for prime sums, not irrationality statements. |
| Criteria it must meet | Never use a sign, a spectral decomposition or a positivity. Reproduce Stepanov over `𝔽_q` (no returns to fear there) as the degenerate case. Pass the two-prime case (continued fractions) and the fixed-`k` case (Baker–Wüstholz). Supply what the sign-free curve proof lacks: a producer for the crude step beyond the precision cap, Chebyshev (integrality) and VK (exponential sums). |
| Questions it must answer | How early can the primes `≤y` return to `δ`-precision, and how early can a heavy subset? How does the lower bound for linear forms in `k` logarithms depend on `k`, and can it be taken uniform for `k≍π(y)`? Which auxiliary integer polynomials on smooth numbers survive the passage from approximate to exact vanishing? How does Turán's power-sum method give ZAL on the finite-rank remainder of `ψ`? |
| Tools it aims to develop | Linear forms in many logarithms with explicit dependence on their number; Schneider–Lang extrapolation along the prime orbit; Turán's second main theorem on thick sets of levels; Poisson, theta, Farey and Dedekind reciprocity as sign-free forms of the FE acting on heights. |
| Objects | The infinite torus and the prime orbit; return times `R(y,δ)`; heavy subsets; frozen polynomials on smooth numbers; integer auxiliaries; power sums `Σb_jz_j^ν`; the finite-rank remainder of `ψ`. |
| Language | return, precision, heavy subset, freezing, auxiliary, extrapolation, zero estimate, power sum, exceptional rank, reciprocity. |
| Mechanisms | Built on: proportional saving ⇔ no early heavy return; Vandermonde elimination at the exceptional rank; the finite-rank Chebyshev exponent `Θ∞`; integrality (small integer auxiliaries are divisible). To discover: an integrality mechanism at many-prime returns, where every prime has its own exact fixed point but no two share one. |

**Main conjecture (quantitative Kronecker for the primes).** For fixed `δ∈(0,1)` the first `δ`-return of all primes `≤y`, and of every heavy subset, occurs after `exp(y^c)` (B97).

**Route.** (1) [L] Proportional saving ⇔ no early heavy return; sign-free elimination on thick sets. (2) Main conjecture ⇒ proportional saving at all heights (B46) ⇒ crude bound on a thick set ⇒ AAL. (3) Turán on `ψ−x` modulo finite exponential sums, with return bounds on the long sums ⇒ ZAL. (4) ZAL ∧ AAL ⇒ RH [L].

**Milestones.** M1 two primes [L]. M2 linear forms in `k≍(log y)^A` logarithms with explicit `k`-dependence. M3 `log R(y,δ)≥(log y)²` (past VK). M4 `log R(y,δ)≥y^c`. M5 sign-free ZAL.

## 2.12 New field for RH as AdS physics: arithmetic holography of the modular horizon

**Goal.** RH as universal damping: every resonance of the mirror-even channel of the modular horizon decays at rate `¼` (⇔ RH [L]).

| Aspect | Content |
|---|---|
| What it is about | A holographic dictionary between three objects: the modular horizon `SL₂(ℤ)\`(Rindler wedge of AdS₄), whose resonances are the zeros; Euclidean AdS₃, where the archimedean place is a worldline with `Δ=½`; and a confined dual whose normal modes are real. RH becomes the statement that the horizon is the modular image of a confined system. |
| What it would be like | AdS₃ gravity in which the BTZ black hole and thermal AdS₃ are S-dual. Quasinormal decay rates are kinematics of real frequencies under the modular map, and the arithmetic of ℤ enters through the Poincaré sum over `SL₂(ℤ)`. Theorems are identities between partition functions plus unitarity of the confined side. |
| Criteria it must meet | Define the confined system from the archimedean place and the primes alone, never from the zeros (otherwise it is a Hilbert–Pólya operator). Avoid the excluded realizations: internal, vacuum-fixing and half-sided Borchers clocks. Fail on graph black holes with `t²>4q` through the companion. Reproduce universal decay `e^{−t/4}`, the horocycle rate `y^{¾−ε}` and the Narain AdS₃ average. |
| Questions it must answer | Which confined system has the worldline modes `½+2k` as its free part and primes as interactions at times `log n`? Which modular map sends its Euclidean correlators to the mirror-even response? Which conformal weight fixes the lowest tower at rate `¼`? Why does arithmeticity (no second place) make the confined side unitary? |
| Tools it aims to develop | Arithmetic S-duality for Poincaré sums of confined seeds; Rademacher expansions with arithmetic poles; Krein-space holography for the mirror-even channel; Rankin–Selberg noncancellation for one cavity mode (B109). |
| Objects | `ℍ³` as Euclidean AdS₃ with the worldline `{(0,0,y)}` and the scalar `m²=−¾` in quantizations `Δ=½,3/2`; the modular horizon with its mirror-even channel and odd cavity; graph black holes and oscillator banks; Eisenstein series as Poincaré sums of `y^s`; the Narain partition function; the Hecke clock `U(log n)`. |
| Language | worldline, normal mode, quasinormal mode, ringdown, S-duality, confined seed, Poincaré sum, mirror channel, cavity, universal damping, Hecke clock. |
| Mechanisms | Built on: `ℍ³` Green-function identity of the archimedean Frobenius; ringdown rate = zero-free width; partner standard forms exist iff damped; oscillator-bank positivity iff strictly stable; in a GNS realization of `Q` the Hecke clock has point spectrum. To discover: the modular confinement map, a kinematic origin of the rate `¼`. |

**Main conjecture (modular confinement).** The mirror-even channel is the modular image of a unitary confined system built from the worldline modes and prime interactions; every resonance `ρ/2` is the image of a real normal mode, with decay `¼`.

**Route.** (1) [L] decay `¼` ⇔ RH; ringdown = width; the Hecke clock needs point spectrum. (2) Confined system: Fock space over worldline modes with prime vertices, self-adjoint by construction. (3) Modular map: Poincaré sum over `SL₂(ℤ)` of the confined seed. (4) Kinematic damping ⇒ rate `¼` ⇒ RH.

**Milestones.** M1 archimedean sector (`½+2k` ↦ Gamma-pole lattice). M2 one damped graph black hole as the image of a finite oscillator bank. M3 a Narain confined seed carrying the arithmetic poles. M4 any positive universal decay rate (zero-free strip). M5 rate `¼` (RH).

## 2.13 New field for RH as topology or geometry: hyperbolic Arakelov theory of Spec ℤ

**Goal.** RH as a Hodge index theorem on an arithmetic surface whose archimedean fibre is `ℍ³` with the dilation geodesic; in the topological branch, as the vanishing of a middle cohomology of an orientation cover over ℤ.

| Aspect | Content |
|---|---|
| What it is about | Building the surface `S=(Spec ℤ×Spec ℤ)_{ℍ³}` only as far as Weil's proof needs it: divisors (Frobenius graphs at integer degrees), an intersection pairing (finite part on `ℙ¹_ℤ`, archimedean part as `ℍ³` Green functions at `s=½`), a diagonal given by a locked coupled damping, Riemann–Roch, and Hodge index. Topologically: Möbius as the point defect of a cover, `M(N)` as a Lefschetz number. |
| What it would be like | Arakelov geometry with a three-dimensional hyperbolic fibre instead of Green currents on a Riemann surface, and without a quotient: the fibre is `ℍ³` with one marked geodesic and `U(1)` symmetry [S]. The diagonal self-intersection is a coupled damping of two divergent channels that lock in the ultraviolet [S], not a counterterm. Topology as in étale cohomology: counts as traces, cancellation as vanishing. |
| Criteria it must meet | Reduce to the zonotope Hodge index and to Castelnuovo–Severi on `C×C` over `𝔽_q`. Reproduce the `ℍ³` identity of the archimedean Frobenius, the plastic sign law, the atomic diagonal `≥N(log N−17)/8`, the genus `c_B(0)/2` of smoothed pairs, `Σ index=1−M(N)` and the Stickelberger cover over `𝔽_q[T]`. Never take a sign from a counterterm; no finite-volume quotient. |
| Questions it must answer | Which Hilbert space carries the causal jet waves and the twisted torsion energies together, with locked divergences? What are the sheaves whose Euler characteristics are the genera `N log N` and `c_B(0)/2`? Which class is ample (the rank-two pole)? Does a twisted infinite-volume Green function carry the torsion (B118′)? Which trace discriminant defines the orientation cover over ℤ, and what is its cohomology? |
| Tools it aims to develop | Hyperbolic Arakelov Green functions at `s=½`; coupled and locked dampings; Riemann–Roch for Frobenius graphs; Hodge index from Riemann–Roch plus ampleness; orientation covers and signed Lefschetz localization; twisted Green functions of geometrically finite groups. |
| Objects | 𝔽₁-zonotope; `ℙ¹_ℤ` with torsion orbits and radial cyclotomic counts; `ℍ³` with points `z_n=(0,0,n)`, Green functions `G_{1/2},G_{3/2}`; the causal jet bundle on `L²(0,∞)`; smoothed Frobenius graphs; the prime-product complex with prime-vertex dynamics and exits; orientation covers over `𝔽_q[T]`, `ℤ[ω]`, ℤ. |
| Language | half-product, Frobenius graph, archimedean fibre, causal wave, coupled damping, locking, genus of a smoothing, ample class, Hodge index, orientation cover, local index, Lefschetz localization. |
| Mechanisms | Built on: off-diagonal = pole − `ℍ³` Green − torsion [L]; counterterm-free damping ⇔ RH, channel coupling and locking [S]; Hasse–Weil at integer degrees ⇔ RH [L]; prime-vertex localization [L]; Stickelberger [L]. To discover: the locked diagonal and Riemann–Roch on `S`; an orientation cover over ℤ with a weight-`½` cohomology. |

**Main conjecture (hyperbolic Hodge index).** The coupled-damping pairing on divisors of `S` is negative semidefinite on the primitive part; on `Γ_1,Γ_n` it gives Hasse–Weil at every integer degree, i.e. RH.

**Route.** (1) [L/S] the off-diagonal identity, zonotope Hodge index, integer-degree Hasse–Weil ⇔ RH, damping ⇔ RH with locking. (2) Construct the locked diagonal. (3) Riemann–Roch on `S`. (4) Hodge index from Riemann–Roch and the ample pole ⇒ RH. Topological branch: orientation cover with a self-map of Lefschetz number `M(N)` and weight-`½` cohomology ⇒ `M(N)≪N^{½+ε}`.

**Milestones.** M1 carriers beyond finite volume (B118′). M2 a locked presentation on windows of aperture `≤181/250` (every threshold `⊤` there [L]). M3 Riemann–Roch reproducing both genera. M4 Hodge index on windows of growing aperture (§2.4). M5 Hodge index on `S` (RH). Topological: covers over `ℤ[ω]` [L], Jacobi symbols as permutation signs [C], the cover over ℤ, its cohomology.

## 3. The one big question

**Is Riemann's functional equation completely rigid on Euler products?** Precisely (B122): does every countable Beurling system whose zeta satisfies Riemann's FE on the critical line with an **integrable** defect `g` (`∫‖g‖<∞`, the corpus defect of §2.5) have the rational primes as its primes?

**What is proved [L].**
| Fact | Module |
|---|---|
| exact FE forces the rational primes (theta-relation rigidity) | `ArithmeticPositiveDuality/BeurlingRiemannFunctionalEquationRigidity` |
| defect `≤1/6400` forces the rational primes | `ArithmeticPositiveDuality/SmallIntegrableDefectsForceTheRationalPrimes` |
| defect `M` fixes the primes up to height `≍M^{−½}`; prime mismatch below `N` forces defect `>1/(400N²)` | `ArithmeticPositiveDuality/ApproximateFunctionalEquationDeterminesThePrimes`, `BeurlingOneOffZeroCountermodelsAndDefectTradeoff` |
| an Euler-log discrepancy absolutely convergent past the critical line plus the FE forces equality | `SelbergClass/SubcriticalEulerRigidity`, `GammaIndependentEulerRigidity` |
| degree three: FE, principal parts and finitely many coefficients allow right-hand zeros | `SelbergClass/FunctionalEquationTwinsWithRightHandZeros` |
| one-offs of every positive class carry finite layers; none satisfies the FE | `ArithmeticPositiveDuality/TheCriticalLineFirewall`, `ADiscreteBeurlingOneOff` |

**What is deduced [D].** Integrability of the defect forces phase-locking of `ζ_B(½+it)` to the Riemann–Siegel phase, hence Riemann–von Mangoldt-many zeros, unless `ζ_B` is integrable on the line; absolutely convergent Euler perturbations of ζ have non-integrable defect. So a non-ζ system with finite defect differs from the rational primes beyond height `M^{−½}` by a discrepancy that is conditionally convergent on the line (§2.5).

**What an answer does.**
| Answer | Effect |
|---|---|
| **B122 true (complete rigidity)** | The FE is an identity that only ζ satisfies to integrable precision. Every argument that excludes off-line zeros in a neighbourhood of ζ in the space of Euler products is dead: deformation and stability arguments for B13, AAL and `ZAL⇒RH`, FE-to-transport by perturbation (B112), compactness in spaces of approximate Euler–FE functions (B84, B103, B80 within Beurling systems). The Γ core must use exact identities of ζ itself — the integer-degree Hasse–Weil identity, the `ℍ³` identity, local squares — and the firewall table of fakes is complete. |
| **B122 false** | A new fake class exists: Euler products with near-FE and Riemann–von Mangoldt-many critical zeros, the closest objects to ζ the corpus can build. Every receiver of the finite stratum and every AAL mechanism must be tested against it; §2.5 asks whether it carries finite layers; if it never does, a stable Euler–FE exclusion exists and becomes the template for B13. |

**Why this one.**
- **It decides the last unrefuted ingredient.** Positivity, Euler products alone, counting, continuation, FE alone, family-uniform laws and scale-separated statistics are refuted [L]. Whether Euler + FE can act stably decides the strategy of the whole Γ core and of every finite-stratum receiver (HF, HKT, AKLT, CWS, SC, ZCG, WD, LA, FFP reach RH only through B13).
- **It kills or establishes either way.** True: kills the stability strategies of BAG, APD, ZCG, SEL, ACS. False: establishes the calibration class every route must pass.
- **It is tractable.** Rigidity at `1/6400`, the height-`M^{−½}` stability and the subcritical rigidity are in Lean; the open case is one named obstacle — conditionally convergent prime discrepancies on the critical line. It is not a famous problem in disguise: neither answer says anything about the zeros of ζ.
- **It has a first rung.** Systems that equal the rational primes up to height `P` and move a positive proportion of primes in every dyadic range beyond `P` by relative amounts `δ_p`: compute the defect as a function of `(P,δ)` and decide whether it can be finite.

| Kind | Best form | T8 verdict | Evidence |
|---|---|---|---|
| Finite stratum | B13 | fails: exceptional-zero problem | [L] |
| Configuration laws | AAL (B83), `ZAL⇒RH` (B111), `LinAt C` (B116) | fail: contain B13 | [L] |
| Tower crude count | B110 | fails: contains AAL | [L] |
| Critical curve | `R_polar=W` (B104, §2.4) | passes; Σ only | [L] |
| FE layer cost | `D_layer` (B84, §2.5) | passes; nested in B122 | [L/D] |
| Geometric carriers | B118′ (§2.8) | passes; geometry only | [S/D] |
| Count, damping | B87, B88 | fail: RH | [L/S] |
| **FE rigidity** | **B122** | **passes; decides the Γ core and the finite-stratum receivers** | **[L/D]** |

### First steps
1. Write the defect of a system equal to the rational primes up to `P`, with primes `p(1+δ_p)` beyond `P`, as `2|ζ(½+it)|e^{Re D}|sin Im D|` plus lower-order terms, and identify the `δ` for which `Im D(½+it)` is small in mean against `|ζ(½+it)|`.
2. Extend the subcritical rigidity from absolutely convergent to conditionally convergent discrepancies with mean-square control on the line.
3. If step 2 fails, build the fake by matching `Im D` to zero along a sparse set of heights and estimating the defect between them.

### Validation
| Test | Verdict |
|---|---|
| T1 | Method question about Euler products; implied by nothing about ζ's zeros. |
| T2 | A stated implication. |
| T3 | The effects table. |
| T4 | No finite rung decides it. |
| T5 | Calibrated on the one-offs (infinite defect) and on ζ (zero defect). |
| T6 | Conditionally convergent discrepancies; unrefuted. |
| T7 | Moves Γ73, Γ124, Γ145, B80, B84, B103, B112. |
| T8 | Passes: not a named problem; first step and obstacle named. |

### Limits
- It decides how the FE can act, not whether ζ has off-line zeros.
- Complete rigidity leaves B13 as a problem about the exact arithmetic of ζ.
- It concerns countable Beurling systems; generalized (continuous) systems with an exact FE are a second axis, tied to positive Fourier-self-dual measures with a gap at `(−1,1)∖{0}`.
